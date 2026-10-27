"""Driver: evaluate every displayed Section 2/4 relation on the Section 5
flat models of Section 7 of the paper, for even N, and write tables to out/.

usage:  python -u run_e2.py [N ...] [--full N ...] [--ablate N ...]
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import sys
import json
import time
from collections import defaultdict
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e2_model import Model, relations, positivity_checks, PROG, STATES, halting_time  # noqa: E402
from e2_engine import evaluate_many  # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
os.makedirs(OUT, exist_ok=True)


def evaluate_model(m, full=False, log=print):
    rels = relations(m)
    groups = defaultdict(list)
    for i, r in enumerate(rels):
        s = frozenset(r[3].supp) or frozenset("x")
        groups[s if not full else frozenset("xqty")].append(i)
    res = [None] * len(rels)
    for s, idx in sorted(groups.items(), key=lambda kv: len(kv[0])):
        t0 = time.time()
        out = evaluate_many([rels[i][3] for i in idx], m.bits, s)
        for i, o in zip(idx, out):
            res[i] = o
        log(f"    support {''.join(sorted(s)):5s} {len(idx):4d} relations  {time.time()-t0:7.1f}s")
    return rels, res


def status(claim, r, N):
    op = r["opnorm"]
    if op is None:
        return "UNDECIDED"
    if claim == "EXACT":
        return "PASS(exact 0)" if op == 0.0 else "FAIL(nonzero)"
    if claim == "EXACT(series)":
        return "PASS(<=1e-15)" if op <= 1e-15 else "FAIL"
    return "PASS(<=claim)" if op <= claim * 4.0 ** (-N) * (1 + 1e-9) else "FAIL(>claim)"


def summarize(m, rels, res):
    N = m.N
    rows = []
    for (name, grp, claim, _), r in zip(rels, res):
        rows.append(dict(name=name, group=grp, claim=claim, regs=r["regs"], dim=r["dim"],
                         opnorm=r["opnorm"], op_method=r["opnorm_method"],
                         op_x4N=None if r["opnorm"] is None else r["opnorm"] * 4.0 ** N,
                         hs_flat=r["hs_flat"], hs_x4N=r["hs_flat"] * 4.0 ** N,
                         maxabs=r["maxabs"], nnz=r["nnz"], top=r["top"][:3],
                         status=status(claim, r, N)))
    return rows


def model_facts(m):
    N = m.N
    n2 = 1 << N
    halt = m.sidx["halt"]
    # q_halt <= F on every (x, m) table entry, hence on every basis state (x,q,t,y)
    hx, hm = np.nonzero(m.ctrl == halt)
    viol = int(np.sum(m.f[hx] == 0))
    # number of basis states (x,q,t) with q_halt = 1
    kq = m.kq
    nh = 0
    for q in range(n2):
        mm = np.arange(n2) & ((1 << kq[q]) - 1)
        nh += int(np.sum(m.ctrl[:, mm] == halt))
    wins = np.array([sum(m.f[(x - j) % n2] for j in range(1, N + 1)) for x in range(n2)])
    return dict(N=N, KN=m.KN, thetaN=m.thetaN, htimes=m.htimes, k=m.k, wmax=int(wins.max()),
                wmin=int(wins.min()), N_theta=N * m.thetaN, log2dim=3 * N + m.k,
                claimed_log2dim_leading=(3 + m.thetaN) * N, Vorder=m.Vorder,
                flagged_addresses=int(m.f.sum()), qhalt_table_entries=int(len(hx)),
                qhalt_basis_states_xqt=nh, qhalt_le_F_violations=viol,
                positivity=positivity_checks(m))


def fmt(v, w=10):
    if v is None:
        return "-".rjust(w)
    if v == 0:
        return "0".rjust(w)
    return f"{v:.3e}".rjust(w)


def write_table(N, facts, rows, series, tag=""):
    lines = [f"# Section 5 relation defects, N = {N}{tag}", "",
             f"K_N = {facts['KN']}, theta_N = {facts['thetaN']}, k_N = {facts['k']}, "
             f"log2 dim = 3N + k_N = {facts['log2dim']}, (3+theta_N)N = {facts['claimed_log2dim_leading']}",
             f"4^-N = {4.0**-N:.6e}", "",
             "| relation | claim | support | op-norm | op*4^N | flat HS | HS*4^N | nnz | status | top state(s) |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        claim = r["claim"] if isinstance(r["claim"], str) else f"<= {r['claim']:.4g} 4^-N"
        top = "; ".join(f"{v:.2e}@{s}" for v, s in r["top"][:2])
        lines.append(f"| {r['name']} | {claim} | {r['regs']} | {fmt(r['opnorm'])} | {fmt(r['op_x4N'])} | "
                     f"{fmt(r['hs_flat'])} | {fmt(r['hs_x4N'])} | {r['nnz']} | {r['status']} | {top} |")
    lines += ["", "Exact integer check of the series relations (22):", "```", json.dumps(series, indent=1), "```"]
    with open(os.path.join(OUT, f"table_N{N}{tag.replace(' ', '_')}.md"), "w") as fh:
        fh.write("\n".join(lines) + "\n")


def run_N(N, full=False):
    t0 = time.time()
    print(f"=== N = {N} ===", flush=True)
    m = Model(N)
    facts = model_facts(m)
    print(f"  K_N={m.KN} theta_N={m.thetaN} k_N={m.k} dim=2^{3*N+m.k} V order={m.Vorder} "
          f"qhalt states={facts['qhalt_basis_states_xqt']} viol={facts['qhalt_le_F_violations']}", flush=True)
    rels, res = evaluate_model(m)
    rows = summarize(m, rels, res)
    series = m.exact_series_check()
    write_table(N, facts, rows, series)
    nfail = sum(1 for r in rows if not r["status"].startswith("PASS"))
    print(f"  {len(rows)} relations, {nfail} not passing, {time.time()-t0:.1f}s", flush=True)
    out = dict(facts=facts, rows=rows, series=series)
    if full:
        t1 = time.time()
        print(f"  full-space cross-check on xqty (dim 2^{3*N+m.k}) ...", flush=True)
        _, resf = evaluate_model(m, full=True)
        diffs = []
        for (name, *_), a, b in zip(rels, res, resf):
            da = abs((a["opnorm"] or 0) - (b["opnorm"] or 0))
            dh = abs(a["hs_flat"] - b["hs_flat"])
            if da > 1e-12 * max(1, a["opnorm"] or 0) or dh > 1e-12 * max(1e-300, a["hs_flat"]) and dh > 1e-18:
                diffs.append((name, a["opnorm"], b["opnorm"], a["hs_flat"], b["hs_flat"]))
        out["fullspace_mismatches"] = diffs
        out["fullspace_seconds"] = time.time() - t1
        print(f"  full-space: {len(diffs)} mismatches vs support evaluation, {time.time()-t1:.1f}s", flush=True)
    with open(os.path.join(OUT, f"results_N{N}.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    return out


ABLATIONS = [
    ("conj=D*TD", dict(conj="D*TD")),
    ("conj=none", dict(conj="none")),
    ("r0=-1", dict(r0=-1)),
    ("rot=down", dict(rot="down")),
    ("addr=msb", dict(addr="msb")),
    ("time=msb", dict(time="msb")),
    ("fuel=top", dict(fuel="top")),
    ("k=k_N-1", dict(kdelta=-1)),
]


def run_ablations(N):
    print(f"=== ablations, N = {N} ===", flush=True)
    base = {r["name"]: r for r in run_cached(N)}
    summary = {}
    for tag, opts in ABLATIONS:
        m = Model(N, opts)
        rels, res = evaluate_model(m, log=lambda *a: None)
        rows = summarize(m, rels, res)
        bad = [dict(name=r["name"], claim=r["claim"], op_x4N=r["op_x4N"], hs_x4N=r["hs_x4N"],
                    status=r["status"], top=r["top"][:1]) for r in rows if not r["status"].startswith("PASS")]
        summary[tag] = dict(opts=opts, KN=m.KN, k=m.k, n_relations=len(rows), n_fail=len(bad), failing=bad)
        print(f"  {tag:12s}: {len(bad)} of {len(rows)} relations fail", flush=True)
    with open(os.path.join(OUT, f"ablations_N{N}.json"), "w") as fh:
        json.dump(summary, fh, indent=1, default=str)
    return summary


def peak_mem_mb():
    """Peak working set of this process (Windows), in MB."""
    try:
        import ctypes
        from ctypes import wintypes

        class PMC(ctypes.Structure):
            _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                        ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                        ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                        ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                        ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]
        pmc = PMC()
        pmc.cb = ctypes.sizeof(PMC)
        k32 = ctypes.WinDLL("kernel32")
        k32.GetCurrentProcess.restype = wintypes.HANDLE
        gpmi = ctypes.WinDLL("psapi").GetProcessMemoryInfo
        gpmi.argtypes = [wintypes.HANDLE, ctypes.POINTER(PMC), wintypes.DWORD]
        gpmi.restype = wintypes.BOOL
        if not gpmi(k32.GetCurrentProcess(), ctypes.byref(pmc), pmc.cb):
            return None
        return pmc.PeakWorkingSetSize / 2 ** 20
    except Exception:
        return None


_cache = {}


def run_cached(N):
    if N not in _cache:
        m = Model(N)
        rels, res = evaluate_model(m, log=lambda *a: None)
        _cache[N] = summarize(m, rels, res)
    return _cache[N]


if __name__ == "__main__":
    args = sys.argv[1:]
    mode, Ns, full, abl = "N", [], set(), []
    for a in args:
        if a == "--full":
            mode = "full"
        elif a == "--ablate":
            mode = "abl"
        elif mode == "N":
            Ns.append(int(a))
        elif mode == "full":
            full.add(int(a))
        else:
            abl.append(int(a))
    for N in Ns:
        run_N(N, full=N in full)
    for N in abl:
        run_ablations(N)
    print(f"peak working set: {peak_mem_mb()} MB", flush=True)
