"""Deterministic, single-threaded attacks on Section 15.2 and Lemmas 15.3 and 15.6.

Run: python -B toy_gate.py
Only writes toy-results.json beside this script. No dense global clock tensor
is allocated: clock-controlled operators are checked through their blocks.
"""
import os
for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
             "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[name] = "1"
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
import ctypes
import itertools
import json
import math
from pathlib import Path
import time
import numpy as np

OUT = Path(__file__).resolve().parent
TOL = 2e-7  # Polar decompositions of singular matrices can lose sqrt(eps).
MAX = {}

def check(label, x, tol=1e-11):
    v = float(np.max(np.abs(x))) if np.size(x) else 0.0
    MAX[label] = max(MAX.get(label, 0.0), v)
    assert v <= tol, (label, v, tol)

def graph(n, edges, colouring):
    # Synchronous vertex-colouring presentation: only equal and edge pairs tested.
    ps = [np.array([[float(colouring[v] == c)]], dtype=complex)
          for v in range(n) for c in range(3)]
    rels = []
    for v in range(n):
        rels.append([(1, (3*v+c,)) for c in range(3)] + [(-1, ())])
        for a in range(3):
            for b in range(3):
                if a != b:
                    rels.append([(1, (3*v+a, 3*v+b))])
    for v, w in edges:
        for c in range(3):
            rels.append([(1, (3*v+c, 3*w+c))])
            rels.append([(1, (3*w+c, 3*v+c))])
    return ps, rels

def two_bases():
    # Only (x,x) tested. Cross-question products must NOT be set to zero.
    z = np.diag([1., 0.]).astype(complex)
    x = np.full((2, 2), .5, dtype=complex)
    eye = np.eye(2)
    ps = [z, eye-z, x, eye-x]
    rels = []
    for q in (0, 2):
        rels += [[(1, (q,)), (1, (q+1,)), (-1, ())],
                 [(1, (q, q+1))], [(1, (q+1, q))]]
    return ps, rels

def product(mats, word, dim):
    ans = np.eye(dim, dtype=complex)
    for letter in word:
        ans = ans @ mats[letter]
    return ans

def packed(ps, rels):
    m, d = len(ps), ps[0].shape[0]
    dim = m*d
    D = np.zeros((dim, dim), dtype=complex)
    E = D.copy()
    E[:d, :d] = np.eye(d)
    W = D.copy()
    for j, p in enumerate(ps):
        D[j*d:(j+1)*d, j*d:(j+1)*d] = p
        W[((j+1)%m)*d:((j+1)%m+1)*d, j*d:(j+1)*d] = np.eye(d)
    letters = {"D": D, "E": E, "W": W, "w": W.conj().T}
    # Polynomials are signed lists, with repeated terms for integer coefficients.
    packed_rels = [[(1, tuple("W"*j+"E"+"w"*j)) for j in range(m)]
                   + [(-1, ())]]
    corner_words = [tuple("E"+"w"*j+"D"+"W"*j+"E") for j in range(m)]
    for j in range(m):
        dj = tuple("w"*j+"D"+"W"*j)
        packed_rels.append([(1, ("E",)+dj), (-1, dj+("E",))])
    for rel in rels:
        result = []
        for sign, mon in rel:
            word = sum((corner_words[j] for j in mon), ()) if mon else ("E",)
            result.append((sign, word))
        packed_rels.append(result)
    check("D_projection", D@D-D)
    check("E_projection", E@E-E)
    check("W_unitary", W.conj().T@W-np.eye(dim))
    check("corner_trace", np.trace(E)/dim-1/m)
    for j, p in enumerate(ps):
        v = product(letters, corner_words[j], dim)
        check("corner_recovery", v[:d, :d]-p)
    return letters, packed_rels

def eval_rel(letters, rel):
    dim = letters["D"].shape[0]
    return sum((sign*product(letters, word, dim) for sign, word in rel),
               np.zeros((dim, dim), dtype=complex))

def instructions(rels):
    # A runtime output stream over a FIXED finite alphabet. This is not a
    # machine-code implementation of the universal classical counter machine.
    ops = []
    for rel in rels:
        b = (len(rel)-1).bit_length()
        ops.append(("T0", None))
        for sign, word in rel:
            ops.append(("MI", None))
            ops += [(letter, None) for letter in word]
            ops.append(("ADD", sign*2.**(-b)))
        ops.append(("CHECK", None))
    return ops

def update(M, T, op, letters):
    name, arg = op
    if name == "T0": return M, np.zeros_like(T)
    if name == "MI": return np.eye(len(M), dtype=complex), T
    if name in letters: return M@letters[name], T
    if name == "ADD": return M, T+arg*M
    if name == "IDLE": return np.eye(len(M), dtype=complex), np.zeros_like(T)
    assert name == "CHECK"
    return M, T

def two_unitaries(A):
    l, s, rh = np.linalg.svd(A)
    s = np.clip(s, 0., 1.)
    phase = s+1j*np.sqrt(np.maximum(0., 1.-s*s))
    u, v = (l*phase)@rh, (l*phase.conj())@rh
    check("unitary_register", u.conj().T@u-np.eye(len(A)), TOL)
    check("unitary_register", v.conj().T@v-np.eye(len(A)), TOL)
    check("register_representation", (u+v)/2-A, TOL)
    return u, v

def run_history(name, letters, rels, expect_perfect):
    dim = len(letters["D"])
    ops = instructions(rels)
    # Choose an even depth large enough to reach every CHECK and the idle state.
    N = max(2, (len(ops)+1).bit_length())
    N += N % 2
    length = 1 << N
    assert N <= 16
    Ms = np.empty((length, dim, dim), dtype=complex)
    Ts = np.empty_like(Ms)
    M, T = np.eye(dim, dtype=complex), np.zeros((dim, dim), dtype=complex)
    cache = {}
    tests, nonzero_tests, biggest_check, biggest_norm = 0, 0, 0., 0.
    noncommute = 0.
    for t in range(length):
        Ms[t], Ts[t] = M, T
        for A in (M, T):
            key = A.tobytes()
            if key not in cache:
                cache[key] = two_unitaries(A)
                norm = float(np.linalg.norm(A, 2))
                biggest_norm = max(biggest_norm, norm)
                assert norm <= 1+1e-12
            # Every instantaneous scalar block is scalar times I, even though
            # its scalar value depends on x, fuel and time.
            for scalar in (0., .125, .5, 1.):
                for unitary in cache[key]:
                    check("scalar_commutators", unitary*scalar-scalar*unitary)
        noncommute = max(noncommute, float(np.linalg.norm(M@letters["D"]-letters["D"]@M, 2)))
        op = ops[t] if t < len(ops) else ("IDLE", None)
        if op[0] == "CHECK":
            tests += 1
            residual = float(np.max(np.abs(T)))
            biggest_check = max(biggest_check, residual)
            nonzero_tests += residual > 1e-11
            if expect_perfect: check("unflagged_CHECK", T)
            check("flagged_CHECK", T*0)
        M, T = update(M, T, op, letters)
    # All possible fuel reset periods and all cyclic time transitions, without
    # allocating the full fuel x time x data matrix. A rank-N fuel class includes
    # the all-ones fuel boundary exactly as in E2.
    transitions, cyclic_boundaries, bad_reset = 0, 0, 0.
    for k in range(N+1):
        period = 1 << k
        for t in range(period):
            nxt = (t+1) % period
            if nxt == 0:
                pm, pt = np.eye(dim), np.zeros((dim, dim))
                # Negative control: omitting reset at the cyclic boundary.
                rawm, rawt = update(Ms[t], Ts[t], ops[t] if t < len(ops) else ("IDLE", None), letters)
                bad_reset = max(bad_reset, float(np.max(np.abs(rawm-pm))), float(np.max(np.abs(rawt-pt))))
                cyclic_boundaries += 1
            else:
                pm, pt = update(Ms[t], Ts[t], ops[t] if t < len(ops) else ("IDLE", None), letters)
            check("operator_transition", Ms[nxt]-pm)
            check("operator_transition", Ts[nxt]-pt)
            transitions += 1
    check("operator_initialization", Ms[0]-np.eye(dim))
    check("operator_initialization", Ts[0])
    direct = max(float(np.max(np.abs(eval_rel(letters, rel)))) for rel in rels)
    if expect_perfect: check("packed_relations", direct)
    else: assert nonzero_tests > 0
    return dict(name=name, packed_dimension=dim, relations=len(rels),
                instructions=len(ops), history_depth=N, time_blocks=length,
                fuel_classes=N+1, transitions=transitions,
                cyclic_boundaries=cyclic_boundaries, checks=tests,
                failed_checks_if_unflagged=nonzero_tests,
                largest_CHECK=biggest_check, direct_relation_residual=direct,
                largest_register_norm=biggest_norm,
                distinct_register_matrices=len(cache),
                computed_word_data_commutator=noncommute,
                omitted_reset_residual=bad_reset,
                history_array_bytes=Ms.nbytes+Ts.nbytes)

def rot_right(x, N):
    return (x >> 1) | ((x & 1) << (N-1))

def decoder(x, N):
    if x == 0: return 0, 0., None
    e = 0
    while x % 4 == 0:
        e += 1
        x //= 4
    return int(x % 4 == 1), 2.**(-e), e

def reset(q, t, N):
    k = 0
    while k < N and (q >> k) & 1: k += 1
    return int(t % (1 << k) == 0)

def windows():
    results, masks, checked_starts = [], 0, 0
    largest_discrepancy = 0.
    for N in range(2, 15, 2):
        length = 1 << N
        xx = np.arange(length, dtype=np.int64)
        local_worst = 0.
        for bits in range(1 << (N//2)):
            chosen = [e for e in range(N//2) if (bits >> e) & 1]
            f = np.ones(length, dtype=np.int64)
            for e in chosen: f[xx % 4**(e+1) == 4**e] = 0
            # j=1,...,N: np.roll(f,j)[x] = f(x-j).
            counts = sum(np.roll(f, j) for j in range(1, N+1))
            mean = 1.-sum(4.**(-e-1) for e in chosen)
            check("mask_mean", np.mean(f)-mean)
            discrepancy = float(np.max(np.abs(counts-N*mean)))
            s = int(math.log(N, 4))
            assert discrepancy <= s+2+N/(3*4**(s+1))+1e-12
            local_worst = max(local_worst, discrepancy)
            # Equation (15.2) and L decoder on EVERY address.
            for x in xx[f == 0]: assert decoder(int(x), N)[0] == 1
            masks += 1
            checked_starts += length
        results.append(dict(N=N, masks=1 << (N//2), starts=length,
                            largest_discrepancy=local_worst))
        largest_discrepancy = max(largest_discrepancy, local_worst)
    # A deliberately reversed address interpretation produces long clusters.
    N = 14
    length = 1 << N
    rev = np.array([int(format(x, f"0{N}b")[::-1], 2) for x in range(length)])
    bad = 1-(rev % 4 == 1).astype(int)
    counts = sum(np.roll(bad, j) for j in range(1, N+1))
    return dict(rows=results, masks=masks, total_starting_addresses=checked_starts,
                largest_discrepancy=largest_discrepancy,
                reversed_bits_N=N,
                reversed_bits_discrepancy=float(np.max(np.abs(counts-.75*N))))

def old_register_geometry():
    count_reset = 0
    for N in (2, 4, 6, 8):
        length = 1 << N
        for x in range(length):
            L, R, _ = decoder(x, N)
            p0, p1 = x & 1, (x >> 1) & 1
            e00, e1 = (1-p0)*(1-p1), p0*(1-p1)
            y = rot_right(rot_right(x, N), N)
            Ly, Ry, _ = decoder(y, N)
            check("decoder_L", L-e1-e00*Ly)
            check("decoder_R", R-(1-e00)-.5*e00*Ry)
        for q in range(length):
            for t in range(length):
                z = reset(q, t, N)
                rhs = (1-(q & 1))+(q & 1)*(1-(t & 1))*reset(rot_right(q, N), rot_right(t, N), N)
                check("reset_recursion", z-rhs)
                count_reset += 1
    # Dressing acts only on optional slots; data blocks on a common factor
    # therefore commute with every required fuel/time permutation and A_a.
    # Verify dressed address recursion as a permutation of (address, slot),
    # which represents its action on all optional bit strings exactly.
    dressing_cases = 0
    N = 6
    length = 1 << N
    f = np.array([int(not (x % 4 == 1 or x % 16 == 4)) for x in range(length)])
    k = 1+max(sum(int(f[(x-j)%length]) for j in range(1, N+1)) for x in range(length))
    h = np.concatenate(([0], np.cumsum(f)))
    def dress(x, slot): return (x, (slot+int(h[x]))%k)
    def undress(x, slot): return (x, (slot-int(h[x]))%k)
    def V(x, slot): return ((x+1)%length, (slot+int(f[x]))%k)
    def T(x, slot):
        x, slot = undress(x, slot)
        x = ((x << 1)&(length-1)) | (x >> (N-1))
        return dress(x, slot)
    def Ti(x, slot):
        x, slot = undress(x, slot)
        return dress(rot_right(x, N), slot)
    def X(x, slot):
        x, slot = undress(x, slot)
        return dress(x^1, slot)
    exceptional = []
    for x in range(length):
        for slot in range(k):
            rhs = (x, slot) if not (x&1) else T(*V(*Ti(x, slot)))
            rhs = X(*rhs)
            if x != length-1: assert rhs == V(x, slot)
            else: exceptional.append((V(x, slot), rhs))
            dressing_cases += 1
            # Replacing a diagonal data value d(x) by optional slot permutations
            # leaves d(x) unchanged. A forbidden [data,V] need not vanish.
    # E2's "same optional permutation" assertion is in the D* gauge. For a
    # complementary mask f(0)=1, the physical output slots differ by f(0).
    # The outputs still have orthogonal addresses, and the norm is sqrt(2).
    assert all(undress(*a)[1] == undress(*b)[1] and a[0] != b[0] for a,b in exceptional)
    return dict(reset_basis_points=count_reset, dressing_basis_points=dressing_cases,
                optional_slots=k, physical_boundary_slots_differ=any(a[1] != b[1] for a,b in exceptional),
                boundary_slots_match_in_dressing_gauge=True,
                guarded_boundary_defect=math.sqrt(2)*4.**(-N),
                forbidden_address_shift_commutator_scalar_example=1.)

def common_factor_check(good):
    # Two witnessed cylinders with common data factor C^9 tensor C^8.
    a, b = good[0][0], good[1][0]
    da, db = len(a["D"]), len(b["D"])
    eye = np.eye(da*db)
    blocks = [{k: np.kron(v, np.eye(db)) for k,v in a.items()},
              {k: np.kron(np.eye(da), v) for k,v in b.items()}]
    for mats, (_, rels) in zip(blocks, good):
        for rel in rels: check("common_factor_relations", eval_rel(mats, rel))
        for scalar in (0., .0625, .25, 1.):
            for mat in mats.values(): check("common_factor_coordinate_commutators", mat@(scalar*eye)-(scalar*eye)@mat)
    return dict(common_dimension=da*db,
                data_change_between_cylinders=float(np.linalg.norm(blocks[0]["D"]-blocks[1]["D"],2)))

def schedule():
    # Costs only, so an enormous hypothetical witness does not allocate memory.
    entries = [(0, 4, 1), (2, 8, 2), (1, 7, 3), (3, 1000, 4)]
    rows = []
    for N in (4, 16, 64, 256, 4096, 1048576):
        total, chosen = 0, []
        for e, cost, arrival in entries:
            if arrival > N or e >= N/2 or total+cost > math.isqrt(N): break
            total += cost
            chosen.append(e)
        assert total <= math.isqrt(N)
        rows.append(dict(N=N, selected=chosen, log_size_bound=total,
                         sqrt_budget=math.isqrt(N)))
    return rows

def peak_memory():
    if os.name == "nt":
        from ctypes import wintypes
        class Counters(ctypes.Structure):
            _fields_ = [("cb", wintypes.DWORD), ("faults", wintypes.DWORD),
                        ("peak_working", ctypes.c_size_t), ("working", ctypes.c_size_t),
                        ("peak_paged", ctypes.c_size_t), ("paged", ctypes.c_size_t),
                        ("peak_nonpaged", ctypes.c_size_t), ("nonpaged", ctypes.c_size_t),
                        ("pagefile", ctypes.c_size_t), ("peak_pagefile", ctypes.c_size_t)]
        counters = Counters()
        counters.cb = ctypes.sizeof(counters)
        ctypes.windll.kernel32.GetCurrentProcess.restype = wintypes.HANDLE
        ctypes.windll.psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD]
        ok = ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.windll.kernel32.GetCurrentProcess(),
                                                      ctypes.byref(counters), counters.cb)
        assert ok
        return counters.peak_working
    import resource
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024

def main():
    started = time.perf_counter()
    specs = [("K3_3colourable", *graph(3, [(0,1),(0,2),(1,2)], [0,1,2]), True),
             ("two_noncommuting_bases_tested_diagonal_only", *two_bases(), True),
             ("K4_bad_colouring_FLAGGED", *graph(4, list(itertools.combinations(range(4),2)), [0,1,2,0]), False)]
    history_results, good = [], []
    for name, ps, rels, perfect in specs:
        letters, packed_rels = packed(ps, rels)
        if perfect: good.append((letters, packed_rels))
        history_results.append(run_history(name, letters, packed_rels, perfect))
    results = dict(histories=history_results,
                   common_factor=common_factor_check(good),
                   windows=windows(), geometry=old_register_geometry(),
                   witness_schedule=schedule(), residual_maxima=MAX)
    pz, _, px, _ = two_bases()[0]
    results["negative_controls"] = dict(untested_cross_product=float(np.linalg.norm(pz@px,2)),
                                         noncommuting_original_projections=float(np.linalg.norm(pz@px-px@pz,2)))
    results["elapsed_seconds"] = time.perf_counter()-started
    results["peak_working_set_bytes"] = peak_memory()
    assert results["peak_working_set_bytes"] < 2_000_000_000
    results["thread_settings"] = {n: os.environ[n] for n in ("OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS")}
    results["numpy_version"] = np.__version__
    (OUT/"toy-results.json").write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(results, indent=2))

if __name__ == "__main__": main()
