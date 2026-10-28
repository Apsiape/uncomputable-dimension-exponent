"""Toy numerical attack on the complete Delta^0_2 construction (Section 16).

Independent cross-check (second model family). Builds the finite upper-model
histories of the construction for small parameters and checks, block by block,
that every NEW equation is exact on unflagged addresses:

  * zero-test equation for the STOP counter c initialised at R_* (paper equation (5.8):
    r = z + (1/2)(1-z)s, encoding n -> 2^-n);
  * transition of c (decrement on the nonzero branch multiplies by 2);
  * the guarded data holding equation (16.6):  (U*XU - X)(I - Z_+)(I - q_LOAD) = 0;
  * register transitions  U*SU = Z_+ Init(S) + (I - Z_+) Phi_S;
  * CHECK (16.7):  q_CHECK Sigma (I - F) = 0;
  * REJECT (16.7): q_REJECT <= F;
  * contraction of the registers and their two-unitary representation.

Negative controls show each check is live (not vacuous).

The upper-model operators are block diagonal in (address x, fuel q, time t) and
U is the time increment, so (U*XU)(t) = X(t+1) blockwise; a separate small
operator-level check (operator_level.py) confirms this without blockwise
reasoning.

Single-threaded; run with:  python -u toy_classification.py
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import json
import math
import sys
import time
from fractions import Fraction as Fr

import numpy as np

# ---------------------------------------------------------------------------
# convergent, NON-monotone computable rational sequences with certified tails
# ---------------------------------------------------------------------------


class Seq:
    def __init__(self, name, alpha, amp, kind):
        self.name, self.alpha, self.amp, self.kind = name, alpha, amp, kind

    def a(self, s):
        if self.kind == "harmonic":
            dev = self.amp / (s + 1)
        else:  # geometric
            dev = self.amp / (2 ** s)
        v = self.alpha + (dev if s % 2 == 0 else -dev)
        return min(Fr(1), max(Fr(0), v))

    def tail(self, s):
        """sup_{t >= s} |a_t - alpha| (exact, the deviation is decreasing)."""
        return self.amp / (s + 1) if self.kind == "harmonic" else self.amp / (2 ** s)


def certified_exists_greater(seq, j, ell, horizon=4000):
    """C(j,w): exists s >= j with a_s > ell.  Returns (truth, certificate)."""
    for s in range(j, j + horizon):
        if seq.a(s) > ell:
            return True, ("witness s", s)
    if seq.alpha + seq.tail(j + horizon) <= ell:
        return False, ("tail bound", j + horizon)
    raise RuntimeError("could not certify C(j,w)")


def certified_forall_greater(seq, m, u, horizon=4000):
    """forall s >= m: a_s > u.  Returns (truth, certificate)."""
    for s in range(m, m + horizon):
        if not seq.a(s) > u:
            return False, ("counterexample s", s)
    if seq.alpha - seq.tail(m + horizon) > u:
        return True, ("tail bound", m + horizon)
    raise RuntimeError("could not certify stopping condition")


# ---------------------------------------------------------------------------
# toy gate presentations (projection presentations, integer coefficients)
# ---------------------------------------------------------------------------

P0 = np.array([[1.0, 0.0], [0.0, 0.0]])
PP = np.array([[0.5, 0.5], [0.5, 0.5]])


def pres_mub():
    """two projections with g0 g1 g0 = g0/2, g1 g0 g1 = g1/2 (true, dim 2)."""
    rels = [[(2, (0, 1, 0)), (-1, (0,))], [(2, (1, 0, 1)), (-1, (1,))]]
    return 2, rels, [P0, PP]


def pres_edge2col():
    """2-colouring of one edge, synchronous, one family (true, dim 1)."""
    rels = [[(1, (0,)), (1, (1,)), (-1, ())], [(1, (2,)), (1, (3,)), (-1, ())],
            [(1, (0, 2))], [(1, (2, 0))], [(1, (1, 3))], [(1, (3, 1))]]
    wit = [np.eye(1) * v for v in (1.0, 0.0, 0.0, 1.0)]
    return 4, rels, wit


def pres_triangle2col():
    """2-colouring of a triangle (FALSE: no model in any dimension, exact or
    approximate: p_a0 = I - p_b0 around an odd cycle forces p = I - p)."""
    rels = []
    for a in range(3):
        rels.append([(1, (2 * a,)), (1, (2 * a + 1,)), (-1, ())])
    for (a, b) in ((0, 1), (1, 2), (2, 0)):
        for c in (0, 1):
            rels.append([(1, (2 * a + c, 2 * b + c))])
            rels.append([(1, (2 * b + c, 2 * a + c))])
    return 6, rels, None


def G(j):
    return "w" * j + "D" + "W" * j


def pack(m, rels):
    """R(A): packing equations of Lemma 15.2 plus substituted relations, each
    expanded into repeated signed monomials (words over D,E,W,w=W*)."""
    out = []
    out.append([(1, "W" * j + "E" + "w" * j) for j in range(m)] + [(-1, "")])
    for j in range(m):
        out.append([(1, "E" + G(j)), (-1, G(j) + "E")])
    for rel in rels:
        terms = []
        for coeff, idx in rel:
            word = "E" if len(idx) == 0 else "".join("E" + G(i) + "E" for i in idx)
            terms += [(1 if coeff > 0 else -1, word)] * abs(coeff)
        out.append(terms)
    return out


def bexp(rel):
    return max(0, math.ceil(math.log2(len(rel))))


def packed_witness(m, wit):
    d = wit[0].shape[0]
    D = np.zeros((m * d, m * d))
    for j in range(m):
        D[j * d:(j + 1) * d, j * d:(j + 1) * d] = wit[j]
    E = np.zeros((m * d, m * d))
    E[:d, :d] = np.eye(d)
    S = np.zeros((m, m))
    for j in range(m):
        S[(j + 1) % m, j] = 1.0
    W = np.kron(S, np.eye(d))
    return {"D": D, "E": E, "W": W, "w": W.T.copy()}


# ---------------------------------------------------------------------------
# lazy operators on the data tensor product (only the factors touched)
# ---------------------------------------------------------------------------

DIMS = {}


class Op:
    __slots__ = ("f", "m")

    def __init__(self, f, m):
        self.f, self.m = tuple(f), m


def scalar(v):
    return Op((), np.array([[float(v)]]))


def lift(op, fids):
    if op.f == fids:
        return op.m
    rest = [f for f in fids if f not in op.f]
    order = list(op.f) + rest
    dims = [DIMS[f] for f in order]
    nrest = int(np.prod([DIMS[f] for f in rest])) if rest else 1
    big = np.kron(op.m, np.eye(nrest))
    if not order:
        return big
    n = len(order)
    perm = [order.index(f) for f in fids]
    big = big.reshape(dims + dims).transpose(perm + [n + i for i in perm])
    D = int(np.prod(dims))
    return big.reshape(D, D)


def union(a, b):
    return tuple(sorted(set(a.f) | set(b.f), key=str))


def mul(a, b):
    f = union(a, b)
    return Op(f, lift(Op(a.f, a.m), f) @ lift(Op(b.f, b.m), f))


def add(a, b, sb=1.0):
    f = union(a, b)
    return Op(f, lift(Op(a.f, a.m), f) + sb * lift(Op(b.f, b.m), f))


def opnorm(a):
    return float(np.linalg.norm(a.m, 2)) if a.m.size > 1 else abs(float(a.m[0, 0]))


def diffnorm(a, b):
    return opnorm(add(a, b, -1.0))


def same_op(a, b):
    return diffnorm(a, b)


# data tuples ---------------------------------------------------------------

DEFAULT = {"D": scalar(0), "E": scalar(1), "W": scalar(1), "w": scalar(1)}


def gate_tuple(fid, pw):
    return {L: Op((fid,), pw[L]) for L in "DEWw"}


def eval_poly(rel, tup):
    b = bexp(rel)
    acc = scalar(0)
    for sign, word in rel:
        mono = scalar(1)
        for L in word:
            mono = mul(mono, tup[L])
        acc = add(acc, mono, sign * 2.0 ** (-b))
    return acc


# ---------------------------------------------------------------------------
# the fixed counter program, as a one-instruction-per-time-step stream
# ---------------------------------------------------------------------------


class World:
    def __init__(self, seq):
        self.seq = seq
        self.cache = {}

    def gate(self, j, p):
        """presentation computed by the program for C(j,w); the TRUTH of C is
        not used by the program, only by the toy's witness bookkeeping."""
        key = (j, p)
        if key in self.cache:
            return self.cache[key]
        ell = Fr(p, 2 ** j)
        truth, cert = certified_exists_greater(self.seq, j, ell)
        if truth:
            m, rels, wit = pres_mub() if j % 2 == 0 else pres_edge2col()
        else:
            m, rels, wit = pres_triangle2col()
        R = pack(m, rels)
        pw = packed_witness(m, wit) if wit is not None else None
        if pw is not None:
            DIMS[key] = pw["D"].shape[0]
            for rel in R:  # the witness really is exact
                r = eval_poly(rel, gate_tuple(key, pw))
                assert opnorm(r) == 0.0, (key, rel)
        g = dict(truth=truth, cert=cert, R=R, pw=pw, m=m)
        self.cache[key] = g
        return g


def stream(world, bits, Rstar, T):
    out = []
    c, j, p = Rstar, 0, 0
    while len(out) < T:
        out.append(("ZT", j, p))
        if c == 1:
            s, u = j, Fr(p + 1, 2 ** j)
            while len(out) < T:
                out.append(("VCOMP", s))
                out.append(("VCMP", s, u))
                if world.seq.a(s) <= u:
                    while len(out) < T:
                        out.append(("REJECT",))
                    break
                s += 1
            break
        g = world.gate(j, p)
        for i in range(2 + j):  # data-independent presentation computation
            out.append(("COMP", j, p, i))
        out.append(("LOAD", j, p))
        for ri, rel in enumerate(g["R"]):
            b = bexp(rel)
            out.append(("CLR",))
            for sign, word in rel:
                out.append(("SETI",))
                for L in word:
                    out.append(("MUL", L))
                out.append(("ACC", sign, b))
            out.append(("CHECK", j, p, ri))
        out.append(("READ", j))
        if j >= len(bits):
            raise RuntimeError("read past supplied bits")
        p, j = 2 * p + bits[j], j + 1
        out.append(("DEC",))
        if c != 1:
            c = 2 * c
    return out[:T]


def interpret(world, ins, unflagged, Rstar, data_override=None):
    """actual initialized history from a reset (the upper-model assignment)."""
    T = len(ins)
    H = []
    c, M, S, tup, tname = Rstar, scalar(1), scalar(0), DEFAULT, "default"
    for t in range(T):
        if data_override is not None:
            tup, tname = data_override(t, ins, tup, tname)
        H.append((c, M, S, tup, tname))
        it = ins[t]
        k = it[0]
        if k == "DEC" and c != 1:
            c = 2 * c
        elif k == "LOAD":
            M, S = scalar(1), scalar(0)
        elif k == "SETI":
            M = scalar(1)
        elif k == "MUL":
            M = mul(M, tup[it[1]])
        elif k == "CLR":
            S = scalar(0)
        elif k == "ACC":
            S = add(S, M, it[1] * 2.0 ** (-it[2]))
        if k == "LOAD" and data_override is None:
            g = world.gate(it[1], it[2])
            if unflagged and g["pw"] is not None:
                tup, tname = gate_tuple((it[1], it[2]), g["pw"]), str((it[1], it[2]))
            else:
                tup, tname = DEFAULT, "default"
    return H


# ---------------------------------------------------------------------------
# the independent checker: every new equation, evaluated as a polynomial
# ---------------------------------------------------------------------------


def zero_test(c):
    """canonical witnesses; returns (z, s, residual).  The residual is the
    least |c - z - (1-z)s/2| over z in {0,1}, s in [0,1]."""
    if c == 1:
        return 1, Fr(0), Fr(0)
    if 0 <= c <= Fr(1, 2):
        return 0, 2 * c, Fr(0)
    # not representable: c in (1/2,1) or outside [0,1]
    best = min(abs(c - 1), abs(c - Fr(1, 2)) if c > Fr(1, 2) else abs(c))
    return 0, Fr(1), best


def sel(it, kind, extra=None):
    if it[0] != kind:
        return 0.0
    if extra is None:
        return 1.0
    return 1.0 if it[1] == extra else 0.0


def phi_M(it, M, tup):
    q_one = sel(it, "SETI") + sel(it, "LOAD")
    out = mul(scalar(q_one), scalar(1))
    q_mul = 0.0
    for L in "DEWw":
        s = sel(it, "MUL", L)
        q_mul += s
        if s:
            out = add(out, mul(M, tup[L]), s)
    rest = 1.0 - q_one - q_mul
    return add(out, M, rest)


def phi_S(it, S, M):
    q_clr = sel(it, "CLR") + sel(it, "LOAD")
    q_acc = 1.0 if it[0] == "ACC" else 0.0
    out = scalar(0)
    if q_acc:
        out = add(add(out, S, 1.0), M, it[1] * 2.0 ** (-it[2]))
    return add(out, S, 1.0 - q_clr - q_acc)


def two_unitary_residual(Sop):
    """paper (15.x): every finite square contraction is (u+v)/2, u,v unitary."""
    A = Sop.m.astype(complex)
    U_, s, Vh = np.linalg.svd(A)
    V0 = U_ @ Vh  # unitary completion of the polar part
    absS = Vh.conj().T @ np.diag(s) @ Vh
    J = absS + 1j * Vh.conj().T @ np.diag(np.sqrt(np.clip(1 - s ** 2, 0, None))) @ Vh
    u, v = V0 @ J, V0 @ J.conj().T
    r1 = np.linalg.norm((u + v) / 2 - A, 2)
    r2 = max(np.linalg.norm(u.conj().T @ u - np.eye(len(A)), 2),
             np.linalg.norm(v.conj().T @ v - np.eye(len(A)), 2))
    return float(max(r1, r2))


def check_history(ins, H, F, Rstar, Ntime, guard_load=True, stats=None):
    """returns dict of maximal residuals over all ordinary and reset
    transitions for every fuel prefix k = 0..Ntime (period 2^k)."""
    T = len(ins)
    r = dict(zt=0.0, ctrans=0.0, ctrl=0.0, data7=0.0, regM=0.0, regS=0.0,
             check=0.0, reject=0, contraction=0.0, init=0.0, two_unitary=0.0,
             n_ordinary=0, n_reset=0, n_load=0, n_check=0, n_check_nonzero_formula=0)
    Init_c, Init_M, Init_S = Rstar, scalar(1), scalar(0)
    for t in range(T):
        c, M, S, tup, _ = H[t]
        it = ins[t]
        z, s, ztres = zero_test(c)
        r["zt"] = max(r["zt"], float(ztres))
        r["contraction"] = max(r["contraction"], opnorm(M) - 1, opnorm(S) - 1)
        if it[0] == "CHECK":
            r["n_check"] += 1
            r["check"] = max(r["check"], opnorm(S) * (1 - F))
        if it[0] == "REJECT" and F == 0:
            r["reject"] += 1
        if it[0] == "LOAD":
            r["n_load"] += 1
        if t % 97 == 0 and S.m.shape[0] > 1:
            r["two_unitary"] = max(r["two_unitary"], two_unitary_residual(S))
        # ordinary transition t -> t+1 (not a reset for fuel k when t+1 < 2^k)
        if t + 1 < T:
            c1, M1, S1, tup1, _ = H[t + 1]
            r["n_ordinary"] += 1
            # c transition, evaluated as the selector polynomial
            qd = 1 if it[0] == "DEC" else 0
            step_c = qd * (z * c + (1 - z) * 2 * c) + (1 - qd) * c
            r["ctrans"] = max(r["ctrans"], float(abs(c1 - step_c)))
            # control branch at the zero test
            if it[0] == "ZT":
                nxt = ins[t + 1][0]
                ok = (nxt == "VCOMP") if z == 1 else (nxt == "COMP")
                r["ctrl"] = max(r["ctrl"], 0.0 if ok else 1.0)
            # Holding equation (16.6): (X_{t+1} - X_t)(1 - Z_{t+1})(1 - qLOAD_t), Z_{t+1}=0 here
            gl = (0.0 if it[0] == "LOAD" else 1.0) if guard_load else 1.0
            if gl:
                for L in "DEW":
                    r["data7"] = max(r["data7"], gl * same_op(tup1[L], tup[L]))
            # registers
            r["regM"] = max(r["regM"], diffnorm(M1, phi_M(it, M, tup)))
            r["regS"] = max(r["regS"], diffnorm(S1, phi_S(it, S, M)))
    # reset transitions: t = 2^k - 1 -> 0 for every fuel prefix k (incl. the
    # cyclic boundary 2^Ntime - 1 -> 0); the guard (1 - Z_+) vanishes there
    c0, M0, S0, _, _ = H[0]
    for k in range(Ntime + 1):
        r["n_reset"] += 1
        r["init"] = max(r["init"], float(abs(c0 - Init_c)), diffnorm(M0, Init_M),
                        diffnorm(S0, Init_S))
    return r


def merge(acc, r):
    for k, v in r.items():
        if k.startswith("n_") or k == "reject":
            acc[k] = acc.get(k, 0) + v
        else:
            acc[k] = max(acc.get(k, 0.0), v)
    return acc


# ---------------------------------------------------------------------------
# moving-window budget (Lemma 16.5)
# ---------------------------------------------------------------------------


def window_budget(b, Nlist):
    out = []
    for N in Nlist:
        x = np.arange(2 ** N, dtype=np.int64)
        v = np.zeros(2 ** N)
        for j in range(N):
            v += ((x >> j) & 1) * 2.0 ** (-j - 1)
        F = (v >= float(b)).astype(np.int64)
        mean = F.mean()
        ext = np.concatenate([F, F[:N]])
        cs = np.concatenate([[0], np.cumsum(ext)])
        win = cs[N:N + 2 ** N] - cs[:2 ** N]
        mx, mn = int(win.max()), int(win.min())
        dev = max(mx - (1 - float(b)) * N, (1 - float(b)) * N - mn)
        out.append(dict(N=N, mean_F=float(mean), exact_mean=float(1 - b),
                        max_window=mx, min_window=mn, k_N=1 + mx,
                        max_dev=float(dev), dev_over_log2N=float(dev / math.log2(N))))
    return out


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------


def bits_of(idx, m):
    return [(idx >> (m - 1 - i)) & 1 for i in range(m)]  # bits[0] = MSB of v


def run_config(name, seq, b, m, Ntime, Rstar=None, label="positive"):
    world = World(seq)
    Rstar = Fr(1, 2 ** m) if Rstar is None else Rstar
    T = 2 ** Ntime
    acc = {}
    info = dict(config=name, label=label, alpha=str(seq.alpha), b=str(b), m=m,
                Rstar=str(Rstar), Ntime=Ntime, classes=0, unflagged_classes=0,
                stop_reached_unflagged=0, verifier_steps_unflagged=0,
                gates_on_unflagged=set(), false_gate_on_unflagged=0)
    for idx in range(2 ** m):
        bits = bits_of(idx, m)
        ell_m = Fr(sum(bt << (m - 1 - i) for i, bt in enumerate(bits)), 2 ** m)
        F = 0 if ell_m < b else 1
        ins = stream(world, bits + [0] * 64, Rstar, T)
        H = interpret(world, ins, F == 0, Rstar)
        r = check_history(ins, H, F, Rstar, Ntime)
        merge(acc, r)
        info["classes"] += 1
        if F == 0:
            info["unflagged_classes"] += 1
            if any(it[0] == "VCOMP" for it in ins):
                info["stop_reached_unflagged"] += 1
                info["verifier_steps_unflagged"] += sum(1 for it in ins if it[0] == "VCMP")
            for it in ins:
                if it[0] == "LOAD":
                    g = world.gate(it[1], it[2])
                    info["gates_on_unflagged"].add((it[1], it[2]))
                    if not g["truth"]:
                        info["false_gate_on_unflagged"] += 1
    gates = sorted(info["gates_on_unflagged"])
    info["gates_on_unflagged"] = [str(g) for g in gates]
    info["ell_b"] = int(np.prod([DIMS[g] for g in gates])) if gates else 1
    info["residuals"] = acc
    return info, world


def stopping_certificate(seq, b, m):
    return dict(dyadic=(b * 2 ** m).denominator == 1,
                forall=certified_forall_greater(seq, m, b))


def main():
    t0 = time.time()
    results = {}
    seq1 = Seq("harmonic", Fr(9, 20), Fr(3, 10), "harmonic")
    seq2 = Seq("geometric", Fr(9, 20), Fr(2, 5), "geometric")
    print("sequence 1 first terms:", [str(seq1.a(s)) for s in range(8)], flush=True)
    print("sequence 2 first terms:", [str(seq2.a(s)) for s in range(8)], flush=True)

    # ---------------- positive runs ----------------
    for name, seq, b, m in (("cfg1", seq1, Fr(3, 8), 4), ("cfg2", seq2, Fr(7, 16), 6)):
        cert = stopping_certificate(seq, b, m)
        print(f"\n[{name}] b={b} m={m} stopping certificate: {cert}", flush=True)
        info, _ = run_config(name, seq, b, m, Ntime=12)
        info["stopping_certificate"] = str(cert)
        results[name] = info
        print(json.dumps(info, indent=1, default=str), flush=True)

    # ---------------- negative controls ----------------
    neg = {}
    # NC1a: guard without the LOAD exemption (Section-15-style invariance)
    world = World(seq1)
    bits = [0, 1, 0, 0]
    ins = stream(world, bits + [0] * 64, Fr(1, 16), 2 ** 12)
    H = interpret(world, ins, True, Fr(1, 16))
    r = check_history(ins, H, 0, Fr(1, 16), 12, guard_load=False)
    neg["NC1a_no_LOAD_exemption_data7"] = r["data7"]
    # NC1b: globally fixed data (one tuple for the whole history)
    worst = []
    for it in ins:
        if it[0] == "LOAD":
            key = (it[1], it[2])
            tupg = gate_tuple(key, world.gate(*key)["pw"])
            Hg = interpret(world, ins, True, Fr(1, 16),
                           data_override=lambda t, ins_, tup, nm, tupg=tupg: (tupg, "global"))
            rg = check_history(ins, Hg, 0, Fr(1, 16), 12)
            worst.append((str(key), rg["check"], rg["data7"]))
    neg["NC1b_global_tuple_check_residual_per_choice"] = worst
    # NC2: stop one level too early (b still dyadic there): verifier rejects
    for name, seq, b, mp in (("cfg1", seq1, Fr(3, 8), 3), ("cfg2", seq2, Fr(7, 16), 5)):
        info, _ = run_config(name, seq, b, mp, Ntime=12, label="NC2 wrong stop depth")
        neg[f"NC2_{name}_m={mp}_reject_on_unflagged"] = info["residuals"]["reject"]
        neg[f"NC2_{name}_certificate"] = str(certified_forall_greater(seq, mp, b))
    # NC3: threshold above alpha (b'=1/2 > alpha=9/20), stop depth 4
    info, _ = run_config("cfg1", seq1, Fr(1, 2), 4, Ntime=12, label="NC3 b>alpha")
    neg["NC3_b_above_alpha_reject_on_unflagged"] = info["residuals"]["reject"]
    # NC4: false gate reached on an unflagged address (R_* = 0, address above
    # alpha): no exact witness; try every candidate tuple we have
    world4 = World(seq1)
    bits4 = [0, 1, 1, 1, 1, 1, 1]  # v = 0.4921875 > alpha
    ins4 = stream(world4, bits4 + [0] * 64, Fr(0), 2 ** 13)
    loads = [(it[1], it[2]) for it in ins4 if it[0] == "LOAD"]
    false_loads = [g for g in loads if not world4.gate(*g)["truth"]]
    first_false = false_loads[0] if false_loads else None
    cands = {"default": DEFAULT}
    for g in loads:
        if world4.gate(*g)["pw"] is not None:
            cands[str(g)] = gate_tuple(g, world4.gate(*g)["pw"])
    rng = np.random.default_rng(1)
    for trial in range(5):
        dd = 12
        Pm = rng.standard_normal((dd, dd)); Pm = Pm + Pm.T
        evals, evecs = np.linalg.eigh(Pm)
        Dm = evecs @ np.diag((evals > 0).astype(float)) @ evecs.T
        Em = evecs @ np.diag((np.arange(dd) % 6 == 0).astype(float)) @ evecs.T
        S6 = np.zeros((6, 6))
        for j in range(6):
            S6[(j + 1) % 6, j] = 1
        Wm = evecs @ np.kron(S6, np.eye(2)) @ evecs.T
        fid = ("rand", trial)
        DIMS[fid] = dd
        cands[f"random{trial}"] = {"D": Op((fid,), Dm), "E": Op((fid,), Em),
                                   "W": Op((fid,), Wm), "w": Op((fid,), Wm.T.copy())}
    nc4 = {}
    if first_false is not None:
        R = world4.gate(*first_false)["R"]
        for nm, tup in cands.items():
            nc4[nm] = max(opnorm(eval_poly(rel, tup)) for rel in R)
    neg["NC4_false_gate"] = dict(gate=str(first_false), min_over_candidates=min(nc4.values()) if nc4 else None,
                                 per_candidate=nc4)
    # NC5: non-dyadic R_* (zero-test equation cannot be exact)
    for Rs in (Fr(3, 10), Fr(5, 7), Fr(3, 4)):
        world5 = World(seq1)
        ins5 = stream(world5, [0, 0, 0, 0] + [0] * 64, Rs, 2 ** 10)
        H5 = interpret(world5, ins5, True, Rs)
        first = next((t, str(H5[t][0]), float(zero_test(H5[t][0])[2]))
                     for t in range(len(H5)) if zero_test(H5[t][0])[2] > 0)
        neg[f"NC5_Rstar={Rs}_first_zero_test_violation(t,c,residual)"] = first
    # NC6: without the holding equation (16.6), time-varying scalar data fake every CHECK of a false gate
    R = world4.gate(*first_false)["R"]
    fake_plan = []
    ok_all = True
    for rel in R:
        forced = sum(sg for sg, wd in rel if wd == "")
        need = -forced
        vals = []
        for sg, wd in rel:
            if wd == "":
                vals.append(1)
            elif need != 0 and sg == (1 if need > 0 else -1):
                vals.append(1); need -= sg
            else:
                vals.append(0)
        ok_all &= (need == 0)
        fake_plan.append(vals)

    def fake_data(t, ins_, tup, nm, state={"rel": -1, "mono": -1, "pos": 0}):
        it = ins_[t]
        if it[0] == "CLR":
            state["rel"] += 1; state["mono"] = -1
        if it[0] == "SETI":
            state["mono"] += 1; state["pos"] = 0
        if it[0] == "MUL" and state["rel"] >= 0:
            # every nonempty word of R(A) contains a D or an E letter, so
            # D = E = v on all its letters gives the monomial the value v
            val = fake_plan[state["rel"]][state["mono"]]
            state["pos"] += 1
            # D,E take the chosen value; W stays 1 (unitary)
            return ({"D": scalar(val), "E": scalar(val), "W": scalar(1), "w": scalar(1)},
                    "fake")
        return (tup, nm)

    # isolate the false gate: build a stream that starts at that gate
    j0, p0 = first_false
    seg = []
    for ri, rel in enumerate(R):
        b_ = bexp(rel)
        seg.append(("CLR",))
        for sign, word in rel:
            seg.append(("SETI",))
            for L in word:
                seg.append(("MUL", L))
            seg.append(("ACC", sign, b_))
        seg.append(("CHECK", j0, p0, ri))
    seg = [("LOAD", j0, p0)] + seg
    H6 = interpret(world4, seg, True, Fr(0), data_override=fake_data)
    r6 = check_history(seg, H6, 0, Fr(0), 0)
    neg["NC6_fake_data_plan_found"] = ok_all
    neg["NC6_fake_data_check_residual"] = r6["check"]
    neg["NC6_fake_data_holding_residual"] = r6["data7"]
    # NC7: perturbed loaded tuple: CHECK sees 2^-b pi(perturbed) exactly
    world7 = World(seq1)
    ins7 = stream(world7, [0, 0, 0, 0] + [0] * 64, Fr(1, 16), 2 ** 12)
    key = next((it[1], it[2]) for it in ins7 if it[0] == "LOAD")
    pw = world7.gate(*key)["pw"]
    pert = {L: pw[L].copy() for L in "DEWw"}
    # replace the second packed generator by the first: g0 g1 g0 = g0 != g0/2,
    # so the perturbed tuple is NOT a witness (reversing D would be one again)
    dd = pw["D"].shape[0] // 2
    pert["D"][dd:, dd:] = pert["D"][:dd, :dd]
    tupP = gate_tuple(key, pert)

    def load_pert(t, ins_, tup, nm):
        if t > 0 and ins_[t - 1][0] == "LOAD" and (ins_[t - 1][1], ins_[t - 1][2]) == key:
            return (tupP, "pert")
        return (tup, nm)
    H7 = interpret(world7, ins7, True, Fr(1, 16), data_override=load_pert)
    maxdev, nonzero = 0.0, 0
    for t, it in enumerate(ins7):
        if it[0] == "CHECK" and (it[1], it[2]) == key:
            S = H7[t][2]
            expect = eval_poly(world7.gate(*key)["R"][it[3]], tupP)
            maxdev = max(maxdev, diffnorm(S, expect))
            nonzero += opnorm(expect) > 0
    neg["NC7_perturbed_tuple_Sigma_minus_formula"] = maxdev
    neg["NC7_perturbed_tuple_nonzero_checks"] = nonzero

    results["negative_controls"] = neg
    print("\nNEGATIVE CONTROLS")
    print(json.dumps(neg, indent=1, default=str), flush=True)

    # ---------------- window budget ----------------
    wb = {}
    for name, b in (("cfg1", Fr(3, 8)), ("cfg2", Fr(7, 16))):
        wb[name] = window_budget(b, [8, 10, 12, 14, 16, 18, 20])
    results["window_budget"] = wb
    print("\nWINDOW BUDGET")
    print(json.dumps(wb, indent=1), flush=True)
    for name in ("cfg1", "cfg2"):
        lb = results[name]["ell_b"]
        b = Fr(results[name]["b"])
        rows = []
        for row in wb[name]:
            N = row["N"]
            ld = 3 * N + row["k_N"] + math.log2(lb)
            rows.append(dict(N=N, log2d=round(ld, 3), four_minus_b_times_N=float((4 - b) * N),
                             excess=round(ld - float((4 - b) * N), 3),
                             log2_ell_b=math.log2(lb)))
        results[name]["log2d_vs_(4-b)N"] = rows
        print(name, "log2 d_N - (4-b)N = log2(ell_b) + window excess (constant in N):",
              [(r_["N"], r_["excess"]) for r_ in rows], "log2 ell_b =", math.log2(lb), flush=True)

    results["elapsed_s"] = round(time.time() - t0, 1)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "toy_results.json")
    with open(out, "w") as fh:
        json.dump(results, fh, indent=1, default=str)
    print("\nwrote", os.path.basename(out), "elapsed", results["elapsed_s"], "s", flush=True)


if __name__ == "__main__":
    main()
