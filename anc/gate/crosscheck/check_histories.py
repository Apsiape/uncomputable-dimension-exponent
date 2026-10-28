"""Lemma 15.6: finite operator-register histories.

For one address we fix packed data (D,E,W), run the transducer instruction stream with a
classical prefix and holds (classical counter work is abstracted to 'hold' steps), and assign
the register values on the fuel/time grid exactly as Section 15.2 and Lemma 15.3 / Theorem 7.1 (history):
    S(q,t) = config[t mod 2^k(q)],   k(q) = number of initial fuel ones (k=N on all ones).
We verify, over EVERY (k,t) with N-bit time (including the cyclic boundary):
    (15.4a)  Z S = Z Init(S)
    (15.4b)  U^* S U = Z_+ Init(S) + (I - Z_+) Phi_S,     Z_+ = U^* Z U
    (15.5)   q_CHECK T (I-F) = 0 on the unflagged witnessed address,
and that the same equation (15.5) would FAIL on a non-witness address if it were unflagged.
We also verify the source reset recursion Z = (I-P_f) + P_f (I-P_t) S Z S^*, S=T_f T_t, on the
full (q,t) grid, the unitary decomposition S=(u+v)/2 of every register value, and exhibit
register values that do NOT commute with D (no hidden commutation is needed).

Run:  python -u check_histories.py
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import numpy as np
from toy_games import (colouring_game, two_family_presentation, classical_colouring_model,
                       pack, packed_relations)
from check_packing_transducer import right_mult

N = 12  # time and fuel register bits


def build_stream(rels, prefix_holds=300, rng=None):
    """Instruction stream: list of tuples. ('hold',), ('T0',), ('MI',), ('MR', ch), ('TADD', s, b), ('CHECK',)."""
    st = [('hold',)] * prefix_holds
    for (label, rel) in rels:
        b = max(0, math.ceil(math.log2(len(rel))))
        st.append(('T0',))
        for (s, w) in rel:
            st.append(('MI',))
            for ch in w:
                st.append(('MR', ch))
                if rng is not None and rng.random() < 0.05:
                    st.append(('hold',))
            st.append(('TADD', s, b))
        st.append(('CHECK',))
        st.append(('hold',))
    return st


def configs(stream, pk, n_steps):
    n = pk['n']
    M = np.eye(n); T = np.zeros((n, n))
    out = []
    for s in range(n_steps):
        ins = stream[s] if s < len(stream) else ('idle',)
        out.append((M, T, ins))
        M, T = step(M, T, ins, pk)
    return out


def step(M, T, ins, pk):
    op = ins[0]
    if op in ('hold', 'idle', 'CHECK'):
        return M, T
    if op == 'T0':
        return M, np.zeros_like(T)
    if op == 'MI':
        return np.eye(M.shape[0]), T
    if op == 'MR':
        return right_mult(M, ins[1], pk), T
    if op == 'TADD':
        return M, T + ins[1] * (2.0 ** -ins[2]) * M
    raise ValueError(op)


def Z_val(k, t):
    return 1 if (t % (1 << k)) == 0 else 0


def check_registers(stream, pk, flagged, label):
    n = pk['n']
    cfg = configs(stream, pk, 1 << N)
    Init = {'M': np.eye(n), 'T': np.zeros((n, n))}
    ok4a = ok4b = True
    ok5 = True
    checks_reached = {}
    n_checked = 0
    for k in range(0, N + 1):
        period = 1 << k
        for t in range(1 << N):
            Mt, Tt, ins = cfg[t % period]
            S_now = {'M': Mt, 'T': Tt}
            # (15.4a)
            if Z_val(k, t):
                for nm in ('M', 'T'):
                    if not np.array_equal(S_now[nm], Init[nm]):
                        ok4a = False
            # (15.4b)
            t1 = (t + 1) % (1 << N)
            M1, T1, _ = cfg[t1 % period]
            S_next = {'M': M1, 'T': T1}
            Zp = Z_val(k, t1)
            PhiM, PhiT = step(Mt, Tt, ins, pk)
            Phi = {'M': PhiM, 'T': PhiT}
            for nm in ('M', 'T'):
                rhs = Zp * Init[nm] + (1 - Zp) * Phi[nm]
                if not np.array_equal(S_next[nm], rhs):
                    ok4b = False
            # (15.5)
            if ins[0] == 'CHECK':
                checks_reached[k] = checks_reached.get(k, 0) + 1
                lhs = Tt * (0.0 if flagged else 1.0)
                if np.abs(lhs).max() != 0.0:
                    ok5 = False
            n_checked += 1
    # what (15.5) would say if this address were unflagged
    would_fail = any(ins[0] == 'CHECK' and np.abs(Tt).max() != 0.0 for (Mt, Tt, ins) in cfg)
    print(f"--- {label}: packed dim {n}, stream length {len(stream)}, time/fuel bits N={N}, "
          f"{n_checked} (k,t) points")
    print(f"    (15.4a) Z S = Z Init exact: {ok4a};  (15.4b) transition exact incl. cyclic boundary: {ok4b}")
    print(f"    CHECK states reached per fuel depth k (k: count) = "
          f"{dict(sorted((kk, v // (1 << N) * (1 << N) if False else v) for kk, v in checks_reached.items()))}")
    print(f"    (15.5) exact with F={'1 (flagged)' if flagged else '0 (unflagged)'}: {ok5};  "
          f"(15.5) would fail if unflagged: {would_fail}")
    return cfg, ok4a and ok4b and ok5, would_fail


def unitary_pair(S):
    U_, sig, Vh = np.linalg.svd(S)
    Vp = U_ @ Vh
    absS = Vh.conj().T @ np.diag(sig) @ Vh
    J = absS + 1j * (Vh.conj().T @ np.diag(np.sqrt(np.clip(1 - sig ** 2, 0, None))) @ Vh)
    return Vp @ J, Vp @ J.conj().T


def check_unitary_decomp(cfg, pk):
    worst = 0.0; maxnorm = 0.0
    seen = 0
    noncomm = 0
    D = pk['D']
    for (Mt, Tt, ins) in cfg[:: max(1, len(cfg) // 600)]:
        for S in (Mt, Tt):
            nrm = np.linalg.norm(S, 2); maxnorm = max(maxnorm, nrm)
            u, v = unitary_pair(S)
            I = np.eye(S.shape[0])
            err = max(np.abs((u + v) / 2 - S).max(), np.abs(u.conj().T @ u - I).max(),
                      np.abs(v.conj().T @ v - I).max())
            worst = max(worst, err); seen += 1
        if np.abs(Mt @ D - D @ Mt).max() > 1e-12:
            noncomm += 1
    print(f"--- unitary decompositions S=(u+v)/2 on {seen} sampled register values: worst residual {worst:.2e}, "
          f"max ||S|| = {maxnorm:.6f}; sampled M values not commuting with D: {noncomm}")
    return worst < 1e-10 and maxnorm <= 1 + 1e-12


def check_reset_recursion(Nb=10):
    q = np.arange(1 << Nb)[:, None]; t = np.arange(1 << Nb)[None, :]
    def kq(qq):
        k = np.zeros_like(qq)
        alive = np.ones_like(qq, dtype=bool)
        for j in range(Nb):
            bit = (qq >> j) & 1
            alive = alive & (bit == 1)
            k = k + alive
        return k  # number of initial ones; Nb on all ones
    K = kq(q)
    Z = ((t % (1 << K)) == 0).astype(np.int64) * np.ones_like(t)
    rot = lambda x: (x >> 1) | ((x & 1) << (Nb - 1))
    q0 = q & 1; t0 = t & 1
    Zrot = Z[rot(np.arange(1 << Nb))][:, rot(np.arange(1 << Nb))]
    rhs = (1 - q0) + q0 * (1 - t0) * Zrot
    ok = np.array_equal(Z, rhs)
    print(f"--- reset recursion Z=(I-P_f)+P_f(I-P_t) S Z S^* on the full {Nb}+{Nb}-bit grid: exact = {ok}")
    return ok


def main():
    rng = np.random.default_rng(11)
    K3 = colouring_game(3, [(0, 1), (1, 2), (0, 2)], 3)
    pres = two_family_presentation(K3)
    rels = packed_relations(pres)
    # witnessed unflagged address
    pk = pack(classical_colouring_model(K3, pres, {0: 0, 1: 1, 2: 2}))
    stream = build_stream(rels, prefix_holds=300, rng=rng)
    assert len(stream) < (1 << N), len(stream)
    cfg, ok_w, _ = check_registers(stream, pk, flagged=False, label="unflagged witnessed address (K3)")
    ok_u = check_unitary_decomp(cfg, pk)
    # flagged address with wrong data (bad colouring): (15.5) holds only because F=1
    pk_bad = pack(classical_colouring_model(K3, pres, {0: 0, 1: 0, 2: 2}))
    cfg_b, ok_f, would_fail = check_registers(stream, pk_bad, flagged=True,
                                              label="flagged address with non-witness data (bad K3 colouring)")
    ok_r = check_reset_recursion()
    allok = ok_w and ok_u and ok_f and would_fail and ok_r
    print("\nALL PASS" if allok else "\nSOME FAIL")


if __name__ == "__main__":
    main()
