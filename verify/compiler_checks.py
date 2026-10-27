"""Compiler identities of Section 3 of the paper, on random instances.

  1.1  u = 2r - I + 2i sqrt(r(I-r)) is unitary and r = (2I+u+u*)/4;
       realification; orthogonal = product of two symmetric involutions.
  1.2  E e_j E = E/L;  EFS = ESE = (2c/L) p E;  sum_v Z^v E Z^v = I;
       identity (1): p = (L/2c) sum_v Z^v E F S Z^v;  ||EF||_f = 2c/(L sqrt L) ||p||_f.
  1.3  the two conjugacy gadgets (doubled extensions) satisfy their contexts.
  1.5  (2): F' = proj onto (I-E) ran F has EF' = 0 and ||F-F'||^2 <= 2||EF||^2,
       with the exact formula #{lambda=1} + 2 sum_{lambda<1} lambda; and the
       max-entangled disagreement probability equals ||P-Q||_f^2.
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import json
from fractions import Fraction
from functools import reduce
import numpy as np
import scipy.linalg as sla

rng = np.random.default_rng(271026)
RES = {}


def rand_orth(n):
    q, r = np.linalg.qr(rng.normal(size=(n, n)))
    return q * np.sign(np.diag(r))


def rand_unitary(n):
    z = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


def rand_invol(n, real=True):
    Q = rand_orth(n) if real else rand_unitary(n)
    s = rng.choice([-1.0, 1.0], size=n)
    return (Q * s) @ Q.conj().T


def rand_proj(n, r, Q=None):
    Q = rand_unitary(n) if Q is None else Q
    return Q[:, :r] @ Q[:, :r].conj().T


def opn(A):
    return float(np.linalg.norm(A, 2))


def fl(A):
    return float(np.linalg.norm(A) / np.sqrt(A.shape[0]))


# ---------------------------------------------------------------- 1.1
def check_11(trials=50):
    worst = dict(unitary=0.0, recon=0.0, realif=0.0, orth_split=0.0, sym=0.0, invol=0.0)
    for _ in range(trials):
        n = int(rng.integers(2, 9))
        U0 = rand_unitary(n)
        lam = rng.uniform(0, 1, size=n)
        lam[: int(rng.integers(0, 2))] = 0.0  # include spectrum endpoints
        if n > 2:
            lam[-1] = 1.0
        r = (U0 * lam) @ U0.conj().T
        r = (r + r.conj().T) / 2
        w, Vv = np.linalg.eigh(r)
        sq = (Vv * np.sqrt(np.clip(w * (1 - w), 0, None))) @ Vv.conj().T
        u = 2 * r - np.eye(n) + 2j * sq
        worst["unitary"] = max(worst["unitary"], opn(u.conj().T @ u - np.eye(n)))
        worst["recon"] = max(worst["recon"], opn((2 * np.eye(n) + u + u.conj().T) / 4 - r))
        # realification preserves products and normalized HS norm
        A, B = rand_unitary(n), rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
        Rf = lambda M: np.block([[M.real, -M.imag], [M.imag, M.real]])
        worst["realif"] = max(worst["realif"], opn(Rf(A @ B) - Rf(A) @ Rf(B)), abs(fl(Rf(B)) - fl(B)))
        # real orthogonal = product of two symmetric orthogonal involutions
        O = rand_orth(n)
        T, Z = sla.schur(O, output="real")
        a = np.zeros((n, n))
        b = np.zeros((n, n))
        i = 0
        while i < n:
            if i + 1 < n and abs(T[i + 1, i]) > 1e-12:
                c, s = T[i, i], T[i + 1, i]  # block [[c,-s],[s,c]]
                a[i:i + 2, i:i + 2] = np.diag([1.0, -1.0])
                b[i:i + 2, i:i + 2] = np.array([[c, -s], [-s, -c]])
                i += 2
            else:
                a[i, i] = 1.0
                b[i, i] = T[i, i]
                i += 1
        a, b = Z @ a @ Z.T, Z @ b @ Z.T
        worst["orth_split"] = max(worst["orth_split"], opn(a @ b - O))
        worst["sym"] = max(worst["sym"], opn(a - a.T), opn(b - b.T))
        worst["invol"] = max(worst["invol"], opn(a @ a - np.eye(n)), opn(b @ b - np.eye(n)))
    RES["1.1"] = worst


# ---------------------------------------------------------------- 1.2
X1 = np.array([[0.0, 1.0], [1.0, 0.0]])
Z1 = np.diag([1.0, -1.0])


def kron_all(ms):
    return reduce(np.kron, ms)


def check_12(trials=30):
    worst = dict(EejE=0.0, partition=0.0, S_unitary=0.0, EFS_ESE=0.0, ESE_p=0.0, ident1=0.0,
                 EF_flat=0.0, F_proj=0.0)
    for _ in range(trials):
        n = int(rng.integers(2, 6))
        # random words in random involutions, random rational coefficients
        invs = [rand_invol(n) for _ in range(3)]
        nw = int(rng.integers(1, 4))
        words = []
        for _w in range(nw):
            ln = int(rng.integers(0, 4))
            W = np.eye(n)
            for _l in range(ln):
                W = W @ invs[int(rng.integers(0, 3))]
            words.append(W)
        coefs = [Fraction(int(rng.integers(-5, 6)), int(rng.integers(1, 5))) for _ in range(nw)]
        p = sum(float(a) * W for a, W in zip(coefs, words))
        # clear denominators: c with 2c a_j integers; signed duplicates + (I,-I) padding to L = 2^q
        c = int(np.lcm.reduce([a.denominator for a in coefs]))
        signed = []
        for a, W in zip(coefs, words):
            m = int(2 * c * a)
            signed += [np.sign(m) * W] * abs(m)
        q = max(1, int(np.ceil(np.log2(max(len(signed), 1)))))
        while (2 ** q - len(signed)) % 2:
            q += 1
        L = 2 ** q
        while len(signed) < L:
            signed += [np.eye(n), -np.eye(n)]
        assert len(signed) == L
        assert np.allclose(sum(signed), 2 * c * p)
        IL, In = np.eye(L), np.eye(n)
        plus = np.ones(L) / np.sqrt(L)
        E = np.kron(np.outer(plus, plus), In)
        e = [np.kron(np.diag(np.eye(L)[j]), In) for j in range(L)]
        for j in range(L):
            worst["EejE"] = max(worst["EejE"], opn(E @ e[j] @ E - E / L))
        S = sum(e[j] @ np.kron(IL, signed[j]) for j in range(L))
        worst["S_unitary"] = max(worst["S_unitary"], opn(S.T @ S - np.eye(L * n)))
        F = S @ E @ S.T
        worst["F_proj"] = max(worst["F_proj"], opn(F @ F - F), opn(F - F.T))
        P = np.kron(IL, p)
        worst["EFS_ESE"] = max(worst["EFS_ESE"], opn(E @ F @ S - E @ S @ E))
        worst["ESE_p"] = max(worst["ESE_p"], opn(E @ S @ E - (2 * c / L) * P @ E))
        Zs = []
        for v in range(L):
            bitsv = [(v >> i) & 1 for i in range(q)]
            Zs.append(np.kron(kron_all([Z1 if b else np.eye(2) for b in bitsv]), In))
        worst["partition"] = max(worst["partition"], opn(sum(Zv @ E @ Zv for Zv in Zs) - np.eye(L * n)))
        rhs = (L / (2 * c)) * sum(Zv @ E @ F @ S @ Zv for Zv in Zs)
        worst["ident1"] = max(worst["ident1"], opn(rhs - P))
        worst["EF_flat"] = max(worst["EF_flat"], abs(fl(E @ F) - 2 * c / (L * np.sqrt(L)) * fl(P)))
    RES["1.2"] = worst


# ---------------------------------------------------------------- 1.3
def is_context(vs):
    """pairwise commuting self-adjoint involutions with product I."""
    d = vs[0].shape[0]
    err = 0.0
    for v in vs:
        err = max(err, opn(v - v.conj().T), opn(v @ v - np.eye(d)))
    for i in range(len(vs)):
        for j in range(i + 1, len(vs)):
            err = max(err, opn(vs[i] @ vs[j] - vs[j] @ vs[i]))
    err = max(err, opn(reduce(np.matmul, vs) - np.eye(d)))
    return err


def check_13(trials=30):
    worst = dict(g1_contexts=0.0, g1_conj=0.0, g2_contexts=0.0, g2_inverse=0.0)
    for _ in range(trials):
        n = int(rng.integers(2, 7))
        # gadget 1: x1 x2 x1 = x3
        X1m, X2m = rand_invol(n, real=False), rand_invol(n, real=False)
        X3m = X1m @ X2m @ X1m
        I_, O_ = np.eye(n), np.zeros((n, n))
        dg = lambda A, B: np.block([[A, O_], [O_, B]])
        off = lambda A, B: np.block([[O_, A], [B, O_]])
        Xs = [X1m, X2m, X3m]
        x = [dg(Xi, Xi) for Xi in Xs]
        y = [dg(Xi, I_) for Xi in Xs]
        z = [dg(I_, Xi) for Xi in Xs]
        f = off(I_, I_)
        w = [off(Xi, Xi) for Xi in Xs]
        g = dg(X2m, X3m)
        err = 0.0
        for i in range(3):
            err = max(err, is_context([x[i], y[i], z[i]]), is_context([x[i], f, w[i]]))
        err = max(err, is_context([g, y[1], z[2]]))
        worst["g1_contexts"] = max(worst["g1_contexts"], err)
        cj = max(max(opn(f @ y[i] @ f - z[i]) for i in range(3)), opn(w[0] @ y[1] @ w[0] - z[2]),
                 max(opn(y[i] @ z[i] - z[i] @ y[i]) for i in range(3)), opn(y[1] @ z[2] - z[2] @ y[1]))
        worst["g1_conj"] = max(worst["g1_conj"], cj)
        # gadget 2: a b a = c with [b, c] = 0 : random rep of the dihedral group of order 8
        blocks_a, blocks_b = [], []
        for _b in range(int(rng.integers(1, 4))):
            if rng.random() < 0.5:
                blocks_a.append(np.array([[rng.choice([-1.0, 1.0])]]))
                blocks_b.append(np.array([[rng.choice([-1.0, 1.0])]]))
            else:  # 2-dim irrep: reflections at angle pi/4 apart
                blocks_a.append(np.array([[1.0, 0.0], [0.0, -1.0]]))
                th = np.pi / 4
                blocks_b.append(np.array([[np.cos(2 * th), np.sin(2 * th)], [np.sin(2 * th), -np.cos(2 * th)]]))
        a0, b0 = sla.block_diag(*blocks_a), sla.block_diag(*blocks_b)
        Q = rand_unitary(a0.shape[0])
        a, b = Q @ a0 @ Q.conj().T, Q @ b0 @ Q.conj().T
        c = a @ b @ a
        m = a.shape[0]
        assert opn(b @ c - c @ b) < 1e-9
        I_, O_ = np.eye(m), np.zeros((m, m))
        dg = lambda A, B: np.block([[A, O_], [O_, B]])
        Mx = lambda A: np.block([[O_, A], [A, O_]])
        d1, d2, d3 = Mx(a), Mx(I_), Mx(b)
        d4 = np.block([[O_, b @ a], [a @ b, O_]])
        d5 = dg(b @ a @ b, a)
        d6 = dg(b @ c, I_)
        d7 = dg(b, c)
        A, Bb, C = dg(a, a), dg(b, b), dg(c, c)
        err = max(is_context([A, d1, d2]), is_context([Bb, d2, d3]), is_context([d3, d4, d5]),
                  is_context([A, d5, d6]), is_context([C, d6, d7]), is_context([d1, d4, d7]))
        worst["g2_contexts"] = max(worst["g2_contexts"], err)
        # the inverse calculation a b a = d1 d2 d2 d3 d5 d6 = d1 d4 d6 = d7 d6 = c (on the doubled space)
        inv = max(opn(A @ Bb @ A - d1 @ d2 @ d2 @ d3 @ d5 @ d6), opn(d1 @ d2 @ d2 @ d3 @ d5 @ d6 - d1 @ d4 @ d6),
                  opn(d1 @ d4 @ d6 - d7 @ d6), opn(d7 @ d6 - C))
        worst["g2_inverse"] = max(worst["g2_inverse"], inv)
    RES["1.3"] = worst


# ---------------------------------------------------------------- 1.5 / (2)
def check_2(trials=400):
    worst_ratio, worst_formula, worst_EFp, worst_le, worst_game = 0.0, 0.0, 0.0, 0.0, 0.0
    cases = 0
    for _ in range(trials):
        n = int(rng.integers(2, 14))
        rE, rF = int(rng.integers(0, n + 1)), int(rng.integers(0, n + 1))
        if rng.random() < 0.3 and rE > 0 and rF > 0:
            # force ran F to meet ran E (eigenvalue lambda = 1 cases)
            Q = rand_unitary(n)
            E = rand_proj(n, rE, Q)
            k = int(rng.integers(1, min(rE, rF) + 1))
            Q2 = rand_unitary(n)
            # rF-k random vectors plus k vectors inside ran E
            basis = np.concatenate([Q[:, :k], Q2[:, : max(rF - k, 0)]], axis=1)
            qf, _ = np.linalg.qr(basis)
            F = qf @ qf.conj().T
        else:
            E, F = rand_proj(n, rE), rand_proj(n, rF)
        In = np.eye(n)
        # F' : projection onto (I-E) ran F
        w, Vv = np.linalg.eigh(F)
        ranF = Vv[:, w > 0.5]
        Mv = (In - E) @ ranF
        if Mv.shape[1]:
            u, s, _ = np.linalg.svd(Mv, full_matrices=False)
            Fp = u[:, s > 1e-9] @ u[:, s > 1e-9].conj().T
        else:
            Fp = np.zeros((n, n))
        hs2 = lambda A: float(np.linalg.norm(A) ** 2)
        lhs, rhs = hs2(F - Fp), 2 * hs2(E @ F)
        lam = np.linalg.eigvalsh(ranF.conj().T @ E @ ranF) if ranF.shape[1] else np.zeros(0)
        formula = float(np.sum(lam > 1 - 1e-9) + 2 * np.sum(lam[lam <= 1 - 1e-9]))
        worst_formula = max(worst_formula, abs(lhs - formula))
        worst_EFp = max(worst_EFp, opn(E @ Fp))
        # F' <= I - E  (so I - E - F' is a projection)
        R = In - E - Fp
        worst_le = max(worst_le, opn(R @ R - R))
        if rhs > 1e-12:
            worst_ratio = max(worst_ratio, lhs / rhs)
        else:
            worst_ratio = max(worst_ratio, 0.0 if lhs < 1e-9 else np.inf)
        # max-entangled disagreement probability of projections P (Alice), Q (Bob) = ||P - Q||_f^2
        Pm, Qm = Fp, F
        d = n
        psi = np.eye(d).reshape(d * d) / np.sqrt(d)
        Pa = np.kron(Pm, In)
        Qb = np.kron(In, Qm.T)
        dis = float(np.real(psi.conj() @ (Pa @ (np.eye(d * d) - Qb) + (np.eye(d * d) - Pa) @ Qb) @ psi))
        worst_game = max(worst_game, abs(dis - hs2(Pm - Qm) / d))
        cases += 1
    RES["1.5 (2)"] = dict(trials=cases, max_ratio_lhs_over_2EF2=worst_ratio, formula_err=worst_formula,
                          max_EFprime=worst_EFp, I_minus_E_minus_Fp_proj_err=worst_le,
                          disagreement_vs_flat2_err=worst_game)


if __name__ == "__main__":
    check_11()
    check_12()
    check_13()
    check_2()
    print(json.dumps(RES, indent=1))
    od = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
    with open(os.path.join(od, "compiler_checks.json"), "w") as fh:
        json.dump(RES, fh, indent=1)
