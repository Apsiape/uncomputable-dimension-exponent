"""Check the inclusion repair used in Proposition 12.2 and
Lemma 9.3: for projections F, Q with |(I-F)Q|_rho <= e and state commutators ||[F,xi]||_2, ||[Q,xi]||_2 <= e
(xi = sqrt(rho)), the repaired Q' = 1_[1/2,1](FQF) satisfies Q' <= F and |Q'-Q|_rho <= 6e.
Also checks the adjoint transfer in Proposition 12.2: ||R^* xi||_2 <= ||R xi||_2 + ||[R,xi]||_2.
Instances: exact (F, Q <= F, rho commuting with both) then perturbed by size lam.  Single-threaded."""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
import numpy as np

rng = np.random.default_rng(5)


def herm(d):
    H = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return (H + H.conj().T) / 2


def expmi(H, t):
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * t * w)) @ V.conj().T


def hs(X):
    return np.linalg.norm(X, 'fro')


def sqrtm_psd(r):
    w, V = np.linalg.eigh((r + r.conj().T) / 2)
    w = np.clip(w, 0, None)
    return (V * np.sqrt(w)) @ V.conj().T


def spec_proj(A, lo):
    w, V = np.linalg.eigh((A + A.conj().T) / 2)
    sel = w >= lo
    return V[:, sel] @ V[:, sel].conj().T


worst_repair = 0.0
worst_adj = 0.0
worst_incl = 0.0
for trial in range(4000):
    d = rng.integers(3, 9)
    nF = rng.integers(1, d + 1)
    nQ = rng.integers(0, nF + 1)
    diagF = np.zeros(d); diagF[:nF] = 1
    diagQ = np.zeros(d); diagQ[:nQ] = 1
    F = np.diag(diagF).astype(complex)
    Q = np.diag(diagQ).astype(complex)
    p = rng.dirichlet(np.ones(d) * rng.uniform(0.2, 2))
    rho = np.diag(p).astype(complex)
    lam = 10 ** rng.uniform(-6, -0.5)
    VF = expmi(herm(d), lam); VQ = expmi(herm(d), lam); VR = expmi(herm(d), lam)
    F = VF @ F @ VF.conj().T
    Q = VQ @ Q @ VQ.conj().T
    rho = VR @ rho @ VR.conj().T
    xi = sqrtm_psd(rho)
    I = np.eye(d)
    e = max(hs((I - F) @ Q @ xi), hs(F @ xi - xi @ F), hs(Q @ xi - xi @ Q))
    Qp = spec_proj(F @ Q @ F, 0.5)
    incl = np.linalg.norm((I - F) @ Qp, 2)
    worst_incl = max(worst_incl, incl)
    if e > 0:
        worst_repair = max(worst_repair, hs((Qp - Q) @ xi) / e)
    R = (I - F) @ Q
    lhs = hs(R.conj().T @ xi)
    rhs = hs(R @ xi) + hs(R @ xi - xi @ R)
    if rhs > 0:
        worst_adj = max(worst_adj, lhs / rhs)
print(f"max ||(I-F)Q'||_op = {worst_incl:.2e} (must be ~0: Q' <= F)")
print(f"max |Q'-Q|_rho / e = {worst_repair:.4f} (claimed <= 6)")
print(f"max ||R* xi|| / (||R xi|| + ||[R,xi]||) = {worst_adj:.4f} (must be <= 1)")
