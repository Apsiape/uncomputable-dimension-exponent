"""Check the one-stage inequality (12.4) in Lemma 12.1.

For ANY three-outcome PVMs (P_perp, P_0, P_1) on Alice and Bob, ANY reflections U_A, U_B and ANY vector xi in
H_A (x) H_B (x) H_E, the claim is

    || (A - I) xi ||  <=  p + (u + c)/sqrt(2),

with A the actual random-target stage and I the analysis-only stage (ideal built from Bob's projections),
p^2 = sum_r ||(P^A_r - P^B_r) xi||^2, u = ||(U_A - U_B) xi||, c^2 = sum_b ||(U_B P^B_b U_B - P^B_{1-b}) xi||^2.

This is a pure inequality, so random instances (far from any structure) are valid tests.
We also run near-structured instances (Alice = transpose of Bob on a maximally entangled vector, perturbed)
and a local random search that tries to maximise LHS/RHS.

Single-threaded numpy; tiny memory.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
import numpy as np

rng = np.random.default_rng(20261027)


def haar_unitary(d):
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def random_pvm3(d, sizes=None):
    W = haar_unitary(d)
    if sizes is None:
        cuts = np.sort(rng.integers(0, d + 1, size=2))
        sizes = [cuts[0], cuts[1] - cuts[0], d - cuts[1]]
    idx = np.cumsum([0] + list(sizes))
    Ps = []
    for k in range(3):
        cols = W[:, idx[k]:idx[k + 1]]
        Ps.append(cols @ cols.conj().T)
    return Ps  # [P_perp, P_0, P_1]


def random_reflection(d):
    W = haar_unitary(d)
    s = rng.choice([-1.0, 1.0], size=d)
    return (W * s) @ W.conj().T


def opA(O, Psi):
    return np.tensordot(O, Psi, axes=(1, 0))


def opB(O, Psi):
    return np.tensordot(O, Psi, axes=(1, 1)).transpose(1, 0, 2)


def nrm(X):
    return np.sqrt(np.vdot(X, X).real)


def stage_lhs_rhs(PA, UA, PB, UB, Psi):
    """PA = [P_perp, P_0, P_1] on Alice etc.  Psi shape (dA,dB,dE)."""
    sq = 0.0
    for a in (0, 1):
        # Alice ops by outcome r in {perp,0,1}
        A_ops = [PA[0], (UA if (a ^ 0) else np.eye(len(UA))) @ PA[1], (UA if (a ^ 1) else np.eye(len(UA))) @ PA[2]]
        B_ops = [PB[0], (UB if (a ^ 0) else np.eye(len(UB))) @ PB[1], (UB if (a ^ 1) else np.eye(len(UB))) @ PB[2]]
        for r in range(3):
            X = opA(A_ops[r], Psi)
            for o in range(3):
                act = opB(B_ops[o], X) / np.sqrt(2)
                if r == 0 and o == 0:
                    ide = opB(PB[0], Psi) / np.sqrt(2)
                elif r == o and r >= 1:
                    ide = opB(PB[1 + a], Psi) / np.sqrt(2)
                else:
                    ide = 0.0
                sq += nrm(act - ide) ** 2
    lhs = np.sqrt(sq)
    p = np.sqrt(sum(nrm(opA(PA[r], Psi) - opB(PB[r], Psi)) ** 2 for r in range(3)))
    u = nrm(opA(UA, Psi) - opB(UB, Psi))
    c = np.sqrt(sum(nrm(opB(UB @ PB[1 + b] @ UB - PB[2 - b], Psi)) ** 2 for b in (0, 1)))
    rhs = p + (u + c) / np.sqrt(2)
    return lhs, rhs


def random_instance(dA, dB, dE):
    PA = random_pvm3(dA)
    PB = random_pvm3(dB)
    UA = random_reflection(dA)
    UB = random_reflection(dB)
    Psi = rng.standard_normal((dA, dB, dE)) + 1j * rng.standard_normal((dA, dB, dE))
    Psi /= nrm(Psi)
    return PA, UA, PB, UB, Psi


def herm(d):
    H = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return (H + H.conj().T) / 2


def expmi(H, t):
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * t * w)) @ V.conj().T


def structured_instance(k, dE, lam):
    """Exact model: Bob space C^k (x) C^3 with ternary PVM on the C^3 factor (perp=|2>), U = X on {0,1} (+) 1,
    tensored with a random real reflection on C^k (no commutation needed at one stage).
    State: flagged mixture p|22><22| + (1-p) Phi_2 on the C^3 factor, times Phi_k, purified.
    Then perturb Bob's PVM, Bob's U, Alice's PVM/U and the state by size ~lam."""
    d = 3 * k
    P = [np.zeros((3, 3)) for _ in range(3)]
    P[0][2, 2] = 1
    P[1][0, 0] = 1
    P[2][1, 1] = 1
    X3 = np.array([[0, 1, 0], [1, 0, 0], [0, 0, 1.0]])
    Ik = np.eye(k)
    w = random_reflection(k).real if False else np.eye(k)
    PB = [np.kron(Ik, Pr) for Pr in P]
    UB = np.kron(w, X3)
    PA = [M.T.copy() for M in PB]
    UA = UB.T.copy()
    pflag = rng.uniform(0.1, 0.9)
    v0 = np.zeros((3, 3)); v0[2, 2] = 1
    v1 = np.zeros((3, 3)); v1[0, 0] = v1[1, 1] = 1 / np.sqrt(2)
    phik = np.eye(k) / np.sqrt(k)
    Psi = np.zeros((d, d, dE), dtype=complex)
    # index ordering kron(k,3): row = i*3 + s
    comp0 = np.einsum('ij,st->isjt', phik, v0).reshape(d, d)
    comp1 = np.einsum('ij,st->isjt', phik, v1).reshape(d, d)
    Psi[:, :, 0] = np.sqrt(pflag) * comp0
    Psi[:, :, 1] = np.sqrt(1 - pflag) * comp1
    # perturbations
    VB = expmi(herm(d), lam)
    PB = [VB @ M @ VB.conj().T for M in PB]
    VB2 = expmi(herm(d), lam)
    UB = VB2 @ UB @ VB2.conj().T
    VA = expmi(herm(d), lam)
    PA = [VA @ M @ VA.conj().T for M in PA]
    noise = rng.standard_normal((d, d, dE)) + 1j * rng.standard_normal((d, d, dE))
    Psi = Psi + lam * noise / nrm(noise)
    Psi /= nrm(Psi)
    return PA, UA, PB, UB, Psi


def main():
    worst = 0.0
    n = 0
    for trial in range(3000):
        dA, dB, dE = rng.integers(2, 6), rng.integers(2, 6), rng.integers(1, 4)
        inst = random_instance(dA, dB, dE)
        lhs, rhs = stage_lhs_rhs(*inst)
        if rhs > 0:
            worst = max(worst, lhs / rhs)
        n += 1
    print(f"random instances: {n}, max LHS/RHS = {worst:.4f}")

    worst_s = 0.0
    rows = []
    for lam in [1e-4, 1e-3, 1e-2, 1e-1, 3e-1]:
        wl = 0.0
        for trial in range(200):
            k = rng.integers(1, 3)
            inst = structured_instance(k, 3, lam)
            lhs, rhs = stage_lhs_rhs(*inst)
            wl = max(wl, lhs / rhs if rhs > 0 else 0.0)
        rows.append((lam, wl))
        worst_s = max(worst_s, wl)
    for lam, wl in rows:
        print(f"structured lam={lam:.0e}: max LHS/RHS = {wl:.4f}")

    # local random search maximising LHS/RHS from random starts (small dims)
    best = 0.0
    for start in range(30):
        dA, dB, dE = 3, 3, 2
        PA, UA, PB, UB, Psi = random_instance(dA, dB, dE)
        lhs, rhs = stage_lhs_rhs(PA, UA, PB, UB, Psi)
        cur = lhs / rhs
        step = 0.3
        for it in range(400):
            VA = expmi(herm(dA), step); VB = expmi(herm(dB), step)
            WA = expmi(herm(dA), step); WB = expmi(herm(dB), step)
            PA2 = [VA @ M @ VA.conj().T for M in PA]
            PB2 = [VB @ M @ VB.conj().T for M in PB]
            UA2 = WA @ UA @ WA.conj().T
            UB2 = WB @ UB @ WB.conj().T
            Psi2 = Psi + step * (rng.standard_normal(Psi.shape) + 1j * rng.standard_normal(Psi.shape)) / 4
            Psi2 /= nrm(Psi2)
            l2, r2 = stage_lhs_rhs(PA2, UA2, PB2, UB2, Psi2)
            if r2 > 0 and l2 / r2 > cur:
                PA, PB, UA, UB, Psi, cur = PA2, PB2, UA2, UB2, Psi2, l2 / r2
            else:
                step *= 0.995
        best = max(best, cur)
    print(f"hill-climb (30 starts x 400 steps, dims 3,3,2): max LHS/RHS = {best:.4f}")


if __name__ == "__main__":
    main()
