"""Full-protocol numerical check of Lemma 12.1 (triangular extraction with an inactive outcome).

Instances: m stages, each binary (compulsory) or ternary (optional).  Exact model on
H = (x)_j C^{k_j}, k_j in {2,3}: P_{j,0}=|0><0|_j, P_{j,1}=|1><1|_j, P_{j,perp}=|2><2|_j (ternary only),
U_j = X_j (swap 0,1; fix 2) (x) W_{>j}, with W_{>j} a product of real reflections on the LATER factors that do
NOT preserve the later digits (Hadamard on {0,1}).  So controls of different stages do not commute and a control
does not preserve later measurements: only the triangular condition (preserve EARLIER measurements) holds.
State: flagged mixture over activity patterns f of the ternary stages, rho = sum_f p_f |psi_f><psi_f|,
psi_f = (x)_j (|22> if inactive else Phi_2 on {0,1}); purified with an environment.
Alice's operators are the transposes (exact mirrors on every psi_f).

Perturbations (size lam): Bob's PVMs and controls conjugated by random near-identity unitaries (stage-dependent,
so triangular commutators become nonzero), Alice's too, and the state mixed with a random low-rank state.

For every instance we compute:
  eta      = max of all hypotheses of the lemma (root aggregates, exactly as stated);
  Dvec     = || actual composite - ideal composite ||  (the history/vector-error proof of Lemma 12.1 claims <= 7 m^3 eta);
  hist     = Sum_j [p_j + (u_j+c_j)/sqrt2] with the TRUE history aggregates (telescoping with (12.4) claim Dvec <= hist),
             and p_j <= (3j^2+1)eta, u_j <= (2j^2+1)eta, c_j <= (1+2 sqrt2 j)eta, Delta_j <= j eta;
  EN       = ideal mean number of active outputs, versus sumF = sum_j Tr(rho_B F_j) - m(m-1) eta  (the mean-activation bound (12.7));
  I_omega  = coherent information I(A>B) of the actual dephased-flag output (the continuity and hashing argument (12.8)), versus
             EN - 6m t - 2g(t) with t = Dvec, a purification-vector upper bound on output half trace distance, and versus the tested extraction lower bound.
Single-threaded, small memory.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
import itertools
import sys
import numpy as np

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
SQ2 = np.sqrt(2.0)


def nrm(X):
    return float(np.sqrt(np.vdot(X, X).real))


def herm(d):
    H = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return (H + H.conj().T) / 2


def expmi(H, t):
    w, V = np.linalg.eigh(H)
    return (V * np.exp(1j * t * w)) @ V.conj().T


def kron_list(mats):
    out = np.array([[1.0 + 0j]])
    for M in mats:
        out = np.kron(out, M)
    return out


def opA(O, Psi):
    return np.tensordot(O, Psi, axes=(1, 0))


def opB(O, Psi):
    return np.tensordot(O, Psi, axes=(1, 1)).transpose(1, 0, 2)


def vn_entropy(rho):
    w = np.linalg.eigvalsh((rho + rho.conj().T) / 2)
    w = w[w > 1e-15]
    return float(-(w * np.log2(w)).sum())


def h2(x):
    if x <= 0 or x >= 1:
        return 0.0
    return float(-x * np.log2(x) - (1 - x) * np.log2(1 - x))


def g(t):
    return (1 + t) * h2(t / (1 + t))


def build_exact(types, mix_weights=None):
    """types: list of 'b' or 't'.  Returns Bob ops, Alice ops, Psi (dA,dB,dE)."""
    m = len(types)
    ks = [2 if t == 'b' else 3 for t in types]
    d = int(np.prod(ks))
    loc_P = []
    loc_X = []
    loc_w = []
    for k in ks:
        Ps = [np.zeros((k, k)) for _ in range(3)]
        if k == 3:
            Ps[0][2, 2] = 1
        Ps[1][0, 0] = 1
        Ps[2][1, 1] = 1
        X = np.eye(k)
        X[0, 0] = X[1, 1] = 0
        X[0, 1] = X[1, 0] = 1
        Hd = np.eye(k)
        Hd[:2, :2] = np.array([[1, 1], [1, -1]]) / SQ2
        loc_P.append(Ps)
        loc_X.append(X)
        loc_w.append(Hd)
    PB = []
    UB = []
    for j in range(m):
        Pj = []
        for r in range(3):
            mats = [np.eye(ks[s]) for s in range(m)]
            mats[j] = loc_P[j][r]
            Pj.append(kron_list(mats))
        PB.append(Pj)
        mats = [np.eye(ks[s]) for s in range(m)]
        mats[j] = loc_X[j]
        for s in range(j + 1, m):
            mats[s] = loc_w[s]  # acts on LATER factors: breaks commutation with later digits
        UB.append(kron_list(mats))
    PA = [[M.T.copy() for M in Pj] for Pj in PB]
    UA = [U.T.copy() for U in UB]
    # flagged mixture over activity patterns of ternary stages
    tern = [j for j in range(m) if types[j] == 't']
    pats = list(itertools.product([0, 1], repeat=len(tern)))
    if mix_weights is None:
        mix_weights = rng.dirichlet(np.ones(len(pats)))
    dE = len(pats)
    Psi = np.zeros((d, d, dE), dtype=complex)
    for e, pat in enumerate(pats):
        act = {j: 1 for j in range(m)}
        for jj, f in zip(tern, pat):
            act[jj] = f
        vecs = []
        for j in range(m):
            k = ks[j]
            v = np.zeros((k, k))
            if act[j]:
                v[0, 0] = v[1, 1] = 1 / SQ2
            else:
                v[2, 2] = 1
            vecs.append(v)
        # combine: psi_f[(i_0..i_m-1),(j_0..j_m-1)] = prod v_s[i_s,j_s]
        M = np.array([[1.0]])
        for v in vecs:
            M = np.einsum('ab,cd->acbd', M, v).reshape(M.shape[0] * v.shape[0], M.shape[1] * v.shape[1])
        Psi[:, :, e] = np.sqrt(mix_weights[e]) * M
    return PA, UA, PB, UB, Psi, ks


def perturb(PA, UA, PB, UB, Psi, lamB, lamA, lamS, noise_rank=3):
    d = PB[0][0].shape[0]
    m = len(PB)
    PB2, UB2, PA2, UA2 = [], [], [], []
    for j in range(m):
        V = expmi(herm(d), lamB)
        PB2.append([V @ M @ V.conj().T for M in PB[j]])
        W = expmi(herm(d), lamB)
        UB2.append(W @ UB[j] @ W.conj().T)
        V = expmi(herm(d), lamA)
        PA2.append([V @ M @ V.conj().T for M in PA[j]])
        W = expmi(herm(d), lamA)
        UA2.append(W @ UA[j] @ W.conj().T)
    # state: rho' = (1-lamS) rho + lamS sigma, sigma random of rank noise_rank; purification by direct sum in E
    dE = Psi.shape[2]
    if lamS > 0:
        S = rng.standard_normal((d, d, noise_rank)) + 1j * rng.standard_normal((d, d, noise_rank))
        S /= nrm(S)
        Psi2 = np.concatenate([np.sqrt(1 - lamS) * Psi, np.sqrt(lamS) * S], axis=2)
    else:
        Psi2 = Psi
    return PA2, UA2, PB2, UB2, Psi2


def hypotheses_eta(PA, UA, PB, UB, Psi, types):
    m = len(PB)
    vals = []
    for j in range(m):
        rs = range(3) if types[j] == 't' else (1, 2)
        vals.append(np.sqrt(sum(nrm(opA(PA[j][r], Psi) - opB(PB[j][r], Psi)) ** 2 for r in range(3))))
        vals.append(nrm(opA(UA[j], Psi) - opB(UB[j], Psi)))
        for s in range(j):
            vals.append(np.sqrt(sum(nrm(opB(PB[j][a] @ PB[s][b] - PB[s][b] @ PB[j][a], Psi)) ** 2
                                    for a in range(3) for b in range(3))))
            vals.append(np.sqrt(sum(nrm(opB(UB[j] @ PB[s][b] - PB[s][b] @ UB[j], Psi)) ** 2 for b in range(3))))
        vals.append(np.sqrt(sum(nrm(opB(UB[j] @ PB[j][1 + b] @ UB[j] - PB[j][2 - b], Psi)) ** 2 for b in (0, 1))))
    return max(vals)


def outcome_labels(types):
    return [list(range(3)) if t == 't' else [1, 2] for t in types]  # 0=perp, 1->bit 0, 2->bit 1


def run_protocol(PA, UA, PB, UB, Psi, types):
    m = len(PB)
    d = PB[0][0].shape[0]
    Id = np.eye(d)
    labs = outcome_labels(types)
    rstrings = list(itertools.product(*labs))
    nR = len(rstrings)
    idx = {r: i for i, r in enumerate(rstrings)}
    flagsA = np.array([tuple(1 if x > 0 else 0 for x in r) for r in rstrings])
    # same flag pattern matrix for dephasing
    same_flag = np.all(flagsA[:, None, :] == flagsA[None, :, :], axis=2)
    omega = np.zeros((nR * nR, nR * nR), dtype=complex)
    Dsq = 0.0
    EN = 0.0
    sigma_probs = {}
    for a in itertools.product([0, 1], repeat=m):
        # branch operators, chronological (stage 0 first => rightmost)
        def branch_ops(P, U):
            ops = {}
            for r in rstrings:
                K = Id.copy()
                for j in range(m):
                    rj = r[j]
                    if rj == 0:
                        step = P[j][0]
                    else:
                        b = rj - 1
                        step = (U[j] @ P[j][rj]) if (a[j] ^ b) else P[j][rj]
                    K = step @ K
                ops[r] = K
            return ops
        KA = branch_ops(PA, UA)
        KB = branch_ops(PB, UB)
        # ideal Bob branch ops: P_perp if inactive else P_{a_j}
        KI = {}
        for r in rstrings:
            K = Id.copy()
            for j in range(m):
                step = PB[j][0] if r[j] == 0 else PB[j][1 + a[j]]
                K = step @ K
            KI[r] = K
        vecs = np.zeros((nR, nR) + Psi.shape, dtype=complex)
        for r in rstrings:
            X = opA(KA[r], Psi)
            for o in rstrings:
                vecs[idx[r], idx[o]] = opB(KB[o], X)
        scale = 2.0 ** (-m / 2)
        for r in rstrings:
            ideal_v = opB(KI[r], Psi)
            for o in rstrings:
                diff = scale * vecs[idx[r], idx[o]] - (scale * ideal_v if r == o else 0)
                Dsq += nrm(diff) ** 2
            pr = (scale ** 2) * nrm(ideal_v) ** 2
            nact = sum(1 for x in r if x > 0)
            EN += pr * nact
        V = vecs.reshape(nR * nR, -1) * scale
        G = V.conj() @ V.T  # G[(r,o),(r',o')] = <v_{r'o'}, v_{ro}> ... conj ordering
        omega += G.T  # omega[(r,o),(r',o')] = <v_{r',o'}|v_{r,o}> as matrix rho = sum |v><v| reduced
    # dephase flags on both sides
    mask = np.einsum('ac,bd->abcd', same_flag, same_flag).reshape(nR * nR, nR * nR)
    omega = omega * mask
    omega = (omega + omega.conj().T) / 2
    tr = np.trace(omega).real
    omega_AB = omega / tr
    omega_B = np.einsum('abad->bd', omega_AB.reshape(nR, nR, nR, nR))
    I_omega = vn_entropy(omega_B) - vn_entropy(omega_AB)
    return dict(Dvec=np.sqrt(Dsq), EN=EN, I_omega=I_omega, trace=tr, nR=nR)


def history_aggregates(PA, UA, PB, UB, Psi, types):
    """True history aggregates of the history/vector-error proof of Lemma 12.1: for each stage j, histories over earlier stages s<j with
    residual Kraus R_{s,a,0}=P_perp/sqrt2, R_{s,a,1}=P_a (Bob, chronological) and Q^A reversed (Alice)."""
    m = len(PB)
    d = PB[0][0].shape[0]
    Id = np.eye(d)
    out = []
    for j in range(m):
        hist_labels = list(itertools.product(*[[(a, f) for a in (0, 1) for f in (0, 1)] for _ in range(j)]))
        pj = uj = cj = Dj = 0.0
        for h in hist_labels:
            KB = Id.copy()
            QA = Id.copy()
            for s, (a, f) in enumerate(h):
                RB = PB[s][0] / SQ2 if f == 0 else PB[s][1 + a]
                RA = PA[s][0] / SQ2 if f == 0 else PA[s][1 + a]
                KB = RB @ KB
                QA = QA @ RA
            xi = opB(KB, Psi)
            Dj += nrm(xi - opA(QA, Psi)) ** 2
            pj += sum(nrm(opA(PA[j][r], xi) - opB(PB[j][r], xi)) ** 2 for r in range(3))
            uj += nrm(opA(UA[j], xi) - opB(UB[j], xi)) ** 2
            cj += sum(nrm(opB(UB[j] @ PB[j][1 + b] @ UB[j] - PB[j][2 - b], xi)) ** 2 for b in (0, 1))
        out.append((np.sqrt(pj), np.sqrt(uj), np.sqrt(cj), np.sqrt(Dj)))
    return out


def trace_F(PB, Psi, types):
    rhoB = np.einsum('abe,ace->bc', Psi, Psi.conj())
    tot = 0.0
    for j, t in enumerate(types):
        F = PB[j][1] + PB[j][2]
        tot += np.trace(rhoB @ F).real
    return tot


def one_case(types, lamB, lamA, lamS, verbose=True):
    PA, UA, PB, UB, Psi, ks = build_exact(types)
    PA, UA, PB, UB, Psi = perturb(PA, UA, PB, UB, Psi, lamB, lamA, lamS)
    m = len(types)
    eta = hypotheses_eta(PA, UA, PB, UB, Psi, types)
    res = run_protocol(PA, UA, PB, UB, Psi, types)
    hist = history_aggregates(PA, UA, PB, UB, Psi, types)
    sumF = trace_F(PB, Psi, types)
    tau = 20 * m ** 3 * eta
    rhs1 = sumF - m * (m - 1) * eta - 6 * m * tau - 2 * g(min(tau, 1.0))
    t_act = res['Dvec']
    step_d = EN_bound = None
    hist_bound = sum(p + (u + c) / SQ2 for (p, u, c, D) in hist)
    checks = {
        'Dvec<=hist(telescoping+(12.4))': res['Dvec'] <= hist_bound * (1 + 1e-9) + 1e-12,
        'Dvec<=7m^3eta': res['Dvec'] <= 7 * m ** 3 * eta + 1e-12,
        'p_j<=(3j^2+1)eta': all(p <= (3 * j * j + 1) * eta + 1e-12 for j, (p, u, c, D) in enumerate(hist)),
        'u_j<=(2j^2+1)eta': all(u <= (2 * j * j + 1) * eta + 1e-12 for j, (p, u, c, D) in enumerate(hist)),
        'c_j<=(1+2sqrt2 j)eta': all(c <= (1 + 2 * SQ2 * j) * eta + 1e-12 for j, (p, u, c, D) in enumerate(hist)),
        'Delta_j<=j eta': all(D <= j * eta + 1e-12 for j, (p, u, c, D) in enumerate(hist)),
        'EN>=sumF-m(m-1)eta': res['EN'] >= sumF - m * (m - 1) * eta - 1e-12,
        'I>=EN-6mt-2g(t)': res['I_omega'] >= res['EN'] - 6 * m * t_act - 2 * g(min(t_act, 1.0)) - 1e-9,
        'I>=RHS(1)': res['I_omega'] >= rhs1 - 1e-9,
    }
    if verbose:
        print(f"types={''.join(types)} lamB={lamB:.0e} lamA={lamA:.0e} lamS={lamS:.0e} | eta={eta:.3e} "
              f"Dvec={res['Dvec']:.3e} (hist {hist_bound:.3e}, 7m^3eta {7*m**3*eta:.3e}) "
              f"sumF={sumF:.5f} EN={res['EN']:.5f} I={res['I_omega']:.5f} RHS1={rhs1:.4f} "
              f"deficit(sumF-I)={sumF-res['I_omega']:.3e}")
        bad = [k for k, v in checks.items() if not v]
        print("   all checks pass" if not bad else f"   FAILED: {bad}")
    return eta, res, sumF, rhs1, checks, hist


def main():
    cases = [
        ('t',), ('b', 't'), ('t', 't'), ('t', 'b'), ('b', 't', 't'), ('t', 't', 't'), ('t', 'b', 't'),
        ('b', 'b', 't', 't'),
    ]
    print("=== exact models (eta = 0): expect I_omega = sumF exactly ===")
    for types in cases:
        one_case(list(types), 0.0, 0.0, 0.0)
    print("=== perturbed models ===")
    for types in cases:
        for lam in [1e-5, 1e-4, 1e-3, 1e-2, 1e-1]:
            one_case(list(types), lam, lam, lam)
    print("=== Bob-only perturbations (triangular relations broken, mirrors broken) ===")
    for types in [('t', 't'), ('t', 't', 't'), ('b', 't', 't')]:
        for lam in [1e-4, 1e-3, 1e-2]:
            one_case(list(types), lam, 0.0, 0.0)
    print("=== state-only perturbations (mirrors broken, Bob relations exact) ===")
    for types in [('t', 't'), ('t', 't', 't')]:
        for lam in [1e-4, 1e-3, 1e-2]:
            one_case(list(types), 0.0, 0.0, lam)


if __name__ == "__main__":
    main()
