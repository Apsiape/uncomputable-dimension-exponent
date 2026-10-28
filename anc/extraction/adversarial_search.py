"""Adversarial hill-climb against the internal inequalities of Steps B-D (m = 2 and 3 ternary stages).
Starting from the exact flagged model, we search over perturbation generators (Bob PVMs, Bob controls,
Alice PVMs, Alice controls, state) at fixed small size and maximise each normalized ratio:
  r_D   = Dvec / sum_j[p_j+(u_j+c_j)/sqrt2]        (telescoping with (12.4); must be <= 1)
  r_B   = Dvec / (7 m^3 eta)                         (the history/vector-error proof of Lemma 12.1 final claim; must be <= 1)
  r_p   = max_j p_j / ((3j^2+1) eta), r_u, r_c, r_Delta similarly   the history estimates in Lemma 12.1
  r_C   = (sumF - EN) / (m(m-1) eta)                 (the mean-activation bound (12.7); must be <= 1)
  r_Dst = (EN - I) / (6 m t + 2 g(t))                (the continuity and hashing argument (12.8) continuity; must be <= 1)
  r_1   = (sumF - I) / (m(m-1)eta + 6 m tau + 2 g(tau)), tau = 20 m^3 eta   ((1); must be <= 1)
Single-threaded, small dims."""
import sys
import numpy as np
import protocol_check as pc

SQ2 = np.sqrt(2.0)


def evaluate(base, gens, lam, types):
    PA, UA, PB, UB, Psi = base
    m = len(types)
    d = PB[0][0].shape[0]
    PB2 = [[pc.expmi(gens['PB'][j], lam) @ M @ pc.expmi(gens['PB'][j], lam).conj().T for M in PB[j]] for j in range(m)]
    UB2 = [pc.expmi(gens['UB'][j], lam) @ UB[j] @ pc.expmi(gens['UB'][j], lam).conj().T for j in range(m)]
    PA2 = [[pc.expmi(gens['PA'][j], lam) @ M @ pc.expmi(gens['PA'][j], lam).conj().T for M in PA[j]] for j in range(m)]
    UA2 = [pc.expmi(gens['UA'][j], lam) @ UA[j] @ pc.expmi(gens['UA'][j], lam).conj().T for j in range(m)]
    Psi2 = Psi + lam * gens['S']
    Psi2 = Psi2 / pc.nrm(Psi2)
    eta = pc.hypotheses_eta(PA2, UA2, PB2, UB2, Psi2, types)
    res = pc.run_protocol(PA2, UA2, PB2, UB2, Psi2, types)
    hist = pc.history_aggregates(PA2, UA2, PB2, UB2, Psi2, types)
    sumF = pc.trace_F(PB2, Psi2, types)
    hb = sum(p + (u + c) / SQ2 for (p, u, c, D) in hist)
    t = res['Dvec']
    tau = 20 * m ** 3 * eta
    r = {
        'r_D': res['Dvec'] / hb,
        'r_B': res['Dvec'] / (7 * m ** 3 * eta),
        'r_p': max(p / ((3 * j * j + 1) * eta) for j, (p, u, c, D) in enumerate(hist)),
        'r_u': max(u / ((2 * j * j + 1) * eta) for j, (p, u, c, D) in enumerate(hist)),
        'r_c': max(c / ((1 + 2 * SQ2 * j) * eta) for j, (p, u, c, D) in enumerate(hist)),
        'r_Delta': max((D / (j * eta) if j > 0 else 0.0) for j, (p, u, c, D) in enumerate(hist)),
        'r_C': (sumF - res['EN']) / (m * (m - 1) * eta) if m > 1 else 0.0,
        'r_Dst': (res['EN'] - res['I_omega']) / (6 * m * t + 2 * pc.g(min(t, 1.0))),
        'r_1': (sumF - res['I_omega']) / (m * (m - 1) * eta + 6 * m * tau + 2 * pc.g(min(tau, 1.0))),
    }
    return r


def random_gens(d, m, dE):
    return {'PB': [pc.herm(d) for _ in range(m)], 'UB': [pc.herm(d) for _ in range(m)],
            'PA': [pc.herm(d) for _ in range(m)], 'UA': [pc.herm(d) for _ in range(m)],
            'S': (pc.rng.standard_normal((d, d, dE)) + 1j * pc.rng.standard_normal((d, d, dE)))}


def mix(g1, g2, s):
    out = {}
    for k in g1:
        if k == 'S':
            out[k] = g1[k] + s * g2[k]
        else:
            out[k] = [a + s * b for a, b in zip(g1[k], g2[k])]
    return out


def scale_mask(g, mask):
    out = {}
    for k in g:
        f = mask.get(k, 1.0)
        out[k] = g[k] * f if k == 'S' else [a * f for a in g[k]]
    return out


def main():
    pc.rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
    keys = ['r_D', 'r_B', 'r_p', 'r_u', 'r_c', 'r_Delta', 'r_C', 'r_Dst', 'r_1']
    overall = {k: 0.0 for k in keys}
    for types in (['t', 't'], ['t', 't', 't']):
        PA, UA, PB, UB, Psi, ks = pc.build_exact(types)
        # give the environment room for state noise
        d = PB[0][0].shape[0]
        Psi = np.concatenate([Psi, np.zeros((d, d, 2), dtype=complex)], axis=2)
        base = (PA, UA, PB, UB, Psi)
        m = len(types)
        dE = Psi.shape[2]
        iters = 60 if m == 2 else 25
        for target in keys:
            for mask in ({}, {'PA': 0, 'UA': 0, 'S': 0}, {'PB': 0, 'UB': 0, 'PA': 0, 'UA': 0}, {'PB': 0, 'PA': 0, 'UA': 0, 'S': 0}):
                for lam in (1e-3, 3e-2):
                    gens = scale_mask(random_gens(d, m, dE), mask)
                    best = evaluate(base, gens, lam, types)[target]
                    step = 0.5
                    for it in range(iters):
                        cand = scale_mask(mix(gens, random_gens(d, m, dE), step), mask)
                        val = evaluate(base, cand, lam, types)[target]
                        if val > best:
                            gens, best = cand, val
                        else:
                            step *= 0.97
                    overall[target] = max(overall[target], best)
            print(f"m={m} {target}: running max = {overall[target]:.4f}", flush=True)
    print("FINAL maxima (each must be <= 1):")
    for k in keys:
        print(f"  {k}: {overall[k]:.4f}")


if __name__ == "__main__":
    main()
