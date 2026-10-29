"""Lighter m = 3 (three ternary stages) adversarial hill-climb; same ratios as adversarial_search.py.
Two masks (all perturbations; Bob-only), lam = 1e-3, 20 steps per target.  Single-threaded."""
import sys
import numpy as np
import protocol_check as pc
import adversarial_search as ad

pc.rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 13)
types = ['t', 't', 't']
PA, UA, PB, UB, Psi, ks = pc.build_exact(types)
d = PB[0][0].shape[0]
Psi = np.concatenate([Psi, np.zeros((d, d, 2), dtype=complex)], axis=2)
base = (PA, UA, PB, UB, Psi)
dE = Psi.shape[2]
keys = ['r_D', 'r_B', 'r_C', 'r_Dst', 'r_1', 'r_p', 'r_Delta']
for target in keys:
    best_all = -np.inf
    for mask in ({}, {'PA': 0, 'UA': 0, 'S': 0}):
        gens = ad.scale_mask(ad.random_gens(d, 3, dE), mask)
        best = ad.evaluate(base, gens, 1e-3, types, target=target)[target]
        step = 0.5
        for it in range(20):
            cand = ad.scale_mask(ad.mix(gens, ad.random_gens(d, 3, dE), step), mask)
            val = ad.evaluate(base, cand, 1e-3, types, target=target)[target]
            if val > best:
                gens, best = cand, val
            else:
                step *= 0.95
        best_all = max(best_all, best)
    print(f"m=3 {target}: max = {best_all:.4f}", flush=True)
