"""Non-trivial check of inequality (1) itself: perturbations small enough that the tested extraction lower bound is positive.
Uses the builders of protocol_check.py.  Single-threaded."""
import sys
import protocol_check as pc

print("=== tiny perturbations: RHS(1) positive, so (1) is tested non-trivially ===")
for seed in (1, 2, 3):
    pc.rng = pc.np.random.default_rng(100 + seed)
    for types in [('t',), ('t', 't'), ('b', 't'), ('t', 't', 't'), ('b', 't', 't')]:
        for lamB, lamS in [(1e-7, 1e-12), (1e-6, 1e-11), (3e-7, 0.0), (0.0, 1e-12)]:
            pc.one_case(list(types), lamB, lamB, lamS)
