"""Exact checks for the pairwise hash bound (hashing barrier for pairwise lamp certificates).

Model: H = l^2(Hfam) (x) (C^2)^{(x)K}, Hfam = {h_{a,b}(u) = ((a*u + b) mod p) mod K : a in 1..p-1, b in 0..p-1},
X_u = sum_h |h><h| (x) X_{h(u)},  Z_u = sum_h |h><h| (x) Z_{h(u)}.
Exact: X_u^2 = Z_u^2 = I, X_u Z_u = -Z_u X_u, [X_u,X_w] = [Z_u,Z_w] = 0, (X_u Z_u)^2 = -I.
Cross: X_u Z_w - Z_w X_u = 0 on blocks with h(u) != h(w), and has norm 2 (it is 2 X Z on that qubit) otherwise, so
||[X_u,Z_w]||_2^2 (normalized) = 4 * Pr_h[h(u) = h(w)].

Part 1 builds the actual matrices for tiny parameters and checks every relation numerically (dense numpy, single thread).
Part 2 computes collision probabilities exactly (combinatorially) for larger parameters and tabulates
   log2 D = K + log2|Hfam|   against   kappa^2 = max_{u != w} 4 Pr[h(u)=h(w)],
showing log2 D <= 8/kappa^2 + 2 log2 p + O(1) for arbitrarily many lamps |U| <= p.
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1"
import json
import math
import sys
from itertools import product

import numpy as np

X1 = np.array([[0, 1], [1, 0]], dtype=float)
Z1 = np.array([[1, 0], [0, -1]], dtype=float)
I1 = np.eye(2)


def pauli_on(K, q, P):
    out = np.array([[1.0]])
    for j in range(K):
        out = np.kron(out, P if j == q else I1)
    return out


def hfam(p, K):
    return [(a, b) for a in range(1, p) for b in range(p)]


def hval(ab, u, p, K):
    a, b = ab
    return ((a * u + b) % p) % K


def part1():
    res = {}
    for (p, K, U) in ((5, 2, 5), (5, 3, 5), (7, 2, 4)):
        fam = hfam(p, K)
        nb = len(fam)
        dimreg = 2 ** K
        D = nb * dimreg
        Xs, Zs = [], []
        for u in range(U):
            Xu = np.zeros((D, D))
            Zu = np.zeros((D, D))
            for i, ab in enumerate(fam):
                q = hval(ab, u, p, K)
                sl = slice(i * dimreg, (i + 1) * dimreg)
                Xu[sl, sl] = pauli_on(K, q, X1)
                Zu[sl, sl] = pauli_on(K, q, Z1)
            Xs.append(Xu)
            Zs.append(Zu)
        I = np.eye(D)
        nhs = lambda M: math.sqrt(np.sum(M * M) / D)  # normalized Hilbert-Schmidt (real matrices)
        maxexact = 0.0
        maxpred = 0.0
        for u in range(U):
            maxexact = max(maxexact, nhs(Xs[u] @ Xs[u] - I), nhs(Zs[u] @ Zs[u] - I),
                           nhs(Xs[u] @ Zs[u] + Zs[u] @ Xs[u]),
                           nhs((Xs[u] @ Zs[u]) @ (Xs[u] @ Zs[u]) + I))
            for w in range(U):
                if w == u:
                    continue
                maxexact = max(maxexact, nhs(Xs[u] @ Xs[w] - Xs[w] @ Xs[u]), nhs(Zs[u] @ Zs[w] - Zs[w] @ Zs[u]))
                c = nhs(Xs[u] @ Zs[w] - Zs[w] @ Xs[u]) ** 2
                pr = sum(1 for ab in fam if hval(ab, u, p, K) == hval(ab, w, p, K)) / nb
                maxpred = max(maxpred, abs(c - 4 * pr))
        res["p%d_K%d_U%d" % (p, K, U)] = {"dim": D, "max_exact_relation_error": maxexact,
                                          "max_|HS^2 - 4Pr(collision)|": maxpred}
        assert maxexact < 1e-12 and maxpred < 1e-12
    return res


def collision_max(p, K, U):
    """max over u != w < U of Pr_{a,b}[((a u + b) mod p) mod K == ((a w + b) mod p) mod K], exactly."""
    best = 0.0
    nb = (p - 1) * p
    # depends only on d = (w-u) mod p; for each a, x=(a u + b) runs over Z_p, y = x + a d.
    for d in range(1, min(U, p)):
        cnt = 0
        for a in range(1, p):
            s = (a * d) % p
            for x in range(p):
                if x % K == ((x + s) % p) % K:
                    cnt += 1
        best = max(best, cnt / nb)
    return best


def part2():
    rows = []
    for K in (4, 8, 16, 32, 64):
        for p in (131, 1031):
            if p < K:
                continue
            U = p  # number of lamps: as many as the prime allows; any |U| <= p works
            pr = collision_max(p, K, U)
            kappa2 = 4 * pr
            log2D = K + math.log2((p - 1) * p)
            rows.append({"K": K, "p": p, "lamps": U, "kappa^2": kappa2, "8/kappa^2": 8 / kappa2,
                         "log2D": log2D, "barrier_holds(log2D<=8/k^2+2log2p+1)": log2D <= 8 / kappa2 + 2 * math.log2(p) + 1,
                         "signed_regular_certifies_at_most": 1 / (50 * kappa2)})
            assert rows[-1]["barrier_holds(log2D<=8/k^2+2log2p+1)"]
    return rows


def main():
    out = {"part1_tiny_exact": part1(), "part2_barrier_table": part2()}
    with open(sys.argv[1] if len(sys.argv) > 1 else "hash_barrier.json", "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out["part1_tiny_exact"], indent=1), flush=True)
    for r in out["part2_barrier_table"]:
        print(r, flush=True)
    print("ALL CHECKS PASSED", flush=True)


if __name__ == "__main__":
    main()
