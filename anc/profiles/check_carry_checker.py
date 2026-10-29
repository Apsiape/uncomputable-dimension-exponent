"""Exact finite checks for the carry-coordinate checker clocks in the profile part.

Single-threaded, standard library only, exact Fraction arithmetic. Operators on the N-qubit
registers are stored as diagonals (lists of Fractions) or as basis permutations, never as dense
matrices. Writes carry_checker.json next to this file.

Rerun:  python -u check_carry_checker.py
"""
import json
import math
import os
from fractions import Fraction as Fr

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "carry_checker.json")


def bit(x, j):
    return (x >> j) & 1


def rot(x, N):
    """T moves the content of slot j to slot j+1 cyclically."""
    return ((x << 1) & ((1 << N) - 1)) | (x >> (N - 1))


def rot_inv(x, N):
    return (x >> 1) | ((x & 1) << (N - 1))


def cantor(x, N):
    return sum(Fr(3 * bit(x, j), 4 ** (j + 1)) for j in range(N))


def init_ones(x, N):
    k = 0
    while k < N and bit(x, k) == 1:
        k += 1
    return k


def conj_diag(d, N):
    """T diag(d) T^*: the value at y is d(T^{-1} y)."""
    return [d[rot_inv(y, N)] for y in range(1 << N)]


def single_clock_checks(N):
    D = 1 << N
    A = [cantor(x, N) for x in range(D)]
    P = [Fr(bit(x, 0)) for x in range(D)]
    TAT = conj_diag(A, N)
    affine = [TAT[x] - 4 * A[x] + 3 * P[x] for x in range(D)]
    # affine defect must be exactly 3*4^{-N} P
    assert all(affine[x] == Fr(3, 4 ** N) * P[x] for x in range(D))
    # [X, TAT*]: X flips bit 0, so (X M X)(x) = M(x^1); commutator of X with diagonal M
    # has entries M(x^1)-M(x) on the off-diagonal pattern; check it equals 3*4^{-N}[X,P].
    for x in range(D):
        assert TAT[x ^ 1] - TAT[x] == Fr(3, 4 ** N) * (P[x ^ 1] - P[x])
    # carry coordinate
    H = [Fr(0) if init_ones(x, N) == N else Fr(1, 4 ** init_ones(x, N)) for x in range(D)]
    THT = conj_diag(H, N)
    for x in range(D):
        assert H[x] == (1 - P[x]) + Fr(1, 4) * P[x] * THT[x], ("carry recursion", N, x)
    # carry step: (U^* A U)(x) = A(x+1); defect A(x+1) - A(x) + 1 - 7/4 H(x)
    carry_def = [A[(x + 1) % D] - A[x] + 1 - Fr(7, 4) * H[x] for x in range(D)]
    nz = [x for x in range(D) if carry_def[x] != 0]
    assert nz == [D - 1] and carry_def[D - 1] == Fr(1, 4 ** N)
    # unguarded increment  U - X[(I-P) + (T U T^*) P]  applied to basis vectors
    # T U T^* |y> = T U |rot_inv(y)> = |rot(rot_inv(y)+1)>
    def tut(y):
        return rot((rot_inv(y, N) + 1) % D, N)

    bad = []
    for x in range(D):
        lhs = {(x + 1) % D: 1}
        if bit(x, 0) == 0:
            y = x
        else:
            y = tut(x)
        y ^= 1  # X flips bit 0
        rhs = {y: 1}
        diff = dict(lhs)
        for key, v in rhs.items():
            diff[key] = diff.get(key, 0) - v
        diff = {k: v for k, v in diff.items() if v != 0}
        if diff:
            bad.append((x, diff))
    assert len(bad) == 1 and bad[0][0] == D - 1
    unguarded_flat_sq = Fr(sum(v * v for v in bad[0][1].values()), D)  # = 2/2^N
    assert unguarded_flat_sq == Fr(2, D)
    # weighted/flat norms (squared) of the carry step and affine defects
    carry_flat_sq = Fr(1, 4 ** (2 * N)) / D
    affine_flat_sq = Fr(9, 4 ** (2 * N)) * Fr(D // 2, D)
    return {
        "N": N,
        "affine_defect_op": float(Fr(3, 4 ** N)),
        "affine_defect_flat": math.sqrt(affine_flat_sq),
        "carry_step_defect_op": float(Fr(1, 4 ** N)),
        "carry_step_defect_flat": math.sqrt(carry_flat_sq),
        "unguarded_increment_defect_flat": math.sqrt(unguarded_flat_sq),
    }


def reset_and_interface_checks(N):
    """Fuel and time N-bit clocks, time increment U = +1, reset Z(q,t)=1{t = 0 mod 2^{k(q)}}.

    Checks the reset recursion exactly and the exact-model content of interface items (i),(ii):
    Z Q = Q and Z_h Q = 0 for 1 <= h < 2^k, where Q = fuel prefix 1^k 0 and time prefix 0^k.
    """
    D = 1 << N

    def kq(q):
        return init_ones(q, N)

    def Z(q, t):
        return 1 if t % (1 << kq(q)) == 0 else 0

    for q in range(D):
        for t in range(D):
            pf, pt = bit(q, 0), bit(t, 0)
            wzw = Z(rot_inv(q, N), rot_inv(t, N))
            rhs = (1 - pf) + pf * (1 - pt) * wzw
            assert Z(q, t) == rhs, ("reset", N, q, t)
    checked = 0
    for k in range(0, N):
        for q in range(D):
            # fuel prefix 1^k then 0
            if not (all(bit(q, i) == 1 for i in range(k)) and bit(q, k) == 0):
                continue
            for t in range(D):
                if any(bit(t, i) for i in range(k)):
                    continue
                assert Z(q, t) == 1  # (i): Z Q = Q
                for h in range(1, 1 << k):
                    # Z_h = U^{-h} Z U^h acts at (q,t) as Z(q, t+h)
                    assert Z(q, (t + h) % D) == 0  # (ii)
                    checked += 1
    return {"N": N, "reset_recursion_exact": True, "interface_points_checked": checked}


def two_adic_lipschitz_checks(Dd=9, hs=(1, 2, 3, 5, 7, 13, 31, 64, 100, 255)):
    """On the depth-Dd truncation of the Cantor set K (2-adic integers mod 2^Dd):
    g_h(x)=x+h is 2-Lipschitz, the digit f_i is 2*4^i-Lipschitz, f_i o g_{-h} is 4^{i+1}-Lipschitz,
    f_i o g_{-h} o g_h = f_i, and the cylinders B_0, B_h (x = 0, resp. h, mod 2^k) are disjoint.
    Pairs are compared through their first differing digit, exactly as in the proof."""
    M = 1 << Dd
    c = [cantor(x, Dd) for x in range(M)]
    worst = {"g_h": Fr(0), "f_i": Fr(0), "f_i_g_minus_h": Fr(0)}
    # Lipschitz ratio bound: |F(x)-F(y)| <= L |c(x)-c(y)|; check max ratio over all pairs.
    import itertools
    pairs = list(itertools.combinations(range(M), 2))
    for h in hs:
        for x, y in pairs:
            dx = abs(c[x] - c[y])
            r = abs(c[(x + h) % M] - c[(y + h) % M]) / dx
            if r > worst["g_h"]:
                worst["g_h"] = r
    assert worst["g_h"] <= 2
    for i in range(0, 5):
        for x, y in pairs:
            dx = abs(c[x] - c[y])
            r = abs(bit(x, i) - bit(y, i)) / dx / Fr(4 ** i)
            if r > worst["f_i"]:
                worst["f_i"] = r
            for h in (1, 3, 7, 20):
                r2 = abs(bit((x - h) % M, i) - bit((y - h) % M, i)) / dx / Fr(4 ** (i + 1))
                if r2 > worst["f_i_g_minus_h"]:
                    worst["f_i_g_minus_h"] = r2
    assert worst["f_i"] <= 2 and worst["f_i_g_minus_h"] <= 1
    for k in range(1, 6):
        for h in range(1, 1 << k):
            B0 = {x for x in range(M) if x % (1 << k) == 0}
            Bh = {x for x in range(M) if (x - h) % (1 << k) == 0}
            assert not (B0 & Bh)
    return {k: float(v) for k, v in worst.items()}


def cost_table():
    """Clock bits needed for loss 2^{-n} (flat precision about 2^{-n/2}), versus the forced count."""
    rows = []
    for n in (16, 32, 64, 128, 256):
        target = Fr(1, 2 ** (n // 2))
        # carry checker: affine flat defect 3*4^{-N}/sqrt(2) dominates
        Nc = 1
        while Fr(9, 2 * 4 ** (2 * Nc)) > target * target:
            Nc += 1
        Nu = 1
        while Fr(2, 2 ** Nu) > target * target:
            Nu += 1
        rows.append({"n": n, "forced_count_bits_log4(1/delta)": n / 4,
                     "carry_checker_bits": Nc, "unguarded_checker_bits": Nu})
    return rows


def main():
    res = {"single_clock": [], "reset_interface": []}
    for N in range(2, 11):
        res["single_clock"].append(single_clock_checks(N))
    for N in range(2, 9):
        res["reset_interface"].append(reset_and_interface_checks(N))
    res["two_adic_lipschitz_worst_ratios_normalized"] = two_adic_lipschitz_checks()
    res["cost_table"] = cost_table()
    for row in res["single_clock"]:
        print(row, flush=True)
    for row in res["reset_interface"]:
        print(row, flush=True)
    print("2-adic Lipschitz (normalized worst ratios):", res["two_adic_lipschitz_worst_ratios_normalized"], flush=True)
    for row in res["cost_table"]:
        print(row, flush=True)
    with open(OUT, "w") as f:
        json.dump(res, f, indent=1)
    print("ALL CARRY-CHECKER ASSERTIONS PASSED; wrote", os.path.basename(OUT), flush=True)


if __name__ == "__main__":
    main()
