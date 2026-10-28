"""Complementary window count (15.9) for the complementary mask, and the
dimension bookkeeping d_N = 2^(3N+k_N) ell_N with the sqrt(N) admission budget of Lemma 15.5.

(15.9): for f_N(x) = 1 - sum_{e in S} 1{x = 4^e mod 4^(e+1)} on Z/2^N, every cyclic window
      sum_{j=1..N} f_N(x-j) equals lambda_N N + O(log N).  The proof of Lemma 15.6 gives the
      explicit bound |count - lambda_N N| <= (s+1) + 1 + 1/3, s = floor(log_4 N).
We test it exhaustively over all x, for even N up to 22 and many subsets S (random, all, empty,
only large e, only small e).

Run:  python -u check_window_count.py
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import numpy as np


def window_stats(N, S):
    n = 1 << N
    x = np.arange(n, dtype=np.int64)
    unfl = np.zeros(n, dtype=np.int8)
    for e in S:
        unfl |= ((x % (4 ** (e + 1))) == 4 ** e).astype(np.int8)
    f = (1 - unfl).astype(np.int32)
    lam = 1.0 - sum(4.0 ** -(e + 1) for e in S)
    assert abs(f.mean() - lam) < 1e-12
    ext = np.concatenate([f, f[:N]])
    cs = np.concatenate([[0], np.cumsum(ext, dtype=np.int64)])
    # window ending just before x (i.e. x-N..x-1) == window starting at x-N; all cyclic windows
    w = cs[N:N + n] - cs[0:n]
    dev = np.abs(w - lam * N)
    s = int(math.floor(math.log(N, 4)))
    bound = (s + 1) + 1 + 1.0 / 3
    return lam, int(w.max()), int(w.min()), float(dev.max()), bound


def main():
    rng = np.random.default_rng(5)
    allok = True
    print(" N   |S|  lambda_N   max_win  min_win  max|win-lam*N|  bound  k_N-lam*N")
    for N in range(4, 23, 2):
        E = list(range(N // 2))
        subsets = [[], E, E[:1], E[-1:], E[: len(E) // 2], E[len(E) // 2:]]
        for _ in range(4):
            subsets.append(sorted(rng.choice(E, size=rng.integers(1, len(E) + 1), replace=False).tolist()))
        for S in subsets:
            lam, mx, mn, dev, bound = window_stats(N, S)
            ok = dev <= bound + 1e-12
            allok &= ok
            kN = 1 + mx
            if S in (E, subsets[-1]) or not ok:
                print(f"{N:3d} {len(S):4d}  {lam:.6f}  {mx:7d}  {mn:7d}  {dev:12.4f}  {bound:6.3f}  {kN - lam * N:8.4f}"
                      + ("" if ok else "  <-- VIOLATION"))
    print("window bound (15.9) holds in every tested case:", allok)

    # Dimension bookkeeping with an adversarial certificate schedule (toy):
    # pretend K = {0,1,3,4,6,...} with certificate sizes a_j = 3^j bits, enumerated at stage 2^j.
    print("\nadmission schedule toy (a_j = 3^j bits, appears at stage 2^j):")
    K = [e for e in range(40) if e % 3 != 2]
    cert = [(e, 3 ** j, 2 ** j) for j, e in enumerate(K)]
    theta = sum(4.0 ** -(e + 1) for e in K)
    lam_inf = 1 - theta
    for N in [16, 64, 256, 1024, 4096, 16384, 65536, 2 ** 20]:
        Sset = []; tot = 0
        for (e, a, stage) in cert:
            if stage <= N and e < N // 2 and tot + a <= math.isqrt(N):
                Sset.append(e); tot += a
            else:
                break
        lamN = 1 - sum(4.0 ** -(e + 1) for e in Sset)
        print(f"  N={N:8d}  |S_N|={len(Sset):2d}  log2 L_N<={tot:5d} (sqrt N={math.isqrt(N):5d})  "
              f"lambda_N-lambda={lamN - lam_inf:.3e}  (log2 L_N)/N={tot / N:.2e}")
    print("\nALL PASS" if allok else "\nSOME FAIL")


if __name__ == "__main__":
    main()
