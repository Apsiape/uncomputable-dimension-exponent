"""Window counts (28)-(29) and the dimension 3N + k_N for larger even N.

For each flag set K_N, f_N(x) = sum_{e in K_N} 1{x = 4^e mod 4^{e+1}} on
Z/2^N, k_N = 1 + max_x sum_{j=1}^N f_N(x-j).  The claim is
max/min window = N theta_N + O(log N), hence log2 d_N = (3+theta_N)N + O(log N).
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import sys
import json
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e2_model import halting_time  # noqa: E402


def h_closed(e):
    """Halting time of the test program M (validated against simulation)."""
    if e == 0:
        return 6
    if e == 1:
        return None
    return 5 + 13 * (4 ** e - 1) // 3 + 3 * e + 1 + 4 ** e + 1


def windows(N, K):
    n = 1 << N
    x = np.arange(n, dtype=np.int64)
    f = np.zeros(n, dtype=np.int32)
    for e in K:
        f += ((x % 4 ** (e + 1)) == 4 ** e)
    assert f.max() <= 1
    ext = np.concatenate([f, f[:N]])
    cs = np.concatenate([[0], np.cumsum(ext, dtype=np.int64)])
    w = cs[N:N + n] - cs[:n]
    return int(w.max()), int(w.min()), float(f.mean())


def main():
    for e in range(0, 8):
        hs = halting_time(e, 200000)
        assert hs == h_closed(e), (e, hs, h_closed(e))
    rng = np.random.default_rng(20261027)
    out = []
    for N in range(4, 25, 2):
        half = N // 2
        KM = [e for e in range(half) if h_closed(e) is not None and h_closed(e) < 2 ** N]
        Kall = list(range(half))
        Keven = list(range(0, half, 2))
        Krand = [e for e in range(half) if rng.random() < 0.5] or [0]
        row = dict(N=N, log2N=float(np.log2(N)))
        for nm, K in (("M", KM), ("all", Kall), ("even", Keven), ("rand", Krand)):
            wmax, wmin, mean = windows(N, K)
            theta = sum(4.0 ** (-(e + 1)) for e in K)
            assert abs(theta - mean) < 1e-12
            row[nm] = dict(K=K, theta=theta, Ntheta=N * theta, wmax=wmax, wmin=wmin,
                           kN=1 + wmax, log2dim=3 * N + 1 + wmax,
                           over=wmax - N * theta, under=N * theta - wmin)
        out.append(row)
        print(N, " ".join(f"{nm}: k={row[nm]['kN']} Ntheta={row[nm]['Ntheta']:.3f} over={row[nm]['over']:.3f} "
                          f"under={row[nm]['under']:.3f}" for nm in ("M", "all", "even", "rand")), flush=True)
    od = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
    with open(os.path.join(od, "dims_study.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
