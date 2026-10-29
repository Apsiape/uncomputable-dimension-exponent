"""Finite rotation/multiplier histories. Single threaded; no scipy required.
This checks finite examples, not dimension-uniform stability.
"""
import os
for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[name] = "1"
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
import json
import math
from pathlib import Path
import numpy as np

OUT = Path(__file__).resolve().parent

def maxabs(x):
    return float(np.max(np.abs(x)))

def finite(alpha, polynomial, nc):
    size = 1 << nc
    w = np.arange(size, dtype=np.int64)
    tail = (w >> 1) | ((w & 1) << (nc - 1))
    inv_tail = ((w << 1) & (size - 1)) | (w >> (nc - 1))
    bit = w & 1
    aclock = sum(3 * 4.0 ** (-i - 1) * ((w >> i) & 1) for i in range(nc))
    aff = maxabs(aclock[tail] - 4 * aclock + 3 * bit)
    flip = maxabs(aclock[tail][w ^ 1] - aclock[tail])
    # U = increment; T maps by inv_tail; X flips bit zero.
    rhs = np.where(bit == 0, w, inv_tail[(tail + 1) % size]) ^ 1
    increment_bad_columns = int(np.count_nonzero(rhs != (w + 1) % size))
    increment_flat = math.sqrt(2 * increment_bad_columns / size)
    assert increment_bad_columns == 1

    periods = []
    for fuel in w:
        k = 0
        while k < nc and ((int(fuel) >> k) & 1):
            k += 1
        periods.append(1 << k)
    periods = np.array(periods)
    age = w[None, :] % periods[:, None]
    z = (age == 0).astype(float)
    reset_rhs = ((1 - bit)[:, None] + bit[:, None] * (1 - bit)[None, :]
                 * z[tail[:, None], tail[None, :]])
    assert maxabs(z - reset_rhs) == 0

    inputs = np.array([0.0, 1.0, .9, .5, .3, .125, .02, 2.0**-20, 2.0**-100])
    phase = age * alpha - np.floor(age * alpha)
    carry = np.floor((age + 1) * alpha) - np.floor(age * alpha)
    c = np.empty((len(inputs), size, size))
    d = np.empty_like(c)
    h = np.empty_like(c)
    p = np.empty_like(c)
    penalties = []
    stop_indices = []
    for ix, t in enumerate(inputs):
        if t == 0:
            stop = 10**6
            s = 0.0
        else:
            k = math.floor(math.log2(1 / t))
            stop = math.ceil((k + 1) / alpha) - 1
            assert math.floor(stop * alpha) == k
            s = 2.0 ** (-stop - 1)
            assert s <= t ** (1 / alpha) * (1 + 1e-12)
        penalties.append(s)
        stop_indices.append(stop)
        run_age = np.minimum(age, stop)
        c[ix] = t * np.exp2(np.floor(run_age * alpha))
        d[ix] = s * np.exp2(run_age)
        h[ix] = age <= stop
        p[ix] = age == stop
    t = inputs[:, None, None]
    s = np.array(penalties)[:, None, None]
    zplus = np.roll(z, -1, axis=1)
    residuals = {
        "reset": maxabs(z - reset_rhs),
        "phase_init": maxabs(z * phase),
        "phase_transition": maxabs(np.roll(phase, -1, axis=1) - (1-zplus)*(phase+alpha-carry)),
        "C_init": maxabs(z*(c-t)),
        "D_init": maxabs(z*(d-s)),
        "H_init": maxabs(z*(h-1)),
        "H_transition": maxabs(np.roll(h, -1, axis=2) - zplus - (1-zplus)*(h-p)),
        "C_transition": maxabs(np.roll(c, -1, axis=2) - zplus*t - (1-zplus)*c*(1+carry*(h-p))),
        "D_transition": maxabs(np.roll(d, -1, axis=2) - zplus*s - (1-zplus)*d*(1+h-p)),
        "stop": maxabs((d-.5)*p),
        "root": abs(polynomial(alpha)),
    }
    assert max(residuals.values()) < 2e-12, residuals
    assert min(np.min(c), np.min(d), np.min(phase)) >= -1e-14
    assert max(np.max(c), np.max(d), np.max(phase)) <= 1+1e-14
    assert maxabs(p*(1-h)) == 0
    return {"clock_bits": nc, "diagonal_dimension": int(c.size),
            "max_new_residual": max(residuals.values()), "residuals": residuals,
            "clock_affine_norm": aff, "clock_flip_norm": flip,
            "increment_flat_norm": increment_flat,
            "increment_bad_columns": increment_bad_columns,
            "penalty_flat_norm": float(np.sqrt(np.mean(s*s))),
            "stop_indices": stop_indices}

def columns_and_bound():
    # Noncommuting P_h,E_h; completeness is algebraic and independent of relations.
    rng = np.random.default_rng(271028)
    dim, depth = 7, 11
    ident = np.eye(dim)
    k = ident.copy()
    completeness = np.zeros((dim,dim))
    for _ in range(depth):
        u, _ = np.linalg.qr(rng.standard_normal((dim,dim)))
        v, _ = np.linalg.qr(rng.standard_normal((dim,dim)))
        e = u[:, :3] @ u[:, :3].T
        p = v[:, :4] @ v[:, :4].T
        bad = (ident-e) @ k
        stop = p @ e @ k
        k = (ident-p) @ e @ k
        completeness += bad.T@bad + stop.T@stop
    completeness += k.T@k
    error = maxabs(completeness-ident)
    assert error < 1e-12
    return error

def schedule(alpha, degree):
    j = np.arange(1, 100001, dtype=float)
    count = np.floor(j*alpha)
    fraction = j*alpha-count
    gap = np.minimum(fraction, 1-fraction)
    weighted = gap * j**(degree-1)
    assert np.min(gap) > 0
    # This finite scan is diagnostic; the report proves the all-j separation.
    return {"depth": len(j), "min_wrap_gap": float(np.min(gap)),
            "min_Liouville_scaled_gap": float(np.min(weighted)),
            "max_log_product_discrepancy": float(np.max(np.abs(count-alpha*j))),
            "ratio_at_final_depth": float(count[-1]/j[-1])}

def main():
    examples = [("sqrt(2)/2", math.sqrt(2)/2, lambda x: 2*x*x-1, 2),
                ("golden_conjugate", (math.sqrt(5)-1)/2, lambda x: x*x+x-1, 2),
                ("cube_root(1/2)", 2**(-1/3), lambda x: 2*x*x*x-1, 3)]
    result = {"thread_limits": {name: os.environ[name] for name in
              ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS")},
              "noncommuting_history_completeness_error": columns_and_bound(), "examples": []}
    for name, alpha, polynomial, degree in examples:
        result["examples"].append({"name": name, "alpha": alpha,
            "finite_models": [finite(alpha, polynomial, nc) for nc in (2,3,5,7)],
            "schedule": schedule(alpha, degree)})
    result["status"] = "PASS (finite examples only)"
    (OUT / "numerics.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(result["status"])
    for case in result["examples"]:
        print(case["name"], "max new residual", max(x["max_new_residual"] for x in case["finite_models"]),
              "schedule ratio", case["schedule"]["ratio_at_final_depth"])
    print("noncommuting completeness error", result["noncommuting_history_completeness_error"])

if __name__ == "__main__":
    main()
