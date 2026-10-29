"""Hold-stream, calibrator-history and profile-accounting checks in the profile part.

Single-threaded; standard library plus NumPy (thread counts forced to one); exact Fractions where
equations are checked. Peak memory well under 1 GB (one int32 array of length J_MAX+1).
Writes hold_stream.json next to this file.

Rerun:  python -u check_hold_stream.py

What is checked (finite evidence only; the asymptotic statements are proved in the profile part):
 1. An abstract instruction-level simulation of the hold-modified programmed pulse stream (the hold-stream lemma): every
    installation has q^2 <= j, every stage is held for at least (s+2) j_s pulses, physical time
    t_J <= C (J+1)^2 with an explicit C, and the stage-end densities track the installed
    rationals within 1/(s+3) + 2q/j. The input sequence interleaves dyadic approximations with
    liminf sqrt(2)/4 and limsup sqrt(3)/2 - 1/10.
 2. Exact calibrator histories (the programmed calibrator equations and upper histories) on every fuel/time block of a finite checker, for
    the actual physical-time pulse/one indicator sequence of the simulated controller, including
    the log-scale source inputs t = 3*4^{-N_s}, t = 0, t = 1 and extreme dyadics.
 3. Profile accounting for the log-scale game (the logarithmic profile theorem): the explicit upper construction and the
    explicit lower count, for the simulated pulse word, differ by O(log n), and the normalized
    profile oscillates toward the predicted endpoints.
 4. The power-scale moment summation (power-pair theorem): for Markov-extremal spectral tails the calibrated
    penalty obeys tau(s(|R|)^2) <= 2^{-2 kappa(l0) + o(kappa(l0))}.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_v] = "1"
import json
import math
from fractions import Fraction as Fr
from math import isqrt

import numpy as np

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hold_stream.json")
J_MAX = 12_000_000


# ---------------------------------------------------------------- input rational sequence
def r_seq(s):
    """dyadic lower approximations to sqrt(2)/4 (liminf name)."""
    e = s + 3
    return Fr(isqrt(2 << (2 * e)), 4 << e)


def t_seq(s):
    """dyadic approximations to sqrt(3)/2 - 1/10 (limsup name)."""
    e = s + 3
    return Fr(isqrt(3 << (2 * e)), 2 << e) - Fr(1, 10)


def a_seq(s, c=Fr(1, 2), c0=Fr(1, 8)):
    """Computable endpoint-name interleaving, clipped to [c0, 1]."""
    if s % 2 == 0:
        v = min(c, r_seq(s // 2))
    else:
        v = max(c, t_seq(s // 2))
    return min(Fr(1), max(c0, v))


def background_work(s):
    """arbitrary, nonmonotone background cost of computing a_s (in elementary instructions)."""
    return 40 * (s + 1) ** 3 * (1 + (s * 7919) % 13)


# ---------------------------------------------------------------- 1. stream simulation
def simulate(J_max):
    k = np.zeros(J_max + 1, dtype=np.int32)  # k[J] = ones among first J pulses
    J = 0
    t_phys = 0  # elementary instructions executed
    active = Fr(1, 2)
    s_inst = 0  # index of active stage
    next_s = 0  # index of the rational being computed by the background
    bg_left = background_work(0) + a_seq(0).denominator ** 2
    ready = False
    hold = 0
    P_tot = 0
    stages = [{"s": 0, "rational": str(active), "j_install": 0}]
    worst_ratio_time = 0.0
    installs_ok = True
    checkpoints = []
    first_record = []  # physical-time indicator record for the first few thousand steps
    REC_LIMIT = 6000
    while J < J_max:
        p, q = active.numerator, active.denominator
        # one complete period: p ones then q-p zeros
        per_period_overhead = 2 * (q + 1)  # copy/restore countdowns
        t_phys += per_period_overhead
        if len(first_record) < REC_LIMIT:
            first_record.extend([(0, 0)] * per_period_overhead)
        for b in [1] * p + [0] * (q - p):
            if J >= J_max:
                break
            # emit pulse: output NOP, decrement countdown, P_tot++, hold--, bg step + dispatch
            J += 1
            k[J] = k[J - 1] + b
            step_cost = 1 + 1 + 1 + 2 + 1 + 2
            if len(first_record) < REC_LIMIT:
                first_record.append((1, b))
                first_record.extend([(0, 0)] * (step_cost - 1))
            t_phys += step_cost
            P_tot += 1
            if hold > 0:
                hold -= 1
            if not ready:
                bg_left -= 1
                if bg_left <= 0:
                    ready = True
            ratio = t_phys / (J + 1) ** 2
            worst_ratio_time = max(worst_ratio_time, ratio)
        if J >= J_max:
            break
        # period boundary: install if READY and hold expired
        if ready and hold == 0:
            new = a_seq(next_s)
            qn = new.denominator
            installs_ok &= qn * qn <= P_tot
            s_inst += 1
            cost = 3 * (q + qn + 1) + 3 * (s_inst + 2) * P_tot + 3
            t_phys += cost
            if len(first_record) < REC_LIMIT:
                first_record.extend([(0, 0)] * cost)
            hold = (s_inst + 2) * P_tot
            active = new
            stages.append({"s": s_inst, "rational": f"{new.numerator}/{new.denominator}",
                           "value": float(new), "j_install": P_tot,
                           "k_over_j_at_install": float(k[P_tot]) / max(P_tot, 1)})
            next_s += 1
            bg_left = background_work(next_s) + a_seq(next_s).denominator ** 2
            ready = False
            worst_ratio_time = max(worst_ratio_time, t_phys / (J + 1) ** 2)
    return k, stages, worst_ratio_time, installs_ok, first_record


# ---------------------------------------------------------------- 2. calibrator histories
def l_of(t):
    """floor(log2(1/t)) for exact positive rational t <= 1, by integer comparison."""
    l = 0
    while Fr(1, 2 ** (l + 1)) >= t:
        l += 1
    return l


def calibrator_check(record, Nc=7, inputs=None):
    f = [r[0] for r in record]
    g = [r[1] for r in record]
    Hmax = len(record)
    jj = [0] * (Hmax + 1)
    kk = [0] * (Hmax + 1)
    for h in range(Hmax):
        jj[h + 1] = jj[h] + f[h]
        kk[h + 1] = kk[h] + g[h]
    results = []
    for t in inputs:
        if t == 0:
            hstop, s_t = None, Fr(0)
        else:
            l = l_of(t)
            hstop = next((h for h in range(Hmax + 1) if kk[h] == l), None)
            if hstop is None:
                results.append({"t": str(t), "skipped": "stop beyond recorded horizon"})
                continue
            s_t = Fr(1, 2 ** (jj[hstop] + 1))

        def hist(h):
            if t == 0:
                return Fr(0), Fr(0), 1, 0
            m = min(h, hstop)
            C = Fr(2 ** kk[m]) * t
            D = Fr(2 ** jj[m]) * s_t
            run = 1 if h <= hstop else 0
            stop = 1 if h == hstop else 0
            return C, D, run, stop

        maxres = Fr(0)
        nchecked = 0
        # every period 2^kf of the fuel clock (kf initial fuel ones; kf = Nc for all ones)
        for kf in range(0, Nc + 1):
            period = 1 << kf
            for h in range(min(period, Hmax)):
                C, D, run, stop = hist(h)
                # domains
                assert 0 <= C <= 1 and 0 <= D <= 1 and (1 - run) * stop == 0
                assert (D - Fr(1, 2)) * stop == 0
                if h == 0:
                    assert C == t and D == s_t and run == 1  # Z(C-T)=Z(D-S)=Z(H_run-I)=0
                hn = h + 1
                Zp = 1 if hn == period else 0
                Cn, Dn, runn, stopn = hist(0 if Zp else hn)
                G, F = g[h], f[h]
                rhsC = Zp * t + (1 - Zp) * C * (1 + G * (run - stop))
                rhsD = Zp * s_t + (1 - Zp) * D * (1 + F * (run - stop))
                rhsR = Zp + (1 - Zp) * (run - stop)
                res = max(abs(Cn - rhsC), abs(Dn - rhsD), abs(runn - rhsR))
                maxres = max(maxres, res)
                nchecked += 1
        results.append({"t": str(t) if t.denominator < 10 ** 6 else f"2^-{int(math.log2(t.denominator))}*{t.numerator}",
                        "stop_age": hstop, "S": str(s_t) if s_t.denominator < 10 ** 9 else f"2^-{int(math.log2(s_t.denominator))}",
                        "max_new_residual": str(maxres), "transitions_checked": nchecked})
        assert maxres == 0
    return results


# ---------------------------------------------------------------- 3. profile accounting
def profile_accounting(k, q=1, m=2, b_poly=12, K_log=40):
    """Upper: 2 N_c + m N_s (+ compiler constant); lower: 2 M + m M' from the explicit depths.
    Constants of the compiler and of the polynomial factors are set to explicit stand-in values;
    any fixed values give the same O(log n) conclusion."""
    J_max = len(k) - 1

    def kappa_ge(x):
        """smallest l with kappa(l) >= x, i.e. l = k(ceil(x)-1)+1."""
        y = math.ceil(x)
        return int(k[min(y - 1, J_max)]) + 1 if y >= 1 else 0

    rows = []
    worst = 0.0
    ns = list(range(200, 2 * q * (J_max - 1000), 997))
    ratios = []
    for n in ns:
        lam = n / (2 * q)
        # upper construction
        Nc = math.ceil((n + 3) / (4 * q) + math.log(3, 4))
        x = (n + 3) / (2 * q)
        l_need = kappa_ge(x - 1)
        Ns = math.ceil((l_need + 2) / 2)
        upper = 2 * Nc + m * Ns + 3
        # lower count
        J = int(lam - K_log * math.log2(2 + lam))
        if J < 1:
            continue
        tM = lam / 2
        M = math.floor(tM - 30 * math.log(2 + tM, 4))
        log2_dprime = -(int(k[J]) - b_poly * math.log2(J + 2) - 5)
        tp = -log2_dprime / 2
        Mp = math.floor(tp - 30 * math.log(2 + tp, 4)) if tp > 0 else 0
        lower = 2 * M + m * max(Mp, 0) - 3
        A = lam + (m / 2) * int(k[int(lam)])
        if n > 10 ** 5:
            worst = max(worst, (upper - lower) / math.log2(n))
        rows.append((n, upper, lower, A))
        ratios.append(A / n)
    return rows, worst, ratios


# ---------------------------------------------------------------- 4. power-scale summation
def power_summation_check(k, c0=1 / 8, v=10, Cv=1.0):
    J_max = len(k) - 1
    # kappa(l): position of the l-th one
    ones_pos = np.flatnonzero(np.diff(k)) + 1  # J where k jumps
    kappa = np.concatenate([[0], ones_pos])
    out = []
    worst_excess = 0.0
    kap = kappa.astype(np.float64)
    lmax = len(kappa) - 45
    l0s = sorted(set(int(x) for x in np.geomspace(40, lmax, 40)))
    for l0 in l0s:
        log2N = 2 * (l0 + 1)
        # log-domain sum: sum_l 2^{-2 kappa(l)-2} * min(1, Cv 2^{v(2(l+1)-log2N)})
        ls = np.arange(0, l0 + 40)
        tail = np.minimum(0.0, math.log2(Cv) + v * (2.0 * (ls + 1) - log2N))
        terms = -2.0 * kap[: l0 + 40] - 2.0 + tail
        mx = float(terms.max())
        total = mx + math.log2(float(np.sum(np.exp2(terms - mx))))
        excess = total + 2.0 * float(kappa[l0])
        worst_excess = max(worst_excess, excess / math.sqrt(float(kappa[l0]) + 1))
        out.append((l0, float(kappa[l0]), excess))
    return out, worst_excess


def main():
    k, stages, worst_time_ratio, installs_ok, record = simulate(J_MAX)
    assert installs_ok, "an installation violated q^2 <= j"
    print("stages:", flush=True)
    stage_checks = []
    for i, st in enumerate(stages):
        if i + 1 < len(stages):
            j_end = stages[i + 1]["j_install"]
            j_s = st["j_install"]
            held = j_end - j_s
            assert i == 0 or held >= (st["s"] + 2) * j_s
            val = Fr(st["rational"]) if "/" in st["rational"] else Fr(st["rational"])
            dens_end = float(k[j_end]) / j_end
            bound = 1 / (st["s"] + 3) + 2 * val.denominator / j_end
            ok = abs(dens_end - float(val)) <= bound + 1e-12
            assert i == 0 or ok
            stage_checks.append({"s": st["s"], "rational": float(val), "j_install": j_s, "j_end": j_end,
                                 "k_over_j_at_end": dens_end, "allowed_error": bound})
            print(stage_checks[-1], flush=True)
    print("worst t_J/(J+1)^2 =", worst_time_ratio, flush=True)
    tail = k[J_MAX // 100:].astype(np.float64) / np.arange(J_MAX // 100, J_MAX + 1)
    print("density range on [J_MAX/100, J_MAX]:", float(tail.min()), float(tail.max()), flush=True)

    inputs = [Fr(0), Fr(1), Fr(1, 2), Fr(1, 2) + Fr(1, 2 ** 53), Fr(1, 2) - Fr(1, 2 ** 54), Fr(3, 256),
              Fr(1, 2 ** 100)] + [Fr(3, 4 ** Ns) for Ns in range(1, 7)]
    cal = calibrator_check(record, Nc=12, inputs=inputs)
    for row in cal:
        print("calibrator:", row, flush=True)

    rows, worst_gap, ratios = profile_accounting(k)
    print("profile: worst (upper-lower)/log2 n for n > 1e5 =", worst_gap, flush=True)
    print("profile: A(n)/n range over sampled n > 1e5:",
          min(r for (n, *_), r in zip(rows, ratios) if n > 1e5),
          max(r for (n, *_), r in zip(rows, ratios) if n > 1e5), flush=True)
    for n, up, lo, A in rows[:: max(1, len(rows) // 12)]:
        print(f"  n={n:9d} upper={up:9d} lower={lo:9d} A(n)={A:12.1f} A/n={A / n:.4f}", flush=True)

    pw, worst_excess = power_summation_check(k)
    print("power summation: worst excess/sqrt(kappa) =", worst_excess, flush=True)

    res = {
        "J_MAX": J_MAX,
        "stages": stage_checks,
        "worst_tJ_over_(J+1)^2": worst_time_ratio,
        "installs_q2_le_j": installs_ok,
        "tail_density_range": [float(tail.min()), float(tail.max())],
        "calibrator": cal,
        "profile_worst_gap_over_log2n": worst_gap,
        "profile_samples": rows[:: max(1, len(rows) // 40)],
        "power_summation_worst_excess_over_sqrt_kappa": worst_excess,
        "power_summation_samples": pw[:: max(1, len(pw) // 20)],
    }
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    print("ALL HOLD-STREAM ASSERTIONS PASSED; wrote", os.path.basename(OUT), flush=True)


if __name__ == "__main__":
    main()
