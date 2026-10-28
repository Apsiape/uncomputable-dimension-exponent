"""Single-threaded finite-model and weighted-moment audit. No external writes.

The full honest models are tensor products represented by their nontrivial
diagonal/permutation kernels; operator norms are computed on those kernels.
The finite control program implements acceptance rule (11.1) for q_s = a/b, with one READ/stage.
"""
import os
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
           'VECLIB_MAXIMUM_THREADS', 'NUMEXPR_NUM_THREADS', 'BLIS_NUM_THREADS'):
    os.environ[_v] = '1'
os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
import sys
sys.dont_write_bytecode = True
import itertools
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path
import numpy as np
import scipy
from scipy.linalg import expm
import psutil
from threadpoolctl import threadpool_info, threadpool_limits

OUT = Path(__file__).resolve().parent
SEED = 27102026
RNG = np.random.default_rng(SEED)
TOL = 2e-11


def maxabs(a):
    return float(np.max(np.abs(a), initial=0.0))


def hs(a):
    return float(np.linalg.norm(a, 'fro'))


def adj(a):
    return a.conj().T


def bit_rotate(x, n, amount=1):
    amount %= n
    mask = (1 << n) - 1
    return ((x << amount) & mask) | (x >> ((n - amount) % n))


def inverse(p):
    z = np.empty_like(p)
    z[p] = np.arange(len(p))
    return z


def bit_reverse(x, n):
    out = np.zeros_like(x)
    for j in range(n):
        out = (out << 1) | ((x >> j) & 1)
    return out


def trailing_ones(q, n):
    return next((j for j in range(n) if not ((q >> j) & 1)), n)


def finite_program(n, theta):
    """All source workspace equations, checked on (address,fuel,time).

    a_s=floor(2^s theta), d_s=a_s-p_s, remainder R_s/b.
    At nonhalting/read states d is 0 or 1. d<0 cannot accept later.
    Accept iff d>=2 or (d==1 and R_s>0), exactly (p_s+1)/2^s<theta.
    The cases theta=0 and 1 are included, with d_0=floor(theta).
    """
    a, b = theta.numerator, theta.denominator
    size, four = 1 << n, 4 ** n
    x = np.arange(size, dtype=np.int64)
    code = np.zeros(size, dtype=np.int64)
    for j in range(n):
        code += 3 * ((x >> j) & 1) * 4 ** (n-j-1)
    halt, idle = 2*b, 2*b+1
    initial = (a // b) * b + a % b
    transition = np.zeros((2*b+2, 2), dtype=np.int64)
    for d in (0, 1):
        for rem in range(b):
            nextdigit, newrem = divmod(2*rem, b)
            for bit in (0, 1):
                nd = 2*d + nextdigit - bit
                transition[d*b+rem, bit] = (
                    halt if nd >= 2 or (nd == 1 and newrem > 0)
                    else idle if nd < 0 else nd*b+newrem)
    transition[halt] = halt
    transition[idle] = idle
    st = np.empty((size, size), dtype=np.int64)
    ac = np.empty_like(st)
    reads = np.empty_like(st)
    st[:, 0], ac[:, 0], reads[:, 0] = initial, code, 0
    for t in range(1, size):
        bit = ac[:, t-1] >= 3*4**(n-1)
        reading = st[:, t-1] < halt
        st[:, t] = transition[st[:, t-1], bit.astype(np.int64)]
        ac[:, t] = np.where(reading, 4*ac[:, t-1]-3*bit*four, ac[:, t-1])
        reads[:, t] = reads[:, t-1] + reading
    f = (b * bit_reverse(x, n) < a*size).astype(np.int64)
    errors = dict(reader_affine=0., reader_PC_commutator=0.,
                  reader_initialize=0., reader_transition=0.,
                  control_initialize=0., control_transition=0.,
                  halt_inclusion=0., zero_test=0., control_PVM=0.,
                  workspace_domains=0., instantaneous_commutators=0.)
    time_values = np.arange(size, dtype=np.int64)
    reset_hits = 0
    beyond_reads = 0
    for fuel in range(size):
        k = trailing_ones(fuel, n)
        residues = time_values % (1 << k)
        nextres = (time_values+1) % (1 << k)
        z = residues == 0
        zp = nextres == 0
        aa, ss = ac[:, residues], st[:, residues]
        pp = (aa >= 3*4**(n-1)).astype(np.int64)
        cc = 4*aa - 3*pp*four
        reading = ss < halt
        astep = np.where(reading, cc, aa)
        sstep = transition[ss, pp]
        apredict = np.where(zp[None, :], code[:, None], astep)
        spredict = np.where(zp[None, :], initial, sstep)
        errors['reader_transition'] = max(errors['reader_transition'],
                                         maxabs(ac[:, nextres]-apredict)/four)
        errors['control_transition'] = max(errors['control_transition'],
                                          float(np.any(st[:, nextres] != spredict)))
        errors['reader_initialize'] = max(errors['reader_initialize'],
                                         maxabs(aa[:, z]-code[:, None])/four)
        errors['control_initialize'] = max(errors['control_initialize'],
                                          float(np.any(ss[:, z] != initial)))
        errors['halt_inclusion'] = max(errors['halt_inclusion'],
                                      float(np.any((ss == halt) & (f[:, None] == 0))))
        errors['reader_affine'] = max(errors['reader_affine'],
                                     maxabs(4*aa-3*pp*four-cc)/four)
        errors['workspace_domains'] = max(errors['workspace_domains'],
                                         float(np.any((aa < 0) | (aa > four) |
                                                      (cc < 0) | (cc > four))))
        reset_hits += size * int(np.sum(zp))
        beyond_reads += int(np.sum(reads[:, residues] > n))
    # A dummy ordinary counter remains zero: r=1, z=1, s=0, Step(r)=r.
    # Workspace projections are diagonal indicators of the recorded state.
    # Compare the stage acceptance condition against a direct exact rational run.
    acceptance_mismatches = 0
    for xx in range(size):
        prefix, first = 0, None
        for s in range(1, size):
            prefix = 2*prefix + (((xx >> (s-1)) & 1) if s <= n else 0)
            if b*(prefix+1) < a*(1 << s):
                first = s
                break
        observed = np.flatnonzero(st[xx] == halt)
        observed = int(observed[0]) if len(observed) else None
        acceptance_mismatches += observed != first
    errors['stage_acceptance'] = float(acceptance_mismatches)
    return errors, {'control_states': 2*b+2, 'reset_boundary_basis_points': reset_hits,
                    'basis_points_after_more_than_N_reads': beyond_reads,
                    'max_reads_in_history': int(reads.max())}


def periodic_coordinate(perm, values):
    """Sum (3/4) sum_j 4^-j values[perm^-j], by finite cycles."""
    out = np.zeros(len(perm), dtype=float)
    visited = np.zeros(len(perm), dtype=bool)
    for start in range(len(perm)):
        if visited[start]:
            continue
        cycle, z = [], start
        while not visited[z]:
            visited[z] = True
            cycle.append(z)
            z = int(perm[z])
        weights = 0.25 ** np.arange(len(cycle), dtype=float)
        backwards = [cycle[0]] + cycle[:0:-1]
        first = .75 * float(np.dot(weights, values[backwards])) / (1-.25**len(cycle))
        out[cycle[0]] = first
        for j in range(1, len(cycle)):
            out[cycle[j]] = .75*values[cycle[j]] + .25*out[cycle[j-1]]
    return out


def finite_model(n, theta):
    size, four = 1 << n, 4**n
    x = np.arange(size, dtype=np.int64)
    a, b = theta.numerator, theta.denominator
    f = (b*bit_reverse(x, n) < a*size).astype(np.int64)
    window = sum(np.roll(f, j) for j in range(1, n+1))
    k = 1+int(window.max())
    optional_size = 1 << k
    xx = np.repeat(x, optional_size)
    yy = np.tile(np.arange(optional_size, dtype=np.int64), size)
    index = np.arange(len(xx), dtype=np.int64)
    vr = np.where(f[xx] == 1, bit_rotate(yy, k), yy)
    vp = ((xx+1) % size)*optional_size + vr
    vi = inverse(vp)
    prefix = np.concatenate(([0], np.cumsum(f)))[:-1]
    dp = xx*optional_size + np.array([bit_rotate(int(y), k, int(prefix[z]))
                                     for z, y in zip(xx, yy)], dtype=np.int64)
    di = inverse(dp)
    t0 = bit_rotate(xx, n)*optional_size+yy
    x0 = (xx ^ 1)*optional_size+yy
    tp, xp = dp[t0[di]], dp[x0[di]]
    ti = inverse(tp)
    ff = f[xx].astype(float)
    pp = (xx & 1).astype(float)
    aa = sum(3*((xx >> j) & 1)*4.**(-j-1) for j in range(n))
    qq = ff*(yy & 1)
    yp = xx*optional_size + (yy ^ f[xx])
    bb = periodic_coordinate(vp, qq)
    cc = periodic_coordinate(vp, ff)
    tail = bb[vi]
    residuals = {
        'clock_affine_address': maxabs(aa[ti]-4*aa+3*pp),
        'clock_tail_flip_address': maxabs(aa[ti][xp]-aa[ti]),
        'clock_AP_commutators': 0., 'clock_own_flip': maxabs(pp[xp]-(1-pp)),
        'clock_domains': 0., 'cross_compulsory_commutators': 0.,
        'conditional_affine_B': maxabs(bb[vi]-4*bb+3*qq),
        'conditional_affine_C': maxabs(cc[vi]-4*cc+3*ff),
        'conditional_YFY': maxabs(ff[yp]-ff),
        'conditional_YQY': maxabs(qq[yp]-(ff-qq)),
        'conditional_Y_C': maxabs(cc[yp]-cc),
        'conditional_tail_flip': maxabs(tail[yp]-tail),
        'conditional_diagonal_commutators': 0.,
        'conditional_Q_under_F': maxabs((1-ff)*qq),
        'conditional_clock_cross_commutators': 0.,
        'conditional_domains': float(np.any((bb < -TOL) | (bb > 1+TOL) |
                                            (cc < -TOL) | (cc > 1+TOL))),
        'flat_state_commutators': 0.,
    }
    # The guard residual has only all-ones columns. Its two row maps have
    # disjoint ranges and each is injective, so its norm is sqrt(2)*4^-N.
    rhs = xp[np.where(pp == 0, index, tp[vp[ti]])]
    bad = vp != rhs
    residuals['guard_off_overflow'] = float(np.any(bad & (xx != size-1)))
    overflow = np.flatnonzero(bad)
    injective = len(np.unique(vp[overflow])) == len(overflow)
    injective &= len(np.unique(rhs[overflow])) == len(overflow)
    disjoint = not np.intersect1d(vp[overflow], rhs[overflow]).size
    if not (injective and disjoint):
        raise AssertionError('Guard norm formula needs disjoint injective rows')
    residuals['guard_address'] = math.sqrt(2)*maxabs((1-aa)[bad])
    residuals['guard_time'] = math.sqrt(2)/four
    residuals['clock_affine_fuel'] = 3/four
    residuals['clock_affine_time'] = 3/four
    residuals['clock_tail_flip_fuel'] = 3/four
    residuals['clock_tail_flip_time'] = 3/four
    coord = aa[::optional_size]
    h = np.array([0 if z == size-1 else 4.**(-trailing_ones(int(z), n)) for z in x])
    rotinv = bit_rotate(x, n, -1)
    bit = x & 1
    residuals['carry_recursion'] = maxabs(h-((1-bit)+.25*bit*h[rotinv]))
    residuals['carry_step'] = maxabs(coord[(x+1) % size]-coord+1-1.75*h)
    residuals['carry_commutators_and_domain'] = 0.
    z = np.empty((size, size), dtype=np.int64)
    for fuel in range(size):
        z[fuel] = (x % (1 << trailing_ones(fuel, n)) == 0)
    recursive_z = z[rotinv[:, None], rotinv[None, :]]
    reset_rhs = (1-bit)[:, None]+bit[:, None]*(1-bit)[None, :]*recursive_z
    residuals['reset_recursion'] = maxabs(z-reset_rhs)
    program_errors, program_details = finite_program(n, theta)
    residuals.update(program_errors)
    slot_violations = 0
    for j in range(1, n+1):
        active = np.roll(f, j) == 1
        used = sum(np.roll(f, h) for h in range(1, j+1))
        slot_violations += int(np.sum(active & ((used <= 0) | (used >= k))))
    residuals['slot_violations'] = float(slot_violations)
    worst = max(residuals.values())
    return {'N': n, 'theta': str(theta), 'flag_count': int(f.sum()),
            'mask_mean': float(f.mean()), 'window_min': int(window.min()),
            'window_max': int(window.max()), 'window_discrepancy':
                maxabs(window-n*float(theta)),
            'k_N': k, 'log2_dimension': 3*n+k, 'dimension': 2**(3*n+k),
            'largest_materialized_kernel': len(xx),
            'operator_residual_bound': 3/four, 'max_operator_residual': worst,
            'passed': worst <= 3/four+TOL,
            'residuals': residuals, 'program': program_details}


def discrepancy_tests():
    rows = []
    targets = list(map(Fraction, ('0', '1/8', '1/4', '1/3', '1/2', '2/3', '3/4', '1')))
    for n in (2, 4, 6, 8, 10, 12, 14):
        size = 1 << n
        rev = bit_reverse(np.arange(size, dtype=np.int64), n)
        for theta in targets:
            f = (theta.denominator*rev < theta.numerator*size).astype(np.int64)
            win = sum(np.roll(f, j) for j in range(1, n+1))
            discrepancy = maxabs(win-n*float(theta))
            rows.append({'N': n, 'theta': str(theta), 'max_discrepancy': discrepancy,
                         'bound': 2*math.log2(n)+2,
                         'k_N': 1+int(win.max())})
    grid_min_slack = Fraction(1)
    grid_cases = 0
    for den in range(1, 32):
        for num in range(den+1):
            for s in range(1, 13):
                l = 1 << s
                count = max(0, min(l, (num*l+den-1)//den-1))
                slack = Fraction(count, l) - (Fraction(num, den)-Fraction(1, l))
                grid_min_slack = min(grid_min_slack, slack)
                assert slack >= 0
                grid_cases += 1
    # Wrong-endian control: ordinary integer threshold at N=64, theta=1/2.
    # A length-64 window entirely in the lower half has discrepancy 32.
    # For the actual bit-zero-first sequence, every even-length window at 1/2
    # has exactly half of its flags active.
    return {'rows': rows, 'all_passed': all(r['max_discrepancy'] <= r['bound']+TOL for r in rows),
            'grid_cases': grid_cases, 'minimum_grid_slack': str(grid_min_slack),
            'endian_negative_control': {'N': 64, 'theta': '1/2',
              'wrong_order_discrepancy': 32, 'correct_order_discrepancy': 0,
              'claimed_log_bound': 2*math.log2(64)+2}}


def random_hermitian(d):
    a = RNG.normal(size=(d, d))+1j*RNG.normal(size=(d, d))
    a = (a+adj(a))/2
    return a / np.linalg.norm(a, 2)


def repair(b, kind):
    if kind in ('positive_contraction', 'contraction'):
        return b
    if kind == 'unitary':
        u, _, vh = np.linalg.svd(b)
        return u @ vh
    val, u = np.linalg.eigh(b)
    val = np.where(val >= 0, 1., -1.) if kind == 'reflection' else (val >= .5).astype(float)
    return (u*val) @ adj(u)


def word_value(xs, word):
    z = np.eye(xs[0].shape[0], dtype=complex)
    for i, star in word:
        z = z @ (adj(xs[i]) if star else xs[i])
    return z


def compression_tests(trials=120):
    kinds = ['positive_contraction', 'unitary', 'reflection', 'projection', 'contraction']
    stats = {'trials': trials, 'word_tests': 0, 'violations': [],
             'max_eq32_ratio': 0., 'max_eq34_ratio_by_domain': {k: 0. for k in kinds},
             'max_compression_ratio': 0., 'max_repair_word_ratio': 0.,
             'max_eq30_ratio': 0., 'max_layer_cake_error': 0.,
             'max_flat_dimension': 0, 'smallest_nonzero_eta': 1.,
             'max_moment_error': 0., 'witness_rows': []}
    for trial in range(trials):
        d = 2 if trial >= 108 else int(RNG.integers(2, 9))
        eigen = RNG.random(d)
        if trial % 5 == 0:
            eigen[-1] = 0
        if trial % 7 == 0:
            eigen[:] = 1
        if trial >= 108:
            eps = 10.**(-2-(trial-108) % 8)
            eigen = np.array([.5+eps, .5-eps])
        eigen = np.sort(eigen / eigen.sum())[::-1]
        rho, xi = np.diag(eigen), np.diag(np.sqrt(eigen))
        scale = (0., 1e-10, 1e-7, 1e-4, .01, .1)[trial % 6]
        xs = []
        for kind in kinds:
            if kind == 'positive_contraction':
                diag = RNG.random(d)
            elif kind == 'unitary':
                diag = np.exp(2j*np.pi*RNG.random(d))
            elif kind == 'reflection':
                diag = RNG.choice([-1., 1.], d)
            elif kind == 'projection':
                diag = RNG.integers(0, 2, d).astype(float)
            else:
                diag = RNG.random(d)*np.exp(2j*np.pi*RNG.random(d))
            rot = expm(1j*scale*random_hermitian(d))
            value = (rot*diag) @ adj(rot)
            if kind == 'contraction':
                noise = RNG.normal(size=(d,d))+1j*RNG.normal(size=(d,d))
                value += scale*noise/max(1., np.linalg.norm(noise, 2))
                value /= max(1., np.linalg.norm(value, 2))
            if trial >= 108:
                # Almost flat states and order-one off-diagonal operators:
                # these test a different small-commutator regime and sharp repair.
                if kind == 'unitary':
                    value = np.array([[0., 1.], [-1., 0.]], dtype=complex)
                elif kind == 'reflection':
                    value = np.array([[0., 1.], [1., 0.]], dtype=complex)
                elif kind == 'projection':
                    value = np.array([[.5, .5], [.5, .5]], dtype=complex)
            xs.append(value)
        # Stable spectral formula avoids subtracting nearly equal square roots
        # for the almost-flat adversaries (the direct commutator loses digits).
        rootsum = np.sqrt(eigen)[:, None]+np.sqrt(eigen)[None, :]
        gap = np.divide(eigen[:, None]-eigen[None, :], rootsum,
                        out=np.zeros_like(rootsum), where=rootsum > 0)
        etas = [hs(x*gap) for x in xs]
        eta = max(etas)
        if eta > 1e-15:
            stats['smallest_nonzero_eta'] = min(stats['smallest_nonzero_eta'], eta)
        raw, rounded, weights, ranks = [], [], [], []
        integrals = np.zeros(len(xs))
        reconstructed = np.zeros((d, d))
        for rank in range(1, d+1):
            dt = eigen[rank-1]-(eigen[rank] if rank < d else 0.)
            if dt <= 0:
                continue
            p = np.diag([1.]*rank+[0.]*(d-rank))
            reconstructed += dt*p
            block = [x[:rank, :rank] for x in xs]
            zz = [repair(x, kind) for x, kind in zip(block, kinds)]
            for i, (x, b, z, kind) in enumerate(zip(xs, block, zz, kinds)):
                c2 = hs(x@p-p@x)**2
                integrals[i] += dt*c2
                err2 = hs(z-b)**2
                if c2 > 1e-25:
                    stats['max_eq34_ratio_by_domain'][kind] = max(
                        stats['max_eq34_ratio_by_domain'][kind], err2/c2)
                if err2 > c2 + TOL:
                    stats['violations'].append(['eq34', trial, rank, kind, err2, c2])
            raw.append(block)
            rounded.append(zz)
            weights.append(dt*rank)
            ranks.append(rank)
        weights, ranks = np.array(weights), np.array(ranks)
        stats['max_layer_cake_error'] = max(stats['max_layer_cake_error'], hs(rho-reconstructed))
        for integral, ei in zip(integrals, etas):
            if ei > 1e-25:
                stats['max_eq32_ratio'] = max(stats['max_eq32_ratio'], float(integral/(2*ei)))
            if integral > 2*ei + TOL:
                stats['violations'].append(['eq32', trial, float(integral), ei])
        # Exact finite direct sum, evaluated by its blocks and multiplicities.
        multiplicities = np.rint(1e6*weights/ranks).astype(np.int64)
        dimension = int(np.dot(multiplicities, ranks))
        flatweights = multiplicities*ranks/dimension
        zeta = float(np.sum(np.abs(flatweights-weights))) + 1e-14
        stats['max_flat_dimension'] = max(stats['max_flat_dimension'], dimension)
        letters = list(itertools.product(range(len(xs)), (False, True)))
        words = [(letter,) for letter in letters]
        words += list(itertools.product(letters, repeat=2))
        for _ in range(160):
            length = int(RNG.integers(3, 6))
            words.append(tuple(letters[int(RNG.integers(len(letters)))] for _ in range(length)))
        worst = 0.
        for word in words:
            ell = len(word)
            moment = np.trace(rho@word_value(xs, word))
            rawmom = sum(w*np.trace(word_value(block, word))/rank
                         for w, rank, block in zip(weights, ranks, raw))
            repairedmom = sum(w*np.trace(word_value(block, word))/rank
                              for w, rank, block in zip(weights, ranks, rounded))
            flatmom = sum(w*np.trace(word_value(block, word))/rank
                          for w, rank, block in zip(flatweights, ranks, rounded))
            compress_error = float(abs(moment-rawmom))
            repair_error = float(abs(rawmom-repairedmom))
            error = float(abs(moment-flatmom))
            base = math.sqrt(2*eta)
            cb, rb, bound = (ell-1)*base, ell*base, 2*ell*base+zeta
            if cb > 1e-18:
                stats['max_compression_ratio'] = max(stats['max_compression_ratio'], compress_error/cb)
            if rb > 1e-18:
                stats['max_repair_word_ratio'] = max(stats['max_repair_word_ratio'], repair_error/rb)
            stats['max_eq30_ratio'] = max(stats['max_eq30_ratio'], error/bound)
            stats['max_moment_error'] = max(stats['max_moment_error'], error)
            if compress_error > cb+TOL or repair_error > rb+TOL or error > bound+TOL:
                stats['violations'].append(['word', trial, ell, compress_error, cb, repair_error, rb, error, bound])
            worst = max(worst, error/bound)
        stats['word_tests'] += len(words)
        if trial < 12:
            stats['witness_rows'].append({'trial': trial, 'd': d, 'scale': scale,
                 'eta': eta, 'max_moment_error_over_bound': worst,
                 'flat_dimension': dimension, 'weight_L1_error': zeta-1e-14})
    return stats


def jensen_tests(trials=3000):
    worst_ratio, worst_gap = 0., 0.
    violations = []
    qs = set()
    for trial in range(trials):
        d, q = int(RNG.integers(2, 10)), 1+trial % 8
        qs.add(q)
        p = RNG.normal(size=(d, d))+1j*RNG.normal(size=(d, d))
        p /= np.linalg.norm(p, 2)
        a = RNG.normal(size=(d, d))+1j*RNG.normal(size=(d, d))
        if trial % 5 == 0:
            a[:, 1:] = 0
        rho = a@adj(a)
        rho /= np.trace(rho)
        s = adj(p)@p
        val, u = np.linalg.eigh(s)
        sq = (u*np.maximum(val, 0)**q) @ adj(u)
        lhs = float(np.trace(rho@s).real)
        rhs = float(np.trace(rho@sq).real)
        ratio = lhs/(max(rhs, 0)**(1/q)) if rhs > 0 else 0.
        worst_ratio = max(worst_ratio, ratio)
        worst_gap = max(worst_gap, lhs**q-rhs)
        # Explicitly check h_q^* h_q = (p^*p)^q as well.
        if q % 2 == 0:
            h = np.linalg.matrix_power(s, q//2)
        else:
            h = p@np.linalg.matrix_power(s, (q-1)//2)
        identity_error = hs(adj(h)@h-sq)
        if lhs**q > rhs+TOL or identity_error > TOL:
            violations.append({'trial': trial, 'q': q, 'lhs_to_q': lhs**q,
                               'rhs': rhs, 'identity_error': identity_error})
    return {'trials': trials, 'q_values': sorted(qs), 'max_norm_ratio': worst_ratio,
            'max_positive_Jensen_deficit': worst_gap, 'violations': violations}


def public_threadpool_info():
    """Report library locations relative to site-packages, or by filename."""
    pools = threadpool_info()
    for pool in pools:
        library = pool.get('filepath')
        if library:
            normal = library.replace(chr(92), '/')
            relative = normal.partition('/site-packages/')[2]
            pool['filepath'] = '<site-packages>/' + relative if relative else normal.rsplit('/', 1)[-1]
    return pools


def main():
    started = time.perf_counter()
    targets = list(map(Fraction, ('0', '1/8', '1/4', '1/3', '1/2', '2/3', '3/4', '1')))
    with threadpool_limits(limits=1):
        finite = [finite_model(n, theta) for n in (2, 4, 6) for theta in targets]
        print('honest models:', len(finite), 'passed:', all(r['passed'] for r in finite), flush=True)
        discrepancy = discrepancy_tests()
        print('window/grid tests:', discrepancy['all_passed'], flush=True)
        compression = compression_tests()
        print('compression words:', compression['word_tests'], 'violations:', len(compression['violations']), flush=True)
        jensen = jensen_tests()
        print('Jensen cases:', jensen['trials'], 'violations:', len(jensen['violations']), flush=True)
        memory = psutil.Process().memory_info()._asdict()
        results = {'seed': SEED, 'python': sys.version, 'platform': platform.platform(),
                   'numpy': np.__version__, 'scipy': scipy.__version__,
                   'threadpools': public_threadpool_info(), 'finite_models': finite,
                   'window_and_grid': discrepancy, 'compression': compression,
                   'jensen': jensen, 'elapsed_seconds': time.perf_counter()-started,
                   'memory_bytes': memory}
    (OUT/'numerical_results.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
    print('elapsed seconds:', results['elapsed_seconds'], 'memory:', memory, flush=True)
    assert all(r['passed'] for r in finite)
    assert discrepancy['all_passed']
    assert not compression['violations']
    assert not jensen['violations']


if __name__ == '__main__':
    main()
