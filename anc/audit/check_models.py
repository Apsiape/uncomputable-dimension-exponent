"""Section 5 audit. No dense matrices; exhaustive basis arithmetic on each support.
Run: python check_models.py --depths 4 6
Only numpy is required. All output stays beside this script.
"""
import os
import sys
sys.dont_write_bytecode = True
for _name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
              'VECLIB_MAXIMUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[_name] = '1'
import argparse
import csv
import itertools
import json
import math
from pathlib import Path
import numpy as np


class Expr:
    def __init__(self, terms):
        combined = {}
        for coeff, word in terms:
            combined[word] = combined.get(word, 0) + coeff
        self.terms = [(c, w) for w, c in combined.items() if c]
    def __add__(self, other):
        other = expr(other)
        return Expr(self.terms + other.terms)
    __radd__ = __add__
    def __neg__(self):
        return Expr([(-c, w) for c, w in self.terms])
    def __sub__(self, other):
        return self + (-expr(other))
    def __rsub__(self, other):
        return expr(other) + (-self)
    def __mul__(self, other):
        other = expr(other)
        return Expr([(c*d, w+v) for c, w in self.terms for d, v in other.terms])
    __rmul__ = __mul__
    def adj(self):
        return Expr([(c, tuple(wi[:-1] if wi.endswith('*') else wi+'*'
                              for wi in reversed(w))) for c, w in self.terms])


def expr(x):
    return x if isinstance(x, Expr) else Expr([(x, ())])


def comm(a, b):
    return a*b-b*a


class Model:
    # Register order: address, optional bits, fuel, time.
    def __init__(self, n):
        assert n >= 2 and n % 2 == 0
        if n > 8:
            raise ValueError('This exhaustive workspace implementation is limited to N<=8 to respect the 4 GB memory budget.')
        self.n = n
        self.p = p = 1 << n
        self.mask = p-1
        self.delta = 4.0**(-n)
        self.kn_set = [e for e in range(n//2) if e % 2 == 0 and e+1 < p]
        self.flag = np.array([int(any(x % 4**(e+1) == 4**e
                                     for e in self.kn_set)) for x in range(p)])
        windows = [sum(self.flag[(x-j) % p] for j in range(1, n+1))
                   for x in range(p)]
        self.k = int(1+max(windows))
        self.yd = 1 << self.k
        self.hprefix = np.concatenate(([0], np.cumsum(self.flag)))[:-1]
        self.sizes = [p, self.yd, p, p]
        self.diag = {}
        self.support = {}
        self.perm = {}
        self.vars = {}
        self.positive = []
        self.projections = []
        self.reflections = []
        self.unitaries = []
        self.rows = []
        self._build()

    @staticmethod
    def rot(v, shift, bits):
        shift = np.asarray(shift) % bits
        return ((v << shift) | (v >> (bits-shift))) & ((1 << bits)-1)

    def add_diag(self, name, table, support, kind=None):
        self.diag[name] = np.asarray(table, dtype=float)
        self.support[name] = tuple(support)
        self.vars[name] = Expr([(1, (name,))])
        if kind:
            getattr(self, kind).append(name)
        return self.vars[name]

    def add_perm(self, name, support, action, reflection=False):
        self.perm[name] = action
        self.support[name] = tuple(support)
        self.vars[name] = Expr([(1, (name,))])
        (self.reflections if reflection else self.unitaries).append(name)
        return self.vars[name]

    def _periodic_coordinate(self, digit, forward):
        # Exactly sum the periodic base-four series with Python integers,
        # then round each rational entry once to float64.
        size = len(digit)
        values = np.empty(size)
        seen = np.zeros(size, dtype=bool)
        for root in range(size):
            if seen[root]:
                continue
            cycle = [root]
            cur = int(forward[root])
            while cur != root:
                cycle.append(cur)
                cur = int(forward[cur])
            ell = len(cycle)
            denom = 4**ell-1
            # Q(root), Q(V^-1 root), ..., Q(V^-(ell-1) root).
            numerator = 0
            for j in range(ell):
                numerator = 4*numerator + 3*int(digit[cycle[-j % ell]])
            values[root] = numerator / denom
            seen[root] = True
            for cur in cycle[1:]:
                numerator, rem = divmod(3*int(digit[cur])*denom+numerator, 4)
                assert rem == 0
                values[cur] = numerator/denom
                seen[cur] = True
        return values

    def _build(self):
        p, n = self.p, self.n
        aa = np.array([sum(3*((x >> j) & 1)*4.0**(-j-1)
                           for j in range(n)) for x in range(p)])
        pp = np.arange(p) & 1
        for tag, reg in [('a', 0), ('f', 2), ('t', 3)]:
            self.add_diag('A'+tag, aa, [reg], 'positive')
            self.add_diag('P'+tag, pp, [reg], 'projections')
            def rotation(state, inverse, reg=reg, tag=tag):
                old = state[:, reg].copy()
                new = self.rot(old, -1 if inverse else 1, n)
                if tag == 'a':
                    state[:, 1] = self.rot(state[:, 1],
                        self.hprefix[new]-self.hprefix[old], self.k)
                state[:, reg] = new
            def flip(state, inverse, reg=reg, tag=tag):
                old = state[:, reg].copy()
                new = old ^ 1
                if tag == 'a':
                    state[:, 1] = self.rot(state[:, 1],
                        self.hprefix[new]-self.hprefix[old], self.k)
                state[:, reg] = new
            self.add_perm('T'+tag, [0, 1] if tag == 'a' else [reg], rotation)
            self.add_perm('X'+tag, [0, 1] if tag == 'a' else [reg], flip, True)
        def increment(state, inverse):
            old = state[:, 0].copy()
            new = (old + (-1 if inverse else 1)) & self.mask
            shifts = -self.flag[new] if inverse else self.flag[old]
            state[:, 1] = self.rot(state[:, 1], shifts, self.k)
            state[:, 0] = new
        self.add_perm('V', [0, 1], increment)
        def time_increment(state, inverse):
            state[:, 3] = (state[:, 3]+(-1 if inverse else 1)) & self.mask
        self.add_perm('U', [3], time_increment)
        hh = []
        ll, rr = [], []
        for x in range(p):
            trailing = 0
            while trailing < n and (x >> trailing) & 1:
                trailing += 1
            hh.append(0 if trailing == n else 4.0**(-trailing))
            first = next((e for e in range(n//2) if (x >> (2*e)) & 3), None)
            ll.append(int(first is not None and ((x >> (2*first)) & 3) == 1))
            rr.append(0 if first is None else 2.0**(-first))
        self.add_diag('H', hh, [0], 'positive')
        self.add_diag('L', ll, [0], 'projections')
        self.add_diag('R', rr, [0], 'positive')
        self.add_diag('F', self.flag, [0], 'projections')
        qtab = self.flag[:, None]*(np.arange(self.yd)[None, :] & 1)
        self.add_diag('Q', qtab, [0, 1], 'projections')
        def opt_flip(state, inverse):
            state[:, 1] ^= self.flag[state[:, 0]]
        self.add_perm('Y', [0, 1], opt_flip, True)
        flat_indices = np.arange(p*self.yd)
        x = flat_indices//self.yd
        y = flat_indices % self.yd
        forward = ((x+1) & self.mask)*self.yd + self.rot(y, self.flag[x], self.k)
        btab = self._periodic_coordinate(qtab.ravel(), forward).reshape(p, self.yd)
        ctab = self._periodic_coordinate(self.flag, (np.arange(p)+1) % p)
        self.add_diag('B', btab, [0, 1], 'positive')
        self.add_diag('C', ctab, [0], 'positive')
        ztab = np.empty((p, p))
        control = np.zeros((p, p, p), dtype=np.int8)
        rval = np.empty((p, p, p))
        # Controls E=0 (start), O=1, H=2, I=3, Spin=4.
        for fuel in range(p):
            k = 0
            while k < n and (fuel >> k) & 1:
                k += 1
            period = 1 << k
            ztab[fuel] = (np.arange(p) % period == 0)
            for x in range(p):
                ctrl = 0 if ll[x] else 3
                counter = rr[x]
                for time in range(p):
                    if time % period == 0:
                        ctrl = 0 if ll[x] else 3
                        counter = rr[x]
                    rval[x, fuel, time] = counter
                    control[x, fuel, time] = ctrl
                    if ctrl in (0, 1):
                        if counter == 1:
                            ctrl = 2 if ctrl == 0 else 4
                        else:
                            counter *= 2
                            ctrl = 1-ctrl
        self.add_diag('Z', ztab, [2, 3], 'projections')
        self.add_diag('r', rval, [0, 2, 3], 'positive')
        self.add_diag('z', rval == 1, [0, 2, 3], 'projections')
        self.add_diag('s', np.where(rval == 1, 0, 2*rval), [0, 2, 3], 'positive')
        for ctrl, name in enumerate(['qE', 'qO', 'qH', 'qI', 'qS']):
            self.add_diag(name, control == ctrl, [0, 2, 3], 'projections')

    def apply_word(self, word, state):
        target = state.copy()
        value = np.ones(len(state))
        for token in reversed(word):
            inverse = token.endswith('*')
            name = token[:-1] if inverse else token
            if name in self.diag:
                indices = tuple(target[:, r] for r in self.support[name])
                value *= self.diag[name][indices]
            else:
                self.perm[name](target, inverse)
        return target, value

    def check(self, label, equation):
        equation = expr(equation)
        support = sorted(set(r for _, w in equation.terms for name in w
                             for r in self.support[name.rstrip('*')]))
        count = math.prod(self.sizes[r] for r in support)
        # For diagonal expressions no target comparison is necessary.
        diagonal = all(token.rstrip('*') in self.diag
                       for _, word in equation.terms for token in word)
        sumsq = 0.0
        maxcol = 0.0
        for begin in range(0, count, 32768):
            codes = np.arange(begin, min(count, begin+32768))
            state = np.zeros((len(codes), 4), dtype=np.int64)
            rest = codes.copy()
            for r in reversed(support):
                state[:, r] = rest % self.sizes[r]
                rest //= self.sizes[r]
            if diagonal:
                val = np.zeros(len(codes))
                for coeff, word in equation.terms:
                    _, weight = self.apply_word(word, state)
                    val += coeff*weight
                normcol2 = val*val
            else:
                # Group equal output rows BEFORE squaring. This avoids
                # catastrophic cancellation of O(1) terms at small defects.
                outputs = []
                for coeff, word in equation.terms:
                    target, weight = self.apply_word(word, state)
                    key = target[:, 0].copy()
                    for r in range(1, 4):
                        key = key*self.sizes[r]+target[:, r]
                    outputs.append([key, coeff*weight])
                normcol2 = np.zeros(len(codes))
                for i, (key, weight) in enumerate(outputs):
                    grouped = weight.copy()
                    for otherkey, otherweight in outputs[i+1:]:
                        same = key == otherkey
                        grouped[same] += otherweight[same]
                        otherweight[same] = 0
                    normcol2 += grouped*grouped
            sumsq += float(np.sum(normcol2))
            maxcol = max(maxcol, float(np.max(normcol2)))
        flat = math.sqrt(sumsq/count)
        self.rows.append({'relation': label, 'flat_defect': flat,
                          'delta_4^-N': self.delta, 'ratio': flat/self.delta,
                          'max_column_norm': math.sqrt(maxcol),
                          'basis_columns_evaluated': count})

    def check_diagonal_values(self, label, values):
        values = np.asarray(values, dtype=float)
        flat = math.sqrt(float(np.mean(values*values)))
        self.rows.append({'relation':label, 'flat_defect':flat,
                          'delta_4^-N':self.delta, 'ratio':flat/self.delta,
                          'max_column_norm':float(np.max(np.abs(values))),
                          'basis_columns_evaluated':int(values.size)})

    def audit(self):
        v = self.vars
        I = expr(1)
        A, P, T, X = [v[c+'a'] for c in 'APTX']
        V, H, L, R, F = [v[x] for x in ['V', 'H', 'L', 'R', 'F']]
        U, Z = v['U'], v['Z']
        B, C, Q, Y = [v[x] for x in ['B', 'C', 'Q', 'Y']]
        for tag in 'aft':
            a, p, t, xx = [v[c+tag] for c in 'APTX']
            tail = t*a*t.adj()
            self.check('(3) '+tag+' [A,P]', comm(a, p))
            self.check('(3) '+tag+' affine', tail-4*a+3*p)
            self.check('(3) '+tag+' flip', xx*p*xx-(I-p))
            self.check('(3) '+tag+' tail flip', comm(xx, tail))
        for tag, inc in [('a', V), ('t', U)]:
            a, p, t, xx = [v[c+tag] for c in 'APTX']
            self.check('(4) '+tag+' guarded increment',
                       (inc-xx*((I-p)+t*inc*t.adj()*p))*(I-a))
        tht = T*H*T.adj()
        self.check('(5) carry recursion', H-(I-P)-.25*P*tht)
        self.check('(5) [P,THT*]', comm(P, tht))
        self.check('(5) [H,A]', comm(H, A))
        self.check('(6) carry increment', V.adj()*A*V-A+I-1.75*H)
        p1 = T*P*T.adj()
        e00 = (I-P)*(I-p1)
        e1 = P*(I-p1)
        self.check('(7) L decoder', L-e1-e00*T*T*L*T.adj()*T.adj())
        self.check('(8) R decoder', R-(I-e00)-.5*e00*T*T*R*T.adj()*T.adj())
        # Derived finite-cylinder identities (9)-(10), including the first
        # impossible cylinder after a whole address-register revolution.
        for e in range(self.n//2+1):
            be = (np.arange(self.p) % (4**(e+1)) == 4**e)
            self.check_diagonal_values('(10) B_'+str(e)+' L', be*(self.diag['L']-1))
            self.check_diagonal_values('(10) B_'+str(e)+' R', be*(self.diag['R']-2.0**(-e)))
        S = v['Tf']*v['Tt']
        self.check('(11) reset recursion', Z-(I-v['Pf'])-
                   v['Pf']*(I-v['Pt'])*S*Z*S.adj())
        for k in range(self.n+1):
            # For k=N the cyclic next digit repeats bit 0, so C_N=0.
            ck = (np.arange(self.p) % (1 << (k+1)) == (1 << k)-1) if k < self.n else np.zeros(self.p)
            dk = (np.arange(self.p) % (1 << k) == 0)
            self.check_diagonal_values('(12) fuel cylinder '+str(k),
                ck[:,None]*(self.diag['Z']-dk[None,:]))
        r, z, s = [v[x] for x in ['r', 'z', 's']]
        self.check('(13) zero test', r-z-.5*(I-z)*s)
        controls = [v[x] for x in ['qE', 'qO', 'qH', 'qI', 'qS']]
        self.check('Section 2.4 control partition', sum(controls)-I)
        for i, j in itertools.combinations(range(len(controls)), 2):
            self.check('Section 2.4 controls orthogonal '+str((i,j)), controls[i]*controls[j])
        qe, qo, qh, qi, qs = controls
        init = {'r': R, 'qE': L, 'qO': 0, 'qH': 0, 'qI': I-L, 'qS': 0}
        step = {'r': 2*r*(qe+qo)*(I-z)+r*((qe+qo)*z+qh+qi+qs),
                'qE': qo*(I-z), 'qO': qe*(I-z), 'qH': qh+qe*z,
                'qI': qi, 'qS': qs+qo*z}
        zp = U.adj()*Z*U
        for name in init:
            w = v[name]
            self.check('(14) initialize '+name, Z*(w-expr(init[name])))
            self.check('(15) update '+name,
                       U.adj()*w*U-zp*expr(init[name])-(I-zp)*step[name])
        self.check('(16) halt flag', qh*(I-F))
        self.check('(21) Q<=F', Q*(I-F))
        for na, nb in [('B','Q'), ('B','F'), ('C','Q'), ('C','F'), ('B','C')]:
            self.check('(21) ['+na+','+nb+']', comm(v[na], v[nb]))
        self.check('(22) data affine', V*B*V.adj()-4*B+3*Q)
        self.check('(22) flag affine', V*C*V.adj()-4*C+3*F)
        self.check('(23) YFY=F', Y*F*Y-F)
        self.check('(23) YQY=F-Q', Y*Q*Y-F+Q)
        self.check('(24) data tail flip', comm(Y, V*B*V.adj()))
        self.check('(24) flag preservation', comm(Y, C))
        # Every commutation explicitly requested in Sections 2.1, 2.5 and 4.
        pairs = set()
        def add_pairs(left, right):
            for a in left:
                for b in right:
                    if a != b:
                        pairs.add(tuple(sorted((a,b))))
        addr = ['Aa','Pa','Ta','Xa','V','H']
        fuel = ['Af','Pf','Tf','Xf']
        time = ['At','Pt','Tt','Xt','U']
        add_pairs(addr, fuel+time)
        add_pairs(fuel, time)
        add_pairs(['L','R','F'], ['L','R','F','Aa']+fuel+time)
        work = ['Z','r','z','s','qE','qO','qH','qI','qS']
        add_pairs(work, work+['Aa','Af','At','L','R','F'])
        add_pairs(['B','C','Q','Y'], ['Aa']+fuel+time)
        for a, b in sorted(pairs):
            self.check('Required commutation ['+a+','+b+']', comm(v[a], v[b]))
        # Exact domains and all state commutators.
        for name in self.positive:
            arr = self.diag[name]
            assert float(arr.min()) >= 0 and float(arr.max()) <= 1, (name, arr.min(), arr.max())
            self.check('Domain selfadjoint '+name, v[name]-v[name].adj())
        for name in self.projections:
            self.check('Domain projection '+name, v[name]*v[name]-v[name])
            self.check('Domain selfadjoint '+name, v[name]-v[name].adj())
        for name in self.reflections:
            self.check('Domain reflection square '+name, v[name]*v[name]-I)
            self.check('Domain reflection selfadjoint '+name, v[name]-v[name].adj())
        for name in self.unitaries:
            self.check('Domain unitary '+name, v[name].adj()*v[name]-I)
            self.check('Domain coisometry '+name, v[name]*v[name].adj()-I)
        # xi=I/sqrt(d): these commutators are identically zero, independent
        # of operator entries. Record each separately, rather than allocate xi.
        for name in v:
            self.rows.append({'relation':'State commutator '+name, 'flat_defect':0,
                'delta_4^-N':self.delta, 'ratio':0, 'max_column_norm':0,
                'basis_columns_evaluated':0})
        return self.rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--depths', type=int, nargs='+', default=[4, 6])
    args = parser.parse_args()
    out = Path(__file__).resolve().parent
    summaries = []
    for n in args.depths:
        model = Model(n)
        rows = model.audit()
        with (out/f'defects_N{n}.csv').open('w', newline='', encoding='utf-8') as file:
            writer = csv.DictWriter(file, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)
        dimension = int(math.prod(model.sizes))
        summary = {'N':n, 'program':'halts iff input is even; one counter',
                   'K_N':model.kn_set, 'theta_N':float(model.flag.mean()),
                   'k_N':int(model.k), 'dimension':dimension,
                   '2^(3N+k_N)':1 << (3*n+int(model.k)),
                   '4^-N':model.delta, 'relations_checked':len(rows),
                   'max_flat_defect':max(r['flat_defect'] for r in rows),
                   'max_ratio':max(r['ratio'] for r in rows),
                   'nonzero_relations':[r for r in rows if r['flat_defect'] > 1e-14]}
        summaries.append(summary)
        print(json.dumps(summary, indent=2), flush=True)
    (out/'model_results.json').write_text(json.dumps(summaries, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
