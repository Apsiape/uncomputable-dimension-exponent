"""Monomial-operator engine for testing finite models of operator relations.

Every operator in the finite models of Section 7 of the paper is a sum of
"monomials": generalized permutations O|s> = c(s)|pi(s)> on a basis of
labels s = (x, q, t, y).  This module never builds a dense matrix.  An
operator is a list of (scalar, Mono) terms; products are composed
symbolically and evaluated column by column on the basis, in chunks.

Each base operator declares its support (the registers it reads or moves).
A relation can be evaluated on the union of the supports of its operators;
on the full space the relation is (relation on support) (x) identity, so its
operator norm and normalized Hilbert-Schmidt norm are unchanged.  run_e2.py
cross-checks this against evaluation on the full joint space.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import connected_components

REG_ORDER = ("x", "q", "t", "y")


class Space:
    """Product of named registers; register r has bits[r] qubits."""

    def __init__(self, regs, bits):
        self.regs = tuple(r for r in REG_ORDER if r in regs)
        self.bits = {r: bits[r] for r in self.regs}
        self.nbits = sum(self.bits.values())
        self.dim = 1 << self.nbits

    def labels(self, start, stop):
        idx = np.arange(start, stop, dtype=np.int64)
        out, shift = {}, 0
        for r in reversed(self.regs):
            b = self.bits[r]
            out[r] = (idx >> shift) & ((1 << b) - 1)
            shift += b
        return out

    def index(self, lab):
        idx = None
        for r in self.regs:
            v = lab[r]
            idx = v.copy() if idx is None else (idx << self.bits[r]) | v
        return idx

    def decode(self, i):
        lab = self.labels(i, i + 1)
        return {r: int(lab[r][0]) for r in self.regs}


_DIRTY_BASE, _DIRTY_COMP = [], []
CACHE_SLOTS = 4


class Mono:
    """O|s> = coef(s) |perm(s)>.  fwd(lab)->(coef, lab'), adj(lab)->(coef, lab')."""

    __slots__ = ("name", "supp", "_fwd", "_adj", "diag", "base", "_cf", "_ca", "_dirty")

    def __init__(self, name, supp, fwd, adj, diag, base):
        self.name, self.supp, self.diag, self.base = name, frozenset(supp), diag, base
        self._fwd, self._adj = fwd, adj
        self._cf, self._ca, self._dirty = [], [], False

    def _get(self, cache, fn, lab):
        for k, v in cache:
            if k is lab:
                return v
        v = fn(lab)
        cache.append((lab, v))
        if len(cache) > CACHE_SLOTS:
            cache.pop(0)
        if not self._dirty:
            self._dirty = True
            (_DIRTY_BASE if self.base else _DIRTY_COMP).append(self)
        return v

    def fwd(self, lab):
        return self._get(self._cf, self._fwd, lab)

    def adj(self, lab):
        return self._get(self._ca, self._adj, lab)

    def clear(self):
        self._cf, self._ca, self._dirty = [], [], False


def clear_caches(base_too=True):
    global _DIRTY_BASE, _DIRTY_COMP
    for m in _DIRTY_COMP:
        m.clear()
    _DIRTY_COMP = []
    if base_too:
        for m in _DIRTY_BASE:
            m.clear()
        _DIRTY_BASE = []


def diag_mono(name, supp, valfn):
    f = lambda lab: (valfn(lab), lab)
    return Mono(name, supp, f, f, True, True)


def perm_mono(name, supp, f, finv):
    return Mono(name, supp, lambda lab: (1.0, f(lab)), lambda lab: (1.0, finv(lab)), False, True)


IDM = Mono("I", (), lambda lab: (1.0, lab), lambda lab: (1.0, lab), True, True)


def mono_mul(A, B):
    """A*B (B acts first)."""
    if A is IDM:
        return B
    if B is IDM:
        return A

    def fwd(lab):
        cb, l1 = B.fwd(lab)
        ca, l2 = A.fwd(l1)
        return cb * ca, l2

    def adj(lab):
        c1, l1 = A.adj(lab)
        c2, l2 = B.adj(l1)
        return c1 * c2, l2

    return Mono(f"({A.name}*{B.name})", A.supp | B.supp, fwd, adj, A.diag and B.diag, False)


def mono_adj(A):
    if A is IDM or (A.diag and A._fwd is A._adj):
        return A
    return Mono(f"{A.name}^*", A.supp, A._adj, A._fwd, A.diag, A.base)


class Op:
    def __init__(self, terms=()):
        self.terms = list(terms)

    @staticmethod
    def of(m):
        return Op([(1.0, m)])

    @property
    def supp(self):
        s = frozenset()
        for _, m in self.terms:
            s |= m.supp
        return s

    def __add__(self, o):
        return Op(self.terms + _as_op(o).terms)

    __radd__ = __add__

    def __neg__(self):
        return Op([(-a, m) for a, m in self.terms])

    def __sub__(self, o):
        return self + (-_as_op(o))

    def __rsub__(self, o):
        return _as_op(o) + (-self)

    def __mul__(self, o):
        if isinstance(o, (int, float, complex)):
            return Op([(a * o, m) for a, m in self.terms])
        o = _as_op(o)
        return Op([(a * b, mono_mul(m, n)) for a, m in self.terms for b, n in o.terms])

    def __rmul__(self, o):
        if isinstance(o, (int, float, complex)):
            return Op([(a * o, m) for a, m in self.terms])
        return _as_op(o) * self

    @property
    def H(self):
        return Op([(np.conj(a), mono_adj(m)) for a, m in self.terms])


def _as_op(o):
    if isinstance(o, Op):
        return o
    if isinstance(o, (int, float, complex)):
        return Op([(o, IDM)]) if o != 0 else Op([])
    raise TypeError(o)


I = Op.of(IDM)
ZERO = Op([])


def comm(A, B):
    return A * B - B * A


# --------------------------------------------------------------------------
# evaluation
# --------------------------------------------------------------------------

class _Acc:
    def __init__(self, dim, topk):
        self.dim, self.topk = dim, topk
        self.sumsq = 0.0
        self.maxabs = 0.0
        self.nnz = 0
        self.top = []
        self.offdiag = False
        self.kr, self.kc, self.kv = [], [], []
        self.kept = 0
        self.overflow = False
        self.rowabs = None
        self.maxcolabs = 0.0


def evaluate_many(ops, bits, regs, chunk=1 << 18, keep_limit=6_000_000, topk=5):
    """Evaluate each operator in `ops` on the space spanned by `regs`.
    Every op's support must be inside regs.  Returns a list of result dicts."""
    sp_ = Space(regs, bits)
    dim = sp_.dim
    for op in ops:
        assert op.supp <= set(sp_.regs), (op.supp, sp_.regs)
    accs = [_Acc(dim, topk) for _ in ops]
    for start in range(0, dim, chunk):
        stop = min(dim, start + chunk)
        n = stop - start
        clear_caches(True)
        lab = sp_.labels(start, stop)
        gcols = np.arange(start, stop, dtype=np.int64)
        for op, acc in zip(ops, accs):
            diag = np.zeros(n)
            R, V = [], []
            for a, m in op.terms:
                c, lab2 = m.fwd(lab)
                if m.diag or lab2 is lab:
                    diag += a * np.broadcast_to(c, (n,))
                    continue
                rows = sp_.index(lab2)
                if np.array_equal(rows, gcols):
                    diag += a * np.broadcast_to(c, (n,))
                    continue
                R.append(rows)
                V.append(a * np.broadcast_to(np.asarray(c, dtype=float), (n,)))
            clear_caches(False)
            if not R:
                nzi = np.nonzero(diag)[0]
                if len(nzi) == 0:
                    continue
                d = diag[nzi]
                acc.nnz += len(nzi)
                acc.sumsq += float(np.dot(d, d))
                acc.maxabs = max(acc.maxabs, float(np.abs(d).max()))
                acc.maxcolabs = max(acc.maxcolabs, float(np.abs(d).max()))
                order = np.argsort(-np.abs(d))[:topk]
                acc.top = sorted(acc.top + [(float(abs(d[i])), start + int(nzi[i])) for i in order],
                                 reverse=True)[:topk]
                _keep(acc, gcols[nzi], gcols[nzi], d, keep_limit)
                continue
            acc.offdiag = True
            R.append(gcols)
            V.append(diag)
            Rr = np.concatenate(R)
            Cc = np.tile(np.arange(n, dtype=np.int64), len(R))
            Vv = np.concatenate([np.asarray(v, dtype=float) for v in V])
            M = sp.csc_matrix((Vv, (Rr, Cc)), shape=(dim, n))
            M.sum_duplicates()
            M.eliminate_zeros()
            if M.nnz == 0:
                continue
            acc.nnz += M.nnz
            dd = M.data
            acc.sumsq += float(np.dot(dd, dd))
            acc.maxabs = max(acc.maxabs, float(np.abs(dd).max()))
            coln = np.sqrt(np.asarray(M.multiply(M).sum(axis=0)).ravel())
            colabs = np.asarray(abs(M).sum(axis=0)).ravel()
            acc.maxcolabs = max(acc.maxcolabs, float(colabs.max()))
            order = np.argsort(-coln)[:topk]
            acc.top = sorted(acc.top + [(float(coln[i]), start + int(i)) for i in order if coln[i] > 0],
                             reverse=True)[:topk]
            Mc = M.tocoo()
            _keep(acc, Mc.row.astype(np.int64), Mc.col.astype(np.int64) + start, Mc.data, keep_limit)
    clear_caches(True)
    out = []
    for acc in accs:
        res = dict(regs="".join(sp_.regs), dim=dim, nnz=acc.nnz, maxabs=acc.maxabs,
                   hs_flat=float(np.sqrt(acc.sumsq / dim)))
        if acc.nnz == 0:
            res.update(opnorm=0.0, opnorm_method="zero", top=[])
        else:
            if not acc.overflow:
                rr, cc, vv = (np.concatenate(acc.kr), np.concatenate(acc.kc), np.concatenate(acc.kv))
                if not acc.offdiag:
                    res["opnorm"], res["opnorm_method"] = acc.maxabs, "diagonal"
                else:
                    res["opnorm"], res["opnorm_method"] = _opnorm_sparse(rr, cc, vv)
            else:
                if not acc.offdiag:
                    res["opnorm"], res["opnorm_method"] = acc.maxabs, "diagonal"
                else:
                    res["opnorm"], res["opnorm_method"] = None, "too many entries; bounds only"
            res["op_lower"] = acc.top[0][0] if acc.top else 0.0
            res["top"] = [(v, sp_.decode(c)) for v, c in acc.top]
        out.append(res)
    return out


def _keep(acc, r, c, v, keep_limit):
    if acc.overflow:
        return
    if acc.kept + len(v) > keep_limit:
        acc.overflow = True
        acc.kr, acc.kc, acc.kv = [], [], []
        return
    acc.kr.append(r)
    acc.kc.append(c)
    acc.kv.append(np.array(v, dtype=float))
    acc.kept += len(v)


def _opnorm_sparse(rr, cc, vv):
    """Exact operator norm of a sparse matrix given as triplets: split into
    connected components of its bipartite row/column graph and take batched
    dense SVDs, grouped by block shape."""
    ur, ri = np.unique(rr, return_inverse=True)
    uc, ci = np.unique(cc, return_inverse=True)
    nr, nc = len(ur), len(uc)
    if nr * nc <= 4_000_000:
        D = np.zeros((nr, nc))
        np.add.at(D, (ri, ci), vv)
        return float(np.linalg.norm(D, 2)), "dense-svd"
    G = sp.coo_matrix((np.ones_like(vv), (ri, nr + ci)), shape=(nr + nc, nr + nc))
    ncomp, lbl = connected_components(G, directed=False)
    rcomp, ccomp = lbl[:nr], lbl[nr:]

    def local(comp):
        order = np.argsort(comp, kind="stable")
        sc = comp[order]
        first = np.searchsorted(sc, sc, side="left")
        loc = np.empty_like(order)
        loc[order] = np.arange(len(order)) - first
        size = np.bincount(comp, minlength=ncomp)
        return loc, size

    rloc, rsize = local(rcomp)
    cloc, csize = local(ccomp)
    ecomp = rcomp[ri]
    best = 0.0
    shapes = {}
    for a, b in set(zip(rsize[np.unique(ecomp)].tolist(), csize[np.unique(ecomp)].tolist())):
        comps = np.nonzero((rsize == a) & (csize == b))[0]
        shapes[(a, b)] = len(comps)
        if a * b * len(comps) <= 20_000_000:
            pos = np.full(ncomp, -1)
            pos[comps] = np.arange(len(comps))
            sel = pos[ecomp] >= 0
            St = np.zeros((len(comps), a, b))
            np.add.at(St, (pos[ecomp[sel]], rloc[ri[sel]], cloc[ci[sel]]), vv[sel])
            s = np.linalg.svd(St, compute_uv=False)
            best = max(best, float(s[:, 0].max()))
        else:
            for k in comps:
                sel = ecomp == k
                D = np.zeros((a, b))
                np.add.at(D, (rloc[ri[sel]], cloc[ci[sel]]), vv[sel])
                best = max(best, float(np.linalg.norm(D, 2)))
    return best, f"components({ncomp}; shapes {dict(list(shapes.items())[:4])})"
