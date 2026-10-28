"""Toy games, two-family projection presentations A_e, the packing R(A) into
data generators D, E, W (Section 15.2 and Lemma 15.2), and the signed-monomial form of R(A)
consumed by the operator-register transducer (Section 15.2 and Lemma 15.3).

All matrices used for the witness games have dyadic-rational entries with small
denominators, so float64 arithmetic below is EXACT for them (no rounding occurs:
every product/sum stays dyadic with < 53 significant bits). Zero tests are
therefore exact equality tests (we still print max-abs residuals).

Letters: 'D', 'E', 'W', 'w'   (w = W^*).
A monomial is (sign, word) with word a string over these letters; the empty word is I.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import itertools
import numpy as np


# ----------------------------------------------------------------------------
# Games.  A game is a dict with Alice questions X, Bob questions Y, answer sets,
# support (list of (x,y) with positive probability) and predicate V(x,y,a,b).
# ----------------------------------------------------------------------------

def colouring_game(n_vertices, edges, n_colours):
    V = list(range(n_vertices))
    E = set()
    for (u, v) in edges:
        E.add((u, v)); E.add((v, u))
    support = [(u, u) for u in V] + sorted(E)
    def pred(x, y, a, b):
        if x == y:
            return a == b
        return a != b
    return dict(name=f"colouring(n={n_vertices},|E|={len(edges)},c={n_colours})",
                X=V, Y=V, A=list(range(n_colours)), B=list(range(n_colours)),
                support=support, pred=pred)


MS_PARITY = {('r', 0): 1, ('r', 1): 1, ('r', 2): 1, ('c', 0): 1, ('c', 1): 1, ('c', 2): -1}


def ms_context_vars(ctx):
    kind, i = ctx
    return [(i, j) for j in range(3)] if kind == 'r' else [(j, i) for j in range(3)]


def magic_square_game(parity=MS_PARITY):
    """BCS game: Alice gets a context (row/col), answers a satisfying assignment;
    Bob gets a variable, answers +-1; win iff consistent."""
    contexts = sorted(parity.keys())
    variables = [(r, c) for r in range(3) for c in range(3)]
    sat = {}
    for ctx in contexts:
        sat[ctx] = [a for a in itertools.product((1, -1), repeat=3)
                    if a[0] * a[1] * a[2] == parity[ctx]]
    # Alice answer index -> assignment; use a common answer alphabet 0..3
    support = [(ctx, v) for ctx in contexts for v in ms_context_vars(ctx)]
    def pred(x, y, a, b):
        ctx, v = x, y
        k = ms_context_vars(ctx).index(v)
        return sat[ctx][a][k] == (1 if b == 0 else -1)
    return dict(name="magic-square" + ("" if parity == MS_PARITY else "(all-even)"),
                X=contexts, Y=variables, A=list(range(4)), B=[0, 1],
                support=support, pred=pred, sat=sat)


def inconsistent_bcs_game():
    """Two one-variable contexts demanding x=+1 and x=-1: no model in any dimension."""
    contexts = ['plus', 'minus']
    sat = {'plus': [(1,)], 'minus': [(-1,)]}
    support = [('plus', 0), ('minus', 0)]
    def pred(x, y, a, b):
        return sat[x][a][0] == (1 if b == 0 else -1)
    return dict(name="inconsistent-BCS", X=contexts, Y=[0], A=[0], B=[0, 1],
                support=support, pred=pred, sat=sat)


# ----------------------------------------------------------------------------
# Two-family projection presentation A_e (Section 15.1):
# Alice projections p[x,a], Bob projections q[y,b]; PVM sums; p[x,a] q[y,b] = 0
# for every tested losing tuple.
# ----------------------------------------------------------------------------

def two_family_presentation(game):
    gens = []  # list of ('A', x, a) or ('B', y, b)
    for x in game['X']:
        for a in game['A']:
            gens.append(('A', x, a))
    for y in game['Y']:
        for b in game['B']:
            gens.append(('B', y, b))
    idx = {g: i for i, g in enumerate(gens)}
    groups = [[idx[('A', x, a)] for a in game['A']] for x in game['X']] + \
             [[idx[('B', y, b)] for b in game['B']] for y in game['Y']]
    losing = []
    for (x, y) in game['support']:
        for a in game['A']:
            for b in game['B']:
                if not game['pred'](x, y, a, b):
                    losing.append((idx[('A', x, a)], idx[('B', y, b)]))
    return dict(gens=gens, idx=idx, groups=groups, losing=losing, m=len(gens))


# ----------------------------------------------------------------------------
# Exact witnesses.
# ----------------------------------------------------------------------------
I2 = np.eye(2); PX = np.array([[0., 1.], [1., 0.]]); PZ = np.array([[1., 0.], [0., -1.]])
PYY = np.kron(np.array([[0., -1j], [1j, 0.]]), np.array([[0., -1j], [1j, 0.]])).real  # Y(x)Y is real

MS_OPS = {
    (0, 0): np.kron(PX, I2), (0, 1): np.kron(I2, PX), (0, 2): np.kron(PX, PX),
    (1, 0): np.kron(I2, PZ), (1, 1): np.kron(PZ, I2), (1, 2): np.kron(PZ, PZ),
    (2, 0): np.kron(PX, PZ), (2, 1): np.kron(PZ, PX), (2, 2): PYY,
}


def classical_colouring_model(game, pres, colouring):
    """Deterministic strategy: both players answer colouring[v]. Returns list of 1x1 projections."""
    proj = []
    for g in pres['gens']:
        _, v, c = g
        proj.append(np.array([[1.0 if colouring[v] == c else 0.0]]))
    return proj


def magic_square_pauli_model(game, pres, ops=MS_OPS):
    d = 4
    proj = []
    for g in pres['gens']:
        side, q, ans = g
        if side == 'A':
            vs = ms_context_vars(q)
            a = game['sat'][q][ans]
            P = np.eye(d)
            for k, v in enumerate(vs):
                P = P @ ((np.eye(d) + a[k] * ops[v]) / 2)
            proj.append(P)
        else:
            s = 1 if ans == 0 else -1
            proj.append((np.eye(d) + s * ops[q]) / 2)
    return proj


def magic_square_classical_attempt(game, pres, assignment):
    """Deterministic: Bob answers assignment[v]; Alice answers, per context, the
    satisfying assignment closest to the global one (first in list on ties)."""
    proj = []
    choice = {}
    for ctx in game['X']:
        vs = ms_context_vars(ctx)
        target = tuple(assignment[v] for v in vs)
        best = max(range(len(game['sat'][ctx])),
                   key=lambda i: sum(int(game['sat'][ctx][i][k] == target[k]) for k in range(3)))
        choice[ctx] = best
    for g in pres['gens']:
        side, q, ans = g
        if side == 'A':
            proj.append(np.array([[1.0 if choice[q] == ans else 0.0]]))
        else:
            s = 1 if ans == 0 else -1
            proj.append(np.array([[1.0 if assignment[q] == s else 0.0]]))
    return proj


# ----------------------------------------------------------------------------
# Packing (Section 15.2 and Lemma 15.2).
# ----------------------------------------------------------------------------

def pack(projs):
    m = len(projs); d = projs[0].shape[0]
    n = m * d
    D = np.zeros((n, n))
    for j, p in enumerate(projs):
        D[j * d:(j + 1) * d, j * d:(j + 1) * d] = p
    E = np.zeros((n, n)); E[:d, :d] = np.eye(d)
    W = np.zeros((n, n))
    for j in range(m):
        jj = (j + 1) % m
        W[jj * d:(jj + 1) * d, j * d:(j + 1) * d] = np.eye(d)
    return dict(D=D, E=E, W=W, Ws=W.T.copy(), m=m, d=d, n=n)


def Dj_word(j):
    return 'w' * j + 'D' + 'W' * j


def Pj_word(j):
    return 'E' + Dj_word(j) + 'E'


def packed_relations(pres):
    """R(A) as a list of (label, [ (sign, word), ... ]) with integer (+-1) signs."""
    m = pres['m']
    rels = []
    rels.append(("sum_j W^j E W^-j - I",
                 [(+1, 'W' * j + 'E' + 'w' * j) for j in range(m)] + [(-1, '')]))
    for j in range(m):
        rels.append((f"[E,D_{j}]", [(+1, 'E' + Dj_word(j)), (-1, Dj_word(j) + 'E')]))
    for gi, g in enumerate(pres['groups']):
        rels.append((f"PVM group {gi}: sum P - E", [(+1, Pj_word(j)) for j in g] + [(-1, 'E')]))
    for (i, j) in pres['losing']:
        rels.append((f"losing P_{i} P_{j}", [(+1, Pj_word(i) + Pj_word(j))]))
    return rels


def letter_mats(pk):
    return {'D': pk['D'], 'E': pk['E'], 'W': pk['W'], 'w': pk['Ws']}


def eval_word(word, L, n):
    M = np.eye(n)
    for ch in word:
        M = M @ L[ch]
    return M


def eval_relation(rel, L, n):
    R = np.zeros((n, n))
    for (s, w) in rel:
        R = R + s * eval_word(w, L, n)
    return R
