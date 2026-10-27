"""Exact checks of the two conjugacy gadgets of the compiler (Section 3 of the paper), with random instances."""
import itertools
import numpy as np

rng = np.random.default_rng(1)


def rand_involution(n):
    # a random orthogonal involution: Q diag(+-1) Q^T
    q, _ = np.linalg.qr(rng.normal(size=(n, n)))
    s = np.diag(rng.choice([-1.0, 1.0], size=n))
    return q @ s @ q.T


def is_inv(m):
    return np.allclose(m @ m, np.eye(len(m))) and np.allclose(m, m.T)


def comm(a, b):
    return np.allclose(a @ b, b @ a)


def check_context(name, ms):
    ok = all(is_inv(m) for m in ms) and all(comm(x, y) for x, y in itertools.combinations(ms, 2))
    prod = np.eye(len(ms[0]))
    for m in ms:
        prod = prod @ m
    ok = ok and np.allclose(prod, np.eye(len(prod)))
    print(f'  {name}: {"ok" if ok else "FAIL"}')
    return ok


I = None
n = 4
# Gadget 2: aba = c with b, c commuting. Take a, b generating a dihedral group of order 8 so that b and aba commute.
# Construct concretely: b = diag(1,-1,1,-1) style and a a permutation with (ab)^4 = 1.
for trial in range(3):
    # random dihedral-8 representation: rotation r of order 4, reflection a; b = a r
    k = 4
    th = np.pi / 2
    rot2 = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
    refl = np.array([[1.0, 0], [0, -1.0]])
    q, _ = np.linalg.qr(rng.normal(size=(2, 2)))
    a = q @ refl @ q.T
    r = q @ rot2 @ q.T
    b = a @ r
    c = a @ b @ a
    assert is_inv(a) and is_inv(b) and comm(b, c)
    E = np.eye(2)
    Z = np.zeros((2, 2))
    M = lambda x: np.block([[Z, x], [x, Z]])
    D = lambda x, y: np.block([[x, Z], [Z, y]])
    d1, d2, d3 = M(a), M(E), M(b)
    d4 = np.block([[Z, b @ a], [a @ b, Z]])
    d5 = D(b @ a @ b, a)
    d6 = D(b @ c, E)
    d7 = D(b, c)
    A2, B2, C2 = D(a, a), D(b, b), D(c, c)
    print(f'gadget aba=c, trial {trial}:')
    res = [check_context('a d1 d2', [A2, d1, d2]), check_context('b d2 d3', [B2, d2, d3]),
           check_context('d3 d4 d5', [d3, d4, d5]), check_context('a d5 d6', [A2, d5, d6]),
           check_context('c d6 d7', [C2, d6, d7]), check_context('d1 d4 d7', [d1, d4, d7])]
    print('  all contexts:', all(res))

# Gadget 1: x1 x2 x1 = x3 (involutions); doubled extension
for trial in range(3):
    x1, x2 = rand_involution(n), rand_involution(n)
    x3 = x1 @ x2 @ x1
    E = np.eye(n)
    Z = np.zeros((n, n))
    D = lambda x, y: np.block([[x, Z], [Z, y]])
    X = {i: D(m, m) for i, m in zip((1, 2, 3), (x1, x2, x3))}
    Y = {i: D(m, E) for i, m in zip((1, 2, 3), (x1, x2, x3))}
    Zz = {i: D(E, m) for i, m in zip((1, 2, 3), (x1, x2, x3))}
    f = np.block([[Z, E], [E, Z]])
    W = {i: np.block([[Z, m], [m, Z]]) for i, m in zip((1, 2, 3), (x1, x2, x3))}
    g = D(x2, x3)
    print(f'gadget x1x2x1=x3, trial {trial}:')
    ok = True
    for i in (1, 2, 3):
        ok &= check_context(f'x{i} y{i} z{i}', [X[i], Y[i], Zz[i]])
        ok &= check_context(f'x{i} f w{i}', [X[i], f, W[i]])
    ok &= check_context('g y2 z3', [g, Y[2], Zz[3]])
    for i in (1, 2, 3):
        good = np.allclose(f @ Y[i] @ f, Zz[i])
        print(f'  f y{i} f = z{i}: {"ok" if good else "FAIL"}')
        ok &= good
    good = np.allclose(W[1] @ Y[2] @ W[1], Zz[3])
    print(f'  w1 y2 w1 = z3: {"ok" if good else "FAIL"}')
    ok &= good
    print('  all:', ok)
