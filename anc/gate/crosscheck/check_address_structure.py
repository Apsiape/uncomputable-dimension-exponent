"""Lemma 15.6: simultaneous address-level model.

Space = address (N bits, bit 0 least significant) (x) optional register (k_N qubits) (x) data factor.
Built exactly as Lemma 15.6 + Theorem 7.1 of the source paper, with the COMPLEMENTARY mask
    f_N(x) = 1 - sum_{e in S} 1{x = 4^e mod 4^(e+1)}
and the address dressing  T_a = Dr (T_0 (x) I) Dr^*,  X_a = Dr (X_0 (x) I) Dr^*,
Dr = (+)_x R_0^{h_N(x)},  h_N(x) = sum_{r<x} f_N(r)   (including the all-ones wraparound).
Data D,E,W: at x in B_e (e in S) the packed witness of game e on its own data factor, identity on
the other factors; elsewhere D=0, E=I, W=I.  Block diagonal in x; identity on optional register.

We print operator-norm residuals of every address-side relation of the source (clock, guarded
increment, carry, decoders L,R, conditional clock) and of the new relations ((15.2), data domains and
data commutations).  Expected nonzero residuals: only the source's 3*4^-N (clock affine / tail),
sqrt2*4^-N (guard), 4^-N (carry step), <= 2*4^-N (conditional tail).  Everything new must be 0.
We also confirm that the data do NOT commute with T_a and V (no such commutation is imposed).

Run:  python -u check_address_structure.py
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import numpy as np
import scipy.sparse as sp
from toy_games import (colouring_game, two_family_presentation, classical_colouring_model,
                       magic_square_game, magic_square_pauli_model, pack, packed_relations,
                       letter_mats, eval_relation)


def trivial_game():
    return dict(name="trivial", X=[0], Y=[0], A=[0], B=[0], support=[(0, 0)],
                pred=lambda x, y, a, b: True)


def opnorm(Msp):
    """Exact operator norm via connected components of the support graph (blocks are small)."""
    from scipy.sparse.csgraph import connected_components
    Msp = sp.csr_matrix(Msp); Msp.eliminate_zeros()
    if Msp.nnz == 0:
        return 0.0
    r_, c_ = Msp.nonzero()
    if np.all(r_ == c_):
        return float(np.abs(Msp.data).max())
    pattern = (abs(Msp) + abs(Msp).T).tocsr()
    ncomp, lab = connected_components(pattern, directed=False)
    active = np.unique(np.concatenate([r_, c_]))
    best = 0.0
    order = np.argsort(lab[active], kind='stable')
    act_sorted = active[order]; lab_sorted = lab[act_sorted]
    splits = np.flatnonzero(np.diff(lab_sorted)) + 1
    for comp in np.split(act_sorted, splits):
        if len(comp) > 3000:
            raise RuntimeError(f"component too large: {len(comp)}")
        sub = Msp[comp][:, comp].toarray()
        best = max(best, float(np.linalg.norm(sub, 2)))
    return best


def perm_matrix(images, n):
    """Unitary with |s> -> |images[s]>."""
    return sp.csr_matrix((np.ones(n), (images, np.arange(n))), shape=(n, n))


def build(N, S_games):
    S = sorted(S_games.keys())
    nA = 1 << N
    f = np.ones(nA, dtype=np.int64)
    for e in S:
        for x in range(nA):
            if x % (4 ** (e + 1)) == 4 ** e:
                f[x] -= 1
    assert f.min() >= 0
    win = max(sum(f[(x - j) % nA] for j in range(1, N + 1)) for x in range(nA))
    k = 1 + win
    nY = 1 << k
    # data factors
    facs = []
    for e in S:
        g = S_games[e]
        pres = two_family_presentation(g['game'])
        pk = pack(g['projs'])
        facs.append((e, pk, pres))
    dims = [pk['n'] for (_, pk, _) in facs]
    Ld = int(np.prod(dims)) if dims else 1
    n = nA * nY * Ld
    print(f"N={N}: S={S}, mean flag lambda_N={f.mean():.6f}, max window={win}, k_N={k}, "
          f"data factor L_N={Ld} (factors {dims}), total dim={n}")
    idx = np.arange(n)
    x_of = idx // (nY * Ld); y_of = (idx // Ld) % nY; z_of = idx % Ld
    def lin(x, y, z):
        return (x * nY + y) * Ld + z
    I = sp.identity(n, format='csr')
    diag = lambda v: sp.diags(np.asarray(v, dtype=float), format='csr')
    bit = lambda j: (x_of >> j) & 1
    P = [diag(bit(j)) for j in range(N)]
    A = sum(3.0 * 4.0 ** (-j - 1) * P[j] for j in range(N))
    rotl = lambda x, nb: ((x << 1) & ((1 << nb) - 1)) | (x >> (nb - 1))
    rotr = lambda x, nb: (x >> 1) | ((x & 1) << (nb - 1))
    def rotl_pow(y, p, nb):
        for _ in range(p % nb):
            y = rotl(y, nb)
        return y
    h = np.concatenate([[0], np.cumsum(f)[:-1]])
    Dr = perm_matrix(lin(x_of, np.array([rotl_pow(int(yy), int(h[xx]), k) for xx, yy in zip(x_of, y_of)]), z_of), n)
    T0 = perm_matrix(lin(rotl(x_of, N), y_of, z_of), n)
    X0 = perm_matrix(lin(x_of ^ 1, y_of, z_of), n)
    Ta = Dr @ T0 @ Dr.T
    Xa = Dr @ X0 @ Dr.T
    Vimg = lin((x_of + 1) % nA, np.array([rotl_pow(int(yy), int(f[xx]), k) for xx, yy in zip(x_of, y_of)]), z_of)
    V = perm_matrix(Vimg, n)
    Vinv_map = np.empty(n, dtype=np.int64); Vinv_map[Vimg] = idx
    F = diag(f[x_of])
    Qv = f[x_of] * (y_of & 1)
    Q = diag(Qv)
    Xslot = perm_matrix(lin(x_of, y_of ^ 1, z_of), n)
    Y = (I - F) + F @ Xslot
    def series(vals):
        out = np.zeros(n); s = idx.copy()
        for j in range(60):
            out += 3.0 * 4.0 ** (-j - 1) * vals[s]
            s = Vinv_map[s]
        return diag(out)
    B = series(Qv.astype(float)); C = series(f[x_of].astype(float))
    # carry coordinate H
    def initial_ones(x):
        c = 0
        while c < N and (x >> c) & 1:
            c += 1
        return c
    Hx = np.array([0.0 if initial_ones(x) == N else 4.0 ** (-initial_ones(x)) for x in range(nA)])
    H = diag(Hx[x_of])
    # decoders
    Lx = np.zeros(nA); Rx = np.zeros(nA)
    for x in range(nA):
        if x == 0:
            continue
        e = 0
        while ((x >> (2 * e)) & 3) == 0:
            e += 1
        Rx[x] = 2.0 ** (-e)
        Lx[x] = 1.0 if ((x >> (2 * e)) & 3) == 1 else 0.0
    L = diag(Lx[x_of]); R = diag(Rx[x_of])
    # data
    Dd = sp.lil_matrix((n, n)); Ed = sp.lil_matrix((n, n)); Wd = sp.lil_matrix((n, n))
    def factor_ops(pos, pk):
        ops = {}
        for nm in ('D', 'E', 'W'):
            mats = [np.eye(dd) for dd in dims]
            mats[pos] = pk[nm]
            M = mats[0]
            for mm in mats[1:]:
                M = np.kron(M, mm)
            ops[nm] = M
        return ops
    cyl = {}
    for x in range(nA):
        ops = None
        for pos, (e, pk, pres) in enumerate(facs):
            if x % (4 ** (e + 1)) == 4 ** e:
                ops = factor_ops(pos, pk); cyl[x] = (pos, e)
        if ops is None:
            ops = {'D': np.zeros((Ld, Ld)), 'E': np.eye(Ld), 'W': np.eye(Ld)}
        for y in range(nY):
            base = lin(x, y, 0)
            sl = slice(base, base + Ld)
            Dd[sl, sl] = ops['D']; Ed[sl, sl] = ops['E']; Wd[sl, sl] = ops['W']
    Dd = Dd.tocsr(); Ed = Ed.tocsr(); Wd = Wd.tocsr()
    return locals()


def run(N, S_games):
    m = build(N, S_games)
    n, I, A, P, Ta, Xa, V, F, Q, Y, B, C, H, L, R = (m[k] for k in
        ('n', 'I', 'A', 'P', 'Ta', 'Xa', 'V', 'F', 'Q', 'Y', 'B', 'C', 'H', 'L', 'R'))
    Dd, Ed, Wd = m['Dd'], m['Ed'], m['Wd']
    P0 = P[0]
    comm = lambda X, Z: X @ Z - Z @ X
    res = {}
    # address clock
    res['[A,P]'] = opnorm(comm(A, P0))
    res['T A T* - 4A + 3P (expect 3*4^-N)'] = opnorm(Ta @ A @ Ta.T - 4 * A + 3 * P0)
    res['X P X - (I-P)'] = opnorm(Xa @ P0 @ Xa - (I - P0))
    res['[X, T A T*] (expect <= 6*4^-N)'] = opnorm(comm(Xa, Ta @ A @ Ta.T))
    res['guard (V - X[(I-P)+(TVT*)P])(I-A) (expect sqrt2*4^-N)'] = opnorm(
        (V - Xa @ ((I - P0) + (Ta @ V @ Ta.T) @ P0)) @ (I - A))
    # carry
    res['H - (I-P) - P T H T*/4'] = opnorm(H - (I - P0) - 0.25 * P0 @ Ta @ H @ Ta.T)
    res['[P, T H T*]'] = opnorm(comm(P0, Ta @ H @ Ta.T))
    res['[H, A]'] = opnorm(comm(H, A))
    res['V* A V - A + I - 7/4 H (expect 4^-N)'] = opnorm(V.T @ A @ V - A + I - 1.75 * H)
    # decoders
    P1 = Ta @ P0 @ Ta.T
    E00 = (I - P0) @ (I - P1); E1 = P0 @ (I - P1)
    T2 = Ta @ Ta
    res['L - E1 - E00 T^2 L T^-2'] = opnorm(L - E1 - E00 @ T2 @ L @ T2.T)
    res['R - (I-E00) - E00 T^2 R T^-2 / 2'] = opnorm(R - (I - E00) - 0.5 * E00 @ T2 @ R @ T2.T)
    # conditional clock
    res['(I-F)Q'] = opnorm((I - F) @ Q)
    for nm, (X1, X2) in {'[B,Q]': (B, Q), '[B,F]': (B, F), '[C,Q]': (C, Q), '[C,F]': (C, F),
                         '[B,C]': (B, C)}.items():
        res[nm] = opnorm(comm(X1, X2))
    res['V B V* - 4B + 3Q'] = opnorm(V @ B @ V.T - 4 * B + 3 * Q)
    res['V C V* - 4C + 3F'] = opnorm(V @ C @ V.T - 4 * C + 3 * F)
    res['Y F Y - F'] = opnorm(Y @ F @ Y - F)
    res['Y Q Y - (F - Q)'] = opnorm(Y @ Q @ Y - (F - Q))
    res['[Y, V B V*] (expect <= 2*4^-N)'] = opnorm(comm(Y, V @ B @ V.T))
    res['[Y, C]'] = opnorm(comm(Y, C))
    for nm, X1 in {'B': B, 'C': C, 'Q': Q, 'Y': Y}.items():
        res[f'[{nm}, A]'] = opnorm(comm(X1, A))
    # NEW relations
    res['Equation (15.2): (I-L)(I-F)'] = opnorm((I - L) @ (I - F))
    res['NEW data domain: D^2-D, E^2-E, W*W-I'] = max(opnorm(Dd @ Dd - Dd), opnorm(Ed @ Ed - Ed),
                                                      opnorm(Wd.T @ Wd - I), opnorm(Dd - Dd.T), opnorm(Ed - Ed.T))
    for dn, Dv in (('D', Dd), ('E', Ed), ('W', Wd)):
        res[f'NEW [{dn}, A_a],[{dn},L],[{dn},R],[{dn},F]'] = max(opnorm(comm(Dv, A)), opnorm(comm(Dv, L)),
                                                                opnorm(comm(Dv, R)), opnorm(comm(Dv, F)))
    # witnessed relations at unflagged addresses
    worst_R = 0.0
    nA, nY, Ld, dims, facs, cyl, lin = m['nA'], m['nY'], m['Ld'], m['dims'], m['facs'], m['cyl'], m['lin']
    unflagged = [x for x in range(nA) if m['f'][x] == 0]
    for x in unflagged:
        pos, e = cyl[x]
        pres = facs[pos][2]
        base = lin(x, 0, 0); sl = slice(base, base + Ld)
        Lm = {'D': Dd[sl, sl].toarray(), 'E': Ed[sl, sl].toarray(), 'W': Wd[sl, sl].toarray()}
        Lm['w'] = Lm['W'].T
        for (_, rel) in packed_relations(pres):
            worst_R = max(worst_R, float(np.abs(eval_relation(rel, Lm, Ld)).max()))
    res['NEW all R_e exact on data at every unflagged address'] = worst_R
    # not imposed: data vs address shifts
    info = {'[D,T_a]': opnorm(comm(Dd, Ta)), '[W,V]': opnorm(comm(Wd, V)), '[D,X_a]': opnorm(comm(Dd, Xa))}
    print(f"  unflagged addresses: {unflagged} (all inside L: {all(m['Lx'][x] == 1 for x in unflagged)})")
    for kname, v in res.items():
        print(f"  {kname:62s} {v:.3e}")
    print(f"  (not imposed) {info}")
    tol = 1e-12
    expected_nonzero = {'T A T* - 4A + 3P (expect 3*4^-N)': 3 * 4.0 ** -N,
                        '[X, T A T*] (expect <= 6*4^-N)': 6 * 4.0 ** -N,
                        'guard (V - X[(I-P)+(TVT*)P])(I-A) (expect sqrt2*4^-N)': np.sqrt(2) * 4.0 ** -N,
                        'V* A V - A + I - 7/4 H (expect 4^-N)': 4.0 ** -N,
                        '[Y, V B V*] (expect <= 2*4^-N)': 2 * 4.0 ** -N}
    ok = True
    for kname, v in res.items():
        bound = expected_nonzero.get(kname, 0.0)
        if v > bound * (1 + 1e-9) + tol:
            ok = False; print(f"  ** exceeds bound: {kname}: {v} > {bound}")
    print(f"  RESULT N={N}: {'PASS' if ok else 'FAIL'}")
    return ok


def main():
    K2 = colouring_game(2, [(0, 1)], 2)
    presK2 = two_family_presentation(K2)
    triv = trivial_game(); prest = two_family_presentation(triv)
    ok1 = run(4, {0: dict(game=K2, projs=classical_colouring_model(K2, presK2, {0: 0, 1: 1})),
                  1: dict(game=triv, projs=[np.array([[1.0]])] * prest['m'])})
    ok2 = run(6, {0: dict(game=triv, projs=[np.array([[1.0]])] * prest['m']),
                  2: dict(game=triv, projs=[np.array([[1.0]])] * prest['m'])})
    ok3 = run(6, {})  # nothing admitted yet: every address flagged
    print("\nALL PASS" if (ok1 and ok2 and ok3) else "\nSOME FAIL")


if __name__ == "__main__":
    main()
