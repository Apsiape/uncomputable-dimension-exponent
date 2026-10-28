"""Finite tests of Section 15.1, packing and programmed testing.

(a) Two-family presentation A_e, exact witnesses, packing R(A) (Section 15.2 and Lemma 15.2):
    every packed relation is exactly zero on the packed witness.
(b) Operator-register transducer (Section 15.2 and Lemma 15.3): the instruction stream
       T:=0; per monomial: M:=I; M:=M*letter ...; T:=T +- 2^-b M; CHECK
    is simulated with right multiplications only.  At each CHECK we verify
       T == 2^-b r(D,E,W)   (exact equality),   ||T|| <= 1,
    and T == 0 on witness data.  Negative controls (no witness / wrong data)
    must show a nonzero CHECK output (which equation (15.5) then forces to be flagged).
(c) Separate-family PCC example (Section 15.1): a symmetric game with a perfect PCC strategy whose
    SINGLE-family presentation has no model in any dimension, while the two-family
    presentation does.
(d) Lemma 15.1 completeness derivation: a PCC perfect strategy with a NON-maximally entangled state;
    both players' operators commute with rho_A and each eigenspace restriction is an
    exact flat model of the two-family A_e.

Run:  python -u check_packing_transducer.py
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import numpy as np
from toy_games import (colouring_game, magic_square_game, inconsistent_bcs_game,
                       two_family_presentation, classical_colouring_model,
                       magic_square_pauli_model, magic_square_classical_attempt,
                       pack, packed_relations, letter_mats, eval_relation)


def right_mult(M, ch, pk):
    m, d = pk['m'], pk['d']
    if ch == 'E':
        R = np.zeros_like(M); R[:, :d] = M[:, :d]; return R
    if ch == 'W':   # (M W)[:, block j] = M[:, block j+1]
        return np.roll(M, -d, axis=1)
    if ch == 'w':   # (M W*)[:, block j] = M[:, block j-1]
        return np.roll(M, d, axis=1)
    if ch == 'D':
        R = np.empty_like(M)
        D = pk['D']
        for j in range(m):
            sl = slice(j * d, (j + 1) * d)
            R[:, sl] = M[:, sl] @ D[sl, sl]
        return R
    raise ValueError(ch)


def run_transducer(pk, rels, check_norm_every_step=False):
    """Simulate the operator instructions. Returns list of (label, T_at_check, b), #instructions."""
    n = pk['n']
    out = []
    n_instr = 0
    max_norm = 0.0
    for (label, rel) in rels:
        K = len(rel)
        b = max(0, math.ceil(math.log2(K)))
        T = np.zeros((n, n)); n_instr += 1            # T := 0
        for (s, w) in rel:
            M = np.eye(n); n_instr += 1                # M := I
            for ch in w:
                M = right_mult(M, ch, pk); n_instr += 1  # M := M ch
            T = T + s * (2.0 ** -b) * M; n_instr += 1  # T := T +- r_b M
            if check_norm_every_step:
                max_norm = max(max_norm, np.linalg.norm(T, 2))
        n_instr += 1                                   # CHECK
        out.append((label, T, b))
        max_norm = max(max_norm, np.linalg.norm(T, 2))
    return out, n_instr, max_norm


def check_case(name, game, projs, expect_zero, exact=True):
    pres = two_family_presentation(game)
    pk = pack(projs)
    rels = packed_relations(pres)
    L = letter_mats(pk)
    # domain checks for the packed data
    D, E, W = pk['D'], pk['E'], pk['W']
    dom = max(np.abs(D @ D - D).max(), np.abs(D - D.T).max(), np.abs(E @ E - E).max(),
              np.abs(W @ W.T - np.eye(pk['n'])).max())
    small = pk['n'] <= 40
    checks, n_instr, max_norm = run_transducer(pk, rels, check_norm_every_step=small)
    worst_mismatch = 0.0
    exact_equal = True
    nonzero = []
    for (label, rel), (lab2, T, b) in zip(rels, checks):
        direct = (2.0 ** -b) * eval_relation(rel, L, pk['n'])
        if (exact and not np.array_equal(direct, T)) or ((not exact) and np.abs(direct - T).max() > 1e-12):
            exact_equal = False
        worst_mismatch = max(worst_mismatch, float(np.abs(direct - T).max()))
        if np.abs(T).max() > (0.0 if exact else 1e-9):
            nonzero.append((label, float(np.abs(T).max())))
    print(f"--- {name}: game={game['name']}  m={pres['m']}  d={pk['d']}  packed dim={pk['n']}")
    print(f"    #relations in R(A) = {len(rels)}   #operator instructions = {n_instr}")
    print(f"    packed-domain residual (D,E projections, W unitary) = {dom}")
    print(f"    CHECK output equals 2^-b r(D,E,W) {'exactly' if exact else 'to 1e-12 (non-dyadic data)'}: {exact_equal} (max |diff| = {worst_mismatch})")
    print(f"    max operator norm of accumulator T {'(every step)' if small else '(at CHECKs)'} = {max_norm:.6f}")
    print(f"    #CHECKs with nonzero output = {len(nonzero)} of {len(checks)}")
    if nonzero:
        print(f"    first nonzero CHECKs: {nonzero[:3]}")
    ok = exact_equal and (max_norm <= 1 + 1e-12) and (dom == 0.0 if exact else dom < 1e-12) and ((len(nonzero) == 0) == expect_zero)
    print(f"    RESULT: {'PASS' if ok else 'FAIL'} (expected all-zero CHECKs: {expect_zero})")
    return ok


def single_vs_two_family():
    """Symmetric anti-synchronous game: one question, answers {0,1}, win iff a != b.
    Perfect PCC (d=1): Alice always 0, Bob always 1.
    Single family p_0+p_1=I, p_0 p_0 = 0, p_1 p_1 = 0 forces p_0=p_1=0: no model in any dim."""
    print("--- Separate-family PCC example (Section 15.1) (single-family vs two-family presentation)")
    # two-family: p_{0,0}=1,p_{0,1}=0 (Alice), q_{0,0}=0,q_{0,1}=1 (Bob); losing (a,b)=(0,0),(1,1)
    p = {0: 1.0, 1: 0.0}; q = {0: 0.0, 1: 1.0}
    two_ok = (p[0] + p[1] == 1.0) and (q[0] + q[1] == 1.0) and p[0] * q[0] == 0 and p[1] * q[1] == 0
    # PCC check (d=1 trivially projective/consistent/commuting); value:
    win = sum(p[a] * q[b] for a in (0, 1) for b in (0, 1) if a != b)
    print(f"    two-family exact model in d=1: {two_ok};  winning probability of the PCC strategy = {win}")
    # single family: tr(p_a p_a) = tr(p_a) must vanish for both a, but tr(p_0)+tr(p_1)=d
    print("    single-family: p_a p_a = 0 implies p_a = 0 (projection), contradicting p_0+p_1=I in every dimension")
    return two_ok and win == 1.0


def pcc_nonmax_entangled():
    """Lemma 15.1 completeness derivation with a PCC perfect strategy whose state is NOT maximally entangled."""
    print("--- Lemma 15.1 completeness: PCC perfect strategy with non-maximally-entangled state -> exact flat models")
    game = magic_square_game()
    pres = two_family_presentation(game)
    base = magic_square_pauli_model(game, pres)          # real symmetric projections, d=4
    d = 4
    # Operators on H = C^4 (+) C^4 (two copies), same for both copies; Schmidt weights differ by copy.
    ops = [np.kron(np.eye(2), P) for P in base]           # A = B-family operators on C^8
    w = np.array([0.7] * d + [0.3] * d) / d               # Schmidt coefficients squared
    Psi = np.diag(np.sqrt(w))                             # |psi> = sum_i sqrt(w_i)|i>|i>
    # consistency: M Psi == Psi M^T for each operator
    cons = max(np.abs(M @ Psi - Psi @ M.T).max() for M in ops)
    rhoA = Psi @ Psi.conj().T
    comm = max(np.abs(M @ rhoA - rhoA @ M).max() for M in ops)
    # losing probability <psi| A (x) B |psi> = tr(Psi^* A Psi B^T)
    lose = 0.0
    for (i, j) in pres['losing']:
        lose += np.trace(Psi.conj().T @ ops[i] @ Psi @ ops[j].T).real
    # eigenspace restrictions
    evals = sorted(set(np.round(np.diag(rhoA), 12)))
    worst = 0.0
    for lam in evals:
        idx = np.where(np.abs(np.diag(rhoA) - lam) < 1e-12)[0]
        R = [M[np.ix_(idx, idx)] for M in ops]
        k = len(idx)
        res = 0.0
        for g in pres['groups']:
            res = max(res, np.abs(sum(R[j] for j in g) - np.eye(k)).max())
        for (i, j) in pres['losing']:
            res = max(res, np.abs(R[i] @ R[j]).max())
        for P in R:
            res = max(res, np.abs(P @ P - P).max())
        worst = max(worst, res)
    print(f"    consistency residual = {cons:.2e}, [ops, rho_A] residual = {comm:.2e}, losing prob = {lose:.2e}")
    print(f"    eigenvalues of rho_A = {evals}; worst exact-model residual on eigenspaces = {worst:.2e}")
    ok = cons < 1e-12 and comm < 1e-12 and abs(lose) < 1e-12 and worst < 1e-12
    print(f"    RESULT: {'PASS' if ok else 'FAIL'}")
    return ok


def main():
    results = []
    # Witness cylinders (would be unflagged once their certificate is admitted)
    K3 = colouring_game(3, [(0, 1), (1, 2), (0, 2)], 3)
    pres = two_family_presentation(K3)
    results.append(check_case("witness e=0 (K3 3-colouring, classical witness)", K3,
                              classical_colouring_model(K3, pres, {0: 0, 1: 1, 2: 2}), True))
    MS = magic_square_game()
    pres = two_family_presentation(MS)
    results.append(check_case("witness e=1 (Mermin-Peres magic square, Pauli witness d=4)", MS,
                              magic_square_pauli_model(MS, pres), True))
    # Negative controls (no finite witness exists; any data must fail some CHECK)
    K4 = colouring_game(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 3)
    pres = two_family_presentation(K4)
    results.append(check_case("control e=2 (K4 3-colouring, classical attempt)", K4,
                              classical_colouring_model(K4, pres, {0: 0, 1: 1, 2: 2, 3: 0}), False))
    rng = np.random.default_rng(7)
    # random rank-one PVMs in d=3 for each question (Alice and Bob)
    def rand_pvm(dim, k):
        Q, _ = np.linalg.qr(rng.standard_normal((dim, dim)))
        return [np.outer(Q[:, i], Q[:, i]) for i in range(k)]
    pv = {}
    for side, qs in (('A', K4['X']), ('B', K4['Y'])):
        for x in qs:
            pv[(side, x)] = rand_pvm(3, 3)
    projs = [pv[(g[0], g[1])][g[2]] for g in pres['gens']]
    # random data are not dyadic; equality test below is then a float test, so report max diff
    results.append(check_case("control e=2' (K4 3-colouring, random d=3 PVMs)", K4, projs, False, exact=False))
    MSc = magic_square_game()
    pres = two_family_presentation(MSc)
    assign = {(r, c): 1 for r in range(3) for c in range(3)}
    results.append(check_case("control e=3 (magic square, classical attempt)", MSc,
                              magic_square_classical_attempt(MSc, pres, assign), False))
    INC = inconsistent_bcs_game()
    pres = two_family_presentation(INC)
    results.append(check_case("control e=4 (inconsistent BCS, classical attempt)", INC,
                              [np.array([[1.0]]) if (g[0] == 'A') or (g[0] == 'B' and g[2] == 0) else np.array([[0.0]])
                               for g in pres['gens']], False))
    results.append(single_vs_two_family())
    results.append(pcc_nonmax_entangled())
    print("\nALL PASS" if all(results) else "\nSOME FAIL: " + str(results))


if __name__ == "__main__":
    main()
