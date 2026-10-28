"""Operator-level check of the new equations (no blockwise shortcut).

For one unflagged address of configuration 1 (b = 3/8, R_* = 1/16), build the
time register C^T (T = 2^Nt) tensor the data factor of every gate whose tuple
occurs in the window, as sparse matrices, with U the genuine cyclic time
increment.  Fuel prefix k gives the reset projection Z = 1{t = 0 mod 2^k};
the history at time t is the actual initialized history at t mod 2^k
(Theorem 7.1 assignment).  Then evaluate as operators:

  hold  (U* X U - X)(I - Z_+)(I - q_LOAD)                 X in {D, E, W}
  reg   U* S U - Z_+ Init(S) - (I - Z_+) Phi_S            S in {M, Sigma}
  ctr   U* c U - Z_+ R_* - (I - Z_+) Step(c)
  zt    c - z - (1/2)(I - z) s
  check q_CHECK Sigma (I - F)                              (F = 0 here)
  comm  [X, A_t], [X, Z], [X, c], [M, Z], [Sigma, Z]

and the negative controls: the holding equation without the LOAD factor, and [X, U] (the data
are NOT time invariant, so the Section-15 hypothesis really is dropped).

Run:  python -u operator_level.py
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import json
import sys
from fractions import Fraction as Fr

import numpy as np
import scipy.sparse as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import toy_classification as tc  # noqa: E402


def spnorm(A):
    A = A.tocsr()
    if A.nnz == 0:
        return 0.0
    # exact data are dyadic; Frobenius norm >= operator norm, and zero iff zero
    return float(np.sqrt((abs(A.data) ** 2).sum()))


def run(Nt, k, bits=(0, 0, 0, 0)):
    seq = tc.Seq("harmonic", Fr(9, 20), Fr(3, 10), "harmonic")
    world = tc.World(seq)
    Rstar = Fr(1, 16)
    T = 2 ** Nt
    P = 2 ** k
    ins = tc.stream(world, list(bits) + [0] * 64, Rstar, P)
    H = tc.interpret(world, ins, True, Rstar)
    # factors touched in the window
    fids = set()
    for (c, M, S, tup, _) in H:
        for op in (M, S, tup["D"], tup["E"], tup["W"]):
            fids |= set(op.f)
    fids = tuple(sorted(fids, key=str))
    dimD = int(np.prod([tc.DIMS[f] for f in fids])) if fids else 1

    def blk(op):
        return sp.csr_matrix(tc.lift(tc.Op(op.f, op.m), fids) if op.f != fids else op.m)

    def blockdiag(get):
        return sp.block_diag([get(t % P) for t in range(T)], format="csr")

    Id = sp.identity(T * dimD, format="csr")
    shift = sp.csr_matrix((np.ones(T), ((np.arange(T) + 1) % T, np.arange(T))), shape=(T, T))
    U = sp.kron(shift, sp.identity(dimD), format="csr")
    Ut = U.T.tocsr()

    def diag_scalar(f):
        return sp.kron(sp.diags([float(f(t % P, t)) for t in range(T)]), sp.identity(dimD), format="csr")

    Z = diag_scalar(lambda r, t: 1 if r == 0 else 0)
    Zp = Ut @ Z @ U
    qLOAD = diag_scalar(lambda r, t: 1 if ins[r][0] == "LOAD" else 0)
    qCHECK = diag_scalar(lambda r, t: 1 if ins[r][0] == "CHECK" else 0)
    qSETI = diag_scalar(lambda r, t: 1 if ins[r][0] == "SETI" else 0)
    qCLR = diag_scalar(lambda r, t: 1 if ins[r][0] == "CLR" else 0)
    qDEC = diag_scalar(lambda r, t: 1 if ins[r][0] == "DEC" else 0)
    qMUL = {L: diag_scalar(lambda r, t, L=L: 1 if ins[r] == ("MUL", L) else 0) for L in "DEWw"}
    qACC = {sg: diag_scalar(lambda r, t, sg=sg: (2.0 ** (-ins[r][2])) if (ins[r][0] == "ACC" and ins[r][1] == sg) else 0)
            for sg in (1, -1)}
    qACCany = diag_scalar(lambda r, t: 1 if ins[r][0] == "ACC" else 0)
    cdiag = diag_scalar(lambda r, t: H[r][0])
    zdiag = diag_scalar(lambda r, t: tc.zero_test(H[r][0])[0])
    sdiag = diag_scalar(lambda r, t: tc.zero_test(H[r][0])[1])
    At = diag_scalar(lambda r, t: sum(3 * 4.0 ** (-j - 1) * ((t >> j) & 1) for j in range(Nt)))

    X = {L: blockdiag(lambda r, L=L: blk(H[r][3][L])) for L in "DEWw"}
    M = blockdiag(lambda r: blk(H[r][1]))
    S = blockdiag(lambda r: blk(H[r][2]))

    res = {}
    gate_guard = (Id - Zp) @ (Id - qLOAD)
    res["holding"] = max(spnorm((Ut @ X[L] @ U - X[L]) @ gate_guard) for L in "DEW")
    res["NC_holding_without_LOAD_factor"] = max(spnorm((Ut @ X[L] @ U - X[L]) @ (Id - Zp)) for L in "DEW")
    res["NC_data_commute_with_U"] = max(spnorm(X[L] @ U - U @ X[L]) for L in "DEW")
    # LOAD initializes M to I and Sigma to zero on its outgoing edge.
    qmulsum = sum(qMUL.values())
    qONE = qSETI + qLOAD
    PhiM = qONE + sum(qMUL[L] @ (M @ X[L]) for L in "DEWw") + (Id - qONE - qmulsum) @ M
    PhiS = qACCany @ S + qACC[1] @ M - qACC[-1] @ M + (Id - qCLR - qLOAD - qACCany) @ S
    res["reg_M"] = spnorm(Ut @ M @ U - Zp @ Id - (Id - Zp) @ PhiM)
    res["reg_Sigma"] = spnorm(Ut @ S @ U - (Id - Zp) @ PhiS)
    stepc = qDEC @ (zdiag @ cdiag + (Id - zdiag) @ (2 * cdiag)) + (Id - qDEC) @ cdiag
    res["counter_c"] = spnorm(Ut @ cdiag @ U - float(Rstar) * Zp - (Id - Zp) @ stepc)
    res["zero_test"] = spnorm(cdiag - zdiag - 0.5 * (Id - zdiag) @ sdiag)
    res["check_unflagged"] = spnorm(qCHECK @ S)
    res["init_ZM_minus_Z"] = spnorm(Z @ M - Z)
    res["init_ZSigma"] = spnorm(Z @ S)
    comm = 0.0
    for L in "DEW":
        for Y in (At, Z, cdiag, zdiag, qLOAD, qCHECK):
            comm = max(comm, spnorm(X[L] @ Y - Y @ X[L]))
    for R_ in (M, S):
        for Y in (At, Z, cdiag):
            comm = max(comm, spnorm(R_ @ Y - Y @ R_))
    res["commutations"] = comm
    res["dims"] = dict(T=T, period=P, data_factor=dimD, total=T * dimD,
                       loads_in_window=sum(1 for it in ins if it[0] == "LOAD"),
                       checks_in_window=sum(1 for it in ins if it[0] == "CHECK"))
    return res


def load_initialization_regression():
    """A nonvacuous LOAD: incoming M = 0 and Sigma = I, outgoing I and 0."""
    ins = [("ACC", 1, 0), ("MUL", "D"), ("LOAD", 0, 0), ("IDLE",)]
    # Keep scalar default data, so the register transition is isolated from
    # witness selection. ACC then MUL D produces exactly the incoming state.
    history = tc.interpret(None, ins, True, Fr(0),
                           data_override=lambda t, instructions, tup, name: (tup, name))
    M, S, tup = history[2][1:4]
    Mnext, Snext = history[3][1:3]
    residuals = {
        "incoming_M_minus_0": tc.diffnorm(M, tc.scalar(0)),
        "incoming_Sigma_minus_I": tc.diffnorm(S, tc.scalar(1)),
        "history_M_next_minus_I": tc.diffnorm(Mnext, tc.scalar(1)),
        "history_Sigma_next_minus_0": tc.diffnorm(Snext, tc.scalar(0)),
        "selector_M_next_minus_I": tc.diffnorm(tc.phi_M(ins[2], M, tup), tc.scalar(1)),
        "selector_Sigma_next_minus_0": tc.diffnorm(tc.phi_S(ins[2], S, M), tc.scalar(0)),
        "NC_hold_M_instead_of_initialize": tc.diffnorm(M, tc.scalar(1)),
        "NC_hold_Sigma_instead_of_initialize": tc.diffnorm(S, tc.scalar(0)),
    }
    assert all(value == 0 for key, value in residuals.items() if not key.startswith("NC_"))
    assert all(value == 1 for key, value in residuals.items() if key.startswith("NC_"))
    return residuals


def main():
    out = {}
    for Nt, k in ((8, 8), (8, 7), (9, 8)):
        r = run(Nt, k)
        assert all(value == 0 for key, value in r.items() if key != "dims" and not key.startswith("NC_"))
        assert all(value > 0 for key, value in r.items() if key.startswith("NC_"))
        out[f"Nt={Nt},k={k}"] = r
        print(f"Nt={Nt} k={k}:", json.dumps(r), flush=True)
    out["LOAD_initialization_regression"] = load_initialization_regression()
    print("LOAD initialization regression:", json.dumps(out["LOAD_initialization_regression"]), flush=True)
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "operator_level_results.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote", os.path.basename(path))


if __name__ == "__main__":
    main()
