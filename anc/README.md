# Ancillary checks

These files support the written proofs. **The arbitrary-state lower bound rests on the written proof, not on computation.** No Lean formalization is included; one is planned.

Two independent checks were made of the construction. A refutation-first proof check by a model of another developer found no false step and no counterexample, and identified three repairs, each with a proof; the paper now applies all three. They are the Boolean variable for the projection `E` in the compiler's orthogonality context (Section 3), the explicit list of joint relations in Lemma 9.3, with commutators between different compulsory clocks and between conditional and fuel or time measurements bounded through the raw conjugated digits, and the linear translation bound (9.4) with the compulsory measurements fixed explicitly. Its two structural observations are Remark 9.4. Its two scripts are in `crosscheck/`. An independently written program, in the repository directory `verify/`, evaluates every relation on the finite models at N = 4, 6, 8; it is described below.

This directory contains the finite-model audit script, the conjugacy-gadget script, the two proof-check scripts, and their recorded outputs. The independent engine is kept with its own recorded output in `verify/` at the repository root.

## Finite models

`audit/check_models.py` is copied from the completed verification audit. It builds the Section 5 operators by basis arithmetic for a fixed one-counter program that halts exactly on even inputs. It checks every defining polynomial relation, the explicitly required commutations, exact domains, flat-state commutators, and the finite decoding and reset identities. It handles N=4,6,8 and reports the dimension against `2^(3N+k_N)` and each flat defect against `4^-N`.

It does not run a universal halting recognizer. It does not numerically prove a lower bound for all states, construct the complete compiled game, or establish convergence as N tends to infinity. Its general upper bounds are proved in the paper.

The script groups equal output rows before squaring coefficients. It computes periodic-coordinate rational entries with Python integers, then rounds once to float64. Therefore its final numeric entries are not interval certificates. The exact analytic bounds in the paper are independent of their rounding. `max_column_norm` means a column norm, not a general operator norm.

The original output is in `audit/recorded/`: `defects_N4.csv`, `defects_N6.csv`, `defects_N8.csv`, `model_results.json`, and `model_run.txt`. Every individual defect and its scale appear in those tables. The recorded checks number 390, 394 and 398. Their largest flat defect is `3*4^-N`. All required program equations have zero defect in these models.

Requirements: Python 3 and NumPy. In PowerShell, from the repository root:

```powershell
$env:OMP_NUM_THREADS='1'
$env:OPENBLAS_NUM_THREADS='1'
$env:MKL_NUM_THREADS='1'
$env:NUMEXPR_NUM_THREADS='1'
$env:PYTHONDONTWRITEBYTECODE='1'
python anc/audit/check_models.py --depths 4 6 8
```

New outputs are written beside the script, leaving `recorded/` intact. The exhaustive workspace implementation rejects N>8. Its original observed peak working set at N=8 was about 1.16 GB; no dense full-space matrices are allocated.

## Conjugacy gadgets

`gadgets/gadget_check.py` is the supplied finite-matrix test of the two conjugacy gadgets, with the original fixed random seed. It checks the involution domains, within-context commutations and products, and the auxiliary conjugacy identities. Its output is `gadgets/results.txt`.

```powershell
python anc/gadgets/gadget_check.py
```

These checks establish that the listed extension matrices pass the tested finite instances. They do not establish the converse algebraic implications, weighted soundness, or a uniform theorem; the paper proves those statements.

## Independent engine (`verify/`)

`verify/` holds a separately written monomial-operator engine. It was built from the construction without access to `audit/check_models.py` or its output, and it uses its own three-counter test program, with a non-halting input and halting inputs both inside and beyond the cutoffs of `K_N`. It stores each operator as a sum of weighted basis permutations, evaluates each relation column by column on the registers it touches, and computes both the operator norm, by exact block decomposition and dense singular values, and the flat (normalized Hilbert-Schmidt) norm. At N = 4 and 6 it re-evaluates every relation on the full space as a cross-check.

What it establishes, at N = 4, 6, 8:

- every defining relation of Sections 4 and 5, every required commutation and domain condition, and the identities (6.1) hold on the Section 7 models: 911, 915 and 919 relations;
- every relation stated to be exact has defect zero; the periodic series (7.6) are also checked with integer arithmetic;
- the same ten relations as in `audit/` have nonzero defects; the nine that do not depend on the program have the same flat ratios, and the conditional-tail ratio agrees at N = 4 and 8, where the two test programs have the same `K_N`;
- the operator-norm defects are `3*4^-N` (clocks), `sqrt(2)*4^-N` (guarded increments), `4^-N` (carry step) and at most `0.012*4^-N` for (5.15), within the bound of Theorem 7.1;
- the dimension is exactly `2^(3N+k_N)`, and the workspace adds no tensor factor;
- the readings fixed by the text are forced: reversing the digit rotation, the address bit order, or the time or fuel indexing breaks a stated relation, and removing the dressing (7.8) breaks the guarded increment (4.7) for `V`.

It also tests the identities of Section 3 on random instances (`verify/compiler_checks.py`) and the window counts (7.3)-(7.4) up to N = 24 (`verify/dims_study.py`). It does not test the arbitrary-state lower bound, the tracial forcing argument, or the compiled game itself.

Requirements: Python 3, NumPy and SciPy. From `verify/`:

```powershell
$env:OMP_NUM_THREADS='1'
$env:OPENBLAS_NUM_THREADS='1'
python -u run_e2.py 8
python -u run_e2.py 4 6 --full 4 6 --ablate 4 6
```

Recorded output is in `verify/out/`: one table per N (`table_N4.md`, `table_N6.md`, `table_N8.md`, with `results_N*.json`), the ablations, the compiler checks, the window study and the run logs. The N = 8 run took about 141 s with a peak working set of about 656 MB.

Both finite-model programs label relations by the numbering of the construction text they were written from. The labels correspond to the paper as follows.

| Label | Paper |
|---|---|
| (3) | clock relations (4.1), for each of the three clocks |
| (4) | guarded increments (4.7) for `V` and `U` |
| (5), (6) | carry relations (5.1)-(5.2); (6) is the last equation of (5.2) |
| (7), (8) | address decoding (5.3), (5.4) |
| (10), (12) | the forced identities (6.1) |
| (11) | reset (5.6) |
| (13), (14), (15), (16) | zero test (5.8), initialization (5.9), transition (5.10), halt flag (5.11) |
| Section 2.4 | control projections of Section 5.3 |
| Section 2.5, 2.5a-c, Required commutation | commutation list of Section 5.4 and the commuting clock families of Section 5.1 |
| 4 (engine group) | commutations of `B`, `C`, `Q`, `Y` stated after (5.15) |
| (21), (22), (23), (24) | conditional clock (5.12), (5.13), (5.14), (5.15) |
| estimate (32) | (7.7) |
| (25), (29), (33) | Theorem 7.1, (7.4), (7.8) |

## Proof-check scripts (`crosscheck/`)

These are the two numerical scripts of the independent proof check, copied unchanged. Their output is `crosscheck/results.txt`. Their comments and output call the selector identity (1) and the orthogonality bound (2); these are (3.3) and (3.6) in the paper. `R1` in `r1.py` names the repair of the orthogonality context.

- `crosscheck/gadgets.py` checks both conjugacy gadgets on random involutions, the selector identities (3.3), and the bound (3.6) on random projection pairs, where the ratio `||F-F'||^2 / (2||EF||^2)` reaches 1, so the bound is tight.
- `crosscheck/r1.py` shows why the compiler's orthogonality context uses its own variable for `E`: for a nearly satisfied source equation with `||EF||` about `1.5e-3`, the repaired projection `F'` has commutator about 2 with a selector variable `X_i` (Frobenius norms), so `{E, F', I-E-F'}` would not be a legal answer to a context listing the `X_i`.

```powershell
python anc/crosscheck/gadgets.py
python anc/crosscheck/r1.py
```

## Licenses

SHA256SUMS records the archived code and data in this directory.

Paper, documentation and recorded outputs: CC BY 4.0. Scripts: MIT or Apache 2.0, at the user's option. See the root RIGHTS.md and license files.
