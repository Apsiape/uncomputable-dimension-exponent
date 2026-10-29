# Ancillary checks

These files support the written proofs. **The arbitrary-state lower bound rests on the written proof, not on computation.** A Lean formalization of Sections 2--10 is in progress and not complete; no completed formal verification is included.

The compiler uses a Boolean variable for the projection `E` in its orthogonality context (Section 3), the joint commutation list of Lemma 9.3 and the linear translation bound (9.4). The numerical checks in `crosscheck/` test the gadgets and the orthogonality context. The independently implemented engine in `verify/` evaluates the finite models at N = 4, 6, 8; its scope is described below.

This directory contains the finite-model audit script, the conjugacy-gadget script, the two proof-check scripts, and their recorded outputs. The independent engine is kept with its own recorded output in `verify/` at the repository root.

## Finite models

`audit/check_models.py` builds the Section 5 operators by basis arithmetic for a fixed one-counter program that halts exactly on even inputs. It checks every defining polynomial relation, the explicitly required commutations, exact domains, flat-state commutators, and the finite decoding and reset identities. It handles N=4,6,8 and reports the dimension against `2^(3N+k_N)` and each flat defect against `4^-N`.

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

Recorded output is in `verify/out/`: one table per N (`table_N4.md`, `table_N6.md`, `table_N8.md`, with `results_N*.json`), the ablations, the compiler checks, the window study and the run logs. The N = 8 run took about 141 s with a peak working set of about 656 MB. The combined `run_e2.py 4 6 --full 4 6 --ablate 4 6` run has a larger previously observed peak of about 1.31 GB; a monitored process-tree run reached 1.36 GB (1,360,596,992 bytes). Run it separately, with one numerical-library thread and a monitored process-tree ceiling below 1.5 GB.

`verify/SHA256SUMS` covers the independent engine's sources and recorded outputs. `paper/prepare_assets.py` refreshes that manifest after intentional reruns.

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

These two numerical scripts test the compiler gadgets and orthogonality context. Their output is `crosscheck/results.txt`. Their comments and output call the selector identity (1) and the orthogonality bound (2); these are (3.3) and (3.6) in the paper.

- `crosscheck/gadgets.py` checks both conjugacy gadgets on random involutions, the selector identities (3.3), and the bound (3.6) on random projection pairs, where the ratio `||F-F'||^2 / (2||EF||^2)` reaches 1, so the bound is tight.
- `crosscheck/orthogonality_context.py` shows why the compiler's orthogonality context uses its own variable for `E`: for a nearly satisfied source equation with `||EF||` about `1.5e-3`, the repaired projection `F'` has commutator about 2 with a selector variable `X_i` (Frobenius norms), so `{E, F', I-E-F'}` would not be a legal answer to a context listing the `X_i`.

```powershell
python anc/crosscheck/gadgets.py
python anc/crosscheck/orthogonality_context.py
```

## Licenses

SHA256SUMS records the archived code and the original outputs under each `recorded/` directory. Reruns write new outputs beside the scripts; those are not covered by the manifest.

Paper, documentation and recorded outputs: CC BY 4.0. Scripts: MIT or Apache 2.0, at the user's option. See the root RIGHTS.md and license files.

## Reader and operational sections: reader, window, compression and Jensen (`spectrum/`)

`spectrum/numerical_attack.py` tests the finite reader models and weighted moments of Sections 11 and 14. Recorded results and the run log are in `spectrum/recorded/`. Running it writes new results beside the script. Recorded `threadpool_info` identifies libraries by site-packages-relative paths.

It establishes the following **finite numerical observations**, with fixed seeds, rather than universal theorems:

- 24 honest reader models at N=2,4,6 and eight rational thresholds (including 0 and 1): reset, initialization, transitions, zero-tail reads, halt inclusion, optional slot noncollision, dressing and operator residuals on their nontrivial kernels. The largest residual is `3*4^-N`; the logical full dimension reaches `2^25` without a dense allocation. The test programs implement constant rational thresholds, not an arbitrary universal counter computation.
- Dyadic-grid counts and arbitrary moving/cyclic window counts for the radical-inverse mask, including adversarial bit-order choices. This tests the finite count; the uniform discrepancy estimate is proved in the paper.
- Compression and domain repair for weighted tuples, finite word moments and direct-sum trace weights. These numerical moment comparisons do not establish the limiting trace-space identity or an effective bound on the compressed dimension.
- 3,000 noncommuting-state Jensen tests of the residual-power inequality for both parities. The proof uses scalar spectral-measure Jensen; numerics are not its justification.

Run from the repository root after setting all the thread variables above and `PYTHONDONTWRITEBYTECODE=1`:

```powershell
python -u anc/spectrum/numerical_attack.py
```

The recorded run contains 32,400 finite word tests. Inspect the structured output for the exact enumeration, tolerances, resource usage and domain repairs. These checks do not test the complete compiled game or prove a lower bound for arbitrary states.

## Reader and operational sections: extraction protocol (`extraction/`)

The six Python files test Lemma 12.1 and Proposition 12.2. Script comments refer to the paper's own numbering. The continuity parameter in `protocol_check.py` is a purification-vector upper bound on output half trace distance. Recorded logs are in `extraction/recorded/`. They compute coherent information of the **actual output**, with inaccessible environment and original systems traced, random targets averaged, flags dephased and active qubits kept coherent. They do not compute distillable entanglement itself.

| Script | Exact scope |
|---|---|
| `stage_inequality.py` | Arbitrary and near-structured one-stage matrix instances, plus bounded search, of the stage isometry inequality. |
| `protocol_check.py` | Exact and perturbed binary/ternary protocols through four stages, with mixed states and noncommuting triangular controls; checks history aggregates, vector error `7*m^3*eta`, mean activation, continuity and the stated extraction bound. |
| `tiny_perturbation.py` | Uses the protocol engine at perturbations where the lower bound is positive, avoiding a vacuous numerical test. |
| `adversarial_search.py` | Complete bounded hill-climb of nine normalized error ratios at m=2 and m=3, with four masks and two perturbation sizes. It does not certify a global maximum. |
| `adversarial_m3.py` | Lighter three-ternary-stage adversarial search, using the preceding engine. |
| `repair_check.py` | One-sided projection-inclusion repair, containment and adjoint-transfer inequality on 4,000 finite random instances. |

There are six Python files (the full engine and five runners/checks). The protocol script accepts a seed; the recorded full run uses 7, the adversarial run 11 and the lighter three-stage run 13. For example:

The protocol evaluator forms the principal blocks retained by flag dephasing and sums their entropies. The search evaluator can compute just its requested objective, omitting unused coherent-information or history calculations. The default evaluator still returns all nine ratios; the seeds, masks, perturbation sizes and iteration counts are unchanged.

```powershell
python -u anc/extraction/protocol_check.py 7
python -u anc/extraction/tiny_perturbation.py
python -u anc/extraction/repair_check.py
```

Run each script as a separate process. The scripts inherit single-thread settings. The paper uses the proved sharper mean error `m*(m-1)*eta/2` and vector error `7*m^3*eta`; the original protocol tests retain the looser mean bound and final `20*m^3*eta` allowance while separately testing the sharper vector bound. No numerical observation replaces the extraction proof, actual-state bridge, hashing theorem, or heat theorem.


## Reader and operational sections: complementary gate (`gate/`)

`gate/toy_gate.py` tests packing, programmed histories and complementary finite models. Its recorded `toy-results.json` is in `gate/recorded/`; a rerun writes `gate/toy-results.json`, which is excluded from SHA256SUMS. These tests check **the new matrix algebra and finite histories on known-answer toy games, not the MIP* games themselves**.

- Packed projection presentations and signed right-multiplication/accumulator instructions for 3-colouring of K3 (dimension 9, 49 CHECKs), two noncommuting binary bases with only diagonal question pairs tested (dimension 8, 11 CHECKs), and a flagged bad K4 colouring (dimension 12, 77 CHECKs). Unflagging the bad colouring gives two nonzero CHECKs, maximum residual 1.
- The mean-of-two-unitaries contraction representation, all distinct fuel reset periods and cyclic time boundaries: 16,893 transitions and 35 cyclic boundaries; all required initialized-history residuals vanish within the stated tolerances. The common data factor has dimension 72 and satisfies all packed equations.
- Decoder and reset recursions, 69,904 fuel/time basis points, and 384 address/optional-slot basis points at N=6. The boundary residual is sqrt(2)*4^-6. Physical and dressing-gauge slot outputs are checked separately.
- All complementary masks at even N=2 through 14: 254 masks and 2,396,744 mask/start cases. The proved window bound passes. Reversing the address-bit convention is a negative control.
- A cost-only slow-admission example, without allocating its hypothetical large witness.

The script does not compile a universal counter machine, run the MIP*=RE reduction, enumerate actual halting-game perfect certificates, prove an infinite limit, or construct the full BCS game. Floating-point polar decompositions are numerical checks, not exact certificates. The script has an internal 2 GB assertion; the documented runs use an external 1.4 GB process limit.

Run with Python 3 and NumPy, after setting all thread variables shown above to one:

```powershell
python -B anc/gate/toy_gate.py
```

Each numerical check uses one numerical-library thread; monitored process trees remain below 1.5 GB.


### Two-family construction checks

The script `gate/toy_gate.py` uses one projection family for both players; its history, reset and window tests are independent of that choice. The two-family presentation of Section 15.1 is tested by the independently written scripts in `gate/crosscheck/`; five source files and four recorded logs are archived there. The recorded address log uses the displayed equation labels with its own column padding. Requirements: Python 3, NumPy and SciPy. Run each command separately from the repository root, with the thread settings above:

```powershell
python -B anc/gate/crosscheck/check_packing_transducer.py
python -B anc/gate/crosscheck/check_histories.py
python -B anc/gate/crosscheck/check_address_structure.py
python -B anc/gate/crosscheck/check_window_count.py
```

The packing check includes separate Alice and Bob families: K3 colouring has 18 generators and packed dimension 18; the magic-square witness has 42 generators and packed dimension 168. It checks the reduced-state eigenspace argument on a nonuniform Schmidt state and an anti-synchronous PCC example that has no single-family model. Negative controls detect nonzero losing products. The history check covers 53,248 points, including reset and cyclic boundaries. The sparse address check tests dimensions 4,096, 16,384 and 8,192, and the window check exhausts even depths through 22. These checks concern known-answer toys, not the actual MIP* games, the universal machine compilation, the asymptotic lower bounds or the full BCS game.

`extraction/recorded/stage_inequality.log` records 3,000 arbitrary instances, 1,000 structured instances and the bounded hill-climb. The complete larger search and the lighter three-stage search are recorded separately.


### Notation in the reader and extraction programs

The programs cite the paper's own sections and equations. `M` and `T` in the numerical implementation denote the monomial and accumulator registers `M` and Sigma of (15.3)–(15.5). The `L_N` data-dimension label in the numerical variables denotes ell_N in Lemma 15.6. Output keys for bounded searches are numerical diagnostics, not additional theorem hypotheses. The structured records contain the tested numerical values and inequalities.

The files `spectrum/numerical_results.json` and `gate/toy-results.json` are generated only by reruns and are not included in this release or its manifest; the archived results in `recorded/` are included and hashed. The spectrum runner also shortens newly reported library paths, so rerunning it does not expose machine-specific directories.

## Stop-or-continue section: stop-or-continue classification (`classification/`)

Four independently developed finite checks accompany Section 16. They test finite histories and the new matrix algebra on known-answer toy games, **not the MIP* games themselves**. Scalar arithmetic is interpreted at instruction level; a universal counter compiler and the final BCS compiler are not executed. None of these tests proves a limiting trace statement or an arbitrary-state lower bound.

| Script | Scope and recorded output |
|---|---|
| `toy_attack.py` | Oscillating rational sequence tending to 11/20; two-family packed edge/odd-cycle colouring toys; finite initialized address/fuel/time blocks; dyadic STOP counters, REJECT and CHECK, one LOAD per gate, constant flagged data, register transitions and two-unitary representations; complementary windows and negative controls. Outputs `toy-results.json` and `upper-checkpoint.json`. |
| `matrix_interface.py` | An 80-dimensional direct matrix model with data that do not commute with time increment; shifted variables reduce the initialized corner and loaded tuples remain fixed; the stop-sector identity is displayed on the survivors of this hand-built instance, where it holds by construction. Dropping coordinate commutation is a negative control. Output `matrix-interface-results.json`. |
| `toy_classification.py` | Two nonmonotone convergent rational sequences, fixed dyadic thresholds and tail certificates; packed mutually unbiased projections and edge-colouring witnesses, an impossible odd-cycle control, initialized block histories, STOP/continue, LOAD initialization of M to I and Sigma to zero on its outgoing edge, register and zero-test relations; window budgets and negative controls. Output `toy_results.json`. These projection toys do not all require the general two-family input reduction. |
| `operator_level.py` | Imports the preceding engine and builds genuine sparse cyclic-time operators for three time/fuel configurations. Tests the holding equation, register transitions including LOAD initialization of M to I and Sigma to zero, counter update, zero test, CHECK and declared commutations, with negative controls for omitting the LOAD factor and imposing time invariance. A synthetic LOAD with incoming M = 0 and Sigma = I checks both the instruction history and polynomial selectors against outgoing M = I and Sigma = 0; holding either incoming register instead gives residual 1. Output `operator_level_results.json`. |

Run these commands separately from the repository root, with every numerical-library thread variable above set to one and `PYTHONDONTWRITEBYTECODE=1`:

```powershell
python -B anc/classification/toy_attack.py
python -B anc/classification/matrix_interface.py
python -B anc/classification/toy_classification.py
python -B anc/classification/operator_level.py
```

Recorded outputs are in `classification/recorded/`: the five JSON files named above, plus `toy.log`, `matrix-interface.log`, `toy_run.log` and `operator_level.log`. The LOAD register equation initializes outgoing M = I and Sigma = 0 in `toy_classification.py` and `operator_level.py`. The nonvacuous synthetic LOAD has incoming M = 0 and Sigma = I; holding either incoming register gives residual 1. The keys `holding`, `counter_on_survivors` and `stop_sector` identify the corresponding Section-16 identities. Negative-control values are expected to be nonzero. Reruns write beside the scripts; their five generated JSON files are excluded from SHA256SUMS. Archived records and sources remain covered by the manifest.

The nonuniform selection of safe thresholds and the slow diagonal witness budget are existence arguments in the proof. Toy tail certificates use known convergent sequences and do not compute a convergence modulus for a general limit name. Floating-point polar decompositions check the contraction representation numerically; its exact existence is proved in the text.


## Power-scale sections (`power/`)

All seven scripts were rerun sequentially, with one numerical-library thread and a monitored combined-process memory ceiling below 1.5 GB. They require Python 3 and NumPy; they write current JSON beside the scripts. The `recorded/` folders retain this run's JSON and console output and are covered by SHA256SUMS. Run each script from its folder, or use `python anc/power/run_checks.py` from the repository root.

| Script under `power/` | Finite scope | JSON output |
|---|---|---|
| `moments/attack_moments_lamps.py` | Exact binary code enumeration, finite full-Fock CAR and affine actions; supports the moment construction without proving an all-depth result numerically | `moments-lamps-results.json` |
| `moments/attack_clock.py` | Rebuilds coordinate links, regions, holonomy, protected affine operations and sparse representation checks, including M=48; never materializes the huge full affine register | `clock-results.json` |
| `stopped/check_stopped_calibrator.py` | Finite unguarded clock, reset and stopped scalar histories at dyadic and ordinary inputs | `calibrator-checks.json` |
| `rotation/check_rotation.py` | Finite isolated-root rotation, carries, reset interruptions, domains and scalar power envelope | `numerics.json` |
| `stack/adversarial_checks.py` | Independent small noncommuting matrices, stopped columns, root/carry and ceiling diagnostics; arrays at most order eight or small diagonal histories | `adversarial-results.json` |
| `claims/check_scaled_machine.py` | Full finite scalar program/calibrator histories, ordered polynomial identities, weighted bad tests, scheduler arithmetic and mixed/chained scalar envelopes | `numerics.json` |
| `validation/independent_checks.py` | Independently specified exact-rational scalar histories, weighted noncommuting finite-window counter/test perturbations, arbitrary-column completeness and supplied-script identity | `independent-results.json` |

The copy of `check_scaled_machine.py` in `validation/` is retained for the independent script's byte comparison, not run as a separate check. Rotation and constant-multiplier scripts preserve reproducible explicit examples; the general proof uses the scaled program route. The scheduler arithmetic test does not compile a universal counter program, and the weighted finite-window perturbations are not complete clock/compiler strategies. No finite test is claimed to prove a density limit, uniform stability, an asymptotic lower bound or a spectrum theorem.


## Precision profiles (`profiles/`)

Run `python -B anc/profiles/run_checks.py` for three sequential finite suites. The carry checker uses exact rational diagonal/permutation storage for overflow, reset cylinders, Lipschitz constants and cost comparison. The hold checker uses twelve million pulses, exact calibration histories for thirteen inputs, and profile/moment-band accounting; it simulates instruction costs without emitting a full universal counter table. The independent suite imports neither supplied checker and tests overflow-state deletion, shared noncommuting inputs, greedy tracking, endpoint rescaling, independent hold accounting and a diagonal decoder. NumPy is required; numerical thread counts are one. No finite test proves asymptotic endpoints, the weighted operator theorem or universal non-realizability.

Each script writes a JSON result and the runner writes logs beside the scripts. `recorded/` contains archived JSON/logs covered by SHA256SUMS; generated adjacent files are excluded. `--record` intentionally refreshes those archived copies, after which `paper/prepare_assets.py` refreshes the manifest.


## Ceiling, pairwise and group interfaces (`frontiers/`)

Run `python -B anc/frontiers/run_checks.py` for four sequential standard-library/NumPy suites. The two supplied programs are `check_sharp_ceiling.py` and `check_hash_barrier.py`. The former checks finite clock defects, exact scalar calibrator residuals, sharp-versus-smooth penalties and stopped multipliers. The latter exhaustively evaluates affine collisions and the pairwise dimension bound; its cubic exhaustive loops can take substantially longer than the other suites. The independently specified `independent_ceiling_checks.py` tests weighted sequential POVM positivity, normalization and effect-approximation ratios, noncommuting complete columns, actual-failure neighborhoods, classical hash flags and exact stopped histories. `independent_groups_checks.py` checks sixteen finite initialized counter programs, exact single-visit trace weights, the seventeen-state squaring loop through four marker visits and matrix canonical-trace normalization. The group test includes 595,050 elementary marker instructions after initialization. NumPy is required, and all numerical thread counts are one.

Each suite writes JSON and console logs; `recorded/` archives this run's outputs and is covered by SHA256SUMS. `--record` refreshes archives intentionally, after which `paper/prepare_assets.py` refreshes hashes. Generated adjacent JSON/logs are excluded from the manifest. These are finite interface checks; no run proves a hierarchy separation, an asymptotic power law, universal trace rigidity, irrationality, or a fixed-game usable separation.
