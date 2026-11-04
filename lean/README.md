# E2 halting-game core

Theorem 1.2 of v4.0.0 (label thm:main, eq. (1.4)) is Lean-checked, conditional on the explicit hypothesis TarskiDecision (Basu-Pollack-Roy, Theorem 13.13). It proves exactly

```lean
E2.challenge (hT : E2.RealArithmetic.TarskiDecision) : E2.MainStatement
```

There exists a finite rational Boolean constraint-system game with quantum value one, no finite-dimensional perfect strategy, dimension exponent `betaK = (3 + thetaK) / 4`, exponent of halting degree, and no eventual computable error envelope for its dyadic logarithmic slopes. Here K is {e : Mathlib partial-recursive code e halts on input 0}; other acceptable numberings are not separately checked. Precision ranges over every positive real, and strategies allow arbitrary mixed states and POVMs. The checked theorem is conditional: the published decision algorithm is not implemented or proved inside this package.

This package does not verify Theorem 1.1, the v4 dimension classification, usable-entanglement classification, or power/profile extensions. See FIDELITY.md.

## Sole published premise

S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition, Springer, 2006, Theorem 13.13, “Existential Theory of the Reals”, printed page 516 (PDF page 520, zero-based index 519). The exact qualitative clause is:

> There exists an algorithm to decide the truth of the sentence

[Primary text, page 516](https://www.cs.umd.edu/~gasarch/COURSES/752/S25/slides/AlgorithmsInRealAlgGeom.pdf#page=520); [publisher chapter](https://doi.org/10.1007/3-540-33099-2_14).

The input described there is a finite existential sentence over a real closed field with a quantifier-free polynomial matrix. We specialize to real numbers and rational coefficients and use the qualitative decision conclusion. No complexity bound is assumed. The explicit Lean premise is `TarskiDecision := ComputablePred OrderedRingTruth`. Syntax uses finite rational sums of products, equality/nonnegativity atoms, literal negation, and a finite disjunction of finite conjunctions. `ordered_truth_finite` verifies that the natural-indexed valuations quantify only finitely many occurring coordinates. This premise mentions no game or strategy.

`propext`, `Classical.choice`, and `Quot.sound` are the permitted foundational axioms. `hT` is a theorem argument, not an extra axiom. Every root printed by Audit.lean uses only those three foundational axioms. The challenge placeholder intentionally uses `sorry`; it specifies the trusted target and is never imported by Solution.lean. Comparator checks the solution proof and recursively compares its target definitions. That placeholder is separate from the 42 historical admissions below.

## Contents and trust boundary

* `Statement.lean` freezes MainStatement; `E2/Game.lean`, `E2/Computability.lean`, `E2/EffectiveCoding.lean`, and `E2/RealArithmetic.lean` supply its transparent game, computability, rational coding, and ordered-ring definitions. The five-file freeze is `STATEMENT-SHA256.json`; FROZEN-STATEMENT.md displays the definitions together.
* `Challenge.lean` is the comparator target; `Solution.lean` contains the original challenge proof with MainStatement moved to Statement.lean. Blueprint.lean imports Solution rather than the placeholder. No mathematical statement or proof is strengthened or weakened by this packaging.
* `Audit.lean` prints axioms for the main result, blueprint, analytic conclusions, halting degree, effective dimension/slopes, and exact feasibility compiler.
* The complete import closure contains 317 project modules (309 E2, 3 Companion, and 5 root modules, including the replaced challenge module) and 93 QIT source modules. Only imported historical admission files are included. V2 and V3 sources are excluded.
* Mathlib is not vendored. Lean is pinned to 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its eight dependency revisions are fixed by lake-manifest.json. A manifest pin suffices; there is no source-level mathematical Mathlib patch required by the release.
* QIT sources come from QuAIR/Lean-QIT at `8a931d4bda61ba503cfc0728704cfef5dedf2cff`, with the existing ContinuousENorm parent-name adaptation in States/TraceNorm/Audenaert.lean and explicit LocalExtr.Basic import in Information/BinaryHypothesisTest/Classical.lean. They are supplied as local modules because the existing port targets the pinned Mathlib version. Their Apache-2.0 license is LICENSE-QIT. SOURCE-PROVENANCE.json records per-file hashes. Companion modules are the three local source dependencies already used by the checked core.

## Build and compare

Install the pinned Lean toolchain. From this directory, obtain the pinned dependency sources and Mathlib cache with `lake exe cache get`. For a fully sequential source build using existing dependency caches, run:

```text
python verify.py --build-only
```

The helper builds one module at a time with `LEAN_NUM_THREADS=1`, `-j1 -M6144`, and a 10,000,000,000-byte Windows Job Object cap (or a per-process address-space limit on Linux). It builds all supplied local dependencies; no retained local object is needed for this command. Python 3.10+ is required. Dependency cache installation is a prerequisite and is not part of the measured replay.

On Linux with bubblewrap installed and usable, the documented comparator command is:

```text
lake comparator --config comparator.json
```

This is leanprover/comparator's maintained successor bundled with Lean 4.35.0; the archived standalone comparator documents this migration. JSON fields are challenge_module, solution_module, theorem_names, and permitted_axioms. There are no definition holes. [Comparator documentation](https://github.com/leanprover/comparator); [pinned implementation](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/CLI/Check.lean).

For one command after dependency-cache setup, including a sequential source build, selected proof export, comparison and both replays:

```text
python verify.py
```

The helper uses comparator's two pre-export options. On Windows, Linux namespaces are unavailable, so it explicitly uses the native trusted-export mode and reports that reduced isolation. This establishes statement equality, allowed axioms and kernel acceptance for the generated exports; it is not an adversarial sandbox validation. The ordinary sandboxed command remains the recommended independent Linux check. Bundled leanchecker is a separate kernel replay process; nanoda is an independent Rust kernel implementation. See REPLAY.md for the run actually performed, exact hashes, times, and limitations.

The paper's other imported inputs (the DM-precision theorem, Holevo's theorem, counter-machine universality, and Shoenfield's limit lemma) are not hypotheses or axioms of the Lean statement.

## What remains unverified

The original project has 42 admissions: five imported core side results, 24 V2 and 13 V3 results. They are not dependencies of the audited headline proof terms. Imported modules may contain an unused admitted theorem; kernel export is rooted in the 14 audited declarations and does not export all unused declarations. There is no claim that every declaration in an imported source file is proved. No V2/V3, general classification, usable-entanglement, heat or profile/power theorem is certified by this release.

| Admitted declaration | Original project file | Shipped source |
|---|---|---|
| `E2.finite_increment` | `E2/Clock.lean` | included |
| `E2.guard_mass` | `E2/Clock.lean` | included |
| `E2.guard_remove` | `E2/Clock.lean` | included |
| `E2.clock_profile` | `E2/ClockProfile.lean` | included |
| `E2.matched_comparison` | `E2/Transfer.lean` | included |
| `E2.V2.gate_packing` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.gate_testing` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.gate_flag` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.gate_finite` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.gate_resources` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.bcs_exponent_arithmetic` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.rational_exponent_arithmetic` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.beyond_left_ce` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.gate_trace_gap` | `E2/V2/Gate.lean` | excluded |
| `E2.V2.gate_witnesses` | `E2/V2/GateSource.lean` | excluded |
| `E2.V2.testing_program_exists` | `E2/V2/GateSource.lean` | excluded |
| `E2.V2.exact_trace_barrier` | `E2/V2/Limits.lean` | excluded |
| `E2.V2.moment_compression` | `E2/V2/Limits.lean` | excluded |
| `E2.V2.weighted_limits` | `E2/V2/Limits.lean` | excluded |
| `E2.V2.approximable_arithmetic` | `E2/V2/Limits.lean` | excluded |
| `E2.V2.reader_program_exists` | `E2/V2/ReaderSource.lean` | excluded |
| `E2.V2.reader_forcing` | `E2/V2/Realization.lean` | excluded |
| `E2.V2.reader_finite` | `E2/V2/Realization.lean` | excluded |
| `E2.V2.realization_parameters` | `E2/V2/Realization.lean` | excluded |
| `E2.V2.accumulation` | `E2/V2/Realization.lean` | excluded |
| `E2.V2.positive_parameter_choice` | `E2/V2/Realization.lean` | excluded |
| `E2.V2.inactive_extraction` | `E2/V2/Usable.lean` | excluded |
| `E2.V2.actual_state_bridge` | `E2/V2/Usable.lean` | excluded |
| `E2.V2.usable_parameters` | `E2/V2/Usable.lean` | excluded |
| `E2.V3.semicomputable_delta` | `E2/V3/Arithmetic.lean` | excluded |
| `E2.V3.limit_flag_16_1` | `E2/V3/Classification.lean` | excluded |
| `E2.V3.limit_flag_lower_16_4` | `E2/V3/Classification.lean` | excluded |
| `E2.V3.limit_finite_16_5` | `E2/V3/Classification.lean` | excluded |
| `E2.V3.limit_resources_16_6` | `E2/V3/Classification.lean` | excluded |
| `E2.V3.positive_parameters` | `E2/V3/Classification.lean` | excluded |
| `E2.V3.rational_dyadic_computable` | `E2/V3/Classification.lean` | excluded |
| `E2.V3.loaded_tuple_16_2` | `E2/V3/CornerStatements.lean` | excluded |
| `E2.V3.stop_sectors_16_3` | `E2/V3/CornerStatements.lean` | excluded |
| `E2.V3.continuation_ce` | `E2/V3/DynamicSource.lean` | excluded |
| `E2.V3.machine_exists` | `E2/V3/Program.lean` | excluded |
| `E2.V3.trace_range_14_5` | `E2/V3/TraceRange.lean` | excluded |
| `E2.V3.budget_obstruction_14_6` | `E2/V3/TraceRange.lean` | excluded |

## Resources and reproducibility

The verification in REPLAY.md reuses hash-recorded compiled dependency artifacts, freshly compiles the 15 affected modules (including all five package entry modules), retaining 395 unchanged modules by their prior source/object hashes, then exports and independently replays the reachable headline proofs. It does not claim a fresh source rebuild of the entire project or Mathlib. The supplied `python verify.py` command provides a fresh local-source build path for another machine. Source-only distribution omits all `.lake` caches, machine paths, downloaded toolchains and large proof exports; evidence logs and numeric resource summaries are retained. Source and archive sizes and actual elapsed times are recorded in REPLAY.md and the turn report. These are computability proofs, with no practical runtime bound for the mathematical dimension-search algorithm.
