# Repaired v4.1.0 package verification (3 November 2026)

The repaired package was checked after the Blueprint and RealArithmetic documentation changes. Theorem 1.2 of v4.0.0 (label thm:main, eq. (1.4)) is Lean-checked conditional on the explicit hypothesis TarskiDecision (Basu-Pollack-Roy, Theorem 13.13, printed p. 516). No mathematical Lean statement or proof was changed.

All 15 affected modules were freshly rebuilt, including all five package entry modules and every local import dependent of E2.RealArithmetic. The other 395 modules have source and object hashes checked against the prior recorded staging evidence. Fresh local compilation took 253.748 seconds. Every compiler used LEAN_NUM_THREADS=1, -j1 -M6144, maxRecDepth=100000, maxHeartbeats=4000000 and autoImplicit=false. The driver and its children ran under a 10,000,000,000-byte Windows Job Object commit cap. The heavy processes ran sequentially. No new peak-RSS measurement is claimed.

Audit.lean freshly printed 14 roots; every root has exactly [propext, Classical.choice, Quot.sound], and no sorryAx. The explicit theorem parameter remains TarskiDecision. New exports were generated from the repaired-source builds. The solution export has 569395278 bytes and SHA-256 `dd97c3a17ac971c80d63ea72dd36d76f5dfa56b9c7a657634b7d80fc92cca83c`; the target export has 71279270 bytes and SHA-256 `7f53b1c7363a2d4a4fc4c586df6890e4b9940b780be9ed598ee216bc84ba261c`. Both exports are byte-identical by hash to the prior staging exports, as expected for documentation-only changes. The target placeholder is never imported by Solution.

The comparator (native trusted-export mode), standalone leanchecker and independent nanoda all exited 0. Comparator ended `Your solution is okay!`. Leanchecker and nanoda produced empty successful logs. Both kernel replays consumed the same freshly generated solution export. Exact portable commands, source/object hashes, build plan, axiom output and logs are in evidence/v4.1/. Tool binaries were checked against evidence/tools.json. Nanoda's private copy changes only the PE stack reserve to 128 MiB; the adjustment hashes are recorded in evidence/v4.1/nanoda-stack-adjustment.json.

The actual comparator command, with paths relative to the verification area, is:

```text
lake comparator --config comparator.json --challenge-from-export .replay/challenge.ndjson --solution-from-export .replay/solution.ndjson --inadvisably-no-sandbox
```

This Windows check establishes target-definition equality, permitted axioms and kernel acceptance for trusted local exports. It does not provide hostile-code isolation. No new Linux namespace sandbox run was made; the historical unsupported-platform failure remains below. Mathlib and all unchanged local modules were not freshly rebuilt. Only the selected reachable proof graph is replayed, so unused side admissions remain outside this check. The one-command full-local-source path after installing pinned dependencies remains `python verify.py`.

| Step | Exit | Seconds |
|---|---:|---:|
| build-E2.RealArithmetic | 0 | 12.5 |
| build-Statement | 0 | 14.006 |
| build-Challenge | 0 | 12.702 |
| build-E2.RealArithmeticComplex | 0 | 14.306 |
| build-E2.RealArithmeticMatrix | 0 | 14.614 |
| build-E2.FeasibilitySentence | 0 | 16.361 |
| build-E2.FeasibilityRaw | 0 | 14.394 |
| build-E2.FeasibilityComputation | 0 | 25.361 |
| build-E2.EffectiveDyadic | 0 | 17.179 |
| build-E2.Effective | 0 | 16.773 |
| build-Solution | 0 | 16.273 |
| build-Blueprint | 0 | 15.456 |
| build-E2.FeasibilityUniform | 0 | 34.612 |
| build-E2.RealArithmeticFinite | 0 | 13.288 |
| build-Audit | 0 | 15.923 |
| export-challenge | 0 | 8.654 |
| export-solution | 0 | 40.761 |
| comparator | 0 | 238.017 |
| leanchecker | 0 | 218.2 |
| nanoda | 0 | 125.617 |

# Original staging verification (historical)

Pinned Lean/lake/leanchecker: 4.35.0, source commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Exporter and NDJSON format: 3.1.0. The independent Rust nanoda kernel is the binary bundled with that toolchain, whose upstream build pins nanoda_lib at 3a2407216ee84a75f9e1aead6803d0578be06ae7. Exact binary digests and the pinned upstream source URL are in evidence/tools.json.

The nanoda executable is the same checked binary used for the prior explicit-game release, with only PE32+ SizeOfStackReserve changed from 1 MiB to 128 MiB. Initial stack commit is still 4096 bytes. The original and adjusted digests, offset and exact change are recorded; no executable code was modified. This is a resource adjustment, not a kernel change.

The frozen statement, trusted target, solution, blueprint and audit were freshly compiled, with successful final compile time 149.609 seconds. 405 other project/QIT modules were retained by hash with unchanged mathematical source; one documentation-only reference was updated in RealArithmetic. This run does not claim a fresh source rebuild of those retained modules, the Mathlib dependency caches, or the entire original project. The supplied helper's whole-source build path was dependency-planned and syntax-checked, but the full 410-module source rebuild was not executed in this run. The actual entry-point compilation and both whole-export replays passed.

The audit contains 14 roots. Every one prints exactly the three standard axioms and no sorryAx. The target has exactly one explicit mathematical parameter, TarskiDecision. Challenge.lean intentionally contains a target placeholder; Solution.lean does not import it.

Successful export SHA-256: `dd97c3a17ac971c80d63ea72dd36d76f5dfa56b9c7a657634b7d80fc92cca83c`, 569395278 bytes. Challenge export: `7f53b1c7363a2d4a4fc4c586df6890e4b9940b780be9ed598ee216bc84ba261c`, 71279270 bytes. Both checker runs used the identical solution export. Large exports and compiled caches are retained in the local verification work area, outside this source distribution.

Commands relative to this directory and the helper's .replay area:

```text
leanexport Challenge -- E2.challenge [kernel primitives and three permitted axioms]
leanexport Audit -- [14 Audit roots, kernel primitives and three permitted axioms]
lake comparator --config comparator.json --challenge-from-export .replay/challenge.ndjson --solution-from-export .replay/solution.ndjson --inadvisably-no-sandbox
leanchecker --silent --from-export .replay/solution.ndjson
nanoda-stack128.exe .replay/nanoda.json
```

The complete, expanded argument lists are in evidence/records.json. The nanoda configuration sets permitted_axioms to the three standard axioms, unpermitted_axiom_hard_error=true, num_threads=1, nat_extension=true and string_extension=true.

Comparator accepted the matching statement and permitted-axiom solution and replayed it through the bundled Lean kernel. Its log ends “Your solution is okay!”. This Windows run used native trusted exports and disabled the unavailable Linux namespace sandbox. The comparator itself warns that this mode is not trustworthy for adversarial input. Its from-export options also do not establish source correspondence by themselves; the recorded source/object hashes and freshly generated exports provide this run's provenance. No hostile-code isolation claim is made. The normal sandboxed command returned exit 2 with: “bwrap, which needs Linux namespaces.” It requires an independent Linux run for that isolation claim. No git command or dependency resolution was executed during these export-mode comparisons.

Standalone leanchecker exited 0 after 175.366 seconds, with empty output in silent mode. Nanoda exited 0 after 91.093 seconds, also with empty output. These are successful independent process replays of the selected reachable proof graph; leanchecker uses Lean's kernel implementation, while nanoda is a separate implementation. They do not certify unused side admissions in imported source files.

Every compiler used LEAN_NUM_THREADS=1 and -j1 -M6144. Each driver and its children ran within a 10,000,000,000-byte Windows Job Object commit cap. All recorded heavy process intervals are disjoint. Peak lane commit across all drivers: 5560291328 bytes; peak sampled child RSS: 2898128896 bytes. Sum of recorded step times, including development failures: 678.584 seconds. Peak values in each driver are cumulative high-water marks, not independent per-step maxima. No unrelated process was stopped or waited for.

One initial package compile failed because QIT's .olean.server companion file was absent; its sibling artifacts and complete public-import source closure were added and the rerun passed. Two early comparator invocations used an unsupported positional config argument and exited before comparing; both were corrected to --config. The expected Linux-sandbox failure is separately recorded. No mathematical source proof was changed to resolve these packaging issues.

| Step | Exit | Seconds | Sampled child peak RSS bytes |
|---|---:|---:|---:|
| build-Statement | 0 | 86.209 | 1684664320 |
| build-Challenge | 0 | 11.284 | 1684463616 |
| build-Solution | 1 | 23.916 | 213811200 |
| build-Solution | 0 | 22.115 | 2097680384 |
| build-Blueprint | 0 | 15.857 | 2108153856 |
| build-Audit | 0 | 14.144 | 2092527616 |
| export-challenge | 0 | 8.314 | 1741799424 |
| export-solution | 0 | 34.896 | 2898128896 |
| comparator-sandbox | 1 | 0.18 | 2060288 |
| comparator-native-trusted-exports | 1 | 0.156 | 2060288 |
| leanchecker | 0 | 175.366 | 921825280 |
| nanoda | 0 | 91.093 | 723943424 |
| comparator-sandbox-corrected | 2 | 0.157 | 2060288 |
| comparator-native-corrected | 0 | 194.897 | 978337792 |
