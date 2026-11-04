import Lake
open Lake DSL
package e2release where
  leanOptions := #[⟨`maxRecDepth, .ofNat 100000⟩, ⟨`maxHeartbeats, .ofNat 4000000⟩, ⟨`autoImplicit, false⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
@[default_target]
lean_lib E2Release where
  roots := #[`Solution, `Audit]
  globs := #[`E2.+, `Companion.+, `QIT.+, `Statement, `Challenge, `Solution, `Blueprint, `Audit]
