import Lake
open Lake DSL

package sphere_fourier_extension where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI
lean_lib RestrictionWork
lean_lib SphereAreaReuse
lean_lib LeanOscillatory
lean_lib CriticalExtensionContract
lean_lib CriticalLocalDual
lean_lib CriticalReplay
lean_lib CriticalTwoPi
lean_lib GlobalDiagonalExtension
lean_lib GlobalMixedExtension
lean_lib JSP001040FinalAudit
@[default_target] lean_lib ManuscriptCorrespondence
@[default_target] lean_lib ManuscriptStatement
lean_lib UnconditionalExtensionReplay
