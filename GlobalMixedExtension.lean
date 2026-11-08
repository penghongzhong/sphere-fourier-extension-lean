import GlobalDiagonalExtension

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CriticalReplay
open OAI.Analysis.Fourier.Wave OAI.Analysis.Fourier.Restriction

/-- The full strict mixed range for the actual ambient representation of
spherical extension. The conclusion has no analytic estimate as a premise. -/
theorem global_mixed_extension : SphericalRestrictionConjecture := by
  apply sphericalRestriction_of_diagonal
  intro n hn s hs
  obtain ⟨C, hC, HC⟩ := global_diagonal_extension hn hs
  refine ⟨C.toReal + 1, by positivity, ?_⟩
  intro g hg
  apply (HC g hg).2.trans
  apply mul_le_mul' _ le_rfl
  calc
    C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC).symm
    _ ≤ ENNReal.ofReal (C.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

end CriticalReplay
