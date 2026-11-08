import RestrictionWork.OriginalGlobalStrictInput
import RestrictionWork.Target

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace RestrictionWork

/-- The strict global estimate is an instance of the exact original target
predicate. The allowed Knapp equality is not included in this theorem. -/
theorem original_strict_target {n : ℕ} (hn : 3 ≤ n) {p : ℝ≥0∞}
    (hp : 1 < p) {q : ℝ}
    (hq : 2 * (n : ℝ) / ((n : ℝ) - 1) < q)
    (hpq : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent p < q) :
    BoundedSphereExtension n p (ENNReal.ofReal q) :=
  original_global_strict_input (by omega) hp hq hpq

end RestrictionWork
