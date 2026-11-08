import RestrictionWork.PhaseExtensionDefinitions
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- Continuity in the physical variables of the actual graph integral. -/
theorem graph_extension_continuous {d : ℕ} {g : Ambient d → ℂ}
    (hg : Integrable g (patchMeasure d)) {φ : Ambient d → ℝ}
    (hφ : Measurable φ) : Continuous (graphExtension g φ) := by
  unfold graphExtension phaseExtension
  apply continuous_of_dominated (bound := fun v => ‖g v‖)
  · intro z
    have hmeas : Measurable (fun v : Ambient d =>
        Complex.exp (((⟪z.1, v⟫ + z.2 * φ v : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    exact hg.aestronglyMeasurable.mul hmeas.aestronglyMeasurable
  · intro z
    filter_upwards [] with v
    simp [norm_mul, Complex.norm_exp]
  · exact hg.norm
  · filter_upwards [] with v
    fun_prop

end RestrictionWork
