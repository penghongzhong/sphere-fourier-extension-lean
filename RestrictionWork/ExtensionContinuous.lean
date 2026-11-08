import RestrictionWork.KernelIntegrable
import Mathlib.Tactic.FunProp

set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace RestrictionWork

theorem extension_continuous {n : ℕ} {f : UnitSphere n → ℂ}
    (hf : Integrable f (sphereMeasure n)) : Continuous (extension f) := by
  apply continuous_of_dominated
    (fun x => (integrable_kernel_product hf x).aestronglyMeasurable)
    (bound := fun ω => ‖f ω‖)
  · intro x
    filter_upwards [] with ω
    simp [norm_mul, kernel_norm]
  · exact hf.norm
  · filter_upwards [] with ω
    unfold kernel
    fun_prop

end RestrictionWork
