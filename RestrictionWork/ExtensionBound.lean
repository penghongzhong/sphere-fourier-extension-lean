import RestrictionWork.KernelIntegrable

set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace RestrictionWork

theorem extension_bound {n : ℕ} {f : UnitSphere n → ℂ}
    (hf : Integrable f (sphereMeasure n)) (x : Ambient n) :
    ‖extension f x‖ ≤ ∫ ω, ‖f ω‖ ∂sphereMeasure n := by
  have _hvalid := integrable_kernel_product hf x
  calc
    ‖extension f x‖ ≤ ∫ ω, ‖f ω * kernel x ω‖ ∂sphereMeasure n :=
      norm_integral_le_integral_norm _
    _ = ∫ ω, ‖f ω‖ ∂sphereMeasure n := by
      congr 1
      funext ω
      simp [norm_mul, kernel_norm]


end RestrictionWork
