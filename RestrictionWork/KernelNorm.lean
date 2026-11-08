import RestrictionWork.Definitions

set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace RestrictionWork

theorem kernel_norm {n : ℕ} (x : Ambient n) (ω : UnitSphere n) :
    ‖kernel x ω‖ = 1 := by
  simp [kernel, Complex.norm_exp]


end RestrictionWork
