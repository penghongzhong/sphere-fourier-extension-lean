import RestrictionWork.KernelNorm
import RestrictionWork.KernelContinuous

set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace RestrictionWork

theorem integrable_kernel_product {n : ℕ} {f : UnitSphere n → ℂ}
    (hf : Integrable f (sphereMeasure n)) (x : Ambient n) :
    Integrable (fun ω => f ω * kernel x ω) (sphereMeasure n) := by
  apply hf.mono (hf.aestronglyMeasurable.mul
    (kernel_continuous x).aestronglyMeasurable)
  filter_upwards [] with ω
  simp [norm_mul, kernel_norm]


end RestrictionWork
