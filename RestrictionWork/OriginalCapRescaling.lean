import RestrictionWork.CanonicalCapExtension
import RestrictionWork.CapRescalingIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RestrictionWork

/-- Exact cap rescaling for the literal original sphere extension and a
concrete sphere input, including actual integrability of its kernel. -/
theorem original_cap_rescaling {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {g : Ambient d → ℂ} (hg : Integrable g (patchMeasure d)) (z : Ambient d × ℝ) :
    Integrable (fun ω => capSphereLift δ g ω *
      kernel ((2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)) ω)
      (sphereMeasure (d + 1)) ∧
    extension (capSphereLift δ g)
        ((2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)) =
      ((δ ^ d : ℝ) : ℂ) * Complex.exp (((-2 * z.2 / δ ^ 2 : ℝ) : ℂ) * Complex.I) *
        sphericalPatchExtension δ g z := by
  have hc := canonical_cap_extension hδ hδ₁ hg (capPhysicalScale δ z)
  exact ⟨hc.1, hc.2.trans (cap_rescaling_integral hδ hδ₁ hg z).2⟩

end RestrictionWork
