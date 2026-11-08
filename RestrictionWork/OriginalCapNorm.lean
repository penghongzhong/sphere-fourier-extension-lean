import RestrictionWork.OriginalCapRescaling
import RestrictionWork.GraphExtensionContinuous

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

/-- Exact output norm correspondence for any physical measure, including
local ball restrictions. The unit modulation causes no loss. -/
theorem original_cap_norm {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {g : Ambient d → ℂ} (hg : Integrable g (patchMeasure d))
    (q : ℝ≥0∞) (ν : Measure (Ambient d × ℝ)) :
    eLpNorm (fun z => extension (capSphereLift δ g)
      ((2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z))) q ν =
      ENNReal.ofReal (δ ^ d) * eLpNorm (sphericalPatchExtension δ g) q ν := by
  have hφ : Measurable (fun v : Ambient d => sphericalPhase δ (‖v‖ ^ 2)) := by
    unfold sphericalPhase
    fun_prop
  have hgraph : Continuous (sphericalPatchExtension δ g) := graph_extension_continuous hg hφ
  have hprod : Continuous (fun z : Ambient d × ℝ =>
      ((δ ^ d : ℝ) : ℂ) * Complex.exp (((-2 * z.2 / δ ^ 2 : ℝ) : ℂ) * Complex.I) *
        sphericalPatchExtension δ g z) := by fun_prop
  have hleft : Continuous (fun z : Ambient d × ℝ => extension (capSphereLift δ g)
      ((2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z))) :=
    hprod.congr (fun z => (original_cap_rescaling hδ hδ₁ hg z).2.symm)
  have hright : Continuous (fun z : Ambient d × ℝ =>
      ((δ ^ d : ℝ) : ℂ) * sphericalPatchExtension δ g z) := by fun_prop
  calc
    _ = eLpNorm (fun z => ((δ ^ d : ℝ) : ℂ) * sphericalPatchExtension δ g z) q ν := by
      apply eLpNorm_congr_norm_ae hleft.aestronglyMeasurable hright.aestronglyMeasurable
      filter_upwards [] with z
      rw [(original_cap_rescaling hδ hδ₁ hg z).2]
      have hm : ‖Complex.exp (((-2 * z.2 / δ ^ 2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Real.exp_zero]
      simp only [norm_mul, hm, mul_one]
    _ = _ := by
      change eLpNorm ((((δ ^ d : ℝ) : ℂ)) • sphericalPatchExtension δ g) q ν = _
      rw [eLpNorm_const_smul, ← ofReal_norm_eq_enorm]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]

end RestrictionWork
