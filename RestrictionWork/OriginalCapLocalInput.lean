import RestrictionWork.OriginalCapNormTransfer
import RestrictionWork.OriginalCapRegion

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- Directly apply a local estimate for the literal original sphere extension
to the actual cap input. The original estimate is an explicit analytic
hypothesis, not an asserted restriction theorem. All geometric and measure
interfaces used in this implication are proved in the present project. -/
theorem original_cap_local_input {d : ℕ} {δ R η : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) (hR : 1 ≤ R)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) {g : Ambient d → ℂ}
    (hg : MemLp g p (patchMeasure d)) (C : ℝ≥0)
    (hinput : ∀ L : ℝ, 1 ≤ L → ∀ f : UnitSphere (d + 1) → ℂ,
      MemLp f p (sphereMeasure (d + 1)) →
      eLpNorm (extension f) q (volume.restrict (Metric.ball 0 L)) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (L ^ η) *
          eLpNorm f p (sphereMeasure (d + 1))) :
    ENNReal.ofReal (δ ^ d) *
        eLpNorm (sphericalPatchExtension δ g) q (volume.restrict (Metric.ball 0 R)) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^ q.toReal⁻¹ *
        (C : ℝ≥0∞) * ENNReal.ofReal ((4 * R / δ ^ 2) ^ η) *
          (ENNReal.ofReal (2 * δ ^ d) ^ p.toReal⁻¹ * eLpNorm g p (patchMeasure d)) := by
  obtain ⟨hmem, _, hnorm, htransfer⟩ :=
    original_cap_norm_transfer hδ hδ₁ hp hg q (Metric.ball 0 R)
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hsmall : δ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hδ.le hδ₁
  have hL : 1 ≤ 4 * R / δ ^ 2 := by
    apply (le_div_iff₀ hδsq).mpr
    nlinarith
  have hregion := original_cap_region (d := d) hδ hδ₁ (by linarith : 0 < R)
  have Hlocal := hinput (4 * R / δ ^ 2) hL (capSphereLift δ g) hmem
  rw [htransfer]
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^ q.toReal⁻¹ *
        eLpNorm (extension (capSphereLift δ g)) q
          (volume.restrict (Metric.ball 0 (4 * R / δ ^ 2))) :=
      mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hregion le_rfl))
    _ ≤ _ := by
      have H := mul_le_mul' (le_refl
        (ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^ q.toReal⁻¹))
        (Hlocal.trans (mul_le_mul' le_rfl hnorm))
      simpa only [mul_assoc] using H

end RestrictionWork
