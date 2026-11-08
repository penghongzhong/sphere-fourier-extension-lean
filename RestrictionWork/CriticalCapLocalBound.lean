import RestrictionWork.OriginalCriticalLocalInput
import RestrictionWork.OriginalCapLocalInput
import RestrictionWork.CriticalCapScaling

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- The actual centered spherical cap has arbitrary positive scale loss.
No local-smoothing, restriction, or cap-area identity is assumed. -/
theorem critical_cap_local_bound {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ≥0, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ R : ℝ, 1 ≤ R →
      ∀ g : Ambient d → ℂ, MemLp g (capCriticalExponent d) (patchMeasure d) →
      MemLp (sphericalPatchExtension δ g) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ∧
      eLpNorm (sphericalPatchExtension δ g) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ≤
        (A : ℝ≥0∞) * ENNReal.ofReal (R ^ η * δ ^ (-2 * η)) *
          eLpNorm g (capCriticalExponent d) (patchMeasure d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpc : capCriticalExponent d =
      ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (d + 1)) := by
    simp only [capCriticalExponent, OAI.Analysis.Fourier.LocalSmoothing.criticalExponent,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have hp : 1 ≤ capCriticalExponent d := by
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ hd0).mpr
    linarith
  obtain ⟨C, HC⟩ := original_critical_local_input (n := d + 1) (by omega) hη
  let A : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ ((d : ℝ) / 2)) *
    (C : ℝ≥0∞) * ENNReal.ofReal (4 ^ η)
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) ENNReal.ofReal_ne_top
  refine ⟨A.toNNReal, ?_⟩
  intro δ hδ hδ₁ R hR g hg
  have H := original_cap_local_input (q := capCriticalExponent d) hδ hδ₁ hR hp hg C
    (fun L hL f hf ↦ by
      rw [hpc] at hf ⊢
      exact (HC L hL f hf).2)
  have hs := critical_cap_scaling hd hδ
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi) ^ ((d : ℝ) / 2))] at hs
  have Hcancel : ENNReal.ofReal (δ ^ d) *
      eLpNorm (sphericalPatchExtension δ g) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ≤
      ENNReal.ofReal (δ ^ d) *
        (ENNReal.ofReal ((2 * Real.pi) ^ ((d : ℝ) / 2)) * (C : ℝ≥0∞) *
          ENNReal.ofReal ((4 * R / δ ^ 2) ^ η) *
          eLpNorm g (capCriticalExponent d) (patchMeasure d)) := by
    calc
      _ ≤ _ := H
      _ = (ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^
            (capCriticalExponent d).toReal⁻¹ *
          ENNReal.ofReal (2 * δ ^ d) ^ (capCriticalExponent d).toReal⁻¹) *
          (C : ℝ≥0∞) * ENNReal.ofReal ((4 * R / δ ^ 2) ^ η) *
          eLpNorm g (capCriticalExponent d) (patchMeasure d) := by ring
      _ = _ := by rw [hs]; ring
  have ha0 : ENNReal.ofReal (δ ^ d) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hδ d)).ne'
  have Hnorm : eLpNorm (sphericalPatchExtension δ g) (capCriticalExponent d)
      (volume.restrict (Metric.ball 0 R)) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ ((d : ℝ) / 2)) * (C : ℝ≥0∞) *
        ENNReal.ofReal ((4 * R / δ ^ 2) ^ η) * eLpNorm g (capCriticalExponent d) (patchMeasure d) := by
    calc
      _ = (ENNReal.ofReal (δ ^ d))⁻¹ *
          (ENNReal.ofReal (δ ^ d) * eLpNorm (sphericalPatchExtension δ g)
            (capCriticalExponent d) (volume.restrict (Metric.ball 0 R))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl Hcancel
      _ = _ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]
  have hpower : (4 * R / δ ^ 2) ^ η = (4 : ℝ) ^ η * (R ^ η * δ ^ (-2 * η)) := by
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by linarith : 0 ≤ R)]
    have he : (δ ^ (2 : ℕ)) ^ η = δ ^ (2 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      norm_num
    rw [he, show -2 * η = -(2 * η) by ring, Real.rpow_neg hδ.le]
    ring
  have Hfinal : eLpNorm (sphericalPatchExtension δ g) (capCriticalExponent d)
      (volume.restrict (Metric.ball 0 R)) ≤
      A * ENNReal.ofReal (R ^ η * δ ^ (-2 * η)) * eLpNorm g (capCriticalExponent d) (patchMeasure d) := by
    rw [hpower, ENNReal.ofReal_mul (by positivity)] at Hnorm
    simpa only [A, mul_assoc] using Hnorm
  rw [ENNReal.coe_toNNReal hA]
  exact ⟨Hfinal.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top).lt_top hg), Hfinal⟩

end RestrictionWork
