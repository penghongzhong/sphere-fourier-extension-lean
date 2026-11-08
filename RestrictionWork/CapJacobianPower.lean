import RestrictionWork.CriticalCapScaling

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace RestrictionWork

/-- The two exact Jacobian factors for arbitrary input and output exponents,
with the full cap-scale power separated from a fixed finite coefficient. -/
theorem cap_jacobian_power (d : ℕ) (p q : ℝ≥0∞) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^ q.toReal⁻¹ *
      ENNReal.ofReal (2 * δ ^ d) ^ p.toReal⁻¹ =
    ENNReal.ofReal ((((2 * Real.pi) ^ (d + 1) / 2) ^ q.toReal⁻¹ *
      (2 : ℝ) ^ p.toReal⁻¹) *
        δ ^ ((((d : ℝ) + 2) * q.toReal⁻¹) + (d : ℝ) * p.toReal⁻¹)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : (2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2 =
      ((2 * Real.pi) ^ (d + 1) / 2) * δ ^ (d + 2) := by ring
  rw [he, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by norm_num) (by positivity)]
  have h₁ : (δ ^ (d + 2)) ^ q.toReal⁻¹ = δ ^ (((d : ℝ) + 2) * q.toReal⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_cast
  have h₂ : (δ ^ d) ^ p.toReal⁻¹ = δ ^ ((d : ℝ) * p.toReal⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  rw [h₁, h₂, Real.rpow_add hδ]
  ring

end RestrictionWork
