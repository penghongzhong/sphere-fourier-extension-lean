import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace RestrictionWork

/-- At large cap scales the original scale loss is bounded directly by
the radius loss. -/
theorem large_cap_scale_loss {κ η R δ : ℝ} (hη : 0 ≤ η) (hR : 1 ≤ R)
    (hδ : 0 < δ) (hbig : 1 ≤ R ^ κ * δ ^ 2) :
    R ^ η * δ ^ (-2 * η) ≤ R ^ (η * (1 + κ)) := by
  have hR0 : 0 < R := by linarith
  have hδpow : (δ ^ (2 : ℕ)) ^ η = δ ^ (2 * η) := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le]
    norm_num
  have H := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbig hη
  rw [Real.one_rpow, Real.mul_rpow (Real.rpow_nonneg hR0.le _) (sq_nonneg δ),
    ← Real.rpow_mul hR0.le, hδpow] at H
  have hi : δ ^ (-2 * η) ≤ R ^ (κ * η) := by
    rw [show -2 * η = -(2 * η) by ring, Real.rpow_neg hδ.le, ← one_div]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr H
  calc
    _ ≤ R ^ η * R ^ (κ * η) := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hR0.le _)
    _ = _ := by rw [← Real.rpow_add hR0]; congr 1; ring

end RestrictionWork
