import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace RestrictionWork

/-- A concrete comparison scale keeps the quadratic error bounded and
converts the scale loss into a radius loss. -/
theorem balanced_cap_scale {κ η R : ℝ} (hκ : 0 ≤ κ) (hR : 1 ≤ R) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1/2 ∧ R ^ κ * σ ^ 2 ≤ 1 ∧
      R ^ η * σ ^ (-2 * η) = (2 : ℝ) ^ (2 * η) * R ^ (η * (1 + κ)) := by
  have hR0 : 0 < R := by linarith
  let σ : ℝ := (1/2) * R ^ (-κ/2)
  have hσ : 0 < σ := mul_pos (by norm_num) (Real.rpow_pos_of_pos hR0 _)
  have hσ₁ : σ ≤ 1/2 := by
    have H := Real.rpow_le_one_of_one_le_of_nonpos hR (show -κ/2 ≤ 0 by linarith)
    dsimp [σ]
    linarith
  have hsquare : σ ^ 2 = (1/4 : ℝ) * R ^ (-κ) := by
    dsimp [σ]
    rw [mul_pow, ← Real.rpow_mul_natCast hR0.le (-κ/2) 2]
    have he : (-κ/2) * ((2 : ℕ) : ℝ) = -κ := by ring
    rw [he]
    norm_num
  have htail : R ^ κ * σ ^ 2 = 1/4 := by
    rw [hsquare]
    calc
      _ = (1/4 : ℝ) * (R ^ κ * R ^ (-κ)) := by ring
      _ = _ := by rw [← Real.rpow_add hR0]; simp
  refine ⟨σ, hσ, hσ₁, by linarith, ?_⟩
  have hhalf : (1/2 : ℝ) ^ (-2 * η) = (2 : ℝ) ^ (2 * η) := by
    rw [show -2 * η = -(2 * η) by ring, Real.rpow_neg_eq_inv_rpow]
    norm_num
  have hexp : (-κ/2) * (-2 * η) = κ * η := by ring
  dsimp [σ]
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hR0.le _),
    ← Real.rpow_mul hR0.le, hexp, hhalf]
  calc
    _ = (2 : ℝ) ^ (2 * η) * (R ^ η * R ^ (κ * η)) := by ring
    _ = _ := by rw [← Real.rpow_add hR0]; congr 2 <;> ring

end RestrictionWork
