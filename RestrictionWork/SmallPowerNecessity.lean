import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open Filter Topology
namespace RestrictionWork

/-- A fixed finite coefficient cannot reverse the order of small-scale powers. -/
theorem small_power_necessity {a b C : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → δ ^ a ≤ C * δ ^ b) : b ≤ a := by
  by_contra hn
  have hab : 0 < b - a := sub_pos.mpr (lt_of_not_ge hn)
  let δ : ℕ → ℝ := fun n ↦ (1/2 : ℝ) ^ (n + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδsmall (n : ℕ) : δ n ≤ 1/2 := by
    dsimp [δ]
    rw [pow_succ]
    have H : (1/2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have H (n : ℕ) : 1 ≤ C * (δ n) ^ (b - a) := by
    have H := mul_le_mul_of_nonneg_left (h (δ n) (hδpos n) (hδsmall n))
      (Real.rpow_nonneg (hδpos n).le (-a))
    have he₁ : (δ n) ^ (-a) * (δ n) ^ a = 1 := by
      rw [← Real.rpow_add (hδpos n)]; simp
    have he₂ : (δ n) ^ (-a) * (C * (δ n) ^ b) = C * (δ n) ^ (b - a) := by
      rw [mul_left_comm, ← Real.rpow_add (hδpos n)]
      congr 2
      ring
    rwa [he₁, he₂] at H
  have ht : Tendsto δ atTop (𝓝 0) := by
    have H := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    simpa only [δ, pow_succ, zero_mul] using H.mul_const (1/2 : ℝ)
  have ht' : Tendsto (fun n ↦ C * (δ n) ^ (b - a)) atTop (𝓝 0) := by
    have H := ((Real.continuous_rpow_const hab.le).tendsto 0).comp ht
    simpa only [Real.zero_rpow (ne_of_gt hab), mul_zero, Function.comp_def] using H.const_mul C
  have Hlim : (1 : ℝ) ≤ 0 := ge_of_tendsto ht' (Filter.Eventually.of_forall H)
  norm_num at Hlim

end RestrictionWork
