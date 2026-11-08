import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace RestrictionWork

/-- The rescaled spherical graph approaches the quadratic graph uniformly.
Here `s` is the squared length of a parameter in the unit ball. -/
theorem spherical_phase_quadratic_error (δ s : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) (hs : 0 ≤ s) (hs₁ : s ≤ 1) :
    |2 * (1 - Real.sqrt (1 - δ ^ 2 * s)) / δ ^ 2 - s| ≤ δ ^ 2 := by
  have hd2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hd2le : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hbase : 0 ≤ 1 - δ ^ 2 * s := by nlinarith
  have hroot := Real.sqrt_nonneg (1 - δ ^ 2 * s)
  have hsq := Real.sq_sqrt hbase
  have hroot₁ : Real.sqrt (1 - δ ^ 2 * s) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    nlinarith
  have hrden : 0 < 1 + Real.sqrt (1 - δ ^ 2 * s) := by positivity
  have hrat : 2 * (1 - Real.sqrt (1 - δ ^ 2 * s)) / δ ^ 2 - s =
      δ ^ 2 * s ^ 2 / (1 + Real.sqrt (1 - δ ^ 2 * s)) ^ 2 := by
    field_simp
    nlinarith [mul_nonneg hs hroot, sq_nonneg (s - 1)]
  rw [hrat, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (sq_pos_of_pos hrden)).mpr
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hden : 1 ≤ (1 + Real.sqrt (1 - δ ^ 2 * s)) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs2 hd2.le,
    mul_le_mul_of_nonneg_left hden hd2.le]

end RestrictionWork
