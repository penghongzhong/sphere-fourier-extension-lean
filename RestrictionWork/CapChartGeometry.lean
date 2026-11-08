import RestrictionWork.CapChartDefinitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RestrictionWork

/-- The actual chart lies on the Euclidean unit sphere. The height and graph
density bounds hold pointwise on the parameter unit ball. -/
theorem cap_chart_geometry {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {v : Ambient d} (hv : v ∈ Metric.ball (0 : Ambient d) 1) :
    (1 / 2 : ℝ) ≤ capHeight δ v ∧ capHeight δ v ≤ 1 ∧
    capPoint δ v ∈ UnitSphere (d + 1) ∧
    δ ^ d ≤ capDensity δ v ∧ capDensity δ v ≤ 2 * δ ^ d := by
  have hvnorm : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hd2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hbase : 0 ≤ 1 - δ ^ 2 * ‖v‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hv2 (sq_nonneg δ)]
  have hw0 : 0 ≤ capHeight δ v := Real.sqrt_nonneg _
  have hwsq : capHeight δ v ^ 2 = 1 - δ ^ 2 * ‖v‖ ^ 2 := Real.sq_sqrt hbase
  have hwlo : (1 / 2 : ℝ) ≤ capHeight δ v := by
    nlinarith [mul_le_mul_of_nonneg_left hv2 (sq_nonneg δ)]
  have hwhi : capHeight δ v ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg ‖v‖)]
  have hvsum : (∑ i : Fin d, (v i) ^ 2) = ‖v‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ) v).symm
  have hnormsq : ‖capPoint δ v‖ ^ 2 = δ ^ 2 * ‖v‖ ^ 2 + capHeight δ v ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => ℝ) (capPoint δ v)]
    change (∑ i : Fin (d + 1), ‖Fin.snoc (α := fun _ : Fin (d + 1) => ℝ)
      (fun j : Fin d => δ * v j) (capHeight δ v) i‖ ^ 2) = _
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum, hvsum]
  have hnorm1 : ‖capPoint δ v‖ ^ 2 = 1 := by rw [hnormsq, hwsq]; ring
  have hnorm : ‖capPoint δ v‖ = 1 := by
    have H := congrArg Real.sqrt hnorm1
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] using H
  have hmem : capPoint δ v ∈ UnitSphere (d + 1) := by
    simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using hnorm
  have hwpos : 0 < capHeight δ v := by linarith
  have hdc0 : 0 ≤ δ ^ d := (pow_pos hδ _).le
  refine ⟨hwlo, hwhi, hmem, ?_, ?_⟩
  · apply (le_div_iff₀ hwpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hwhi hdc0
  · apply (div_le_iff₀ hwpos).mpr
    have H := mul_le_mul_of_nonneg_left hwlo (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdc0)
    nlinarith only [H]

end RestrictionWork
