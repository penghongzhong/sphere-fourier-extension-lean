import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace RestrictionWork

/-- Weighted Hölder on a finite matrix with controlled row and column sums. -/
theorem weighted_matrix_rpow_sum_le {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (K : ι → κ → ℝ≥0∞) (a : ι → ℝ≥0∞) (b : κ → ℝ≥0∞)
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) {C D : ℝ≥0∞}
    (hrow : ∀ i ∈ I, ∑ j ∈ J, K i j ≤ C)
    (hcol : ∀ j ∈ J, ∑ i ∈ I, K i j ≤ D) :
    (∑ i ∈ I, ∑ j ∈ J, K i j * a i ^ θ * b j ^ (1 - θ)) ≤
      (C * ∑ i ∈ I, a i) ^ θ * (D * ∑ j ∈ J, b j) ^ (1 - θ) := by
  have hθ' : 0 < 1 - θ := sub_pos.mpr hθ₁
  have hc : Real.HolderConjugate θ⁻¹ (1 - θ)⁻¹ := {
    inv_add_inv_eq_inv := by simp
    left_pos := inv_pos.mpr hθ
    right_pos := inv_pos.mpr hθ' }
  let F : ι × κ → ℝ≥0∞ := fun z => (K z.1 z.2 * a z.1) ^ θ
  let G : ι × κ → ℝ≥0∞ := fun z => (K z.1 z.2 * b z.2) ^ (1 - θ)
  have hprod (i : ι) (j : κ) :
      F (i, j) * G (i, j) = K i j * a i ^ θ * b j ^ (1 - θ) := by
    dsimp only [F, G]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ'.le,
      mul_mul_mul_comm, ← ENNReal.rpow_add_of_nonneg _ _ hθ.le hθ'.le]
    simp [mul_assoc]
  have hF (z : ι × κ) : F z ^ θ⁻¹ = K z.1 z.2 * a z.1 := by
    simp only [F, ← ENNReal.rpow_mul, mul_inv_cancel₀ hθ.ne', ENNReal.rpow_one]
  have hG (z : ι × κ) : G z ^ (1 - θ)⁻¹ = K z.1 z.2 * b z.2 := by
    simp only [G, ← ENNReal.rpow_mul, mul_inv_cancel₀ hθ'.ne', ENNReal.rpow_one]
  have hrow' : (∑ z ∈ I ×ˢ J, K z.1 z.2 * a z.1) ≤ C * ∑ i ∈ I, a i := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    change (∑ j ∈ J, K i j * a i) ≤ C * a i
    rw [← Finset.sum_mul]
    exact mul_le_mul' (hrow i hi) le_rfl
  have hcol' : (∑ z ∈ I ×ˢ J, K z.1 z.2 * b z.2) ≤ D * ∑ j ∈ J, b j := by
    rw [Finset.sum_product_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    change (∑ i ∈ I, K i j * b j) ≤ D * b j
    rw [← Finset.sum_mul]
    exact mul_le_mul' (hcol j hj) le_rfl
  calc
    _ = ∑ z ∈ I ×ˢ J, F z * G z := by rw [Finset.sum_product]; simp only [hprod]
    _ ≤ (∑ z ∈ I ×ˢ J, K z.1 z.2 * a z.1) ^ θ *
        (∑ z ∈ I ×ˢ J, K z.1 z.2 * b z.2) ^ (1 - θ) := by
      simpa only [hF, hG, one_div, inv_inv] using
        ENNReal.inner_le_Lp_mul_Lq (I ×ˢ J) F G hc
    _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hrow' hθ.le) (ENNReal.rpow_le_rpow hcol' hθ'.le)

/-- Uniform matrix bound for two families with total masses at most one. -/
theorem weighted_matrix_rpow_sum_le_of_normalized {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (K : ι → κ → ℝ≥0∞) (a : ι → ℝ≥0∞) (b : κ → ℝ≥0∞)
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) {C : ℝ≥0∞}
    (hrow : ∀ i ∈ I, ∑ j ∈ J, K i j ≤ C)
    (hcol : ∀ j ∈ J, ∑ i ∈ I, K i j ≤ C)
    (ha : ∑ i ∈ I, a i ≤ 1) (hb : ∑ j ∈ J, b j ≤ 1) :
    (∑ i ∈ I, ∑ j ∈ J, K i j * a i ^ θ * b j ^ (1 - θ)) ≤ C := by
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁.le
  calc
    _ ≤ (C * ∑ i ∈ I, a i) ^ θ * (C * ∑ j ∈ J, b j) ^ (1 - θ) :=
      weighted_matrix_rpow_sum_le I J K a b hθ hθ₁ hrow hcol
    _ ≤ C ^ θ * C ^ (1 - θ) := by
      refine mul_le_mul' (ENNReal.rpow_le_rpow ?_ hθ.le) (ENNReal.rpow_le_rpow ?_ hθ')
      · exact (mul_le_mul' le_rfl ha).trans_eq (mul_one C)
      · exact (mul_le_mul' le_rfl hb).trans_eq (mul_one C)
    _ = C := by rw [← ENNReal.rpow_add_of_nonneg _ _ hθ.le hθ']; simp

end RestrictionWork
