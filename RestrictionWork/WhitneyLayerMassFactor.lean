import RestrictionWork.WhitneyDyadicMassSum

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace RestrictionWork

/-- Extract the common scaling factor from a layer with sequence exponent
equal to the output exponent. -/
theorem whitney_layer_mass_factor {ι : Type*} (s : Finset ι)
    {F m : ι → ℝ≥0∞} {K : ℝ≥0∞} {α y : ℝ} (hy : 0 < y)
    (hF : ∀ i ∈ s, F i ≤ K * m i ^ α) :
    (∑ i ∈ s, F i ^ y⁻¹) ^ y ≤ K * (∑ i ∈ s, m i ^ (α / y)) ^ y := by
  have hy' : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
  calc
    _ ≤ (∑ i ∈ s, (K * m i ^ α) ^ y⁻¹) ^ y :=
      ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i hi =>
        ENNReal.rpow_le_rpow (hF i hi) hy') hy.le
    _ = _ := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hy', ← ENNReal.rpow_mul, div_eq_mul_inv]
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ hy.le,
        ← ENNReal.rpow_mul, inv_mul_cancel₀ hy.ne', ENNReal.rpow_one]

end RestrictionWork
