import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section
open Filter Finset
open scoped ENNReal BigOperators

namespace RestrictionWork

set_option maxHeartbeats 800000 in
/-- The two decay bounds on either side of the mass scale sum uniformly,
including the case where the crossing occurs at the first scale. -/
theorem whitney_geometric_sum {M b : ℝ≥0∞} (hM : 0 < M) (hMt : M < ⊤)
    (hb : 0 < b) (hb₁ : b < 1) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∑' j : ℕ, min ((M / b ^ j) ^ a) (((b ^ j) / M) ^ c)) ≤
      (1 - b ^ a)⁻¹ + (1 - b ^ c)⁻¹ := by
  classical
  let w (j : ℕ) := min ((M / b ^ j) ^ a) (((b ^ j) / M) ^ c)
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb₁).eventually
    (eventually_lt_nhds hM)).exists
  have hex : ∃ j : ℕ, b ^ j ≤ M := ⟨n, hn.le⟩
  let J := Nat.find hex
  have hJ : b ^ J ≤ M := Nat.find_spec hex
  have hprev (j : ℕ) (hj : j < J) : M ≤ b ^ j :=
    (lt_of_not_ge (Nat.find_min hex hj)).le
  have hbPowTop (j : ℕ) : b ^ j ≠ ⊤ :=
    (ENNReal.pow_lt_top (hb₁.trans ENNReal.one_lt_top)).ne
  have hpow (j : ℕ) (p : ℝ) : (b ^ j) ^ p = (b ^ p) ^ j := by
    calc
      _ = b ^ ((j : ℝ) * p) := by rw [ENNReal.rpow_mul, ENNReal.rpow_natCast]
      _ = _ := by rw [mul_comm, ENNReal.rpow_mul, ENNReal.rpow_natCast]
  have hprefix : (∑ j ∈ range J, w j) ≤ ∑' j : ℕ, (b ^ a) ^ j := by
    rw [← Finset.sum_range_reflect w J]
    refine (sum_le_sum (g := fun j => (b ^ a) ^ j) fun j hj => ?_).trans (ENNReal.sum_le_tsum _)
    have hj' := mem_range.mp hj
    have he : J - 1 - j + j = J - 1 := by omega
    have hbound : M / b ^ (J - 1 - j) ≤ b ^ j := by
      apply (ENNReal.div_le_iff (pow_ne_zero _ hb.ne') (hbPowTop _)).mpr
      rw [← pow_add, add_comm j, he]
      exact hprev _ (by omega)
    calc
      _ ≤ (M / b ^ (J - 1 - j)) ^ a := min_le_left _ _
      _ ≤ (b ^ j) ^ a := ENNReal.rpow_le_rpow hbound ha.le
      _ = _ := hpow j a
  have htail (j : ℕ) : w (J + j) ≤ (b ^ c) ^ j := by
    have hbound : b ^ (J + j) / M ≤ b ^ j := by
      apply (ENNReal.div_le_iff hM.ne' hMt.ne).mpr
      rw [pow_add, mul_comm (b ^ J)]
      exact mul_le_mul' le_rfl hJ
    calc
      _ ≤ (b ^ (J + j) / M) ^ c := min_le_right _ _
      _ ≤ (b ^ j) ^ c := ENNReal.rpow_le_rpow hbound hc.le
      _ = _ := hpow j c
  change (∑' j : ℕ, w j) ≤ _
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  calc
    _ ≤ ∑ j ∈ range (J + N), w j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => zero_le)
    _ = (∑ j ∈ range J, w j) + ∑ j ∈ range N, w (J + j) := by
      simpa only [Nat.add_comm J] using (sum_range_add w J N)
    _ ≤ ((∑' j : ℕ, (b ^ a) ^ j) + ∑' j : ℕ, (b ^ c) ^ j) := by
      refine add_le_add hprefix ?_
      exact (sum_le_sum fun j _ => htail j).trans (ENNReal.sum_le_tsum _)
    _ = _ := congrArg₂ (· + ·) (ENNReal.tsum_geometric (b ^ a)) (ENNReal.tsum_geometric (b ^ c))

end RestrictionWork
