import RestrictionWork.WhitneyGeometricSum
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators

namespace RestrictionWork

private theorem sum_le_geometric_of_injective {I : Finset ℤ} {u : ℤ → ℝ≥0∞}
    {r : ℝ≥0∞} {n : ℤ → ℕ}
    (hinj : ∀ i ∈ I, ∀ j ∈ I, n i = n j → i = j)
    (hbound : ∀ i ∈ I, u i ≤ r ^ n i) :
    (∑ i ∈ I, u i) ≤ (1 - r)⁻¹ := by
  calc
    _ ≤ ∑ i ∈ I, r ^ n i := Finset.sum_le_sum hbound
    _ = ∑ k ∈ I.image n, r ^ k := by rw [Finset.sum_image hinj]
    _ ≤ ∑' k : ℕ, r ^ k := ENNReal.sum_le_tsum _
    _ = _ := ENNReal.tsum_geometric r

set_option maxHeartbeats 600000 in
/-- The exponential decay kernel has a uniform sum along any integer
lattice of fixed positive spacing, independently of its translation. -/
theorem dyadic_exponential_kernel_sum_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : ℝ) (I : Finset ℤ),
      (∑ i ∈ I, ENNReal.ofReal ((2 : ℝ) ^ (-c * |a * (i : ℝ) + b|))) ≤ C := by
  let r := ENNReal.ofReal ((2 : ℝ) ^ (-c * a))
  have hr : r < 1 := by
    have h : (2 : ℝ) ^ (-c * a) < 1 := by
      rw [← Real.rpow_zero (2 : ℝ)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by nlinarith only [mul_pos hc ha])
    simpa only [r, ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 h
  have hG : (1 - r)⁻¹ < ⊤ := (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hr).ne').lt_top
  refine ⟨(1 - r)⁻¹ + (1 - r)⁻¹, ENNReal.add_lt_top.mpr ⟨hG, hG⟩, ?_⟩
  intro b I
  let m : ℤ := ⌊-b / a⌋
  let u (i : ℤ) := ENNReal.ofReal ((2 : ℝ) ^ (-c * |a * (i : ℝ) + b|))
  have hm : a * (m : ℝ) + b ≤ 0 := by
    have h := (le_div_iff₀ ha).mp (Int.floor_le (-b / a))
    change (m : ℝ) * a ≤ -b at h
    linarith [mul_comm a (m : ℝ)]
  have hm' : 0 ≤ a * ((m + 1 : ℤ) : ℝ) + b := by
    have h := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (-b / a))
    change -b < ((m : ℝ) + 1) * a at h
    push_cast
    linarith [mul_comm a ((m : ℝ) + 1)]
  have hpow (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ (-c * (a * (n : ℝ)))) = r ^ n := by
    rw [show -c * (a * (n : ℝ)) = (-c * a) * (n : ℝ) by ring, Real.rpow_mul (by norm_num),
      Real.rpow_natCast, ENNReal.ofReal_pow (by positivity)]
  have hterm (i : ℤ) (n : ℕ) (hn : a * (n : ℝ) ≤ |a * (i : ℝ) + b|) : u i ≤ r ^ n := by
    rw [← hpow]
    apply ENNReal.ofReal_le_ofReal
    apply (Real.rpow_le_rpow_left_iff (by norm_num : 1 < (2 : ℝ))).2
    exact mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr hc.le)
  have hL : (∑ i ∈ I.filter (fun i => i ≤ m), u i) ≤ (1 - r)⁻¹ := by
    apply sum_le_geometric_of_injective (n := fun i => (m - i).toNat)
    · intro i hi j hj h
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      omega
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hcast : (((m - i).toNat : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hi')
      apply hterm
      rw [hcast]
      exact (by linarith only [hm, mul_sub a (m : ℝ) (i : ℝ)] :
        a * ((m : ℝ) - (i : ℝ)) ≤ -(a * (i : ℝ) + b)).trans (neg_le_abs _)
  have hR : (∑ i ∈ I.filter (fun i => ¬i ≤ m), u i) ≤ (1 - r)⁻¹ := by
    apply sum_le_geometric_of_injective (n := fun i => (i - (m + 1)).toNat)
    · intro i hi j hj h
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      omega
    · intro i hi
      have hi' : m + 1 ≤ i := by
        have h := (Finset.mem_filter.mp hi).2
        omega
      have hcast : (((i - (m + 1)).toNat : ℕ) : ℝ) = (i : ℝ) - ((m + 1 : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hi')
      apply hterm
      rw [hcast]
      exact (by linarith only [hm', mul_sub a (i : ℝ) ((m + 1 : ℤ) : ℝ)] :
        a * ((i : ℝ) - ((m + 1 : ℤ) : ℝ)) ≤ a * (i : ℝ) + b).trans (le_abs_self _)
  change (∑ i ∈ I, u i) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not I (fun i => i ≤ m) u]
  exact add_le_add hL hR

/-- After normalizing both input and dual bands, the dyadic pairing
exponent along a line z = a(1-x) is a fixed multiple of the same lattice
coordinate at either neighboring exponent. -/
theorem dyadic_pairing_exponent_on_line {p q' a x x' z z' : ℝ}
    (hpx : p * x = 1) (hqz : q' * (1 - z) = 1)
    (hz : z = a * (1 - x)) (hz' : z' = a * (1 - x')) (j k : ℤ) :
    (1 - p * x') * (j : ℝ) + (1 - q' * (1 - z')) * (k : ℝ) =
      -(x' - x) * (p * (j : ℝ) + a * q' * (k : ℝ)) := by
  have hfirst : 1 - p * x' = -p * (x' - x) := by
    linear_combination -hpx
  have hsecond : 1 - q' * (1 - z') = q' * (z' - z) := by
    linear_combination -hqz
  rw [hfirst, hsecond, hz, hz']
  ring

end RestrictionWork
