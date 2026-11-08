import RestrictionWork.DyadicWhitneyPairs
import RestrictionWork.WhitneyDyadicMassSum

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace RestrictionWork

private theorem card_dyadic_whitney_fiber_le {d : ℕ} (j : ℕ)
    (side : ((Fin d → ℤ) × (Fin d → ℤ)) → (Fin d → ℤ))
    (hinj : ∀ p q, side p = side q →
      (∀ i, p.1 i - p.2 i = q.1 i - q.2 i) → p = q)
    (k : Fin d → ℤ) :
    (by classical exact ((dyadicWhitneyPairs d j).filter fun p => side p = k).card) ≤ 7 ^ d := by
  classical
  let W := (dyadicWhitneyPairs d j).filter fun p => side p = k
  let B := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-3 : ℤ) 3)
  let offset (p : (Fin d → ℤ) × (Fin d → ℤ)) (i : Fin d) := p.1 i - p.2 i
  have hc : W.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn offset
    · intro p hp
      exact Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_Icc.mpr (abs_le.mp (dyadic_whitney_pair_index_gap (Finset.mem_filter.mp hp).1 i))
    · intro p hp q hq he
      exact hinj p q ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
        (congrFun he)
  have hB : (Finset.Icc (-3 : ℤ) 3).card = 7 := by rw [Int.card_Icc]; norm_num
  simpa only [B, Fintype.card_piFinset_const, hB] using hc

/-- A fixed first cell has at most (7^d) partners at the given level. -/
theorem card_dyadic_whitney_left_fiber_le {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    (by classical exact ((dyadicWhitneyPairs d j).filter fun p => p.1 = k).card) ≤ 7 ^ d := by
  apply card_dyadic_whitney_fiber_le j Prod.fst _ k
  intro p q h he
  refine Prod.ext h (funext fun i => ?_)
  exact sub_right_injective (by simpa only [h] using he i)

/-- A fixed second cell has at most (7^d) partners at the given level. -/
theorem card_dyadic_whitney_right_fiber_le {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    (by classical exact ((dyadicWhitneyPairs d j).filter fun p => p.2 = k).card) ≤ 7 ^ d := by
  apply card_dyadic_whitney_fiber_le j Prod.snd _ k
  intro p q h he
  refine Prod.ext (funext fun i => ?_) h
  exact sub_left_injective (by simpa only [h] using he i)

private theorem disjoint_dyadic_parameter_cell {d : ℕ} (n : ℕ) {k l : Fin d → ℤ}
    (hne : k ≠ l) : Disjoint (dyadicParameterCell n k) (dyadicParameterCell n l) := by
  apply disjoint_left.mpr
  intro u hu hv
  exact hne (funext fun i => (mem_dyadic_parameter_cell.mp hu i).symm.trans
    (mem_dyadic_parameter_cell.mp hv i))

private theorem sum_cell_mass_le {d : ℕ} (A : Set (Ambient d)) (n : ℕ)
    (I : Finset (Fin d → ℤ)) :
    (∑ k ∈ I, volume (A ∩ dyadicParameterCell n k)) ≤ volume A := by
  let μ : Measure (Ambient d) := volume.restrict A
  have heq (k : Fin d → ℤ) :
      volume (A ∩ dyadicParameterCell n k) = μ (dyadicParameterCell n k) := by
    change _ = (volume.restrict A) (dyadicParameterCell n k)
    rw [Measure.restrict_apply (measurable_dyadic_parameter_cell n k), inter_comm]
  have hd : (↑I : Set (Fin d → ℤ)).PairwiseDisjoint (dyadicParameterCell n) := by
    intro k _ l _ hkl
    exact disjoint_dyadic_parameter_cell n hkl
  simp_rw [heq]
  rw [← measure_biUnion_finset hd (fun k _ => measurable_dyadic_parameter_cell n k)]
  exact (measure_mono (subset_univ _)).trans_eq (Measure.restrict_apply_univ A)

private theorem sum_paired_cell_mass_le {d : ℕ} (A : Set (Ambient d)) (j : ℕ)
    (side : ((Fin d → ℤ) × (Fin d → ℤ)) → (Fin d → ℤ))
    (hcard : ∀ k,
      (by classical exact ((dyadicWhitneyPairs d j).filter fun p => side p = k).card) ≤ 7 ^ d) :
    (∑ p ∈ dyadicWhitneyPairs d j, volume (A ∩ dyadicParameterCell (j + 1) (side p))) ≤
      ((7 ^ d : ℕ) : ℝ≥0∞) * volume A := by
  classical
  let W := dyadicWhitneyPairs d j
  let I := W.image side
  let m (k : Fin d → ℤ) := volume (A ∩ dyadicParameterCell (j + 1) k)
  have hm : ∀ p ∈ W, side p ∈ I := fun p hp => Finset.mem_image_of_mem side hp
  calc
    (∑ p ∈ W, m (side p)) = ∑ k ∈ I, ∑ p ∈ W with side p = k, m k :=
      (Finset.sum_fiberwise_of_maps_to' hm m).symm
    _ ≤ ∑ k ∈ I, ((7 ^ d : ℕ) : ℝ≥0∞) * m k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul' (Nat.cast_le.mpr (hcard k)) le_rfl
    _ = ((7 ^ d : ℕ) : ℝ≥0∞) * ∑ k ∈ I, m k := by rw [Finset.mul_sum]
    _ ≤ ((7 ^ d : ℕ) : ℝ≥0∞) * volume A := mul_le_mul' le_rfl (sum_cell_mass_le A (j + 1) I)

/-- The common mass dominating both parts of a Whitney pair. -/
def dyadicWhitneyMass {d : ℕ} (A : Set (Ambient d)) (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ≥0∞ :=
  max (volume (A ∩ dyadicParameterCell (j + 1) p.1))
    (volume (A ∩ dyadicParameterCell (j + 1) p.2))

theorem dyadic_whitney_mass_prod_le {d : ℕ} (A : Set (Ambient d)) (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    volume (A ∩ dyadicParameterCell (j + 1) p.1) *
        volume (A ∩ dyadicParameterCell (j + 1) p.2) ≤ dyadicWhitneyMass A j p ^ (2 : ℕ) := by
  rw [pow_two]
  exact mul_le_mul' (le_max_left _ _) (le_max_right _ _)

theorem dyadic_whitney_mass_sum_le {d : ℕ} (A : Set (Ambient d)) (j : ℕ) :
    (∑ p ∈ dyadicWhitneyPairs d j, dyadicWhitneyMass A j p) ≤
      ((2 * 7 ^ d : ℕ) : ℝ≥0∞) * volume A := by
  calc
    _ ≤ ∑ p ∈ dyadicWhitneyPairs d j,
        (volume (A ∩ dyadicParameterCell (j + 1) p.1) +
          volume (A ∩ dyadicParameterCell (j + 1) p.2)) :=
      Finset.sum_le_sum fun _ _ => max_le (le_add_right le_rfl) (le_add_left le_rfl)
    _ ≤ ((7 ^ d : ℕ) : ℝ≥0∞) * volume A + ((7 ^ d : ℕ) : ℝ≥0∞) * volume A := by
      rw [Finset.sum_add_distrib]
      exact add_le_add
        (sum_paired_cell_mass_le A j Prod.fst (card_dyadic_whitney_left_fiber_le j))
        (sum_paired_cell_mass_le A j Prod.snd (card_dyadic_whitney_right_fiber_le j))
    _ = _ := by rw [← two_mul, ← mul_assoc, Nat.cast_mul, Nat.cast_ofNat]

theorem volume_dyadic_parameter_cell_at_whitney_level {d : ℕ} (j : ℕ)
    (k : Fin d → ℤ) :
    volume (dyadicParameterCell (j + 1) k) =
      ((2 : ℝ≥0∞)⁻¹ ^ d) * ((2 : ℝ≥0∞)⁻¹ ^ d) ^ j := by
  rw [volume_dyadic_parameter_cell, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.inv_pow,
    pow_succ', mul_pow, ← pow_mul, Nat.mul_comm j d, pow_mul]

theorem dyadic_whitney_mass_le {d : ℕ} (A : Set (Ambient d)) (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    dyadicWhitneyMass A j p ≤ ((2 : ℝ≥0∞)⁻¹ ^ d) * ((2 : ℝ≥0∞)⁻¹ ^ d) ^ j := by
  unfold dyadicWhitneyMass
  exact max_le
    ((measure_mono inter_subset_right).trans_eq (volume_dyadic_parameter_cell_at_whitney_level j p.1))
    ((measure_mono inter_subset_right).trans_eq (volume_dyadic_parameter_cell_at_whitney_level j p.2))

/-- The dyadic mass sum applied to the actual restrictions of a set to the Whitney cells. -/
theorem dyadic_whitney_mass_tsum_le {d : ℕ} (hd : 1 ≤ d)
    {α k y : ℝ} (hy : 0 < y) (hyk : y < k) (hkα : k < α) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ A : Set (Ambient d), 0 < volume A → volume A < ⊤ →
      (∑' j : ℕ, (((2 : ℝ≥0∞)⁻¹ ^ d) ^ j) ^ (-(α - k)) *
        (∑ p ∈ dyadicWhitneyPairs d j, dyadicWhitneyMass A j p ^ (α / y)) ^ y)
      ≤ C * volume A ^ k := by
  let b := (2 : ℝ≥0∞)⁻¹ ^ d
  have ht : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.mpr (by norm_num)
  have hb : 0 < b := ENNReal.pow_pos ht _
  have hb' : b < 1 := pow_lt_one₀ ht.le (ENNReal.inv_lt_one.mpr (by norm_num)) (by omega)
  obtain ⟨C, hC, H⟩ := whitney_dyadic_mass_sum hb hb'
    (ENNReal.natCast_lt_top (2 * 7 ^ d)) (hb'.trans ENNReal.one_lt_top) hy hyk hkα
  refine ⟨C, hC, fun A hA hAt => ?_⟩
  exact H hA hAt (dyadicWhitneyPairs d) (dyadicWhitneyMass A) (dyadic_whitney_mass_sum_le A)
    (fun j p _ => dyadic_whitney_mass_le A j p)

end RestrictionWork
