import RestrictionWork.DyadicWhitneyPairs

set_option autoImplicit false
noncomputable section

open Set

namespace RestrictionWork

private theorem scaled_coordinate_bounds {d n : ℕ} {k : Fin d → ℤ} {u : Ambient d}
    (hu : u ∈ dyadicParameterCell n k) (i : Fin d) :
    (k i : ℝ) ≤ (2 : ℝ) ^ n * u i ∧ (2 : ℝ) ^ n * u i < (k i : ℝ) + 1 :=
  Int.floor_eq_iff.mp (mem_dyadic_parameter_cell.mp hu i)

private theorem cell_distance_le {d n : ℕ} (hd : 1 ≤ d)
    {k l : Fin d → ℤ} (hkl : ∀ i, |k i - l i| ≤ 3)
    {u v : Ambient d} (hu : u ∈ dyadicParameterCell n k)
    (hv : v ∈ dyadicParameterCell n l) :
    ‖u - v‖ ≤ (4 * (d : ℝ)) * ((2 : ℝ) ^ n)⁻¹ := by
  let D := (2 : ℝ) ^ n
  have hD : 0 < D := by positivity
  have hcoord (i : Fin d) : |u i - v i| ≤ 4 * D⁻¹ := by
    obtain ⟨h₁, h₂⟩ := scaled_coordinate_bounds hu i
    obtain ⟨h₃, h₄⟩ := scaled_coordinate_bounds hv i
    have h₅ : |(k i : ℝ) - (l i : ℝ)| ≤ 3 := by exact_mod_cast hkl i
    obtain ⟨h₅, h₆⟩ := abs_le.mp h₅
    have h : |D * (u i - v i)| ≤ 4 := by
      dsimp only [D]
      rw [mul_sub]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos hD] at h
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using h)
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _ : Fin d, (4 * D⁻¹) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [PiLp.sub_apply, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) _
    _ = (d : ℝ) * (4 * D⁻¹) ^ 2 := by simp
    _ ≤ ((4 * (d : ℝ)) * D⁻¹) ^ 2 := by
      have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hd'' : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
      calc
        _ ≤ (d : ℝ) ^ 2 * (4 * D⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right hd'' (sq_nonneg _)
        _ = _ := by ring

/-- Every pair of points in an enumerated Whitney rectangle is separated
by at least one fine cell length. -/
theorem dyadic_whitney_pair_distance_ge {d j : ℕ} {p : (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : p ∈ dyadicWhitneyPairs d j) {u v : Ambient d}
    (hu : u ∈ dyadicParameterCell (j + 1) p.1)
    (hv : v ∈ dyadicParameterCell (j + 1) p.2) :
    ((2 : ℝ) ^ (j + 1))⁻¹ ≤ ‖v - u‖ := by
  classical
  have hgap : ¬ ∀ i, |p.1 i - p.2 i| ≤ 1 := by
    unfold dyadicWhitneyPairs at hp
    exact (Finset.mem_filter.mp hp).2.2
  obtain ⟨i, hi⟩ := not_forall.mp hgap
  let D := (2 : ℝ) ^ (j + 1)
  have hD : 0 < D := by positivity
  obtain ⟨h₁, h₂⟩ := scaled_coordinate_bounds hu i
  obtain ⟨h₃, h₄⟩ := scaled_coordinate_bounds hv i
  have h : 1 ≤ |D * (v i - u i)| := by
    by_contra! H
    dsimp only [D] at H
    rw [mul_sub] at H
    obtain ⟨h₅, h₆⟩ := abs_lt.mp H
    have hl : (-2 : ℝ) < (p.1 i : ℝ) - (p.2 i : ℝ) := by linarith
    have hr : (p.1 i : ℝ) - (p.2 i : ℝ) < 2 := by linarith
    have hl' : (-2 : ℤ) < p.1 i - p.2 i := by exact_mod_cast hl
    have hr' : p.1 i - p.2 i < (2 : ℤ) := by exact_mod_cast hr
    exact hi (abs_le.mpr ⟨by omega, by omega⟩)
  rw [abs_mul, abs_of_pos hD] at h
  have H : D⁻¹ ≤ |v i - u i| := by
    rw [← one_div]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using h)
  refine H.trans ?_
  simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (v - u) i

/-- Localize an actual Whitney pair in the small parameter patch to a ball
of comparable radius. Coarse pairs use the origin as the center. -/
theorem dyadic_whitney_pair_localize {d j : ℕ} (hd : 1 ≤ d)
    {p : (Fin d → ℤ) × (Fin d → ℤ)} (hp : p ∈ dyadicWhitneyPairs d j)
    {A B : Set (Ambient d)} (hA : A ⊆ Metric.ball 0 (1 / 4))
    (hB : B ⊆ Metric.ball 0 (1 / 4))
    (hAp : A ⊆ dyadicParameterCell (j + 1) p.1)
    (hBp : B ⊆ dyadicParameterCell (j + 1) p.2)
    (hne : A.Nonempty) :
    ∃ (a : Ambient d) (r : ℝ), ‖a‖ ≤ 1 / 2 ∧ 0 < r ∧ r ≤ 1 / 2 ∧
      ((2 : ℝ) ^ (j + 1))⁻¹ ≤ r ∧ A ⊆ Metric.ball a r ∧ B ⊆ Metric.ball a r ∧
      (∀ u ∈ A, ∀ v ∈ B, (5 * (d : ℝ))⁻¹ * r ≤ ‖v - u‖) := by
  let h := ((2 : ℝ) ^ (j + 1))⁻¹
  let c := 5 * (d : ℝ)
  have hh : 0 < h := by positivity
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 < c := by dsimp [c]; positivity
  have hcoarse : h ≤ 1 / 2 := by
    have H : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ]
      nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) H
  have hcr : h ≤ c * h := by
    have H : (1 : ℝ) ≤ c := by dsimp [c]; linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right H hh.le
  have hsep (r : ℝ) (hr : r ≤ c * h) (u : Ambient d) (hu : u ∈ A)
      (v : Ambient d) (hv : v ∈ B) : c⁻¹ * r ≤ ‖v - u‖ := by
    have H := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hc.le)
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at H
    exact H.trans (dyadic_whitney_pair_distance_ge hp (hAp hu) (hBp hv))
  by_cases hfin : c * h ≤ 1 / 2
  · obtain ⟨a, ha⟩ := hne
    have ha' : ‖a‖ ≤ 1 / 2 := by
      have H : ‖a‖ < 1 / 4 := by simpa [Metric.mem_ball, dist_zero_right] using hA ha
      linarith
    have hstrict : (4 * (d : ℝ)) * h < c * h := by
      apply mul_lt_mul_of_pos_right _ hh
      dsimp [c]
      linarith
    refine ⟨a, c * h, ha', mul_pos hc hh, hfin, hcr, ?_, ?_, hsep _ le_rfl⟩
    · intro u hu
      rw [Metric.mem_ball, dist_eq_norm]
      exact (cell_distance_le hd (fun i => by simp) (hAp hu) (hAp ha)).trans_lt hstrict
    · intro v hv
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
      exact (cell_distance_le hd (dyadic_whitney_pair_index_gap hp) (hAp ha) (hBp hv)).trans_lt
        hstrict
  · refine ⟨0, 1 / 2, by simp, by norm_num, le_rfl, hcoarse, ?_, ?_, hsep _ (le_of_not_ge hfin)⟩
    · exact hA.trans (Metric.ball_subset_ball (by norm_num))
    · exact hB.trans (Metric.ball_subset_ball (by norm_num))

end RestrictionWork
