import RestrictionWork.DyadicWhitneyPairLocalize
import RestrictionWork.DyadicWhitneyMass
import RestrictionWork.GraphWhitneyMoment
import RestrictionWork.ShiftedGraphRestrictedRescale

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

theorem norm_cell_indicator_le {d n : ℕ} (k : Fin d → ℤ) {A : Set (Ambient d)}
    {f : Ambient d → ℂ} (hf : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) :
    ∀ u, ‖(dyadicParameterCell n k).indicator f u‖ ≤
      (A ∩ dyadicParameterCell n k).indicator (fun _ => (1 : ℝ)) u := by
  intro u
  by_cases hu : u ∈ dyadicParameterCell n k
  · rw [indicator_of_mem hu]
    by_cases huA : u ∈ A
    · simpa [hu, huA] using hf u
    · simpa [huA] using hf u
  · simp [hu]

private theorem ofReal_fine_scale_pow (d j : ℕ) :
    ENNReal.ofReal ((((2 : ℝ) ^ (j + 1))⁻¹) ^ d) =
      ((2 : ℝ≥0∞)⁻¹ ^ d) * ((2 : ℝ≥0∞)⁻¹ ^ d) ^ j := by
  rw [ENNReal.ofReal_pow (by positivity), ← volume_dyadic_parameter_cell (j + 1) (0 : Fin d → ℤ),
    volume_dyadic_parameter_cell_at_whitney_level]

set_option maxHeartbeats 500000 in
/-- The actual Whitney terms satisfy the improved Knapp pair bound with
the exact dyadic scale factor. The fixed factor of one extra generation is
absorbed in the constant. -/
theorem spherical_graph_whitney_term_bound {d : ℕ} (hd : 2 ≤ d)
    {y : ℝ} (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ x : ℝ, knappProductInput d y < x ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
        ∀ {A : Set (Ambient d)}, MeasurableSet A → A ⊆ Metric.ball 0 (1 / 4) →
          ∀ {f : Ambient d → ℂ}, Measurable f →
            (∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
            ∀ (j : ℕ) {p : (Fin d → ℤ) × (Fin d → ℤ)}, p ∈ dyadicWhitneyPairs d j →
              eLpNorm (graphWhitneyTerm j p (sphericalGraphPhase δ) f f)
                  (ENNReal.ofReal y)⁻¹ volume ≤
                C * (((2 : ℝ≥0∞)⁻¹ ^ d) ^ j) ^ (-(2 * (x - knappProductInput d y))) *
                  dyadicWhitneyMass A j p ^ (2 * x) := by
  have hd₁ : 1 ≤ d := by omega
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hσ : 0 < (5 * (d : ℝ))⁻¹ := by positivity
  obtain ⟨x, hx, C, hC, H⟩ := shifted_graph_whitney_pair_bound hd hσ hy hyD
  have hk : 0 < knappProductInput d y := by
    have he := knapp_input_sub_diagonal (by omega : 0 < d) y
    have hp : 0 < ((d : ℝ) + 1) / d * ((d : ℝ) / ((d : ℝ) + 1) - y) :=
      mul_pos (by positivity) (sub_pos.mpr hyD)
    linarith
  have hx₀ : 0 ≤ x := (hk.trans hx).le
  let e := 2 * (x - knappProductInput d y)
  have he : 0 ≤ e := by dsimp [e]; linarith
  let b := (2 : ℝ≥0∞)⁻¹ ^ d
  have hb : b ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))
  have hbt : b ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))
  have hbf : b ^ (-e) < ⊤ := (ENNReal.rpow_ne_top_of_ne_zero hb hbt).lt_top
  refine ⟨x, hx, C * b ^ (-e), ENNReal.mul_lt_top hC hbf, ?_⟩
  intro δ hδ hδhalf A hA hAb f hf hfb j p hp
  let U := A ∩ dyadicParameterCell (j + 1) p.1
  let V := A ∩ dyadicParameterCell (j + 1) p.2
  let F := (dyadicParameterCell (j + 1) p.1).indicator f
  let G := (dyadicParameterCell (j + 1) p.2).indicator f
  have hU : MeasurableSet U := hA.inter (measurable_dyadic_parameter_cell _ _)
  have hV : MeasurableSet V := hA.inter (measurable_dyadic_parameter_cell _ _)
  have hFm : Measurable F := hf.indicator (measurable_dyadic_parameter_cell _ _)
  have hGm : Measurable G := hf.indicator (measurable_dyadic_parameter_cell _ _)
  have hFb := norm_cell_indicator_le (n := j + 1) p.1 hfb
  have hGb := norm_cell_indicator_le (n := j + 1) p.2 hfb
  by_cases hUne : U.Nonempty
  · obtain ⟨a, r, ha, hr, hrhalf, hle, hUr, hVr, hsep⟩ :=
      dyadic_whitney_pair_localize hd₁ hp (inter_subset_left.trans hAb)
        (inter_subset_left.trans hAb) inter_subset_right inter_subset_right hUne
    have hrad : b * b ^ j ≤ ENNReal.ofReal (r ^ d) := by
      rw [← ofReal_fine_scale_pow]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hle _)
    have hradpow : ENNReal.ofReal (r ^ d) ^ (-e) ≤ b ^ (-e) * (b ^ j) ^ (-e) := by
      rw [← ENNReal.mul_rpow_of_ne_top hbt (ENNReal.pow_ne_top hbt), ENNReal.rpow_neg,
        ENNReal.rpow_neg, ENNReal.inv_le_inv]
      exact ENNReal.rpow_le_rpow hrad he
    have hmass : (volume U * volume V) ^ x ≤ dyadicWhitneyMass A j p ^ (2 * x) := by
      calc
        _ ≤ (dyadicWhitneyMass A j p ^ (2 : ℕ)) ^ x :=
          ENNReal.rpow_le_rpow (dyadic_whitney_mass_prod_le A j p) hx₀
        _ = _ := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    calc
      _ ≤ C * ENNReal.ofReal (r ^ d) ^ (-e) * (volume U * volume V) ^ x :=
        H hδ hδhalf ha hr hrhalf hU hV hUr hVr hsep hFm hGm hFb hGb
      _ ≤ C * (b ^ (-e) * (b ^ j) ^ (-e)) * dyadicWhitneyMass A j p ^ (2 * x) :=
        mul_le_mul' (mul_le_mul' le_rfl hradpow) hmass
      _ = _ := by
        change C * (b ^ (-e) * (b ^ j) ^ (-e)) * _ = C * b ^ (-e) * (b ^ j) ^ (-e) * _
        simp only [mul_assoc]
  · have hF₀ : F = 0 := by
      funext u
      have H := hFb u
      rw [indicator_of_notMem (fun hu => hUne ⟨u, hu⟩)] at H
      exact norm_eq_zero.mp (le_antisymm H (norm_nonneg _))
    change eLpNorm (graphExtension F _ * graphExtension G _) _ _ ≤ _
    rw [hF₀]
    have hz : graphExtension (0 : Ambient d → ℂ) (sphericalGraphPhase δ) = 0 := by
      ext z
      simp [graphExtension, phaseExtension]
    rw [hz, zero_mul, eLpNorm_zero]
    exact zero_le

end RestrictionWork
