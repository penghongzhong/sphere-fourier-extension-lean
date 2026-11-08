import RestrictionWork.GraphRebaseProductNorm
import RestrictionWork.ShiftedGraphRestrictedKnapp

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

private theorem normalized_restricted_data {d : ℕ} {a : Ambient d} {r : ℝ} (hr : 0 < r)
    {A : Set (Ambient d)} (hA : MeasurableSet A) (hAr : A ⊆ Metric.ball a r)
    {f : Ambient d → ℂ} (hf : Measurable f)
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) :
    let L := graphParameterMap a r
    let S := L ⁻¹' A
    let F := f ∘ L
    MeasurableSet S ∧ S ⊆ Metric.ball 0 1 ∧ Measurable F ∧
      (∀ u, ‖F u‖ ≤ S.indicator (fun _ => (1 : ℝ)) u) ∧
      MemLp F 1 (patchMeasure d) ∧ graphRebaseInput a r F = f ∧
      volume S = (ENNReal.ofReal (r ^ d))⁻¹ * volume A := by
  intro L S F
  have hL : MeasurableEmbedding L := graph_parameter_embedding a hr
  have hS : MeasurableSet S := hA.preimage hL.measurable
  have hSb : S ⊆ Metric.ball 0 1 := by
    intro u hu
    have H := Metric.mem_ball.mp (hAr hu)
    change dist (a + r • u) a < r at H
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at H
    rw [Metric.mem_ball, dist_zero_right]
    have H' : ‖u‖ < r / r := (lt_div_iff₀ hr).mpr (by rwa [mul_comm ‖u‖ r])
    simpa only [div_self hr.ne'] using H'
  have hFm : Measurable F := hf.comp hL.measurable
  have hFb (u : Ambient d) : ‖F u‖ ≤ S.indicator (fun _ => (1 : ℝ)) u := by
    by_cases hu : u ∈ S
    · simpa only [F, Function.comp_apply, indicator_of_mem hu,
        indicator_of_mem (show L u ∈ A from hu)] using hfb (L u)
    · simpa only [F, Function.comp_apply, indicator_of_notMem hu,
        indicator_of_notMem (show L u ∉ A from hu)] using hfb (L u)
  let : IsFiniteMeasure (patchMeasure d) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hF₁ : MemLp F 1 (patchMeasure d) := by
    refine MemLp.of_bound hFm.aestronglyMeasurable 1 (.of_forall fun u => (hFb u).trans ?_)
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu]
      norm_num
  have hFid : graphRebaseInput a r F = f := by
    funext v
    by_cases hv : v ∈ Metric.ball a r
    · have he : L (graphParameterInverse a r v) = v := by
        simp [L, graphParameterMap, graphParameterInverse, smul_smul, hr.ne']
      rw [graphRebaseInput, indicator_of_mem hv]
      change f (L (graphParameterInverse a r v)) = f v
      rw [he]
    · have hvA : v ∉ A := fun H => hv (hAr H)
      have hb := hfb v
      rw [indicator_of_notMem hvA] at hb
      rw [graphRebaseInput, indicator_of_notMem hv,
        norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))]
  have hmass := congrArg (fun μ : Measure (Ambient d) => μ A)
    (graph_parameter_map_measure a hr)
  change ((patchMeasure d).map L) A =
    ((ENNReal.ofReal (r ^ d))⁻¹ • volume.restrict (Metric.ball a r)) A at hmass
  rw [Measure.map_apply hL.measurable hA, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, inter_eq_left.mpr hAr] at hmass
  change patchMeasure d S = _ at hmass
  rw [patchMeasure, Measure.restrict_apply hS, inter_eq_left.mpr hSb] at hmass
  exact ⟨hS, hSb, hFm, hFb, hF₁, hFid, hmass⟩

set_option maxHeartbeats 850000 in
/-- Actual separated pieces inside a ball of radius r satisfy the restricted
product estimate with the exact scale factor on the Knapp line. -/
theorem shifted_graph_whitney_pair_bound {d : ℕ} (hd : 2 ≤ d)
    {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ x : ℝ, knappProductInput d y < x ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ {A B : Set (Ambient d)}, MeasurableSet A → MeasurableSet B →
        A ⊆ Metric.ball a r → B ⊆ Metric.ball a r →
        (∀ u ∈ A, ∀ v ∈ B, σ * r ≤ ‖v - u‖) →
        ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g →
          (∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
          (∀ v, ‖g v‖ ≤ B.indicator (fun _ => (1 : ℝ)) v) →
          let φ := sphericalGraphPhase δ (d := d)
          eLpNorm (graphExtension f φ * graphExtension g φ) (ENNReal.ofReal y)⁻¹ volume ≤
            C * ENNReal.ofReal (r ^ d) ^ (-(2 * (x - knappProductInput d y))) *
              (volume A * volume B) ^ x := by
  obtain ⟨x, hx, C, hC, H⟩ := shifted_graph_restricted_knapp_gain hd hσ hy hyD
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hx₀ : 0 ≤ x := by
    have he := knapp_input_sub_diagonal (by omega : 0 < d) y
    have hpos : 0 < ((d : ℝ) + 1) / d * ((d : ℝ) / ((d : ℝ) + 1) - y) :=
      mul_pos (by positivity) (sub_pos.mpr hyD)
    linarith
  refine ⟨x, hx, C, hC, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf A B hA hB hAr hBr hsep f g hf hg hfb hgb φ
  let L := graphParameterMap a r
  let S := L ⁻¹' A
  let T := L ⁻¹' B
  let F := f ∘ L
  let G := g ∘ L
  have hF : MeasurableSet S ∧ S ⊆ Metric.ball 0 1 ∧ Measurable F ∧
      (∀ u, ‖F u‖ ≤ S.indicator (fun _ => (1 : ℝ)) u) ∧
      MemLp F 1 (patchMeasure d) ∧ graphRebaseInput a r F = f ∧
      volume S = (ENNReal.ofReal (r ^ d))⁻¹ * volume A :=
    normalized_restricted_data hr hA hAr hf hfb
  have hG : MeasurableSet T ∧ T ⊆ Metric.ball 0 1 ∧ Measurable G ∧
      (∀ u, ‖G u‖ ≤ T.indicator (fun _ => (1 : ℝ)) u) ∧
      MemLp G 1 (patchMeasure d) ∧ graphRebaseInput a r G = g ∧
      volume T = (ENNReal.ofReal (r ^ d))⁻¹ * volume B :=
    normalized_restricted_data hr hB hBr hg hgb
  obtain ⟨hS, hSb, hFm, hFb, hF₁, hFid, hSm⟩ := hF
  obtain ⟨hT, hTb, hGm, hGb, hG₁, hGid, hTm⟩ := hG
  have hST : ∀ u ∈ S, ∀ v ∈ T, σ ≤ ‖v - u‖ := by
    intro u hu v hv
    have he : L v - L u = r • (v - u) := by
      simp [L, graphParameterMap, smul_sub]
    have H' := hsep (L u) hu (L v) hv
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_comm r] at H'
    have H'' : σ ≤ (‖v - u‖ * r) / r := (le_div_iff₀ hr).mpr H'
    simpa only [mul_div_cancel_right₀ _ hr.ne'] using H''
  have hφ : Measurable φ := by unfold φ sphericalGraphPhase sphericalPhase; fun_prop
  let l := sphericalGraphSlope δ a
  let ψ := shiftedSphericalGraphPhase δ a r
  let q := (ENNReal.ofReal y)⁻¹
  let R := ENNReal.ofReal r
  let Lmass := ENNReal.ofReal (r ^ d)
  let J := ENNReal.ofReal (r ^ (d + 2))
  let c := ENNReal.ofReal (r ^ d * r ^ d)
  let m := volume A * volume B
  have htransfer := graph_rebase_product_norm_transfer hφ (l := l) hr ha hrhalf hy.le hF₁ hG₁
  rw [hFid, hGid] at htransfer
  change c * eLpNorm (graphExtension F ψ * graphExtension G ψ) q volume =
    J ^ y * eLpNorm (graphExtension f φ * graphExtension g φ) q volume at htransfer
  have hJ₀ : 0 < J := ENNReal.ofReal_pos.mpr (pow_pos hr _)
  have hJt : J ≠ ⊤ := ENNReal.ofReal_ne_top
  have hJy₀ := (ENNReal.rpow_pos_of_nonneg hJ₀ hy.le).ne'
  have hJyt := (ENNReal.rpow_lt_top_of_nonneg hy.le hJt).ne
  have hR₀ : R ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hRt : R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hMass : Lmass = R ^ (d : ℝ) := by
    simp only [Lmass, R, ENNReal.rpow_natCast, ENNReal.ofReal_pow hr.le]
  have hJ : (J ^ y)⁻¹ = R ^ (-(((d : ℝ) + 2) * y)) := by
    dsimp only [J, R]
    rw [ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_neg, Nat.cast_add, Nat.cast_ofNat]
  have hc : c = R ^ ((d : ℝ) + d) := by
    dsimp only [c]
    rw [ENNReal.ofReal_mul (pow_nonneg hr.le _), ENNReal.rpow_add _ _ hR₀ hRt, ← hMass]
  have hMassPower : (Lmass⁻¹ * Lmass⁻¹) ^ x = R ^ (-((d : ℝ) + d) * x) := by
    rw [hMass, ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hR₀ hRt, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hscale : (J ^ y)⁻¹ * c * (Lmass⁻¹ * Lmass⁻¹) ^ x =
      Lmass ^ (-(2 * (x - knappProductInput d y))) := by
    rw [hJ, hc, hMassPower, hMass, ← ENNReal.rpow_add _ _ hR₀ hRt,
      ← ENNReal.rpow_add _ _ hR₀ hRt, ← ENNReal.rpow_mul]
    congr 1
    unfold knappProductInput
    field_simp [hd₀.ne']
    ring
  have hm : volume S * volume T = (Lmass⁻¹ * Lmass⁻¹) * m := by
    rw [hSm, hTm]
    unfold Lmass m
    ac_rfl
  change eLpNorm (graphExtension f φ * graphExtension g φ) q volume ≤
    C * Lmass ^ (-(2 * (x - knappProductInput d y))) * m ^ x
  calc
    _ = (J ^ y)⁻¹ * (J ^ y * eLpNorm (graphExtension f φ * graphExtension g φ) q volume) := by
      rw [ENNReal.inv_mul_cancel_left hJy₀ hJyt]
    _ = (J ^ y)⁻¹ * (c * eLpNorm (graphExtension F ψ * graphExtension G ψ) q volume) := by
      rw [← htransfer]
    _ ≤ (J ^ y)⁻¹ * (c * (C * (volume S * volume T) ^ x)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl
        (H hδ hδhalf ha hr hrhalf hS hT hSb hTb hST hFm hGm hFb hGb))
    _ = _ := by
      rw [hm, ENNReal.mul_rpow_of_nonneg _ _ hx₀, ← hscale]
      ac_rfl

end RestrictionWork
