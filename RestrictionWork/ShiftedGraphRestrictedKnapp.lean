import RestrictionWork.ReciprocalLpInterpolation
import RestrictionWork.KnappInterpolationGeometry
import RestrictionWork.ShiftedGraphGlobalExtension
import RestrictionWork.ShiftedSphericalTransverseKnappGain

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace RestrictionWork

/-- A uniform restricted product estimate for the actual normalized spherical
graphs. The input and output coordinates are reciprocals of exponents. -/
def ShiftedGraphRestrictedProductBound (d : ℕ) (σ y x : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
    0 < r → r ≤ 1 / 2 → ∀ {A B : Set (Ambient d)}, MeasurableSet A → MeasurableSet B →
    A ⊆ Metric.ball (0 : Ambient d) 1 → B ⊆ Metric.ball (0 : Ambient d) 1 →
    (∀ u ∈ A, ∀ v ∈ B, σ ≤ ‖v - u‖) →
    ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g →
      (∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
      (∀ v, ‖g v‖ ≤ B.indicator (fun _ => (1 : ℝ)) v) →
      let φ := shiftedSphericalGraphPhase δ a r
      eLpNorm (graphExtension f φ * graphExtension g φ) (ENNReal.ofReal y)⁻¹ volume ≤
        C * (volume A * volume B) ^ x

private theorem patch_restricted_data_norm {d : ℕ} {A : Set (Ambient d)}
    (hA : MeasurableSet A) (hAb : A ⊆ Metric.ball (0 : Ambient d) 1)
    {f : Ambient d → ℂ} (hf : Measurable f)
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u)
    {x : ℝ} (hx : 0 < x) :
    MemLp f (ENNReal.ofReal x)⁻¹ (patchMeasure d) ∧
      eLpNorm f (ENNReal.ofReal x)⁻¹ (patchMeasure d) ≤ (volume A) ^ x := by
  let P := (ENNReal.ofReal x)⁻¹
  have hP0 : P ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hPt : P ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hx).ne'
  have hAv : volume A < ⊤ := (measure_mono hAb).trans_lt measure_ball_lt_top
  have hμA : patchMeasure d A = volume A := by
    rw [patchMeasure, Measure.restrict_apply hA, inter_eq_left.mpr hAb]
  have H := eLpNorm_mono_ae (p := P) (μ := patchMeasure d)
    (g := A.indicator (fun _ => (1 : ℝ))) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => (hfb u).trans (by
      rw [Real.norm_eq_abs]
      exact le_abs_self _))
  rw [eLpNorm_indicator_const hA.nullMeasurableSet hP0 hPt, enorm_one, one_mul,
    one_div, ENNReal.toReal_inv, inv_inv, ENNReal.toReal_ofReal hx.le, hμA] at H
  exact ⟨H.trans_lt (ENNReal.rpow_lt_top_of_nonneg hx.le hAv.ne), H⟩

private theorem graph_extension_enorm_le_one_norm {d : ℕ}
    {f : Ambient d → ℂ} (hf : Measurable f) (φ : Ambient d → ℝ) (z : Ambient d × ℝ) :
    ‖graphExtension f φ z‖ₑ ≤ eLpNorm f 1 (patchMeasure d) := by
  unfold graphExtension phaseExtension
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  refine (enorm_integral_le_lintegral_enorm _).trans_eq (lintegral_congr fun u => ?_)
  rw [enorm_mul, ← ofReal_norm (Complex.exp _), Complex.norm_exp_ofReal_mul_I,
    ENNReal.ofReal_one, mul_one]

private theorem shifted_graph_restricted_product_measurable {d : ℕ} {δ r : ℝ} {a : Ambient d}
    {A B : Set (Ambient d)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : A ⊆ Metric.ball (0 : Ambient d) 1) (hBb : B ⊆ Metric.ball (0 : Ambient d) 1)
    {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u)
    (hgb : ∀ v, ‖g v‖ ≤ B.indicator (fun _ => (1 : ℝ)) v) :
    AEStronglyMeasurable
      (graphExtension f (shiftedSphericalGraphPhase δ a r) *
        graphExtension g (shiftedSphericalGraphPhase δ a r)) volume := by
  have hf₁ : MemLp f 1 (patchMeasure d) := by
    simpa using (patch_restricted_data_norm hA hAb hf hfb zero_lt_one).1
  have hg₁ : MemLp g 1 (patchMeasure d) := by
    simpa using (patch_restricted_data_norm hB hBb hg hgb zero_lt_one).1
  have hφ : Measurable (shiftedSphericalGraphPhase δ a r) := by
    unfold shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  exact ((graph_extension_continuous (memLp_one_iff_integrable.mp hf₁) hφ).mul
    (graph_extension_continuous (memLp_one_iff_integrable.mp hg₁) hφ)).aestronglyMeasurable

private theorem shifted_graph_restricted_product_top (d : ℕ) (σ : ℝ) :
    ShiftedGraphRestrictedProductBound d σ 0 1 1 := by
  intro δ r a _ _ _ _ _ A B hA hB hAb hBb _ f g hf hg hfb hgb φ
  have hf₁ : eLpNorm f 1 (patchMeasure d) ≤ volume A := by
    simpa using (patch_restricted_data_norm hA hAb hf hfb zero_lt_one).2
  have hg₁ : eLpNorm g 1 (patchMeasure d) ≤ volume B := by
    simpa using (patch_restricted_data_norm hB hBb hg hgb zero_lt_one).2
  rw [ENNReal.ofReal_zero, ENNReal.inv_zero,
    eLpNorm_exponent_top (shifted_graph_restricted_product_measurable hA hB hAb hBb hf hg hfb hgb),
    ENNReal.rpow_one, one_mul]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact .of_forall fun z => by
    rw [Pi.mul_apply, enorm_mul]
    exact mul_le_mul' ((graph_extension_enorm_le_one_norm hf φ z).trans hf₁)
      ((graph_extension_enorm_le_one_norm hg φ z).trans hg₁)

private theorem shifted_graph_restricted_product_diagonal {d : ℕ} (hd : 1 ≤ d)
    (σ : ℝ) {y : ℝ} (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ShiftedGraphRestrictedProductBound d σ y (y / 2) C := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdiag : 2 * ((d : ℝ) + 1) / d < 2 / y := by
    apply (div_lt_div_iff₀ hd₀ hy).mpr
    have H := (lt_div_iff₀ (by positivity : 0 < (d : ℝ) + 1)).mp hyD
    nlinarith only [H]
  obtain ⟨C, hC, H⟩ := shifted_graph_global_diagonal_product hd hdiag
  refine ⟨C, hC.lt_top, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf A B hA hB hAb hBb _ f g hf hg hfb hgb φ
  have hy₂ : 0 < y / 2 := by positivity
  obtain ⟨hfP, hfN⟩ := patch_restricted_data_norm hA hAb hf hfb hy₂
  obtain ⟨hgP, hgN⟩ := patch_restricted_data_norm hB hBb hg hgb hy₂
  have hP : ENNReal.ofReal (2 / y) = (ENNReal.ofReal (y / 2))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hy₂]
    congr 1
    rw [inv_div]
  have hQ : ((ENNReal.ofReal (2 / y))⁻¹ + (ENNReal.ofReal (2 / y))⁻¹)⁻¹ =
      (ENNReal.ofReal y)⁻¹ := by
    rw [hP, inv_inv, ← ENNReal.ofReal_add hy₂.le hy₂.le, show y / 2 + y / 2 = y by ring]
  have H' := (H hδ hδhalf ha hr hrhalf f g (hP ▸ hfP) (hP ▸ hgP)).2
  rw [hQ, hP] at H'
  refine H'.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hy₂.le, ← mul_assoc]
  exact mul_le_mul' (mul_le_mul' le_rfl hfN) hgN

private theorem shifted_graph_restricted_product_mix {d : ℕ} {σ s t u v θ : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hθ : 0 < θ) (hθ₁ : θ < 1) {C D : ℝ≥0∞}
    (HC : ShiftedGraphRestrictedProductBound d σ s u C)
    (HD : ShiftedGraphRestrictedProductBound d σ t v D) :
    ShiftedGraphRestrictedProductBound d σ (θ * s + (1 - θ) * t)
      (θ * u + (1 - θ) * v) (C ^ θ * D ^ (1 - θ)) := by
  intro δ r a hδ hδhalf ha hr hrhalf A B hA hB hAb hBb hsep f g hf hg hfb hgb φ
  have hF := shifted_graph_restricted_product_measurable (δ := δ) (r := r) (a := a)
    hA hB hAb hBb hf hg hfb hgb
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hC := HC hδ hδhalf ha hr hrhalf hA hB hAb hBb hsep hf hg hfb hgb
  have hD := HD hδ hδhalf ha hr hrhalf hA hB hAb hBb hsep hf hg hfb hgb
  refine (eLpNorm_reciprocal_interpolate hF hs ht hθ hθ₁).trans
    ((mul_le_mul' (ENNReal.rpow_le_rpow hC hθ.le) (ENNReal.rpow_le_rpow hD hθ')).trans_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ',
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hθ.le hu) (mul_nonneg hθ' hv)]
  ac_rfl

set_option maxHeartbeats 750000 in
/-- The actual separated spherical graph has a strict restricted input gain
at every finite output on the allowed Knapp line. -/
theorem shifted_graph_restricted_knapp_gain {d : ℕ} (hd : 2 ≤ d)
    {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ x : ℝ, knappProductInput d y < x ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ShiftedGraphRestrictedProductBound d σ y x C := by
  obtain ⟨x₀, hx₀, _, hgap, C, hC, HC⟩ := shifted_graph_transverse_knapp_gain hd hσ
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hx : knappProductInput d (1 / 2) < x₀ := by
    have H := (div_lt_iff₀ (by positivity : 0 < (d : ℝ) + 2)).mp
      (show (2 * (d : ℝ) * (1 - x₀)) / ((d : ℝ) + 2) < 1 / 2 by
        simpa only [div_mul_eq_mul_div] using hgap)
    have H' : 1 - x₀ < (1 / 2 * ((d : ℝ) + 2)) / (2 * d) :=
      (lt_div_iff₀ (by positivity : 0 < 2 * (d : ℝ))).mpr (by
        rwa [mul_comm (1 - x₀)])
    unfold knappProductInput
    have he : ((d : ℝ) + 2) / (2 * d) * (1 / 2) =
        (1 / 2 * ((d : ℝ) + 2)) / (2 * d) := by ring
    linarith
  have htwo : (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ = 2 := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have H₂ : ShiftedGraphRestrictedProductBound d σ (1 / 2) x₀ C := by
    intro δ r a hδ hδhalf ha hr hrhalf A B hA hB hAb hBb hsep f g hf hg hfb hgb φ
    rw [htwo]
    exact HC hδ hδhalf ha hr hrhalf hA hB hAb hBb hsep hf hg hfb hgb
  rcases lt_trichotomy y (1 / 2) with hy₂ | rfl | hy₂
  · let θ := 2 * y
    have hθ : 0 < θ := by dsimp [θ]; positivity
    have hθ₁ : θ < 1 := by dsimp [θ]; linarith
    have hmix : ShiftedGraphRestrictedProductBound d σ (θ * (1 / 2) + (1 - θ) * 0)
        (θ * x₀ + (1 - θ) * 1) (C ^ θ * (1 : ℝ≥0∞) ^ (1 - θ)) :=
      shifted_graph_restricted_product_mix (by norm_num) le_rfl hx₀.le zero_le_one
        hθ hθ₁ H₂ (shifted_graph_restricted_product_top d σ)
    have hY : θ * (1 / 2) + (1 - θ) * 0 = y := by unfold θ; ring
    rw [hY, mul_one, ENNReal.one_rpow, mul_one] at hmix
    refine ⟨θ * x₀ + (1 - θ), ?_, C ^ θ, ENNReal.rpow_lt_top_of_nonneg hθ.le hC.ne, hmix⟩
    have H := mul_lt_mul_of_pos_left hx hθ
    unfold knappProductInput θ at *
    nlinarith only [H]
  · exact ⟨x₀, hx, C, hC, H₂⟩
  · obtain ⟨θ, z, hθ, hθ₁, hz, hzD, hY, hX⟩ := knapp_diagonal_interpolation hd hx hy₂ hyD
    obtain ⟨D, hD, HD⟩ := shifted_graph_restricted_product_diagonal (by omega : 1 ≤ d) σ hz hzD
    have hmix : ShiftedGraphRestrictedProductBound d σ (θ * (1 / 2) + (1 - θ) * z)
        (θ * x₀ + (1 - θ) * (z / 2)) (C ^ θ * D ^ (1 - θ)) :=
      shifted_graph_restricted_product_mix (by norm_num) hz.le hx₀.le
        (by positivity : 0 ≤ z / 2) hθ hθ₁ H₂ HD
    rw [hY] at hmix
    refine ⟨_, hX, _, ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hθ.le hC.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by linarith) hD.ne), hmix⟩

/-- A single finite constant works on an open interval of input reciprocals
around the Knapp line, with the bilinear output exponent fixed. -/
theorem shifted_graph_restricted_knapp_neighborhood {d : ℕ} (hd : 2 ≤ d)
    {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ x : ℝ, |x - knappProductInput d y| < ε →
        ShiftedGraphRestrictedProductBound d σ y x C := by
  obtain ⟨x₁, hx₁, C, hC, HC⟩ := shifted_graph_restricted_knapp_gain hd hσ hy hyD
  let k := knappProductInput d y
  have hk : 0 < k := by
    have H := knapp_input_sub_diagonal (by omega : 0 < d) y
    have hdiff : 0 < (d : ℝ) / ((d : ℝ) + 1) - y := sub_pos.mpr hyD
    have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have H' : 0 < ((d : ℝ) + 1) / d * ((d : ℝ) / ((d : ℝ) + 1) - y) :=
      mul_pos (by positivity) hdiff
    dsimp only [k]
    linarith
  let ε := min k (x₁ - k) / 2
  have hε : 0 < ε := half_pos (lt_min hk (sub_pos.mpr hx₁))
  let V := volume (Metric.ball (0 : Ambient d) 1)
  let W := max (1 : ℝ≥0∞) (V * V)
  have hW : W < ⊤ := max_lt ENNReal.one_lt_top (ENNReal.mul_lt_top measure_ball_lt_top measure_ball_lt_top)
  have hx₁₀ : 0 ≤ x₁ := (hk.trans hx₁).le
  refine ⟨ε, hε, C * W ^ x₁, ENNReal.mul_lt_top hC
    (ENNReal.rpow_lt_top_of_nonneg hx₁₀ hW.ne), ?_⟩
  intro x hx δ r a hδ hδhalf ha hr hrhalf A B hA hB hAb hBb hsep f g hf hg hfb hgb φ
  have hx' := abs_lt.mp hx
  have hεk : ε ≤ k / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hε₁ : ε ≤ (x₁ - k) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hx₀ : 0 ≤ x := by linarith [hx'.1]
  have hxx : x ≤ x₁ := by linarith [hx'.2]
  let m : ℝ≥0∞ := volume A * volume B
  have hm : m ≤ W := (mul_le_mul' (measure_mono hAb) (measure_mono hBb)).trans (le_max_right _ _)
  have hpow : m ^ (x₁ - x) ≤ W ^ x₁ :=
    (ENNReal.rpow_le_rpow hm (sub_nonneg.mpr hxx)).trans
      (ENNReal.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith))
  refine (HC hδ hδhalf ha hr hrhalf hA hB hAb hBb hsep hf hg hfb hgb).trans ?_
  change C * m ^ x₁ ≤ C * W ^ x₁ * m ^ x
  have he := ENNReal.rpow_add_of_nonneg (x := m) x (x₁ - x) hx₀ (sub_nonneg.mpr hxx)
  rw [show x + (x₁ - x) = x₁ by ring] at he
  rw [he]
  calc
    _ ≤ C * (m ^ x * W ^ x₁) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hpow)
    _ = _ := by ac_rfl

end RestrictionWork
