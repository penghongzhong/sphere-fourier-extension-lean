import RestrictionWork.GraphWhitneySummation
import RestrictionWork.GraphRestrictedKnappData

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

/-- The squared norm form of (L^2) almost orthogonality for an actual Whitney layer. -/
theorem graph_whitney_layer_eLpNorm_two_sq {d : ℕ} (j : ℕ) {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0)
    (hgs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) :
    eLpNorm (graphWhitneyLayer j φ f g) 2 volume ^ (2 : ℕ) ≤
      ((7 ^ d * 3 ^ d : ℕ) : ℝ≥0∞) *
        ∑ p ∈ dyadicWhitneyPairs d j,
          eLpNorm (graphWhitneyTerm j p φ f g) 2 volume ^ (2 : ℕ) := by
  have hterm p : Continuous (graphWhitneyTerm j p φ f g) :=
    (graph_extension_continuous
      (hfi.indicator (measurable_dyadic_parameter_cell _ _)).restrict hφ).mul
      (graph_extension_continuous
        (hgi.indicator (measurable_dyadic_parameter_cell _ _)).restrict hφ)
  have hL : Continuous (graphWhitneyLayer j φ f g) :=
    continuous_finsetSum _ fun p _ => hterm p
  have hpow (u : Ambient d × ℝ → ℂ) (hu : AEStronglyMeasurable u volume) :
      eLpNorm u 2 volume ^ (2 : ℕ) = ∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) := by
    simpa only [ENNReal.ofReal_ofNat, ENNReal.rpow_two] using
      OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral (p := 2) (by norm_num) hu
  simp_rw [hpow _ hL.aestronglyMeasurable, hpow _ (hterm _).aestronglyMeasurable]
  exact graph_whitney_layer_L2 j hφ hf hg hfi hgi hfs hgs hM

/-- Same-layer almost orthogonality in reciprocal coordinates, including (R=2). -/
theorem graph_whitney_layer_eLpNorm {d : ℕ} {y : ℝ} (hy₂ : 1 / 2 ≤ y) (hy₁ : y < 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ) {φ : Ambient d → ℝ},
      Measurable φ → ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g →
      Integrable f → Integrable g →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0) →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0) →
      ∀ {M : ℝ}, (∀ u, ‖g u‖ ≤ M) →
      eLpNorm (graphWhitneyLayer j φ f g) (ENNReal.ofReal y)⁻¹ volume ≤
        C * (∑ p ∈ dyadicWhitneyPairs d j,
          eLpNorm (graphWhitneyTerm j p φ f g) (ENNReal.ofReal y)⁻¹ volume ^ y⁻¹) ^ y := by
  rcases hy₂.eq_or_lt with he | hlt
  · subst y
    let K : ℝ≥0∞ := ((7 ^ d * 3 ^ d : ℕ) : ℝ≥0∞)
    refine ⟨K ^ (1 / 2 : ℝ), ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.natCast_ne_top _), ?_⟩
    intro j φ hφ f g hf hg hfi hgi hfs hgs M hM
    have hq : (ENNReal.ofReal (1 / 2))⁻¹ = 2 := by
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num
    have hhalf (x : ℝ≥0∞) : (x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = x := by
      rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num
    have h := ENNReal.rpow_le_rpow
      (graph_whitney_layer_eLpNorm_two_sq j hφ hf hg hfi hgi hfs hgs hM)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [hhalf, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
    simpa only [hq, inv_div, div_one, ENNReal.rpow_two, K] using h
  · have hy : 0 < y := by linarith
    have hR₁ : 1 < y⁻¹ := (one_lt_inv₀ hy).mpr hy₁
    have hR₂ : y⁻¹ < 2 := by
      rw [inv_lt_iff_one_lt_mul₀ hy]
      linarith
    obtain ⟨C, hC, H⟩ := graph_whitney_layer_eLpNorm_lt_two (d := d) hR₁ hR₂
    refine ⟨C, hC, ?_⟩
    intro j φ hφ f g hf hg hfi hgi hfs hgs M _
    rw [← ENNReal.ofReal_inv_of_pos hy]
    simpa only [one_div, inv_inv] using H j hφ hf hg hfi hgi hfs hgs


/-- The trivial output endpoint for a genuine product on the graph patch. -/
theorem graph_extension_product_eLpNorm_top_le_mass {d : ℕ} {A B : Set (Ambient d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {f g : Ambient d → ℂ} (hfi : Integrable f (patchMeasure d))
    (hgi : Integrable g (patchMeasure d))
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u)
    (hgb : ∀ u, ‖g u‖ ≤ B.indicator (fun _ => (1 : ℝ)) u) :
    eLpNorm (graphExtension f φ * graphExtension g φ) ⊤ volume ≤ volume A * volume B := by
  rw [eLpNorm_exponent_top ((graph_extension_continuous hfi hφ).mul
    (graph_extension_continuous hgi hφ)).aestronglyMeasurable]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact .of_forall fun z => by
    rw [Pi.mul_apply, enorm_mul]
    exact mul_le_mul' (graph_extension_enorm_le_restricted_mass hA hfb φ z)
      (graph_extension_enorm_le_restricted_mass hB hgb φ z)

end RestrictionWork
