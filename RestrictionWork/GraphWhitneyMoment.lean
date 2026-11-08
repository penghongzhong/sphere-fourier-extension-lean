import RestrictionWork.GraphWhitneyProjectionInterpolation

set_option autoImplicit false
noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal

namespace RestrictionWork

/-- One product in a Whitney layer in the physical spacetime coordinates. -/
def graphWhitneyTerm {d : ℕ} (j : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ))
    (φ : Ambient d → ℝ) (f g : Ambient d → ℂ) (z : Ambient d × ℝ) : ℂ :=
  graphExtension ((dyadicParameterCell (j + 1) p.1).indicator f) φ z *
    graphExtension ((dyadicParameterCell (j + 1) p.2).indicator g) φ z

private theorem lintegral_horizontal_dilate {d : ℕ} {K : Ambient d → ℝ≥0∞}
    (hK : Measurable K) {a : ℝ} (ha : a ≠ 0) :
    (∫⁻ x : Ambient d, K (a • x)) =
      ENNReal.ofReal |(a ^ d)⁻¹| * ∫⁻ x, K x := by
  rw [← lintegral_map hK (measurable_const_smul a), Measure.map_addHaar_smul volume ha,
    lintegral_smul_measure, smul_eq_mul]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin]

set_option maxHeartbeats 1200000 in
/-- Uniform horizontal R-moment inequality for the actual Whitney terms
at each time, with 1 < R < 2. -/
theorem graph_whitney_layer_horizontal_moment_lt_two {d : ℕ} {R : ℝ}
    (hR₁ : 1 < R) (hR₂ : R < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ) {φ : Ambient d → ℝ},
      Measurable φ → ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g →
      Integrable f → Integrable g →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0) →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0) → ∀ t : ℝ,
      (∫⁻ x, ‖graphWhitneyLayer j φ f g (x, t)‖ₑ ^ R) ≤
        C * ∑ p ∈ dyadicWhitneyPairs d j,
          ∫⁻ x, ‖graphWhitneyTerm j p φ f g (x, t)‖ₑ ^ R := by
  obtain ⟨C, hC, H⟩ := graph_whitney_projection_moment_lt_two (d := d) hR₁ hR₂
  refine ⟨C, hC, ?_⟩
  intro j φ hφ f g hf hg hfi hgi hfs hgs t
  let J := dyadicWhitneyPairs d j
  let a := (2 * Real.pi)⁻¹
  let A := ENNReal.ofReal |(a ^ d)⁻¹|
  let F (p : (Fin d → ℤ) × (Fin d → ℤ)) := (dyadicParameterCell (j + 1) p.1).indicator f
  let G (p : (Fin d → ℤ) × (Fin d → ℤ)) := (dyadicParameterCell (j + 1) p.2).indicator g
  let K (p : (Fin d → ℤ) × (Fin d → ℤ)) := graphProductConvolution φ (F p) (G p) t
  let U (p : (Fin d → ℤ) × (Fin d → ℤ)) := 𝓕⁻ (K p)
  have ha : a ≠ 0 := by unfold a; positivity
  have hF p : Measurable (F p) := hf.indicator (measurable_dyadic_parameter_cell _ _)
  have hG p : Measurable (G p) := hg.indicator (measurable_dyadic_parameter_cell _ _)
  have hFi p : Integrable (F p) := hfi.indicator (measurable_dyadic_parameter_cell _ _)
  have hGi p : Integrable (G p) := hgi.indicator (measurable_dyadic_parameter_cell _ _)
  have hFs p u (hu : u ∉ Metric.ball (0 : Ambient d) 1) : F p u = 0 := by simp [F, hfs u hu]
  have hGs p u (hu : u ∉ Metric.ball (0 : Ambient d) 1) : G p u = 0 := by simp [G, hgs u hu]
  have hKi p : Integrable (K p) :=
    graph_product_convolution_integrable hφ (hF p) (hG p) (hFi p) (hGi p) t
  have hU p : Continuous (U p) :=
    OAI.Analysis.Fourier.BochnerRiesz.continuous_fourierInv_of_integrable (hKi p)
  have hUb p : ∃ M : ℝ, ∀ x, ‖U p x‖ ≤ M := by
    refine ⟨∫ s, ‖K p s‖, fun x => ?_⟩
    change ‖(𝓕⁻ (K p)) x‖ ≤ _
    rw [Real.fourierInv_eq']
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hterm p x : graphWhitneyTerm j p φ f g (x, t) = U p (a • x) := by
    change graphExtension (F p) φ (x, t) * graphExtension (G p) φ (x, t) =
      (𝓕⁻ (K p)) (a • x)
    rw [graph_extension_product_eq_fourier hφ (hF p) (hG p) (hFi p) (hGi p) (hFs p) (hGs p) x t,
      Real.fourierInv_eq_fourier_neg, ← neg_smul]
    simp only [a, ← inv_neg, neg_mul]
    rfl
  have hrepro p :
      OAI.Analysis.Fourier.WavePackets.complexConvolution
        (𝓕⁻ (graphWhitneyCutoff j p)) (U p) volume = U p :=
    graph_whitney_cutoff_reproduces j p hφ hf hg hfi hgi t
  have hlayer x : graphWhitneyLayer j φ f g (x, t) = graphWhitneyProjection j U (a • x) := by
    unfold graphWhitneyLayer graphWhitneyProjection
    apply Finset.sum_congr rfl
    intro p _
    rw [hrepro]
    exact hterm p x
  have hP := graph_whitney_projection_measurable j (fun p _ => (hU p).measurable)
  simp_rw [hterm, hlayer, lintegral_horizontal_dilate (hP.enorm.pow_const R) ha]
  have hpiece p :
      (∫⁻ x : Ambient d, ‖U p (a • x)‖ₑ ^ R) = A * ∫⁻ x, ‖U p x‖ₑ ^ R :=
    lintegral_horizontal_dilate ((hU p).measurable.enorm.pow_const R) ha
  simp_rw [hpiece, ← Finset.mul_sum]
  exact (mul_le_mul' (a := A) (b := A) le_rfl
    (H j U (fun p _ => (hU p).measurable) (fun p _ => hUb p))).trans_eq (by ac_rfl)

set_option maxHeartbeats 1000000 in
/-- Spacetime L^R almost orthogonality of the actual Whitney layer
in the range 1 < R < 2. -/
theorem graph_whitney_layer_moment_lt_two {d : ℕ} {R : ℝ}
    (hR₁ : 1 < R) (hR₂ : R < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ) {φ : Ambient d → ℝ},
      Measurable φ → ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g →
      Integrable f → Integrable g →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0) →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0) →
      (∫⁻ z, ‖graphWhitneyLayer j φ f g z‖ₑ ^ R) ≤
        C * ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ z, ‖graphWhitneyTerm j p φ f g z‖ₑ ^ R := by
  obtain ⟨C, hC, H⟩ := graph_whitney_layer_horizontal_moment_lt_two (d := d) hR₁ hR₂
  refine ⟨C, hC, ?_⟩
  intro j φ hφ f g hf hg hfi hgi hfs hgs
  let J := dyadicWhitneyPairs d j
  let P p := graphWhitneyTerm j p φ f g
  have hP p : Continuous (P p) := by
    refine (graph_extension_continuous ?_ hφ).mul (graph_extension_continuous ?_ hφ)
    · exact (hfi.indicator (measurable_dyadic_parameter_cell _ _)).restrict
    · exact (hgi.indicator (measurable_dyadic_parameter_cell _ _)).restrict
  have hL : Continuous (graphWhitneyLayer j φ f g) := continuous_finsetSum J (fun p _ => hP p)
  change (∫⁻ z : Ambient d × ℝ, ‖graphWhitneyLayer j φ f g z‖ₑ ^ R) ≤
    C * ∑ p ∈ J, ∫⁻ z : Ambient d × ℝ, ‖P p z‖ₑ ^ R
  conv_lhs => rw [Measure.volume_eq_prod, lintegral_prod_symm' _ (hL.measurable.enorm.pow_const R)]
  have hterm p : (∫⁻ z : Ambient d × ℝ, ‖P p z‖ₑ ^ R) =
      ∫⁻ t : ℝ, ∫⁻ x : Ambient d, ‖P p (x, t)‖ₑ ^ R := by
    rw [Measure.volume_eq_prod, lintegral_prod_symm' _ ((hP p).measurable.enorm.pow_const R)]
  simp_rw [hterm]
  have hm p : Measurable (fun t : ℝ => ∫⁻ x : Ambient d, ‖P p (x, t)‖ₑ ^ R) :=
    ((hP p).measurable.enorm.pow_const R).lintegral_prod_left'
  rw [← lintegral_finsetSum J (fun p _ => hm p), ← lintegral_const_mul' C _ hC.ne]
  exact lintegral_mono (H j hφ hf hg hfi hgi hfs hgs)

end RestrictionWork
