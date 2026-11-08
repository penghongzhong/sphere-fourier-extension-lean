import RestrictionWork.GraphWhitneyExpansion
import RestrictionWork.GraphWhitneyFrequency
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace RestrictionWork

private theorem square_norm_finset_sum_le {ι : Type*} (J : Finset ι) (C : ι → ℂ) :
    ‖∑ p ∈ J, C p‖ₑ ^ (2 : ℕ) ≤ (J.card : ℝ≥0∞) * ∑ p ∈ J, ‖C p‖ₑ ^ (2 : ℕ) := by
  have h : ‖∑ p ∈ J, C p‖ ^ (2 : ℕ) ≤ (J.card : ℝ) * ∑ p ∈ J, ‖C p‖ ^ (2 : ℕ) := by
    calc
      _ ≤ (∑ p ∈ J, ‖C p‖) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
      _ ≤ _ := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) (fun p => ‖C p‖)
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at h'
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_natCast] using h'


theorem dyadic_whitney_frequency_square_sum_le {d : ℕ} (j b : ℕ)
    (C : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℂ)
    (hC : ∀ p ∈ dyadicWhitneyPairs d j, Function.support (C p) ⊆ dyadicPairFrequency j b p)
    (s : Ambient d) :
    ‖∑ p ∈ dyadicWhitneyPairs d j, C p s‖ₑ ^ (2 : ℕ) ≤
      ((7 ^ d * (2 * b + 1) ^ d : ℕ) : ℝ≥0∞) * ∑ p ∈ dyadicWhitneyPairs d j, ‖C p s‖ₑ ^ (2 : ℕ) := by
  classical
  let J := dyadicWhitneyPairs d j
  let W := J.filter fun p => s ∈ dyadicPairFrequency j b p
  have hs : ∑ p ∈ W, C p s = ∑ p ∈ J, C p s := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hp, hC p hp hne⟩)
  have hc : W.card ≤ 7 ^ d * (2 * b + 1) ^ d := by
    simpa only using card_dyadic_whitney_frequency_overlap j b s
  rw [← hs]
  apply (square_norm_finset_sum_le W (fun p => C p s)).trans
  exact mul_le_mul' (by exact_mod_cast hc)
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))

theorem horizontal_fourier_finset_sum {d : ℕ} {ι : Type*} (J : Finset ι)
    {C : ι → Ambient d → ℂ} (hC : ∀ p ∈ J, Integrable (C p)) (x : Ambient d) :
    (𝓕 (fun s => ∑ p ∈ J, C p s)) x = ∑ p ∈ J, (𝓕 (C p)) x := by
  simp only [Real.fourier_eq', Finset.smul_sum]
  apply integral_finsetSum
  intro p hp
  have hm : Measurable (fun s : Ambient d =>
      Complex.exp ((↑(-2 * Real.pi * ⟪s, x⟫) : ℂ) * Complex.I)) := by fun_prop
  refine (hC p hp).mono (hm.aestronglyMeasurable.smul (hC p hp).aestronglyMeasurable) ?_
  filter_upwards [] with s
  simp only [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

set_option maxHeartbeats 1000000 in
/-- Horizontal L² almost orthogonality for the genuine Whitney layer at
each physical time. -/
theorem graph_whitney_layer_horizontal_L2 {d : ℕ} (j : ℕ) {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0)
    (hgs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) (t : ℝ) :
    (∫⁻ x : Ambient d, ‖graphWhitneyLayer j φ f g (x, t)‖ₑ ^ (2 : ℕ)) ≤
      ((7 ^ d * 3 ^ d : ℕ) : ℝ≥0∞) *
        ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x : Ambient d,
          ‖graphExtension ((dyadicParameterCell (j + 1) p.1).indicator f) φ (x, t) *
            graphExtension ((dyadicParameterCell (j + 1) p.2).indicator g) φ (x, t)‖ₑ ^ (2 : ℕ) := by
  let J := dyadicWhitneyPairs d j
  let F (p : (Fin d → ℤ) × (Fin d → ℤ)) := (dyadicParameterCell (j + 1) p.1).indicator f
  let G (p : (Fin d → ℤ) × (Fin d → ℤ)) := (dyadicParameterCell (j + 1) p.2).indicator g
  let C (p : (Fin d → ℤ) × (Fin d → ℤ)) := graphProductConvolution φ (F p) (G p) t
  let K := ((7 ^ d * 3 ^ d : ℕ) : ℝ≥0∞)
  let A := ENNReal.ofReal ((2 * Real.pi) ^ d)
  have hF p : Measurable (F p) := hf.indicator (measurable_dyadic_parameter_cell _ _)
  have hG p : Measurable (G p) := hg.indicator (measurable_dyadic_parameter_cell _ _)
  have hFi p : Integrable (F p) := hfi.indicator (measurable_dyadic_parameter_cell _ _)
  have hGi p : Integrable (G p) := hgi.indicator (measurable_dyadic_parameter_cell _ _)
  have hFs p u (hu : u ∉ Metric.ball (0 : Ambient d) 1) : F p u = 0 := by simp [F, hfs u hu]
  have hGs p u (hu : u ∉ Metric.ball (0 : Ambient d) 1) : G p u = 0 := by simp [G, hgs u hu]
  have hGb p u : ‖G p u‖ ≤ M := by
    by_cases hu : u ∈ dyadicParameterCell (j + 1) p.2
    · simpa [G, hu] using hM u
    · simp only [G, indicator_of_notMem hu, norm_zero]
      exact (norm_nonneg (g u)).trans (hM u)
  have hCi p : Integrable (C p) :=
    graph_product_convolution_integrable hφ (hF p) (hG p) (hFi p) (hGi p) t
  have hC₂ p : MemLp (C p) 2 :=
    graph_product_convolution_memLp_two hφ (hF p) (hG p) (hFi p) (hGi p) (hGb p) t
  have hprod p x : graphExtension (F p) φ (x, t) * graphExtension (G p) φ (x, t) =
      (𝓕 (C p)) ((-2 * Real.pi)⁻¹ • x) :=
    graph_extension_product_eq_fourier hφ (hF p) (hG p) (hFi p) (hGi p) (hFs p) (hGs p) x t
  have hsum x : graphWhitneyLayer j φ f g (x, t) =
      (𝓕 (fun s => ∑ p ∈ J, C p s)) ((-2 * Real.pi)⁻¹ • x) := by
    rw [horizontal_fourier_finset_sum J (fun p _ => hCi p)]
    exact Finset.sum_congr rfl (fun p _ => hprod p x)
  simp_rw [hsum]
  rw [horizontal_fourier_plancherel_square (integrable_finsetSum J (fun p _ => hCi p))
      (memLp_finsetSum J (fun p _ => hC₂ p))]
  change A * (∫⁻ s, ‖∑ p ∈ J, C p s‖ₑ ^ (2 : ℕ)) ≤
    K * ∑ p ∈ J, ∫⁻ x, ‖graphExtension (F p) φ (x, t) *
      graphExtension (G p) φ (x, t)‖ₑ ^ (2 : ℕ)
  simp_rw [hprod, horizontal_fourier_plancherel_square (hCi _) (hC₂ _)]
  have hi : (∫⁻ s, ‖∑ p ∈ J, C p s‖ₑ ^ (2 : ℕ)) ≤
      K * ∑ p ∈ J, ∫⁻ s, ‖C p s‖ₑ ^ (2 : ℕ) := by
    rw [← lintegral_finsetSum' J (fun p _ => (hCi p).aemeasurable.enorm.pow_const _),
      ← lintegral_const_mul' K _ (ENNReal.natCast_ne_top _)]
    exact lintegral_mono (dyadic_whitney_frequency_square_sum_le j 1 C
      (fun p _ => graph_whitney_convolution_support j p φ f g t))
  rw [← Finset.mul_sum]
  exact (mul_le_mul' le_rfl hi).trans_eq (by dsimp only [A]; ac_rfl)

set_option maxHeartbeats 1000000 in
/-- Spacetime L² almost orthogonality for each actual Whitney layer, with
a constant depending only on the parameter dimension. -/
theorem graph_whitney_layer_L2 {d : ℕ} (j : ℕ) {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0)
    (hgs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) :
    (∫⁻ z : Ambient d × ℝ, ‖graphWhitneyLayer j φ f g z‖ₑ ^ (2 : ℕ)) ≤
      ((7 ^ d * 3 ^ d : ℕ) : ℝ≥0∞) *
        ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ z : Ambient d × ℝ,
          ‖graphExtension ((dyadicParameterCell (j + 1) p.1).indicator f) φ z *
            graphExtension ((dyadicParameterCell (j + 1) p.2).indicator g) φ z‖ₑ ^ (2 : ℕ) := by
  let J := dyadicWhitneyPairs d j
  let K := ((7 ^ d * 3 ^ d : ℕ) : ℝ≥0∞)
  let P (p : (Fin d → ℤ) × (Fin d → ℤ)) (z : Ambient d × ℝ) :=
    graphExtension ((dyadicParameterCell (j + 1) p.1).indicator f) φ z *
      graphExtension ((dyadicParameterCell (j + 1) p.2).indicator g) φ z
  have hP p : Continuous (P p) := by
    refine (graph_extension_continuous ?_ hφ).mul (graph_extension_continuous ?_ hφ)
    · exact (hfi.indicator (measurable_dyadic_parameter_cell _ _)).restrict
    · exact (hgi.indicator (measurable_dyadic_parameter_cell _ _)).restrict
  have hL : Continuous (graphWhitneyLayer j φ f g) := continuous_finsetSum J (fun p _ => hP p)
  change (∫⁻ z : Ambient d × ℝ, ‖graphWhitneyLayer j φ f g z‖ₑ ^ (2 : ℕ)) ≤
    K * ∑ p ∈ J, ∫⁻ z : Ambient d × ℝ, ‖P p z‖ₑ ^ (2 : ℕ)
  conv_lhs => rw [Measure.volume_eq_prod, lintegral_prod_symm' _ (hL.measurable.enorm.pow_const _)]
  have hterm p : (∫⁻ z : Ambient d × ℝ, ‖P p z‖ₑ ^ (2 : ℕ)) =
      ∫⁻ t : ℝ, ∫⁻ x : Ambient d, ‖P p (x, t)‖ₑ ^ (2 : ℕ) := by
    rw [Measure.volume_eq_prod, lintegral_prod_symm' _ ((hP p).measurable.enorm.pow_const _)]
  simp_rw [hterm]
  have hm p : Measurable (fun t : ℝ => ∫⁻ x : Ambient d, ‖P p (x, t)‖ₑ ^ (2 : ℕ)) :=
    ((hP p).measurable.enorm.pow_const (2 : ℕ)).lintegral_prod_left'
  rw [← lintegral_finsetSum J (fun p _ => hm p), ← lintegral_const_mul' K _ (ENNReal.natCast_ne_top _)]
  exact lintegral_mono (graph_whitney_layer_horizontal_L2 j hφ hf hg hfi hgi hfs hgs hM)

end RestrictionWork
