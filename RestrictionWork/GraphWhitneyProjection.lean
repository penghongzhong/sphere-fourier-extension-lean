import RestrictionWork.GraphWhitneyCutoff
import RestrictionWork.GraphWhitneyL2

set_option autoImplicit false
noncomputable section

open MeasureTheory FourierTransform
open OAI.Analysis.Fourier.WavePackets
open scoped ENNReal Convolution

namespace RestrictionWork

/-- Sum of the horizontal cutoff projections at a fixed Whitney level.
The inputs are expressed in the normalized Fourier coordinates. -/
def graphWhitneyProjection {d : ℕ} (j : ℕ)
    (F : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℂ) (x : Ambient d) : ℂ :=
  ∑ p ∈ dyadicWhitneyPairs d j,
    complexConvolution (𝓕⁻ (graphWhitneyCutoff j p)) (F p) volume x

private theorem measurable_whitney_inverse_kernel {d : ℕ} (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Measurable (𝓕⁻ (graphWhitneyCutoff j p)) := by
  obtain ⟨h, hc⟩ := graph_whitney_cutoff_smooth_compact j p
  exact (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourierInv_of_integrable
    (h.continuous.integrable_of_hasCompactSupport hc)).measurable

theorem graph_whitney_projection_measurable {d : ℕ} (j : ℕ)
    {F : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℂ}
    (hF : ∀ p ∈ dyadicWhitneyPairs d j, Measurable (F p)) :
    Measurable (graphWhitneyProjection j F) := by
  unfold graphWhitneyProjection
  apply Finset.measurable_sum
  intro p hp
  have hk := measurable_whitney_inverse_kernel j p
  have h : Measurable (fun z : Ambient d × Ambient d =>
      (𝓕⁻ (graphWhitneyCutoff j p)) z.2 * F p (z.1 - z.2)) :=
    (hk.comp measurable_snd).mul ((hF p hp).comp (measurable_fst.sub measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- Uniform L¹ endpoint for the sum of actual smooth Whitney projections. -/
theorem graph_whitney_projection_one {d : ℕ} :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ)
      (F : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℂ),
      (∀ p ∈ dyadicWhitneyPairs d j, Measurable (F p)) →
      (∫⁻ x, ‖graphWhitneyProjection j F x‖ₑ) ≤
        C * ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x, ‖F p x‖ₑ := by
  obtain ⟨C, hC, H⟩ := graph_whitney_cutoff_kernel_bound d
  refine ⟨C, hC, ?_⟩
  intro j F hF
  let J := dyadicWhitneyPairs d j
  let P (p : (Fin d → ℤ) × (Fin d → ℤ)) :=
    complexConvolution (𝓕⁻ (graphWhitneyCutoff j p)) (F p) volume
  have hmeas p (hp : p ∈ J) : AEMeasurable (fun x => ‖P p x‖ₑ) volume :=
    (aestronglyMeasurable_complexConvolution (H j p).1.aestronglyMeasurable
      (hF p hp).aestronglyMeasurable).aemeasurable.enorm
  have hterm p (hp : p ∈ J) : (∫⁻ x, ‖P p x‖ₑ) ≤ C * ∫⁻ x, ‖F p x‖ₑ := by
    have h := complexConvolution_rpow_integral_le (μ := volume)
      (measurable_whitney_inverse_kernel j p) (hF p hp) (p := (1 : ℝ)) le_rfl
    simpa only [ENNReal.rpow_one, ← eLpNorm_one_eq_lintegral_enorm
      (H j p).1.aestronglyMeasurable, (H j p).2.2] using h
  calc
    _ ≤ ∫⁻ x, ∑ p ∈ J, ‖P p x‖ₑ :=
      lintegral_mono fun x => enorm_sum_le J (fun p => P p x)
    _ = ∑ p ∈ J, ∫⁻ x, ‖P p x‖ₑ := lintegral_finsetSum' J hmeas
    _ ≤ _ := by rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm

set_option maxHeartbeats 1100000 in
/-- Uniform L² endpoint on arbitrary inputs to the sum of smooth projections.
The frequency overlap is for the enlarged cutoff supports. -/
theorem graph_whitney_projection_two {d : ℕ} (j : ℕ)
    {F : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℂ}
    (hFi : ∀ p ∈ dyadicWhitneyPairs d j, Integrable (F p))
    (hF₂ : ∀ p ∈ dyadicWhitneyPairs d j, MemLp (F p) 2) :
    (∫⁻ x, ‖graphWhitneyProjection j F x‖ₑ ^ (2 : ℕ)) ≤
      ((7 ^ d * (2 * (2 * d + 2) + 1) ^ d : ℕ) : ℝ≥0∞) *
        ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x, ‖F p x‖ₑ ^ (2 : ℕ) := by
  let J := dyadicWhitneyPairs d j
  let b := 2 * d + 2
  let N := ((7 ^ d * (2 * b + 1) ^ d : ℕ) : ℝ≥0∞)
  let P (p : (Fin d → ℤ) × (Fin d → ℤ)) :=
    complexConvolution (𝓕⁻ (graphWhitneyCutoff j p)) (F p) volume
  let G (p : (Fin d → ℤ) × (Fin d → ℤ)) (s : Ambient d) :=
    graphWhitneyCutoff j p s * (𝓕 (F p)) s
  obtain ⟨_, _, H⟩ := graph_whitney_cutoff_kernel_bound d
  have hPi p (hp : p ∈ J) : Integrable (P p) :=
    (H j p).1.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (hFi p hp)
  have hP₂ p (hp : p ∈ J) : MemLp (P p) 2 :=
    memLp_complexConvolution (H j p).1 (hF₂ p hp) (by norm_num) ENNReal.ofNat_ne_top
  have hPG p (hp : p ∈ J) (s : Ambient d) : (𝓕 (P p)) s = G p s := by
    change (𝓕 ((𝓕⁻ (graphWhitneyCutoff j p)) ⋆[ContinuousLinearMap.mul ℂ ℂ] F p)) s = _
    rw [Real.fourier_mul_convolution_eq (H j p).1 (hFi p hp), (H j p).2.1]
  have hsum s : (𝓕 (graphWhitneyProjection j F)) s = ∑ p ∈ J, G p s := by
    change (𝓕 (fun x => ∑ p ∈ J, P p x)) s = _
    rw [horizontal_fourier_finset_sum J hPi]
    exact Finset.sum_congr rfl (fun p hp => hPG p hp s)
  have hG p (_hp : p ∈ J) : Function.support (G p) ⊆ dyadicPairFrequency j b p := by
    intro s hs
    apply graph_whitney_cutoff_support j p
    intro he
    apply hs
    simp [G, he]
  have hGle p s : ‖G p s‖ₑ ≤ ‖(𝓕 (F p)) s‖ₑ := by
    have h : ‖graphWhitneyCutoff j p s‖ₑ ≤ 1 := by
      simpa only [ofReal_norm, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (graph_whitney_cutoff_norm_le_one j p s)
    calc
      _ = ‖graphWhitneyCutoff j p s‖ₑ * ‖(𝓕 (F p)) s‖ₑ := enorm_mul _ _
      _ ≤ _ := (mul_le_mul' h le_rfl).trans_eq (one_mul _)
  have hL : Integrable (graphWhitneyProjection j F) := integrable_finsetSum J hPi
  have hL₂ : MemLp (graphWhitneyProjection j F) 2 := memLp_finsetSum J hP₂
  have hFcont p (hp : p ∈ J) : Continuous (𝓕 (F p)) :=
    OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable (hFi p hp)
  calc
    _ = ∫⁻ s, ‖(𝓕 (graphWhitneyProjection j F)) s‖ₑ ^ (2 : ℕ) := by
      rw [horizontal_square_lintegral_eq hL.aestronglyMeasurable,
        horizontal_square_lintegral_eq
          (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hL).aestronglyMeasurable,
        horizontal_fourier_eLpNorm_two hL hL₂]
    _ = ∫⁻ s, ‖∑ p ∈ J, G p s‖ₑ ^ (2 : ℕ) := lintegral_congr (fun s => by rw [hsum])
    _ ≤ ∫⁻ s, N * ∑ p ∈ J, ‖(𝓕 (F p)) s‖ₑ ^ (2 : ℕ) := by
      apply lintegral_mono
      intro s
      exact (dyadic_whitney_frequency_square_sum_le j b G hG s).trans
        (mul_le_mul' le_rfl (Finset.sum_le_sum
          (fun p _ => pow_le_pow_left' (hGle p s) _)))
    _ = N * ∑ p ∈ J, ∫⁻ s, ‖(𝓕 (F p)) s‖ₑ ^ (2 : ℕ) := by
      rw [lintegral_const_mul' N _ (ENNReal.natCast_ne_top _),
        lintegral_finsetSum J (fun p hp => (hFcont p hp).measurable.enorm.pow_const _)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [horizontal_square_lintegral_eq (hFcont p hp).aestronglyMeasurable,
        horizontal_fourier_eLpNorm_two (hFi p hp) (hF₂ p hp),
        ← horizontal_square_lintegral_eq (hFi p hp).aestronglyMeasurable]

end RestrictionWork
