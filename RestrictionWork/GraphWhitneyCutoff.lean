import RestrictionWork.GraphWhitneyFrequency
import OAI.Analysis.Fourier.WavePackets.LinearKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import OAI.Analysis.Fourier.BochnerRiesz.SmoothFactor

set_option autoImplicit false
noncomputable section

open MeasureTheory Set FourierTransform
open scoped ContDiff ENNReal RealInnerProductSpace

namespace RestrictionWork

private def whitneyBump (d : ℕ) : ContDiffBump (0 : Ambient d) where
  rIn := 2 * d + 1
  rOut := 2 * d + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

private def whitneyBaseCutoff (d : ℕ) (s : Ambient d) : ℂ :=
  (whitneyBump d s : ℂ)

private def whitneyFrequencyCenter {d : ℕ} (p : (Fin d → ℤ) × (Fin d → ℤ)) : Ambient d :=
  WithLp.toLp 2 (fun i => ((p.1 i + p.2 i : ℤ) : ℝ))

/-- A smooth cutoff for a specific Whitney pair in the sum variable. -/
def graphWhitneyCutoff {d : ℕ} (j : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ))
    (s : Ambient d) : ℂ :=
  whitneyBaseCutoff d (((2 : ℝ) ^ (j + 1)) • s - whitneyFrequencyCenter p)

theorem graph_whitney_cutoff_eq_one {d : ℕ} {j : ℕ} {p : (Fin d → ℤ) × (Fin d → ℤ)}
    {s : Ambient d} (hs : s ∈ dyadicPairFrequency j 1 p) : graphWhitneyCutoff j p s = 1 := by
  let w := ((2 : ℝ) ^ (j + 1)) • s - whitneyFrequencyCenter p
  have hcoord (i : Fin d) : |w i| ≤ 2 := by
    have hi := hs i
    let x := (2 : ℝ) ^ (j + 1) * s i
    let m := p.1 i + p.2 i
    have hlo : -1 ≤ ⌊x⌋ - m := (abs_le.mp hi).1
    have hhi : ⌊x⌋ - m ≤ 1 := (abs_le.mp hi).2
    have hlo' : -1 ≤ (⌊x⌋ : ℝ) - (m : ℝ) := by exact_mod_cast hlo
    have hhi' : (⌊x⌋ : ℝ) - (m : ℝ) ≤ 1 := by exact_mod_cast hhi
    change |x - (m : ℝ)| ≤ 2
    exact abs_le.mpr ⟨by linarith [Int.floor_le x], by linarith [Int.lt_floor_add_one x]⟩
  have hsq : ‖w‖ ^ 2 ≤ (4 : ℝ) * d := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sq_abs]
        simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
          pow_le_pow_left₀ (abs_nonneg _) (hcoord i) (2 : ℕ)
      _ = _ := by simp [mul_comm]
  have hball : w ∈ Metric.closedBall (0 : Ambient d) (whitneyBump d).rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖w‖ ≤ 2 * d + 1
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [hsq, sq_nonneg (d : ℝ)]
  change (whitneyBump d w : ℂ) = 1
  rw [(whitneyBump d).one_of_mem_closedBall hball, Complex.ofReal_one]

theorem graph_whitney_cutoff_support {d : ℕ} (j : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Function.support (graphWhitneyCutoff j p) ⊆ dyadicPairFrequency j (2 * d + 2) p := by
  intro s hs i
  let w := ((2 : ℝ) ^ (j + 1)) • s - whitneyFrequencyCenter p
  have hnonzero : whitneyBump d w ≠ 0 := by
    intro he
    exact hs (by change (whitneyBump d w : ℂ) = 0; rw [he, Complex.ofReal_zero])
  have hball : w ∈ Metric.ball (0 : Ambient d) (whitneyBump d).rOut := by
    rwa [← (whitneyBump d).support_eq]
  have hn : ‖w‖ < (2 * d + 2 : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right, whitneyBump] using hball
  have hcoord : |w i| < (2 * d + 2 : ℝ) :=
    (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w i : |w i| ≤ ‖w‖).trans_lt hn
  let x := (2 : ℝ) ^ (j + 1) * s i
  let m := p.1 i + p.2 i
  let b : ℤ := 2 * (d : ℤ) + 2
  change |x - (m : ℝ)| < (2 * d + 2 : ℝ) at hcoord
  have hx : |x - (m : ℝ)| < (b : ℝ) := by
    simpa only [b, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hcoord
  obtain ⟨hl, hu⟩ := abs_lt.mp hx
  have hf₁ : m - b ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have hf₂ : ⌊x⌋ < m + b := Int.floor_lt.mpr (by push_cast; linarith)
  change |⌊x⌋ - m| ≤ ((2 * d + 2 : ℕ) : ℤ)
  push_cast
  change |⌊x⌋ - m| ≤ b
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem graph_whitney_cutoff_smooth_compact {d : ℕ} (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    ContDiff ℝ ∞ (graphWhitneyCutoff j p) ∧ HasCompactSupport (graphWhitneyCutoff j p) := by
  let χ := whitneyBaseCutoff d
  let v := whitneyFrequencyCenter p
  let ψ := fun s => χ (s - v)
  let A := OAI.Analysis.Fourier.BochnerRiesz.realDilationEquiv d ((2 : ℝ) ^ (j + 1))
    (pow_ne_zero _ (by norm_num))
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp (whitneyBump d).contDiff
  have hχs : HasCompactSupport χ :=
    (whitneyBump d).hasCompactSupport.comp_left Complex.ofReal_zero
  have hψ : ContDiff ℝ ∞ ψ := hχ.comp (by fun_prop)
  have hψs : HasCompactSupport ψ := hχs.comp_homeomorph (Homeomorph.addRight (-v))
  exact ⟨hψ.comp A.contDiff, hψs.comp_homeomorph A.toHomeomorph⟩

theorem graph_whitney_cutoff_norm_le_one {d : ℕ} (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) (s : Ambient d) : ‖graphWhitneyCutoff j p s‖ ≤ 1 := by
  unfold graphWhitneyCutoff whitneyBaseCutoff
  rw [Complex.norm_real, Real.norm_of_nonneg (whitneyBump d).nonneg]
  exact (whitneyBump d).le_one

private theorem fourierInv_translate {d : ℕ} (χ : Ambient d → ℂ) (v x : Ambient d) :
    (𝓕⁻ (fun s => χ (s - v))) x =
      Complex.exp ((↑(2 * Real.pi * ⟪v, x⟫) : ℂ) * Complex.I) * (𝓕⁻ χ) x := by
  simp only [Real.fourierInv_eq', smul_eq_mul]
  rw [← integral_add_right_eq_self (fun s : Ambient d =>
    Complex.exp ((↑(2 * Real.pi * ⟪s, x⟫) : ℂ) * Complex.I) * χ (s - v)) v,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [add_sub_cancel_right, inner_add_left, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

set_option maxHeartbeats 1000000 in
/-- All actual translated and dilated cutoffs have integrable inverse Fourier
kernels, with one finite L¹ bound for the entire family. -/
theorem graph_whitney_cutoff_kernel_bound (d : ℕ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)),
      Integrable (𝓕⁻ (graphWhitneyCutoff j p)) ∧
      (𝓕 (𝓕⁻ (graphWhitneyCutoff j p))) = graphWhitneyCutoff j p ∧
      eLpNorm (𝓕⁻ (graphWhitneyCutoff j p)) 1 volume = C := by
  let χ := whitneyBaseCutoff d
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp (whitneyBump d).contDiff
  have hχs : HasCompactSupport χ :=
    (whitneyBump d).hasCompactSupport.comp_left Complex.ofReal_zero
  have hχK : Integrable (𝓕⁻ χ) := by
    have he : ((𝓕⁻ (hχs.toSchwartzMap hχ) : SchwartzMap (Ambient d) ℂ) : Ambient d → ℂ) =
        𝓕⁻ χ := SchwartzMap.fourierInv_coe _
    rw [← he]
    exact (𝓕⁻ (hχs.toSchwartzMap hχ) : SchwartzMap (Ambient d) ℂ).integrable
  refine ⟨eLpNorm (𝓕⁻ χ) 1 volume, (memLp_one_iff_integrable.mpr hχK).eLpNorm_lt_top, ?_⟩
  intro j p
  let v := whitneyFrequencyCenter p
  let ψ := fun s => χ (s - v)
  let A := OAI.Analysis.Fourier.BochnerRiesz.realDilationEquiv d ((2 : ℝ) ^ (j + 1))
    (pow_ne_zero _ (by norm_num))
  have hψ : ContDiff ℝ ∞ ψ := hχ.comp (by fun_prop)
  have hψs : HasCompactSupport ψ := hχs.comp_homeomorph (Homeomorph.addRight (-v))
  obtain ⟨hcut, hcuts⟩ := graph_whitney_cutoff_smooth_compact j p
  let cut := hcuts.toSchwartzMap hcut
  have hK : (𝓕⁻ (graphWhitneyCutoff j p)) = (𝓕⁻ cut : SchwartzMap (Ambient d) ℂ) := by
    rw [SchwartzMap.fourierInv_coe]
    rfl
  refine ⟨hK ▸ (𝓕⁻ cut : SchwartzMap (Ambient d) ℂ).integrable, ?_, ?_⟩
  · rw [hK, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
    rfl
  · change eLpNorm (𝓕⁻ (ψ ∘ A)) 1 volume = _
    have hψm : Measurable (𝓕⁻ ψ) := by
      have he : ((𝓕⁻ (hψs.toSchwartzMap hψ) : SchwartzMap (Ambient d) ℂ) : Ambient d → ℂ) =
          𝓕⁻ ψ := SchwartzMap.fourierInv_coe _
      rw [← he]
      exact (𝓕⁻ (hψs.toSchwartzMap hψ) : SchwartzMap (Ambient d) ℂ).continuous.measurable
    rw [OAI.Analysis.Fourier.WavePackets.eLpNorm_fourierInv_comp_linearEquiv A ψ hψm,
      eLpNorm_one_eq_lintegral_enorm hψm.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hχK.aestronglyMeasurable]
    apply lintegral_congr
    intro x
    have he := fourierInv_translate χ v x
    change (𝓕⁻ ψ) x = _ at he
    rw [he, enorm_mul, ← ofReal_norm (Complex.exp _),
      Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one, one_mul]

/-- Projecting the inverse Fourier representation of an actual Whitney
product leaves the product unchanged. The variable here is in the
normalized inverse Fourier convention. -/
theorem graph_whitney_cutoff_reproduces {d : ℕ} (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g) (t : ℝ) :
    let C := graphProductConvolution φ
      ((dyadicParameterCell (j + 1) p.1).indicator f)
      ((dyadicParameterCell (j + 1) p.2).indicator g) t
    OAI.Analysis.Fourier.WavePackets.complexConvolution
      (𝓕⁻ (graphWhitneyCutoff j p)) (𝓕⁻ C) volume = 𝓕⁻ C := by
  intro C
  have hC : Integrable C := graph_product_convolution_integrable hφ
    (hf.indicator (measurable_dyadic_parameter_cell _ _))
    (hg.indicator (measurable_dyadic_parameter_cell _ _))
    (hfi.indicator (measurable_dyadic_parameter_cell _ _))
    (hgi.indicator (measurable_dyadic_parameter_cell _ _)) t
  obtain ⟨hcut, hcuts⟩ := graph_whitney_cutoff_smooth_compact j p
  rw [← OAI.Analysis.Fourier.BochnerRiesz.fourierInv_mul_smooth_eq_convolution hcut hcuts hC]
  congr 1
  funext s
  by_cases hs : C s = 0
  · simp [hs]
  · have hfreq : s ∈ dyadicPairFrequency j 1 p :=
      graph_whitney_convolution_support j p φ f g t hs
    rw [graph_whitney_cutoff_eq_one hfreq, one_mul]

end RestrictionWork
