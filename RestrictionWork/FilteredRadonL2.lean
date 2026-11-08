import RestrictionWork.PhaseExtensionDefinitions
import OAI.Analysis.Fourier.BochnerRiesz.MultiplierCompatibility
import OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation
import OAI.Analysis.Fourier.Restriction.Basic
import OAI.Analysis.Fourier.Restriction.Polar
import OAI.Analysis.Fourier.SquareFunction.FourierL2

set_option autoImplicit false
noncomputable section
open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

/-- Fourier-slice realization of the hyperplane transform with a multiplier
in the one-dimensional offset frequency. -/
def filteredRadon {d : ℕ} (m : ℝ → ℂ) (f : Ambient d → ℂ) (z : Ambient d × ℝ) : ℂ :=
  (𝓕⁻ (fun ρ : ℝ => m ρ * (𝓕 f) (ρ • z.1))) z.2

theorem filtered_radon_measurable {d : ℕ} {m : ℝ → ℂ} {f : Ambient d → ℂ}
    (hm : Measurable m) (hf : Integrable f) : Measurable (filteredRadon m f) := by
  have hF := OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf
  have hmeas : Measurable (fun z : (Ambient d × ℝ) × ℝ =>
      Complex.exp ((↑(2 * Real.pi * ⟪z.2, z.1.2⟫) : ℂ) * Complex.I) *
        (m z.2 * (𝓕 f) (z.2 • z.1.1))) := by
    fun_prop
  have he : filteredRadon m f = fun z : Ambient d × ℝ =>
      ∫ ρ : ℝ, Complex.exp ((↑(2 * Real.pi * ⟪ρ, z.2⟫) : ℂ) * Complex.I) *
        (m ρ * (𝓕 f) (ρ • z.1)) := by
    funext z
    simp only [filteredRadon, Real.fourierInv_eq', smul_eq_mul]
  rw [he]
  exact hmeas.stronglyMeasurable.integral_prod_right'.measurable

private theorem norm_fourier_le_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℂ) (ξ : E) : ‖(𝓕 f) ξ‖ ≤ ∫ x, ‖f x‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ E) f ξ

theorem filtered_radon_slice_integrable {d : ℕ} {m : ℝ → ℂ} {f : Ambient d → ℂ}
    (hm : Integrable m) (hf : Integrable f) (θ : Ambient d) :
    Integrable (fun ρ : ℝ => m ρ * (𝓕 f) (ρ • θ)) := by
  have hF := OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf
  refine (hm.norm.mul_const (∫ x, ‖f x‖)).mono'
    (hm.aestronglyMeasurable.mul (show Continuous (fun ρ : ℝ => (𝓕 f) (ρ • θ)) by
      fun_prop).aestronglyMeasurable) ?_
  filter_upwards [] with ρ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_fourier_le_integral f (ρ • θ)) (norm_nonneg _)

theorem filtered_radon_uniform_bound {d : ℕ} {m : ℝ → ℂ} {f : Ambient d → ℂ}
    (hm : Integrable m) (hf : Integrable f) (z : Ambient d × ℝ) :
    ‖filteredRadon m f z‖ₑ ≤ eLpNorm m 1 volume * eLpNorm f 1 volume := by
  let g := fun ρ : ℝ => m ρ * (𝓕 f) (ρ • z.1)
  have hn : ‖filteredRadon m f z‖ ≤ (∫ ρ, ‖m ρ‖) * ∫ x, ‖f x‖ := by
    change ‖(𝓕⁻ g) z.2‖ ≤ _
    rw [Real.fourierInv_eq_fourier_neg, ← integral_mul_const]
    refine (norm_fourier_le_integral g (-z.2)).trans (integral_mono
      (filtered_radon_slice_integrable hm hf z.1).norm (hm.norm.mul_const _) ?_)
    intro ρ
    change ‖g ρ‖ ≤ ‖m ρ‖ * ∫ x, ‖f x‖
    rw [show ‖g ρ‖ = ‖m ρ‖ * ‖(𝓕 f) (ρ • z.1)‖ from norm_mul _ _]
    exact mul_le_mul_of_nonneg_left (norm_fourier_le_integral f _) (norm_nonneg _)
  rw [← ofReal_norm, eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hm,
    ← ofReal_integral_norm_eq_lintegral_enorm hf, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hn

private theorem radon_two_norm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : X → ℂ} (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
  simpa only [ENNReal.ofReal_ofNat, ENNReal.rpow_two] using
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral (p := (2 : ℝ)) (by norm_num) hF

private theorem radon_fourier_inv_line_norm {g : ℝ → ℂ} (hg : Integrable g) (h₂ : MemLp g 2) :
    eLpNorm (𝓕⁻ g) 2 volume = eLpNorm g 2 volume := by
  have hc : Continuous (𝓕 g) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hg)]
    exact (Real.Lp.fourierTransform _).continuous
  rw [show 𝓕⁻ g = 𝓕 g ∘ Neg.neg from funext (Real.fourierInv_eq_fourier_neg g),
    eLpNorm_comp_measurePreserving hc.aestronglyMeasurable (Measure.measurePreserving_neg volume)]
  exact OAI.Analysis.Fourier.SquareFunction.eLpNorm_fourier_line hg h₂

/-- A positive-offset-frequency band gains (d−1)/2 derivatives in L².
The square form avoids any choice of real-valued norm representatives. -/
theorem filtered_radon_two_norm_sq_le {d : ℕ} (hd : 1 ≤ d)
    {m : ℝ → ℂ} (hm : Measurable m) (hmi : Integrable m) (hm₂ : MemLp m 2)
    (hmb : ∀ ρ, ‖m ρ‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hms : ∀ ρ < R, m ρ = 0) {f : Ambient d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2) :
    eLpNorm (filteredRadon m f) 2
        ((OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod volume) ^ 2 ≤
      (ENNReal.ofReal (R ^ (d - 1)))⁻¹ * eLpNorm f 2 volume ^ 2 := by
  let μ := OAI.Analysis.Fourier.Restriction.sphereMeasure d
  let g (θ : Ambient d) (ρ : ℝ) := m ρ * (𝓕 f) (ρ • θ)
  let A := ENNReal.ofReal (R ^ (d - 1))
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hR _)).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hF := OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf
  have hfiltered := filtered_radon_measurable hm hf
  have hgm (θ : Ambient d) : Measurable (g θ) := by
    unfold g
    fun_prop
  have hg₂ (θ : Ambient d) : MemLp (g θ) 2 := by
    have hdom := hm₂.norm.const_mul (∫ x, ‖f x‖)
    apply hdom.mono' (hgm θ).aestronglyMeasurable
    filter_upwards [] with ρ
    change ‖m ρ * (𝓕 f) (ρ • θ)‖ ≤ (∫ x, ‖f x‖) * ‖m ρ‖
    rw [norm_mul, mul_comm (∫ x, ‖f x‖)]
    exact mul_le_mul_of_nonneg_left (norm_fourier_le_integral f _) (norm_nonneg _)
  have hslice (θ : Ambient d) :
      (∫⁻ t, ‖filteredRadon m f (θ, t)‖ₑ ^ 2) = ∫⁻ ρ, ‖g θ ρ‖ₑ ^ 2 := by
    have hs : Measurable (fun t : ℝ => filteredRadon m f (θ, t)) :=
      hfiltered.comp (measurable_const.prodMk measurable_id)
    rw [← radon_two_norm_sq hs.aestronglyMeasurable, ← radon_two_norm_sq (hgm θ).aestronglyMeasurable]
    exact congrArg (fun z : ℝ≥0∞ => z ^ (2 : ℕ))
      (radon_fourier_inv_line_norm (filtered_radon_slice_integrable hmi hf θ) (hg₂ θ))
  have hband (θ : Ambient d) :
      (∫⁻ ρ, ‖g θ ρ‖ₑ ^ 2) ≤ A⁻¹ *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (d - 1)) * ‖(𝓕 f) (ρ • θ)‖ₑ ^ 2 := by
    have hgF : Measurable (fun ρ : ℝ => (𝓕 f) (ρ • θ)) :=
      hF.measurable.comp (measurable_id.smul measurable_const)
    have hmeas : Measurable (fun ρ : ℝ => ENNReal.ofReal (ρ ^ (d - 1)) *
        ‖(𝓕 f) (ρ • θ)‖ₑ ^ 2) := by fun_prop
    rw [← lintegral_const_mul _ hmeas, ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_mono
    intro ρ
    change ‖g θ ρ‖ₑ ^ 2 ≤ (Ioi (0 : ℝ)).indicator (fun t =>
      A⁻¹ * (ENNReal.ofReal (t ^ (d - 1)) * ‖(𝓕 f) (t • θ)‖ₑ ^ 2)) ρ
    by_cases hρ : R ≤ ρ
    · have hpρ : ρ ∈ Ioi (0 : ℝ) := hR.trans_le hρ
      rw [indicator_of_mem hpρ]
      have hb : ‖m ρ‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hmb ρ)
      have hρA : 1 ≤ A⁻¹ * ENNReal.ofReal (ρ ^ (d - 1)) := by
        rw [← ENNReal.inv_mul_cancel hA0 hAt]
        exact mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hR.le hρ _)) zero_le
      calc
        _ ≤ ‖(𝓕 f) (ρ • θ)‖ₑ ^ 2 := by
          apply pow_le_pow_left₀ zero_le
          dsimp only [g]
          rw [enorm_mul]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (show 0 ≤ ‖(𝓕 f) (ρ • θ)‖ₑ from zero_le)
        _ ≤ _ := by
          rw [← mul_assoc]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hρA (by positivity :
            0 ≤ ‖(𝓕 f) (ρ • θ)‖ₑ ^ (2 : ℕ))
    · rw [show g θ ρ = 0 by simp [g, hms ρ (lt_of_not_ge hρ)], enorm_zero, zero_pow (by norm_num)]
      exact zero_le
  have hpolar : Measurable (fun x : Ambient d => ‖(𝓕 f) x‖ₑ ^ 2) := by fun_prop
  have hjoint : Measurable (fun z : Ambient d × ℝ =>
      ENNReal.ofReal (z.2 ^ (d - 1)) * ‖(𝓕 f) (z.2 • z.1)‖ₑ ^ 2) := by
    have hcomp : Measurable (fun z : Ambient d × ℝ => (𝓕 f) (z.2 • z.1)) :=
      hF.measurable.comp (measurable_snd.smul measurable_fst)
    fun_prop
  have hmeasθ : Measurable (fun θ : Ambient d => ∫⁻ ρ in Ioi (0 : ℝ),
      ENNReal.ofReal (ρ ^ (d - 1)) * ‖(𝓕 f) (ρ • θ)‖ₑ ^ 2) :=
    (Measurable.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ))) hjoint)
  have hF₂ : eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
    rw [← eLpNorm_congr_ae (OAI.Analysis.Fourier.BochnerRiesz.fourier_toLp_ae hf hf₂),
      ← Lp.enorm_def, ← ofReal_norm, LinearIsometryEquiv.norm_map, ofReal_norm,
      Lp.enorm_def, eLpNorm_congr_ae hf₂.coeFn_toLp]
  have hprod : Measurable (fun z => ‖filteredRadon m f z‖ₑ ^ (2 : ℕ)) :=
    hfiltered.enorm.pow_const _
  rw [radon_two_norm_sq hfiltered.aestronglyMeasurable, lintegral_prod _ hprod.aemeasurable]
  calc
    _ = ∫⁻ θ, ∫⁻ ρ, ‖g θ ρ‖ₑ ^ 2 ∂volume ∂μ := lintegral_congr hslice
    _ ≤ ∫⁻ θ, A⁻¹ * (∫⁻ ρ in Ioi (0 : ℝ),
        ENNReal.ofReal (ρ ^ (d - 1)) * ‖(𝓕 f) (ρ • θ)‖ₑ ^ 2) ∂μ := lintegral_mono hband
    _ = A⁻¹ * (∫⁻ x : Ambient d, ‖(𝓕 f) x‖ₑ ^ 2) := by
      rw [lintegral_const_mul _ hmeasθ, OAI.Analysis.Fourier.Restriction.lintegral_polar_sphereMeasure hd hpolar]
    _ = _ := by rw [← radon_two_norm_sq hF.aestronglyMeasurable, hF₂]

end RestrictionWork
