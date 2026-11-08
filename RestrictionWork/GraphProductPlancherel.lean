import RestrictionWork.PhaseExtensionDefinitions
import OAI.Analysis.Fourier.BochnerRiesz.MultiplierCompatibility
import OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false
noncomputable section
open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace Convolution
namespace RestrictionWork

/-- The horizontal convolution at fixed time, in the sum variable s. -/
def graphProductConvolution {d : ℕ} (φ : Ambient d → ℝ) (f g : Ambient d → ℂ)
    (t : ℝ) (s : Ambient d) : ℂ :=
  ∫ u, (f u * g (s - u)) *
    Complex.exp ((↑(t * (φ u + φ (s - u))) : ℂ) * Complex.I)

theorem graph_product_convolution_measurable {d : ℕ} {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z : ℝ × Ambient d => graphProductConvolution φ f g z.1 z.2) := by
  have hm : Measurable (fun z : (ℝ × Ambient d) × Ambient d =>
      (f z.2 * g (z.1.2 - z.2)) *
        Complex.exp ((↑(z.1.1 * (φ z.2 + φ (z.1.2 - z.2))) : ℂ) * Complex.I)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private def modulate {d : ℕ} (φ : Ambient d → ℝ) (t : ℝ) (f : Ambient d → ℂ)
    (u : Ambient d) : ℂ :=
  f u * Complex.exp ((↑(t * φ u) : ℂ) * Complex.I)

private theorem measurable_modulate {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {f : Ambient d → ℂ} (hf : Measurable f) (t : ℝ) : Measurable (modulate φ t f) := by
  unfold modulate
  fun_prop

private theorem integrable_modulate {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {f : Ambient d → ℂ} (hf : Measurable f) (hfi : Integrable f) (t : ℝ) :
    Integrable (modulate φ t f) := by
  refine hfi.mono (measurable_modulate hφ hf t).aestronglyMeasurable ?_
  exact .of_forall fun u => by
    simp only [modulate, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]

private theorem graph_convolution_eq {d : ℕ} (φ : Ambient d → ℝ)
    (f g : Ambient d → ℂ) (t : ℝ) :
    graphProductConvolution φ f g t =
      modulate φ t f ⋆[ContinuousLinearMap.mul ℂ ℂ] modulate φ t g := by
  funext s
  rw [convolution_def]
  unfold graphProductConvolution
  apply integral_congr_ae
  filter_upwards [] with u
  change _ = modulate φ t f u * modulate φ t g (s - u)
  simp only [modulate, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

private theorem graph_extension_eq_fourier {d : ℕ} (φ : Ambient d → ℝ)
    {f : Ambient d → ℂ} (hf : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0)
    (t : ℝ) (x : Ambient d) :
    graphExtension f φ (x, t) = (𝓕 (modulate φ t f)) ((-2 * Real.pi)⁻¹ • x) := by
  have hπ : (-2 * Real.pi) ≠ 0 := by positivity
  rw [graphExtension, phaseExtension, patchMeasure, ← integral_indicator measurableSet_ball,
    Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with u
  have he : -2 * Real.pi * ⟪u, (-2 * Real.pi)⁻¹ • x⟫ = ⟪x, u⟫ := by
    rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul, real_inner_comm]
  rw [he]
  by_cases hu : u ∈ Metric.ball (0 : Ambient d) 1
  · simp only [indicator_of_mem hu, modulate, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  · simp [indicator_of_notMem hu, modulate, hf u hu]

theorem graph_product_convolution_integrable {d : ℕ} {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g) (t : ℝ) :
    Integrable (graphProductConvolution φ f g t) := by
  rw [graph_convolution_eq]
  exact (integrable_modulate hφ hf hfi t).integrable_convolution _
    (integrable_modulate hφ hg hgi t)

set_option maxHeartbeats 800000 in
theorem graph_product_convolution_memLp_two {d : ℕ} {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g) {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M)
    (t : ℝ) : MemLp (graphProductConvolution φ f g t) 2 := by
  let C := graphProductConvolution φ f g t
  have hCi := graph_product_convolution_integrable hφ hf hg hfi hgi t
  have hCbound (s : Ambient d) : ‖C s‖ ≤ (∫ u, ‖f u‖) * M := by
    let k : Ambient d → ℂ := fun u => f u * g (s - u) *
      Complex.exp ((↑(t * (φ u + φ (s - u))) : ℂ) * Complex.I)
    have hkm : Measurable k := by unfold k; fun_prop
    have hk (u : Ambient d) : ‖k u‖ ≤ ‖f u‖ * M := by
      simp only [k, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    have hi := hfi.norm.mul_const M
    have hki := hi.mono' hkm.aestronglyMeasurable (.of_forall hk)
    calc
      _ ≤ ∫ u, ‖k u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u, ‖f u‖ * M := integral_mono hki.norm hi hk
      _ = _ := integral_mul_const _ _
  have hCm : Measurable C :=
    (graph_product_convolution_measurable hφ hf hg).comp (measurable_const.prodMk measurable_id)
  apply (memLp_two_iff_integrable_sq_norm hCi.aestronglyMeasurable).mpr
  refine (hCi.norm.mul_const ((∫ u, ‖f u‖) * M)).mono'
    (hCm.norm.pow_const (2 : ℕ)).aestronglyMeasurable ?_
  filter_upwards [] with s
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_left (hCbound s) (norm_nonneg _)

/-- The horizontal Fourier representation of an actual graph product. -/
theorem graph_extension_product_eq_fourier {d : ℕ} {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0)
    (hgs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0) (x : Ambient d) (t : ℝ) :
    graphExtension f φ (x, t) * graphExtension g φ (x, t) =
      (𝓕 (graphProductConvolution φ f g t)) ((-2 * Real.pi)⁻¹ • x) := by
  rw [graph_extension_eq_fourier φ hfs, graph_extension_eq_fourier φ hgs,
    graph_convolution_eq, Real.fourier_mul_convolution_eq
      (integrable_modulate hφ hf hfi t) (integrable_modulate hφ hg hgi t)]

theorem horizontal_fourier_eLpNorm_two {d : ℕ} {C : Ambient d → ℂ}
    (hCi : Integrable C) (hC₂ : MemLp C 2) :
    eLpNorm (𝓕 C) 2 volume = eLpNorm C 2 volume := by
  rw [← eLpNorm_congr_ae (OAI.Analysis.Fourier.BochnerRiesz.fourier_toLp_ae hCi hC₂),
    ← Lp.enorm_def, ← ofReal_norm, LinearIsometryEquiv.norm_map, ofReal_norm,
    Lp.enorm_def, eLpNorm_congr_ae hC₂.coeFn_toLp]

theorem horizontal_square_lintegral_eq {d : ℕ} {C : Ambient d → ℂ}
    (hC : AEStronglyMeasurable C volume) :
    (∫⁻ s, ‖C s‖ₑ ^ (2 : ℕ)) = eLpNorm C 2 volume ^ (2 : ℕ) := by
  symm
  simpa only [ENNReal.ofReal_ofNat, ENNReal.rpow_two] using
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral (p := (2 : ℝ)) (by norm_num) hC

set_option maxHeartbeats 800000 in
/-- Horizontal Plancherel in the physical convention of the graph extension. -/
theorem horizontal_fourier_plancherel_square {d : ℕ} {C : Ambient d → ℂ}
    (hCi : Integrable C) (hC₂ : MemLp C 2) :
    (∫⁻ x : Ambient d, ‖(𝓕 C) ((-2 * Real.pi)⁻¹ • x)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal ((2 * Real.pi) ^ d) * ∫⁻ s, ‖C s‖ₑ ^ (2 : ℕ) := by
  have hF := OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hCi
  have hπ : (-2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have hm : Measurable (fun ξ : Ambient d => ‖(𝓕 C) ξ‖ₑ ^ (2 : ℕ)) := hF.measurable.enorm.pow_const _
  rw [← lintegral_map hm (measurable_const_smul ((-2 * Real.pi)⁻¹)),
    Measure.map_addHaar_smul volume hπ, lintegral_smul_measure, smul_eq_mul,
    horizontal_square_lintegral_eq hF.aestronglyMeasurable,
    horizontal_fourier_eLpNorm_two hCi hC₂, ← horizontal_square_lintegral_eq hCi.aestronglyMeasurable]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv,
    abs_pow, abs_mul, abs_of_nonneg Real.pi_pos.le, show |(-2 : ℝ)| = 2 by norm_num]


/-- Plancherel in the physical horizontal variable for the genuine product.
The factor (2π)^d is the change of Fourier convention. -/
theorem graph_extension_product_plancherel {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {f g : Ambient d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0)
    (hgs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) (t : ℝ) :
    (∫⁻ x : Ambient d, ‖graphExtension f φ (x, t) * graphExtension g φ (x, t)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal ((2 * Real.pi) ^ d) *
        ∫⁻ s, ‖graphProductConvolution φ f g t s‖ₑ ^ (2 : ℕ) := by
  simp_rw [graph_extension_product_eq_fourier hφ hf hg hfi hgi hfs hgs]
  exact horizontal_fourier_plancherel_square
    (graph_product_convolution_integrable hφ hf hg hfi hgi t)
    (graph_product_convolution_memLp_two hφ hf hg hfi hgi hM t)

end RestrictionWork
