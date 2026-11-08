import RestrictionWork.FilteredRadonL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- The Fourier-slice definition is exactly convolution in the offset
against the inverse Fourier transform of its filter. -/
theorem filtered_radon_kernel {d : ℕ} {m : ℝ → ℂ} {f : Ambient d → ℂ}
    (hm : Measurable m) (hmi : Integrable m) (hf : Measurable f) (hfi : Integrable f)
    (z : Ambient d × ℝ) :
    filteredRadon m f z = ∫ v, (𝓕⁻ m) (z.2 - ⟪v, z.1⟫) * f v := by
  let K (ρ : ℝ) (v : Ambient d) : ℂ :=
    Complex.exp ((↑(2 * Real.pi * (ρ * (z.2 - ⟪v, z.1⟫))) : ℂ) * Complex.I) * m ρ * f v
  have hKm : Measurable (Function.uncurry K) := by unfold K Function.uncurry; fun_prop
  have hK : Integrable (Function.uncurry K)
      ((volume : Measure ℝ).prod (volume : Measure (Ambient d))) := by
    refine (hmi.norm.mul_prod hfi.norm).mono' hKm.aestronglyMeasurable ?_
    filter_upwards [] with p
    simp only [Function.uncurry, K, norm_mul, Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, Real.exp_zero, one_mul]
    exact le_rfl
  have hfirst : filteredRadon m f z = ∫ ρ, ∫ v, K ρ v := by
    unfold filteredRadon
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with ρ
    change Complex.exp ((↑(2 * Real.pi * ⟪ρ, z.2⟫) : ℂ) * Complex.I) *
      (m ρ * (𝓕 f) (ρ • z.1)) = _
    rw [Real.fourier_eq', ← mul_assoc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    have he :
        Complex.exp ((↑(2 * Real.pi * ⟪ρ, z.2⟫) : ℂ) * Complex.I) *
          Complex.exp ((↑(-2 * Real.pi * ⟪v, ρ • z.1⟫) : ℂ) * Complex.I) =
          Complex.exp ((↑(2 * Real.pi * (ρ * (z.2 - ⟪v, z.1⟫))) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, real_inner_smul_right]
      simp only [Real.inner_apply]
      congr 1
      push_cast
      ring
    change (Complex.exp ((↑(2 * Real.pi * ⟪ρ, z.2⟫) : ℂ) * Complex.I) * m ρ) *
        (Complex.exp ((↑(-2 * Real.pi * ⟪v, ρ • z.1⟫) : ℂ) * Complex.I) * f v) = _
    dsimp only [K]
    rw [← he]
    ring
  rw [hfirst, integral_integral_swap hK]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [Real.fourierInv_eq', ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with ρ
  simp only [K, smul_eq_mul, Real.inner_apply, mul_comm ρ (z.2 - ⟪v, z.1⟫)]

def radonGaussianSymbol (h : ℝ) (ρ : ℝ) : ℂ :=
  (Real.exp (-(Real.pi * h ^ 2) * ρ ^ 2) : ℂ)

def radonGaussianKernel (h : ℝ) (t : ℝ) : ℝ :=
  h⁻¹ * Real.exp (-Real.pi * (t / h) ^ 2)

theorem radon_gaussian_symbol_measurable (h : ℝ) : Measurable (radonGaussianSymbol h) := by
  unfold radonGaussianSymbol
  fun_prop

theorem radon_gaussian_symbol_integrable {h : ℝ} (hh : 0 < h) :
    Integrable (radonGaussianSymbol h) := by
  exact Complex.ofRealCLM.integrable_comp
    (integrable_exp_neg_mul_sq (mul_pos Real.pi_pos (pow_pos hh 2)))

theorem radon_gaussian_symbol_norm_le_one (h ρ : ℝ) : ‖radonGaussianSymbol h ρ‖ ≤ 1 := by
  rw [radonGaussianSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg h)))
    (sq_nonneg ρ)

theorem inverse_fourier_radon_gaussian {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (𝓕⁻ (radonGaussianSymbol h)) t = (radonGaussianKernel h t : ℂ) := by
  let b : ℂ := ((h ^ 2 : ℝ) : ℂ)
  have hb : 0 < b.re := by
    change 0 < ((h ^ 2 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact pow_pos hh 2
  have he : radonGaussianSymbol h = fun x : ℝ => Complex.exp (-Real.pi * b * x ^ 2) := by
    funext x
    rw [radonGaussianSymbol, Complex.ofReal_exp]
    congr 1
    dsimp only [b]
    push_cast
    ring
  have hs : b ^ (1 / 2 : ℂ) = (h : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    change ((h ^ 2 : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ)) = _
    rw [← Complex.ofReal_cpow (sq_nonneg h), ← Real.sqrt_eq_rpow, Real.sqrt_sq hh.le]
  rw [Real.fourierInv_eq_fourier_neg, he, fourier_gaussian_pi hb, hs, radonGaussianKernel,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_exp, one_div]
  dsimp only [b]
  push_cast
  rw [neg_sq]
  field_simp [show (h : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hh.ne']

end RestrictionWork
