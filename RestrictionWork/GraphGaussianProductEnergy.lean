import RestrictionWork.GraphProductPlancherel
import RestrictionWork.FilteredRadonKernel

set_option autoImplicit false
noncomputable section
open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace ComplexConjugate
namespace RestrictionWork

private theorem gaussian_time_integral {h : ℝ} (hh : 0 < h) (phase : ℝ) :
    (∫ t, radonGaussianSymbol h t * Complex.exp ((↑(t * phase) : ℂ) * Complex.I)) =
      (radonGaussianKernel h (phase / (2 * Real.pi)) : ℂ) := by
  rw [← inverse_fourier_radon_gaussian hh (phase / (2 * Real.pi)), Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with t
  have he : 2 * Real.pi * ⟪t, phase / (2 * Real.pi)⟫ = t * phase := by
    rw [Real.inner_apply]
    field_simp [Real.pi_ne_zero]
  rw [he, smul_eq_mul, mul_comm]

private theorem gaussian_oscillatory_square {d : ℕ} {h : ℝ} (hh : 0 < h)
    {A : Ambient d → ℂ} (hA : Measurable A) (hAi : Integrable A)
    {phase : Ambient d → ℝ} (hphase : Measurable phase) :
    let O := fun t u => A u * Complex.exp ((↑(t * phase u) : ℂ) * Complex.I)
    (∫⁻ t, ‖radonGaussianSymbol h t‖ₑ * ‖∫ u, O t u‖ₑ ^ (2 : ℕ)) ≤
      ∫⁻ u, ∫⁻ w, ‖A u‖ₑ * ‖A w‖ₑ *
        ENNReal.ofReal (radonGaussianKernel h ((phase u - phase w) / (2 * Real.pi))) := by
  intro O
  let X (t : ℝ) (p : Ambient d × Ambient d) :=
    radonGaussianSymbol h t * (O t p.1 * conj (O t p.2))
  have hXm : Measurable (Function.uncurry X) := by
    unfold X Function.uncurry O radonGaussianSymbol
    fun_prop
  have hXi : Integrable (Function.uncurry X)
      ((volume : Measure ℝ).prod ((volume : Measure (Ambient d)).prod volume)) := by
    refine ((radon_gaussian_symbol_integrable hh).norm.mul_prod
      (hAi.norm.mul_prod hAi.norm)).mono' hXm.aestronglyMeasurable ?_
    filter_upwards [] with p
    simp only [Function.uncurry, X, O, norm_mul, Complex.norm_conj,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact le_rfl
  let E : ℝ → ℝ := fun t => Real.exp (-(Real.pi * h ^ 2) * t ^ 2) *
    ‖∫ u, O t u‖ ^ (2 : ℕ)
  have hE0 (t : ℝ) : 0 ≤ E t := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hpair (t : ℝ) : (∫ p, X t p ∂(volume : Measure (Ambient d)).prod volume) = (E t : ℂ) := by
    unfold X E
    rw [integral_const_mul, integral_prod_mul (O t) (fun w => conj (O t w)),
      integral_conj, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, radonGaussianSymbol, Complex.ofReal_mul]
  have hEi : Integrable E := by
    refine hXi.integral_prod_left.norm.congr (.of_forall fun t => ?_)
    change ‖∫ p, X t p ∂(volume : Measure (Ambient d)).prod volume‖ = E t
    rw [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hE0 t)]
  have hEt (t : ℝ) : ENNReal.ofReal (E t) =
      ‖radonGaussianSymbol h t‖ₑ * ‖∫ u, O t u‖ₑ ^ (2 : ℕ) := by
    unfold E
    have hG : ‖radonGaussianSymbol h t‖ₑ = ENNReal.ofReal (Real.exp (-(Real.pi * h ^ 2) * t ^ 2)) := by
      rw [← ofReal_norm, radonGaussianSymbol, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    rw [hG, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have htime (p : Ambient d × Ambient d) :
      (∫ t, X t p) = (A p.1 * conj (A p.2)) *
        (radonGaussianKernel h ((phase p.1 - phase p.2) / (2 * Real.pi)) : ℂ) := by
    rw [← gaussian_time_integral hh, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    have hex :
        Complex.exp ((↑(t * phase p.1) : ℂ) * Complex.I) *
          conj (Complex.exp ((↑(t * phase p.2) : ℂ) * Complex.I)) =
        Complex.exp ((↑(t * (phase p.1 - phase p.2)) : ℂ) * Complex.I) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        ← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold X O
    rw [map_mul, ← hex]
    ring
  calc
    _ = ENNReal.ofReal (∫ t, E t) := by
      rw [ofReal_integral_eq_lintegral_ofReal hEi (.of_forall hE0)]
      exact lintegral_congr (fun t => (hEt t).symm)
    _ = ‖∫ t, ∫ p, X t p ∂(volume : Measure (Ambient d)).prod volume‖ₑ := by
      simp_rw [hpair]
      rw [integral_complex_ofReal (f := E), ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg hE0)]
    _ ≤ ∫⁻ p, ‖∫ t, X t p‖ₑ ∂(volume : Measure (Ambient d)).prod volume := by
      rw [integral_integral_swap hXi]
      exact enorm_integral_le_lintegral_enorm _
    _ = _ := by
      have hc (v : ℂ) : ‖conj v‖ₑ = ‖v‖ₑ := by
        simp only [← ofReal_norm, Complex.norm_conj]
      simp_rw [htime, enorm_mul, hc]
      have hK : ∀ x, ‖(radonGaussianKernel h x : ℂ)‖ₑ =
          ENNReal.ofReal (radonGaussianKernel h x) := fun x => by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        unfold radonGaussianKernel
        positivity
      simp_rw [hK]
      exact lintegral_prod _ (by unfold radonGaussianKernel; fun_prop)

private theorem integrable_product_slice {d : ℕ} {f g : Ambient d → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) (s : Ambient d) :
    Integrable (fun u => f u * g (s - u)) := by
  refine (hfi.norm.mul_const M).mono' (by fun_prop) (.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

set_option maxHeartbeats 900000 in
/-- The actual Gaussian-weighted physical product energy is controlled by
the positive collision integral. The horizontal sum has already been
eliminated by the change of variables s = u + y. -/
theorem graph_extension_gaussian_product_energy_le {d : ℕ} {φ : Ambient d → ℝ}
    (hφ : Measurable φ) {f g : Ambient d → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f) (hgi : Integrable g)
    (hfs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0)
    (hgs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0)
    {M : ℝ} (hM : ∀ u, ‖g u‖ ≤ M) {h : ℝ} (hh : 0 < h) :
    (∫⁻ t, ‖radonGaussianSymbol h t‖ₑ *
      ∫⁻ x : Ambient d, ‖graphExtension f φ (x, t) * graphExtension g φ (x, t)‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ d) *
        ∫⁻ u, ∫⁻ y, ∫⁻ w, ‖f u‖ₑ * ‖g y‖ₑ * (‖f (u + y - w)‖ₑ * ‖g w‖ₑ) *
          ENNReal.ofReal (radonGaussianKernel h
            ((φ u + φ y - φ w - φ (u + y - w)) / (2 * Real.pi))) := by
  let C := ENNReal.ofReal ((2 * Real.pi) ^ d)
  let K := fun a : ℝ => ENNReal.ofReal (radonGaussianKernel h (a / (2 * Real.pi)))
  let S := fun s u => φ u + φ (s - u)
  let P := fun s u => ‖f u‖ₑ * ‖g (s - u)‖ₑ
  let E := fun z : ℝ × Ambient d => ‖radonGaussianSymbol h z.1‖ₑ *
    ‖graphProductConvolution φ f g z.1 z.2‖ₑ ^ (2 : ℕ)
  have hEm : Measurable E := ((radon_gaussian_symbol_measurable h).enorm.comp measurable_fst).mul
    ((graph_product_convolution_measurable hφ hf hg).enorm.pow_const _)
  have hswap : (∫⁻ t, ∫⁻ s, E (t, s)) = ∫⁻ s, ∫⁻ t, E (t, s) :=
    lintegral_lintegral_swap hEm.aemeasurable
  have hinner (s : Ambient d) :
      (∫⁻ t, E (t, s)) ≤ ∫⁻ u, ∫⁻ w, P s u * P s w * K (S s u - S s w) := by
    have hA : Measurable (fun u => f u * g (s - u)) := by fun_prop
    have hS : Measurable (S s) := by unfold S; fun_prop
    have H := gaussian_oscillatory_square hh hA (integrable_product_slice hf hg hfi hM s) hS
    simpa only [E, P, K, graphProductConvolution, enorm_mul] using H
  have hrow : Measurable (fun p : Ambient d × Ambient d =>
      ∫⁻ w, P p.1 p.2 * P p.1 w * K (S p.1 p.2 - S p.1 w)) := by
    have hm : Measurable (fun p : (Ambient d × Ambient d) × Ambient d =>
        P p.1.1 p.1.2 * P p.1.1 p.2 * K (S p.1.1 p.1.2 - S p.1.1 p.2)) := by
      unfold P K S radonGaussianKernel
      fun_prop
    exact hm.lintegral_prod_right'
  have ht : Measurable (fun t : ℝ => ∫⁻ s : Ambient d, E (t, s)) := hEm.lintegral_prod_right'
  calc
    _ = ∫⁻ t, C * (∫⁻ s, E (t, s)) := by
      apply lintegral_congr
      intro t
      have hq : Measurable (fun s : Ambient d => ‖graphProductConvolution φ f g t s‖ₑ ^ (2 : ℕ)) :=
        ((graph_product_convolution_measurable hφ hf hg).comp
          (measurable_const.prodMk measurable_id)).enorm.pow_const _
      change _ = C * ∫⁻ s, ‖radonGaussianSymbol h t‖ₑ *
        ‖graphProductConvolution φ f g t s‖ₑ ^ (2 : ℕ)
      rw [graph_extension_product_plancherel hφ hf hg hfi hgi hfs hgs hM t,
        lintegral_const_mul _ hq]
      unfold C
      ac_rfl
    _ = C * (∫⁻ t, ∫⁻ s, E (t, s)) := lintegral_const_mul C ht
    _ ≤ C * (∫⁻ s, ∫⁻ u, ∫⁻ w, P s u * P s w * K (S s u - S s w)) := by
      rw [hswap]
      exact mul_le_mul' le_rfl (lintegral_mono hinner)
    _ = _ := by
      rw [lintegral_lintegral_swap hrow.aemeasurable]
      congr 1
      apply lintegral_congr
      intro u
      have htranslate := measurePreserving_add_left (volume : Measure (Ambient d)) u
      have hrowu : Measurable (fun s : Ambient d => ∫⁻ w,
          P s u * P s w * K (S s u - S s w)) :=
        hrow.comp (measurable_id.prodMk measurable_const)
      calc
        _ = ∫⁻ y, ∫⁻ w, P (u + y) u * P (u + y) w *
            K (S (u + y) u - S (u + y) w) := (htranslate.lintegral_comp hrowu).symm
        _ = _ := by
          apply lintegral_congr
          intro y
          have hreflect := (volume : Measure (Ambient d)).measurePreserving_sub_left (u + y)
          have hm : Measurable (fun w => P (u + y) u * P (u + y) w *
              K (S (u + y) u - S (u + y) w)) := by
            unfold P S K radonGaussianKernel
            fun_prop
          calc
            _ = ∫⁻ w, P (u + y) u * P (u + y) (u + y - w) *
                K (S (u + y) u - S (u + y) (u + y - w)) :=
              (hreflect.lintegral_comp hm).symm
            _ = _ := by
              apply lintegral_congr
              intro w
              simp only [P, S, K, add_sub_cancel_left, sub_sub_cancel]
              congr 1
              congr 1
              congr 1
              abel_nf

end RestrictionWork
