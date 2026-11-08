import RestrictionWork.FilteredRadonKernel
import RestrictionWork.FilteredRadonSummation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

/-- Lebesgue average of a function over an offset strip of half-width h,
divided by h. The direction and offset are the two output coordinates. -/
def radonStrip {d : ℕ} (h : ℝ) (f : Ambient d → ℝ) (z : Ambient d × ℝ) : ℝ :=
  h⁻¹ * ∫ v in {v : Ambient d | |z.2 - ⟪v, z.1⟫| ≤ h}, f v

theorem radon_strip_measurable {d : ℕ} (h : ℝ) {f : Ambient d → ℝ}
    (hf : Measurable f) : Measurable (radonStrip h f) := by
  let S : Set ((Ambient d × ℝ) × Ambient d) :=
    {p | |p.1.2 - ⟪p.2, p.1.1⟫| ≤ h}
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hJ := (hf.comp measurable_snd).indicator hSm
  have he : radonStrip h f = fun z : Ambient d × ℝ =>
      h⁻¹ * ∫ v, S.indicator (fun p => f p.2) (z, v) := by
    funext z
    unfold radonStrip
    rw [← integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    rfl
  rw [he]
  exact measurable_const.mul hJ.stronglyMeasurable.integral_prod_right'.measurable

theorem radon_strip_le_gaussian_filter {d : ℕ} {h : ℝ} (hh : 0 < h)
    {f : Ambient d → ℝ} (hf : Measurable f) (hfi : Integrable f)
    (hf0 : ∀ v, 0 ≤ f v) (z : Ambient d × ℝ) :
    ‖radonStrip h f z‖ ≤ Real.exp Real.pi *
      ‖filteredRadon (radonGaussianSymbol h) (fun v => (f v : ℂ)) z‖ := by
  let S : Set (Ambient d) := {v | |z.2 - ⟪v, z.1⟫| ≤ h}
  let k : Ambient d → ℝ := fun v => radonGaussianKernel h (z.2 - ⟪v, z.1⟫)
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hk0 (v : Ambient d) : 0 ≤ k v := by
    dsimp only [k, radonGaussianKernel]
    positivity
  have hkle (v : Ambient d) : k v ≤ h⁻¹ := by
    unfold k radonGaussianKernel
    calc
      _ ≤ h⁻¹ * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))) (by positivity)
      _ = _ := mul_one _
  have hkfi : Integrable (fun v => k v * f v) := by
    refine (hfi.norm.const_mul h⁻¹).mono' (by unfold k radonGaussianKernel; fun_prop) ?_
    filter_upwards [] with v
    change ‖k v * f v‖ ≤ h⁻¹ * ‖f v‖
    rw [norm_mul, Real.norm_eq_abs (k v), abs_of_nonneg (hk0 v)]
    exact mul_le_mul_of_nonneg_right (hkle v) (norm_nonneg _)
  have hfcastm : Measurable (fun v => (f v : ℂ)) := Complex.continuous_ofReal.measurable.comp hf
  have hfcasti : Integrable (fun v => (f v : ℂ)) := Complex.ofRealCLM.integrable_comp hfi
  have he : filteredRadon (radonGaussianSymbol h) (fun v => (f v : ℂ)) z =
      ((∫ v, k v * f v : ℝ) : ℂ) := by
    rw [filtered_radon_kernel (radon_gaussian_symbol_measurable h)
      (radon_gaussian_symbol_integrable hh) hfcastm hfcasti z]
    simp_rw [inverse_fourier_radon_gaussian hh, ← Complex.ofReal_mul]
    exact integral_ofReal
  have hstrip0 : 0 ≤ radonStrip h f z :=
    mul_nonneg (inv_nonneg.mpr hh.le) (integral_nonneg hf0)
  have hkn : 0 ≤ ∫ v, k v * f v := integral_nonneg fun v => mul_nonneg (hk0 v) (hf0 v)
  rw [he, Real.norm_eq_abs, abs_of_nonneg hstrip0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hkn, ← integral_const_mul]
  change h⁻¹ * (∫ v in S, f v) ≤ _
  rw [← integral_indicator hS, ← integral_const_mul]
  apply integral_mono ((hfi.indicator hS).const_mul _) (hkfi.const_mul _)
  intro v
  by_cases hv : v ∈ S
  · have hx : |z.2 - ⟪v, z.1⟫| ≤ h := hv
    have hd : |(z.2 - ⟪v, z.1⟫) / h| ≤ 1 := by
      rw [abs_div, abs_of_pos hh, div_le_iff₀ hh, one_mul]
      exact hx
    have hsq := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hd
    rw [sq_abs, one_pow] at hsq
    have hgl : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * ((z.2 - ⟪v, z.1⟫) / h) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le])
    have hpoint : h⁻¹ ≤ Real.exp Real.pi * k v := by
      calc
        _ = h⁻¹ * (Real.exp Real.pi * Real.exp (-Real.pi)) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ h⁻¹ * (Real.exp Real.pi *
            Real.exp (-Real.pi * ((z.2 - ⟪v, z.1⟫) / h) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgl (Real.exp_pos _).le) (by positivity)
        _ = _ := by unfold k radonGaussianKernel; ring
    change h⁻¹ * S.indicator f v ≤ Real.exp Real.pi * (k v * f v)
    rw [indicator_of_mem hv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hpoint (hf0 v)
  · change h⁻¹ * S.indicator f v ≤ Real.exp Real.pi * (k v * f v)
    rw [indicator_of_notMem hv, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hk0 v) (hf0 v))

/-- The genuine strip averages obey an estimate uniform in the half-width,
in the range 2 ≤ q < d+1. For bounded data of mass M the high-frequency term
has the Radon power M^(1−1/q). -/
theorem radon_strip_uniform_bound {d : ℕ} (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h)
    {f : Ambient d → ℝ} (hf : Measurable f) (hfi : Integrable f) (hf₂ : MemLp f 2)
    (hf0 : ∀ v, 0 ≤ f v) {q : ℝ} (hq : 2 ≤ q) (hqd : q < (d : ℝ) + 1) (L : ℝ) :
    let ν := (OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod
      (volume.restrict (Icc (-L) L))
    eLpNorm (radonStrip h f) (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal (2 * Real.exp Real.pi) *
        (eLpNorm f 1 volume * ν univ ^ (1 / q) +
          (eLpNorm f 1 volume ^ ((q - 2) / q) * eLpNorm f 2 volume ^ (2 / q)) *
            ENNReal.ofReal ((1 - (2 : ℝ) ^ (1 - ((d : ℝ) + 1) / q))⁻¹)) := by
  intro ν
  let g : Ambient d → ℂ := fun v => f v
  let m := radonGaussianSymbol h
  have hgm : Measurable g := Complex.continuous_ofReal.measurable.comp hf
  have hgi : Integrable g := Complex.ofRealCLM.integrable_comp hfi
  have hgNorm (p : ℝ≥0∞) : eLpNorm g p volume = eLpNorm f p volume := by
    apply eLpNorm_congr_norm_ae hgm.aestronglyMeasurable hf.aestronglyMeasurable
    exact .of_forall fun v => Complex.norm_real (f v)
  have hg₂ : MemLp g 2 := by
    rw [memLp_iff, hgNorm]
    exact hf₂.eLpNorm_lt_top
  have H := filtered_radon_uniform_frequency_bound hd (radon_gaussian_symbol_measurable h)
    (radon_gaussian_symbol_integrable hh) (radon_gaussian_symbol_norm_le_one h) hgi hg₂ hq hqd L
  change eLpNorm (filteredRadon m g) (ENNReal.ofReal q) ν ≤ _ at H
  rw [hgNorm 1, hgNorm 2] at H
  have hpoint : ∀ᵐ z ∂ν, ‖radonStrip h f z‖ ≤
      ‖((Real.exp Real.pi : ℝ) : ℂ) • filteredRadon m g z‖ := by
    filter_upwards [] with z
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs (Real.exp Real.pi), abs_of_pos (Real.exp_pos _)]
    exact radon_strip_le_gaussian_filter hh hf hfi hf0 z
  have HS := eLpNorm_mono_ae
    (f := radonStrip h f) (g := ((Real.exp Real.pi : ℝ) : ℂ) • filteredRadon m g)
    (p := ENNReal.ofReal q) (radon_strip_measurable h hf).aestronglyMeasurable hpoint
  rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at HS
  apply HS.trans
  calc
    _ ≤ _ := mul_le_mul' (le_refl _) H
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      ring

/-- For data bounded by an indicator, the strip estimate has the support
measure power 1−1/q. The constant is uniform in the strip half-width. -/
theorem radon_strip_restricted_bound {d : ℕ} (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h)
    {f : Ambient d → ℝ} (hf : Measurable f) {A : Set (Ambient d)} (hA : MeasurableSet A)
    {V : ℝ≥0∞} (hV : V < ⊤) (hAV : volume A ≤ V)
    (hf0 : ∀ v, 0 ≤ f v) (hfA : ∀ v, f v ≤ A.indicator (fun _ => (1 : ℝ)) v)
    {q : ℝ} (hq : 2 ≤ q) (hqd : q < (d : ℝ) + 1) (L : ℝ) :
    let ν := (OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod
      (volume.restrict (Icc (-L) L))
    eLpNorm (radonStrip h f) (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal (2 * Real.exp Real.pi) *
        (V ^ (1 / q) * ν univ ^ (1 / q) +
          ENNReal.ofReal ((1 - (2 : ℝ) ^ (1 - ((d : ℝ) + 1) / q))⁻¹)) *
        (volume A) ^ (1 - 1 / q) := by
  intro ν
  let M := volume A
  have hM : M < ⊤ := hAV.trans_lt hV
  have hq0 : 0 < q := by linarith
  have hq1 : 0 ≤ 1 / q := by positivity
  have hq' : 0 ≤ 1 - 1 / q := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hq0).mpr
    linarith
  have hqα : 0 ≤ (q - 2) / q := by positivity
  have hqβ : 0 ≤ 2 / q := by positivity
  have hnorm (p : ℝ) (hp : 0 < p) :
      eLpNorm f (ENNReal.ofReal p) volume ≤ M ^ (1 / p) := by
    refine (eLpNorm_mono_ae (g := A.indicator (fun _ => (1 : ℝ))) hf.aestronglyMeasurable
      (.of_forall fun v => by
        rw [Real.norm_eq_abs (f v), abs_of_nonneg (hf0 v)]
        exact (hfA v).trans (le_abs_self _))).trans_eq ?_
    rw [eLpNorm_indicator_const hA.nullMeasurableSet (by positivity) ENNReal.ofReal_ne_top]
    simp only [← ofReal_norm, Real.norm_eq_abs, abs_one, ENNReal.ofReal_one, one_mul, ENNReal.toReal_ofReal hp.le, M]
  have h1 : eLpNorm f 1 volume ≤ M := by
    simpa only [ENNReal.ofReal_one, one_div_one, ENNReal.rpow_one] using hnorm 1 zero_lt_one
  have h2 : eLpNorm f 2 volume ≤ M ^ (1 / 2 : ℝ) := by
    simpa only [ENNReal.ofReal_ofNat] using hnorm 2 (by norm_num)
  have hfi : Integrable f := memLp_one_iff_integrable.mp (h1.trans_lt hM)
  have hf₂ : MemLp f 2 := h2.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne)
  have hlow : M ≤ V ^ (1 / q) * M ^ (1 - 1 / q) := by
    calc
      _ = M ^ (1 / q) * M ^ (1 - 1 / q) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hq1 hq', add_sub_cancel, ENNReal.rpow_one]
      _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hAV hq1) le_rfl
  have hhigh : eLpNorm f 1 volume ^ ((q - 2) / q) * eLpNorm f 2 volume ^ (2 / q) ≤
      M ^ (1 - 1 / q) := by
    calc
      _ ≤ M ^ ((q - 2) / q) * (M ^ (1 / 2 : ℝ)) ^ (2 / q) :=
        mul_le_mul' (ENNReal.rpow_le_rpow h1 hqα) (ENNReal.rpow_le_rpow h2 hqβ)
      _ = _ := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ hqα (by positivity)]
        congr 1
        field_simp
        ring
  let C := ENNReal.ofReal ((1 - (2 : ℝ) ^ (1 - ((d : ℝ) + 1) / q))⁻¹)
  apply (radon_strip_uniform_bound hd hh hf hfi hf₂ hf0 hq hqd L).trans
  change ENNReal.ofReal (2 * Real.exp Real.pi) *
    (eLpNorm f 1 volume * ν univ ^ (1 / q) +
      (eLpNorm f 1 volume ^ ((q - 2) / q) * eLpNorm f 2 volume ^ (2 / q)) * C) ≤ _
  calc
    _ ≤ ENNReal.ofReal (2 * Real.exp Real.pi) *
        ((V ^ (1 / q) * M ^ (1 - 1 / q)) * ν univ ^ (1 / q) + M ^ (1 - 1 / q) * C) :=
      mul_le_mul' le_rfl (add_le_add (mul_le_mul' (h1.trans hlow) le_rfl) (mul_le_mul' hhigh le_rfl))
    _ = _ := by dsimp only [M, C]; ring

end RestrictionWork
