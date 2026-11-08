import RestrictionWork.FilteredRadonL2
import OAI.Analysis.Fourier.Restriction.BandPowers
import OAI.Analysis.Fourier.Radial.Sphere.Measure
import OAI.Analysis.Fourier.Restriction.BoundedInput

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter FourierTransform
open scoped ENNReal Topology RealInnerProductSpace
namespace RestrictionWork

private theorem radon_offset_character_integrable (t : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun ρ : ℝ => Real.fourierChar ⟪ρ, t⟫ • g ρ) := by
  have hc : Continuous (fun ρ : ℝ => (Real.fourierChar ⟪ρ, t⟫ : ℂ)) := by fun_prop
  simp only [Circle.smul_def]
  exact hg.bdd_smul 1 hc.aestronglyMeasurable (.of_forall fun _ => by simp)

private theorem filtered_radon_add {d : ℕ} {m n : ℝ → ℂ} {f : Ambient d → ℂ}
    (hm : Integrable m) (hn : Integrable n) (hf : Integrable f) :
    filteredRadon (m + n) f = filteredRadon m f + filteredRadon n f := by
  funext z
  simp only [filteredRadon, Pi.add_apply, Real.fourierInv_eq, add_mul, smul_add]
  exact integral_add
    (radon_offset_character_integrable z.2 (filtered_radon_slice_integrable hm hf z.1))
    (radon_offset_character_integrable z.2 (filtered_radon_slice_integrable hn hf z.1))

private theorem filtered_radon_indicator_limit {d : ℕ} {m : ℝ → ℂ} {f : Ambient d → ℂ}
    (hmi : Integrable m) (hf : Integrable f) (z : Ambient d × ℝ) :
    Tendsto (fun N : ℕ => filteredRadon ((Iio ((2 : ℝ) ^ N)).indicator m) f z)
      atTop (𝓝 (filteredRadon m f z)) := by
  let g (ρ : ℝ) : ℂ := Real.fourierChar ⟪ρ, z.2⟫ • (m ρ * (𝓕 f) (ρ • z.1))
  have hg : Integrable g :=
    radon_offset_character_integrable z.2 (filtered_radon_slice_integrable hmi hf z.1)
  have he (N : ℕ) : filteredRadon ((Iio ((2 : ℝ) ^ N)).indicator m) f z =
      ∫ ρ, (Iio ((2 : ℝ) ^ N)).indicator g ρ := by
    unfold filteredRadon
    rw [Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards [] with ρ
    by_cases h : ρ ∈ Iio ((2 : ℝ) ^ N)
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul, smul_zero]
  simp_rw [he, show filteredRadon m f z = ∫ ρ, g ρ by rw [filteredRadon, Real.fourierInv_eq]]
  apply tendsto_integral_of_dominated_convergence (fun ρ => ‖g ρ‖)
  · exact fun N => (hg.indicator measurableSet_Iio).aestronglyMeasurable
  · exact hg.norm
  · intro N
    filter_upwards [] with ρ
    by_cases h : ρ ∈ Iio ((2 : ℝ) ^ N) <;> simp [h]
  · filter_upwards [] with ρ
    have hp : Tendsto (fun N : ℕ => (2 : ℝ) ^ N) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    apply tendsto_const_nhds.congr'
    filter_upwards [hp.eventually_gt_atTop ρ] with N hN
    exact (indicator_of_mem (show ρ ∈ Iio ((2 : ℝ) ^ N) from hN) g).symm

private theorem norm_radon_indicator_le_one {s : Set ℝ} {m : ℝ → ℂ}
    (hm : ∀ ρ, ‖m ρ‖ ≤ 1) (ρ : ℝ) : ‖s.indicator m ρ‖ ≤ 1 := by
  by_cases h : ρ ∈ s
  · rw [indicator_of_mem h]
    exact hm ρ
  · rw [indicator_of_notMem h, norm_zero]
    exact zero_le_one

private theorem radon_frequency_interval_one_norm {m : ℝ → ℂ}
    (hm : Measurable m) (hb : ∀ ρ, ‖m ρ‖ ≤ 1) {l u : ℝ} :
    eLpNorm ((Ico l u).indicator m) 1 volume ≤ ENNReal.ofReal (u - l) := by
  have H := OAI.Analysis.Fourier.Restriction.eLpNorm_le_bound_mul_measure
    (volume : Measure ℝ) (E := Ico l u) (hm.indicator measurableSet_Ico).aestronglyMeasurable
    measurableSet_Ico (A := (1 : ℝ)) zero_le_one
    (norm_radon_indicator_le_one hb)
    (fun ρ h => indicator_of_notMem h m) (p := 1) (by norm_num)
  simpa only [ENNReal.ofReal_one, one_mul, one_div_one, ENNReal.rpow_one, Real.volume_Ico] using H

private theorem filtered_radon_band_bound {d : ℕ} (hd : 1 ≤ d)
    {m : ℝ → ℂ} (hm : Measurable m) (hmi : Integrable m) (hm₂ : MemLp m 2)
    (hmb : ∀ ρ, ‖m ρ‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hms : ∀ ρ < R, m ρ = 0) (hm₁ : eLpNorm m 1 volume ≤ ENNReal.ofReal R)
    {f : Ambient d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2)
    {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm (filteredRadon m f) (ENNReal.ofReal q)
        ((OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod volume) ≤
      (ENNReal.ofReal R) ^ (1 - ((d : ℝ) + 1) / q) *
        (eLpNorm f 1 volume ^ ((q - 2) / q) * eLpNorm f 2 volume ^ (2 / q)) := by
  let ν := (OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod (volume : Measure ℝ)
  let Rm := filteredRadon m f
  let A := ENNReal.ofReal R
  let U := eLpNorm f 1 volume
  let V := eLpNorm f 2 volume
  have hq0 : 0 < q := by linarith
  have hq1 : 0 ≤ (q - 2) / q := div_nonneg (sub_nonneg.mpr hq) hq0.le
  have hq2 : 0 ≤ 1 / q := by positivity
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint : ∀ᵐ z ∂ν, ‖Rm z‖ₑ ≤ A * U := .of_forall fun z =>
    (filtered_radon_uniform_bound hmi hf z).trans (mul_le_mul' hm₁ le_rfl)
  have h₂ := filtered_radon_two_norm_sq_le hd hm hmi hm₂ hmb hR hms hf hf₂
  have H := OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_enorm_bound ν
    (filtered_radon_measurable hm hf).aestronglyMeasurable (by norm_num : (0 : ℝ) < 2) hq hpoint
  have he (B : ℝ≥0∞) : B ^ (2 / q) = (B ^ (2 : ℕ)) ^ (1 / q) := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hdecay : A ^ ((q - 2) / q) * ((ENNReal.ofReal (R ^ (d - 1)))⁻¹) ^ (1 / q) =
      A ^ (1 - ((d : ℝ) + 1) / q) := by
    rw [ENNReal.ofReal_pow hR.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_neg,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ hA0 hAt]
    have hdcast : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd, Nat.cast_one]
    rw [hdcast]
    congr 1
    field_simp
    ring
  apply (show eLpNorm Rm (ENNReal.ofReal q) ν ≤
      (A * U) ^ ((q - 2) / q) * eLpNorm Rm 2 ν ^ (2 / q) by
    simpa only [ENNReal.ofReal_ofNat] using H).trans
  calc
    _ ≤ (A * U) ^ ((q - 2) / q) *
        (((ENNReal.ofReal (R ^ (d - 1)))⁻¹) * V ^ (2 : ℕ)) ^ (1 / q) := by
      rw [he]
      exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow h₂ hq2)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq1, ENNReal.mul_rpow_of_nonneg _ _ hq2, ← he]
      calc
        _ = (A ^ ((q - 2) / q) * ((ENNReal.ofReal (R ^ (d - 1)))⁻¹) ^ (1 / q)) *
            (U ^ ((q - 2) / q) * V ^ (2 / q)) := by ac_rfl
        _ = _ := by rw [hdecay]

/-- Uniform summation of all positive frequency bands below the Radon
endpoint, with only a finite offset interval used for the low band. -/
theorem filtered_radon_positive_frequency_bound {d : ℕ} (hd : 1 ≤ d)
    {m : ℝ → ℂ} (hm : Measurable m) (hmi : Integrable m)
    (hmb : ∀ ρ, ‖m ρ‖ ≤ 1) (hms : ∀ ρ < 0, m ρ = 0)
    {f : Ambient d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2)
    {q : ℝ} (hq : 2 ≤ q) (hqd : q < (d : ℝ) + 1) (T : Set ℝ) :
    let ν := (OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod (volume.restrict T)
    eLpNorm (filteredRadon m f) (ENNReal.ofReal q) ν ≤
      eLpNorm f 1 volume * ν univ ^ (1 / q) +
        (eLpNorm f 1 volume ^ ((q - 2) / q) * eLpNorm f 2 volume ^ (2 / q)) *
          ENNReal.ofReal ((1 - (2 : ℝ) ^ (1 - ((d : ℝ) + 1) / q))⁻¹) := by
  intro ν
  let μ := (OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod (volume : Measure ℝ)
  let A := eLpNorm f 1 volume * ν univ ^ (1 / q)
  let B := eLpNorm f 1 volume ^ ((q - 2) / q) * eLpNorm f 2 volume ^ (2 / q)
  let s : ℝ := 1 - ((d : ℝ) + 1) / q
  let r : ℝ := (2 : ℝ) ^ s
  let mcut (N : ℕ) := (Iio ((2 : ℝ) ^ N)).indicator m
  let mband (j : ℕ) := (Ico ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))).indicator m
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by dsimp only [s]; linarith only [(lt_div_iff₀ hq0).mpr (by simpa using hqd : 1 * q < (d : ℝ) + 1)])
  have hν : ν ≤ μ := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hcutm (N : ℕ) : Measurable (mcut N) := hm.indicator measurableSet_Iio
  have hcuti (N : ℕ) : Integrable (mcut N) := hmi.indicator measurableSet_Iio
  have hbandi (j : ℕ) : Integrable (mband j) := hmi.indicator measurableSet_Ico
  have hlow : eLpNorm (filteredRadon (mcut 0) f) (ENNReal.ofReal q) ν ≤ A := by
    have he : mcut 0 = (Ico (0 : ℝ) 1).indicator m := by
      funext ρ
      simp only [mcut, pow_zero, indicator_apply, mem_Iio, mem_Ico]
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact hms ρ (lt_of_not_ge (fun h => h₂ ⟨h, h₁⟩))
      · tauto
      · rfl
    have hm1 : eLpNorm (mcut 0) 1 volume ≤ 1 := by
      rw [he]
      simpa using (radon_frequency_interval_one_norm hm hmb (l := 0) (u := 1))
    have hb : ∀ᵐ z ∂ν, ‖filteredRadon (mcut 0) f z‖ₑ ≤ eLpNorm f 1 volume :=
      .of_forall fun z => (filtered_radon_uniform_bound (hcuti 0) hf z).trans
        (by simpa only [one_mul] using mul_le_mul' hm1 (le_refl (eLpNorm f 1 volume)))
    simpa only [A, smul_eq_mul, ENNReal.toReal_ofReal hq0.le, one_div] using
      (eLpNorm_le_of_ae_enorm_bound (p := ENNReal.ofReal q)
        (filtered_radon_measurable (hcutm 0) hf).aestronglyMeasurable hb)
  have hband (j : ℕ) :
      eLpNorm (filteredRadon (mband j) f) (ENNReal.ofReal q) ν ≤ B * ENNReal.ofReal (r ^ j) := by
    have hb : ∀ ρ, ‖mband j ρ‖ ≤ 1 := norm_radon_indicator_le_one hmb
    have hm2 : MemLp (mband j) 2 := by
      have hmem := memLp_top_of_bound (hm.indicator measurableSet_Ico).aestronglyMeasurable
        (1 : ℝ) (μ := volume) (.of_forall hb)
      exact hmem.mono_exponent_of_measure_support_ne_top
        (s := Ico ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)))
        (fun ρ h => indicator_of_notMem h m)
        (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top) le_top
    have hs : ∀ ρ < (2 : ℝ) ^ j, mband j ρ = 0 := fun ρ h =>
      indicator_of_notMem (fun hx : ρ ∈ Ico ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)) => h.not_ge hx.1) m
    have hm1 : eLpNorm (mband j) 1 volume ≤ ENNReal.ofReal ((2 : ℝ) ^ j) := by
      have he : (2 : ℝ) ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; ring
      simpa only [mband, he] using radon_frequency_interval_one_norm hm hmb
        (l := (2 : ℝ) ^ j) (u := (2 : ℝ) ^ (j + 1))
    have h := (eLpNorm_mono_measure (filteredRadon (mband j) f) hν).trans
      (filtered_radon_band_bound hd (hm.indicator measurableSet_Ico) (hbandi j) hm2 hb
        (by positivity) hs hm1 hf hf₂ hq)
    have hrp : (ENNReal.ofReal ((2 : ℝ) ^ j)) ^ s = ENNReal.ofReal (r ^ j) := by
      rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← Real.rpow_natCast_mul (by norm_num),
        mul_comm (j : ℝ) s, Real.rpow_mul_natCast (by norm_num)]
    rw [mul_comm B, ← hrp]
    exact h
  have hsplit (N : ℕ) : mcut (N + 1) = mcut N + mband N := by
    funext ρ
    have hp : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (N + 1) := by
      rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N]
    by_cases hl : ρ < (2 : ℝ) ^ N
    · simp [mcut, mband, hl, hl.trans_le hp, hl.not_ge]
    · by_cases hu : ρ < (2 : ℝ) ^ (N + 1)
      · simp [mcut, mband, hl, hu, le_of_not_gt hl]
      · simp [mcut, mband, hl, hu]
  have hcut (N : ℕ) : eLpNorm (filteredRadon (mcut N) f) (ENNReal.ofReal q) ν ≤
      A + ∑ j ∈ Finset.range N, B * ENNReal.ofReal (r ^ j) := by
    induction N with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using hlow
    | succ N ih =>
      rw [hsplit, filtered_radon_add (hcuti N) (hbandi N) hf, Finset.sum_range_succ, ← add_assoc]
      exact (eLpNorm_add_le hq1).trans (add_le_add ih (hband N))
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise ν
    (fun N => (filtered_radon_measurable (hcutm N) hf).aestronglyMeasurable)
    (filtered_radon_measurable hm hf).aestronglyMeasurable
    (filtered_radon_indicator_limit hmi hf) hq0
  intro N
  exact (hcut N).trans (add_le_add le_rfl
    (OAI.Analysis.Fourier.Restriction.sum_mul_ofReal_geometric_le B hr0 hr1 N))

private theorem filtered_radon_reflect {d : ℕ} (m : ℝ → ℂ) (f : Ambient d → ℂ) :
    filteredRadon m f = filteredRadon (fun ρ => m (-ρ)) f ∘
      (fun z : Ambient d × ℝ => (-z.1, -z.2)) := by
  funext z
  simp only [filteredRadon, Function.comp_apply, Real.fourierInv_eq]
  have h := integral_neg_eq_self (fun ρ : ℝ =>
    Real.fourierChar ⟪ρ, -z.2⟫ • (m (-ρ) * (𝓕 f) (ρ • -z.1))) volume
  simpa only [Function.comp_apply, neg_neg, inner_neg_left, inner_neg_right, neg_smul, smul_neg] using h

/-- An arbitrary bounded integrable offset-frequency multiplier has a
uniform Radon estimate below the endpoint, independent of its cutoff scale. -/
theorem filtered_radon_uniform_frequency_bound {d : ℕ} (hd : 1 ≤ d)
    {m : ℝ → ℂ} (hm : Measurable m) (hmi : Integrable m) (hmb : ∀ ρ, ‖m ρ‖ ≤ 1)
    {f : Ambient d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2)
    {q : ℝ} (hq : 2 ≤ q) (hqd : q < (d : ℝ) + 1) (L : ℝ) :
    let ν := (OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod
      (volume.restrict (Icc (-L) L))
    eLpNorm (filteredRadon m f) (ENNReal.ofReal q) ν ≤
      2 * (eLpNorm f 1 volume * ν univ ^ (1 / q) +
        (eLpNorm f 1 volume ^ ((q - 2) / q) * eLpNorm f 2 volume ^ (2 / q)) *
          ENNReal.ofReal ((1 - (2 : ℝ) ^ (1 - ((d : ℝ) + 1) / q))⁻¹)) := by
  intro ν
  let T := Icc (-L) L
  let mpos := (Ici (0 : ℝ)).indicator m
  let mneg := (Iio (0 : ℝ)).indicator m
  let mref : ℝ → ℂ := fun ρ => mneg (-ρ)
  have hpos : Measurable mpos := hm.indicator measurableSet_Ici
  have hneg : Measurable mneg := hm.indicator measurableSet_Iio
  have hposi : Integrable mpos := hmi.indicator measurableSet_Ici
  have hnegi : Integrable mneg := hmi.indicator measurableSet_Iio
  have href : Measurable mref := hneg.comp measurable_neg
  have hrefi : Integrable mref :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hnegi
  have hsum : m = mpos + mneg := by
    funext ρ
    change m ρ = (Ici (0 : ℝ)).indicator m ρ + (Iio (0 : ℝ)).indicator m ρ
    by_cases hρ : 0 ≤ ρ
    · rw [indicator_of_mem (show ρ ∈ Ici (0 : ℝ) from hρ),
        indicator_of_notMem (show ρ ∉ Iio (0 : ℝ) from not_lt_of_ge hρ), add_zero]
    · rw [indicator_of_notMem (show ρ ∉ Ici (0 : ℝ) from hρ),
        indicator_of_mem (show ρ ∈ Iio (0 : ℝ) from lt_of_not_ge hρ), zero_add]
  have hTpre : (fun t : ℝ => -t) ⁻¹' T = T := by
    ext t
    change (-L ≤ -t ∧ -t ≤ L) ↔ (-L ≤ t ∧ t ≤ L)
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hTneg : MeasurePreserving (fun t : ℝ => -t) (volume.restrict T) (volume.restrict T) := by
    refine ⟨measurable_neg, ?_⟩
    conv_lhs => rw [← hTpre]
    rw [← Measure.restrict_map measurable_neg measurableSet_Icc, Measure.map_neg_eq_self]
  have hSneg : MeasurePreserving (fun θ : Ambient d => -θ)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure d)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure d) :=
    OAI.Analysis.Fourier.Radial.measurePreserving_sphere_orthogonal (LinearIsometryEquiv.neg ℝ)
  have hnormneg : eLpNorm (filteredRadon mneg f) (ENNReal.ofReal q) ν =
      eLpNorm (filteredRadon mref f) (ENNReal.ofReal q) ν := by
    rw [filtered_radon_reflect mneg f]
    exact eLpNorm_comp_measurePreserving (filtered_radon_measurable href hf).aestronglyMeasurable
      (hSneg.prod hTneg)
  have hbpos : ∀ ρ, ‖mpos ρ‖ ≤ 1 := norm_radon_indicator_le_one hmb
  have hbref : ∀ ρ, ‖mref ρ‖ ≤ 1 := fun ρ => norm_radon_indicator_le_one hmb (-ρ)
  have hspos : ∀ ρ < 0, mpos ρ = 0 := fun ρ h => indicator_of_notMem h.not_ge m
  have hsref : ∀ ρ < 0, mref ρ = 0 := fun ρ h =>
    indicator_of_notMem (show -ρ ∉ Iio (0 : ℝ) by change ¬-ρ < 0; linarith) m
  have hq1 : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [hsum, filtered_radon_add hposi hnegi hf, two_mul]
  apply (eLpNorm_add_le hq1).trans
  rw [hnormneg]
  exact add_le_add (filtered_radon_positive_frequency_bound hd hpos hposi hbpos hspos hf hf₂ hq hqd T)
    (filtered_radon_positive_frequency_bound hd href hrefi hbref hsref hf hf₂ hq hqd T)

end RestrictionWork
