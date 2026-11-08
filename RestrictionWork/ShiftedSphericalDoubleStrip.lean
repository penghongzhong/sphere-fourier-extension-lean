import RestrictionWork.ShiftedSphericalStereoMeasure
import RestrictionWork.RadonStripBound
import OAI.MeasureTheory.Kakeya.Maximal
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

private def radialCoordinates {d : ℕ} (v : Ambient d) : Ambient d × ℝ :=
  (‖v‖⁻¹ • v, ‖v‖)

private theorem measurable_radialCoordinates (d : ℕ) :
    Measurable (@radialCoordinates d) := by
  unfold radialCoordinates
  fun_prop

private theorem polar_annulus_bound {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L)
    {F : Ambient d × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v in {v : Ambient d | 0 < ‖v‖ ∧ ‖v‖ ≤ L}, F (radialCoordinates v)) ≤
      ENNReal.ofReal (L ^ (d - 1)) *
        ∫⁻ z, F z ∂(OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod
          (volume.restrict (Icc (-L) L)) := by
  let U : Set (Ambient d) := {v | 0 < ‖v‖ ∧ ‖v‖ ≤ L}
  let I := Icc (-L) L
  let μ := OAI.Analysis.Fourier.Restriction.sphereMeasure d
  let C := ENNReal.ofReal (L ^ (d - 1))
  have hn : Measurable (fun v : Ambient d => ‖v‖) := measurable_id.norm
  have hU : MeasurableSet U := (measurableSet_lt measurable_const hn).inter
    (measurableSet_le hn measurable_const)
  have hG := (hF.comp (measurable_radialCoordinates d)).indicator hU
  have hslice : Measurable (fun ω : Ambient d => ∫⁻ t in I, F (ω, t)) :=
    hF.lintegral_prod_right'
  change (∫⁻ v in U, (F ∘ radialCoordinates) v) ≤ C * ∫⁻ z, F z ∂μ.prod (volume.restrict I)
  rw [← lintegral_indicator hU,
    OAI.Analysis.Fourier.Restriction.lintegral_polar_sphereMeasure hd hG,
    lintegral_prod _ hF.aemeasurable, ← lintegral_const_mul C hslice]
  apply lintegral_mono_ae
  filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm d] with ω hω
  have hFω : Measurable (fun t : ℝ => F (ω, t)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_const_mul C hFω,
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Icc]
  apply lintegral_mono
  intro t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have ht0 : 0 < t := ht
    have hn : ‖t • ω‖ = t := by rw [norm_smul, hω, Real.norm_eq_abs, abs_of_pos ht0, mul_one]
    have hc : radialCoordinates (t • ω) = (ω, t) := by
      rw [radialCoordinates, hn, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
    rw [indicator_of_mem ht]
    by_cases htL : t ≤ L
    · have htU : t • ω ∈ U := ⟨by rwa [hn], by rwa [hn]⟩
      have htI : t ∈ I := ⟨by linarith, htL⟩
      rw [indicator_of_mem htU, indicator_of_mem htI, Function.comp_apply, hc]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht0.le htL _)) le_rfl
    · have htU : t • ω ∉ U := fun h => htL (hn ▸ h.2)
      rw [indicator_of_notMem htU, mul_zero]
      exact zero_le
  · rw [indicator_of_notMem ht]
    exact zero_le

private theorem strip_volume_eq {d : ℕ} {h : ℝ} (hh : 0 < h)
    {V : Set (Ambient d)} (hV : MeasurableSet V) (hVf : volume V < ⊤)
    (z : Ambient d × ℝ) :
    volume (V ∩ {v | |z.2 - ⟪v, z.1⟫| ≤ h}) =
      ENNReal.ofReal h * ‖radonStrip h (V.indicator (fun _ => (1 : ℝ))) z‖ₑ := by
  let S : Set (Ambient d) := {v | |z.2 - ⟪v, z.1⟫| ≤ h}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hVS : volume (V ∩ S) ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt hVf).ne
  have he : radonStrip h (V.indicator (fun _ => (1 : ℝ))) z =
      h⁻¹ * (volume (V ∩ S)).toReal := by
    unfold radonStrip
    change h⁻¹ * (∫ v in S, V.indicator (fun _ => (1 : ℝ)) v) = _
    rw [integral_indicator hV, setIntegral_const, Measure.real_def, Measure.restrict_apply hV, smul_eq_mul, mul_one]
  rw [← ofReal_norm, he, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ← ENNReal.ofReal_mul hh.le, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul,
    ENNReal.ofReal_toReal hVS]

private theorem stereo_image_measurable {d : ℕ} {δ r σ : ℝ} {a u : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) (hσ : 0 < σ)
    (hPu : shiftedCapPoint δ a r u ≠ 0)
    {B : Set (Ambient d)} (hB : MeasurableSet B)
    (hBD : B ⊆ {v | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖}) :
    MeasurableSet ((shiftedStereoChart δ a r u hPu) '' B) := by
  refine hB.image_of_measurable_injOn (shifted_stereo_chart_measurable δ a r u hPu) ?_
  intro x hx y hy he
  let P := shiftedCapPoint δ a r
  let S := fun v => sphereStereo (δ * r) (P u) (P v)
  let L := sphereTangentCoordinates (P u) hPu
  have ht (v : Ambient d) (hv : v ∈ B) : ⟪P u, S v⟫ = 0 :=
    (shifted_spherical_stereo_tangent_annulus hδ hδhalf ha hr hrhalf hu
      (hBD hv).1 hσ (hBD hv).2).1
  have hsub : ⟪P u, S x - S y⟫ = 0 := by rw [inner_sub_right, ht x hx, ht y hy, sub_self]
  have he' : L (S x - S y) = 0 := by
    change L (S x) = L (S y) at he
    rw [map_sub, he, sub_self]
  have hs : S x - S y = 0 := by
    have H := sphere_tangent_coordinates_inner hPu hsub hsub
    rw [he', inner_zero_left, real_inner_self_eq_norm_sq, eq_comm, pow_eq_zero_iff (by decide : 2 ≠ 0),
      norm_eq_zero] at H
    exact H
  have hb := (shifted_spherical_stereo_distance_bounds hδ hδhalf ha hr hrhalf hu
    (hBD hx).1 (hBD hy).1 hσ (hBD hx).2 (hBD hy).2).1
  change ‖x - y‖ / 16 ≤ ‖S x - S y‖ at hb
  rw [hs, norm_zero] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg _)))

/-- A double collision strip for the normalized spherical graph has the
restricted Radon powers in both supports. The constant is independent of
the scale, shift, strip width, and choice of pole. -/
theorem shifted_collision_double_strip_bound {d : ℕ} (hd : 1 ≤ d)
    {q σ : ℝ} (hq : 2 ≤ q) (hqd : q < (d : ℝ) + 1) (hσ : 0 < σ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {δ r ε : ℝ} {a u : Ambient d},
        0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 → 0 < r → r ≤ 1 / 2 →
        ‖u‖ ≤ 1 → 0 < ε →
        ∀ {A B : Set (Ambient d)}, MeasurableSet A → MeasurableSet B →
          A ⊆ {v | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖} →
          B ⊆ {v | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖} →
          (∫⁻ y in A, volume (B ∩ {w | ‖u + y - w‖ ≤ 1 ∧
            |shiftedCollisionPhase δ a r u y w| ≤ ε})) ≤
              C * ENNReal.ofReal ε * (volume A) ^ (1 - 1 / q) * (volume B) ^ (1 - 1 / q) := by
  let L := 1 / σ
  let J := ENNReal.ofReal (2 / σ ^ 2) ^ d
  let V₀ := J * volume (Metric.closedBall (0 : Ambient d) 1)
  let ν := (OAI.Analysis.Fourier.Restriction.sphereMeasure d).prod (volume.restrict (Icc (-L) L))
  let C₀ := ENNReal.ofReal (2 * Real.exp Real.pi) *
    (V₀ ^ (1 / q) * ν univ ^ (1 / q) +
      ENNReal.ofReal ((1 - (2 : ℝ) ^ (1 - ((d : ℝ) + 1) / q))⁻¹))
  let K := ((16 : ℝ≥0∞) ^ d * ENNReal.ofReal (L ^ (d - 1))) ^ (1 / q)
  have hq0 : 0 < q := by linarith
  have hq' : 0 ≤ 1 - 1 / q := sub_nonneg.mpr ((div_le_iff₀ hq0).mpr (by linarith))
  have hV₀ : V₀ < ⊤ := by
    unfold V₀ J
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (isCompact_closedBall _ _).measure_lt_top
  have hν : ν univ < ⊤ := by dsimp [ν]; exact measure_lt_top _ _
  have hC₀ : C₀ < ⊤ := by
    unfold C₀
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.add_lt_top.mpr
    exact ⟨ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hV₀.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hν.ne), ENNReal.ofReal_lt_top⟩
  have hK : K < ⊤ := by
    unfold K
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.mul_lt_top
      (ENNReal.pow_lt_top (by norm_num)) ENNReal.ofReal_lt_top).ne
  let C := (16 : ℝ≥0∞) ^ d * ENNReal.ofReal (6 / σ ^ 4) * K * C₀ * J ^ (1 - 1 / q)
  refine ⟨C, ?_, ?_⟩
  · unfold C
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top (by norm_num)) ENNReal.ofReal_lt_top) hK) hC₀)
      (ENNReal.rpow_lt_top_of_nonneg hq' (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne)
  intro δ r ε a u hδ hδhalf ha hr hrhalf hu hε A B hA hB hAD hBD
  have hPu : shiftedCapPoint δ a r u ≠ 0 := by
    have H := shifted_cap_point_norm_one hδ.le hδhalf ha hr.le hrhalf hu
    exact fun he => by rw [he, norm_zero] at H; exact zero_ne_one H
  let Ψ := shiftedStereoChart δ a r u hPu
  let V := Ψ '' B
  let h := 6 * ε / σ ^ 4
  have hh : 0 < h := by dsimp [h]; positivity
  have hVm : MeasurableSet V := stereo_image_measurable hδ hδhalf ha hr hrhalf hu hσ hPu hB hBD
  have hVb : volume V ≤ J * volume B :=
    ((shifted_stereo_chart_measure_bounds hδ hδhalf ha hr hrhalf hu hσ hPu) B hBD).2
  have hV₀b : volume V ≤ V₀ := hVb.trans (mul_le_mul' le_rfl (measure_mono fun x hx => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hBD hx).1))
  have hVf : volume V < ⊤ := hV₀b.trans_lt hV₀
  let f := V.indicator (fun _ => (1 : ℝ))
  let R := radonStrip h f
  let G := R ∘ radialCoordinates ∘ Ψ
  have hf : Measurable f := measurable_const.indicator hVm
  have hR := radon_strip_measurable h hf
  have hG := hR.comp ((measurable_radialCoordinates d).comp
    (shifted_stereo_chart_measurable δ a r u hPu))
  have hbound := radon_strip_restricted_bound hd hh hf hVm hV₀ hV₀b
    (fun v => indicator_nonneg (fun _ _ => zero_le_one) _) (fun _ => le_rfl) hq hqd L
  change eLpNorm R (ENNReal.ofReal q) ν ≤ C₀ * (volume V) ^ (1 - 1 / q) at hbound
  have hW : Ψ '' A ⊆ {v : Ambient d | 0 < ‖v‖ ∧ ‖v‖ ≤ L} := by
    rintro v ⟨y, hy, rfl⟩
    have hyy : |shiftedCollisionPhase δ a r u y y| ≤ 0 := by simp [shiftedCollisionPhase]
    have ht := shifted_collision_chart_strip hδ hδhalf ha hr hrhalf hu (hAD hy).1 (hAD hy).1
      (by simpa only [add_sub_cancel_right] using hu) hσ (hAD hy).2 (hAD hy).2 hyy hPu
    exact ⟨lt_of_lt_of_le (by norm_num) ht.2.1, ht.2.2.1⟩
  have hpow : (∫⁻ y in A, ‖G y‖ₑ ^ q) ≤
      ((16 : ℝ≥0∞) ^ d * ENNReal.ofReal (L ^ (d - 1))) *
        ∫⁻ z, ‖R z‖ₑ ^ q ∂ν := by
    have hF : Measurable (fun z => ‖R z‖ₑ ^ q) := hR.enorm.pow_const q
    have htrans := shifted_stereo_chart_lintegral_le hδ hδhalf ha hr hrhalf hu hσ hPu hAD
      (hF.comp (measurable_radialCoordinates d))
    refine htrans.trans ?_
    rw [mul_assoc]
    exact mul_le_mul' le_rfl ((lintegral_mono_set hW).trans
      (polar_annulus_bound hd (by dsimp [L]; positivity) hF))
  have hGq : eLpNorm G (ENNReal.ofReal q) (volume.restrict A) ≤
      K * eLpNorm R (ENNReal.ofReal q) ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hG.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hR.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
    simpa only [K, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / q)] using
      ENNReal.rpow_le_rpow hpow (by positivity : 0 ≤ 1 / q)
  have hG₁ : (∫⁻ y in A, ‖G y‖ₑ) ≤
      K * (C₀ * (volume V) ^ (1 - 1 / q)) * (volume A) ^ (1 - 1 / q) := by
    have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict A) (f := G) (p := 1) (q := ENNReal.ofReal q)
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
      hG.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hG.aestronglyMeasurable, ENNReal.toReal_one, one_div_one,
      ENNReal.toReal_ofReal hq0.le, Measure.restrict_apply_univ] at H
    exact H.trans (mul_le_mul' (hGq.trans (mul_le_mul' le_rfl hbound)) le_rfl)
  calc
    _ ≤ ∫⁻ y in A, ((16 : ℝ≥0∞) ^ d * ENNReal.ofReal h) * ‖G y‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with y hy
      have H := shifted_collision_fiber_measure_le (ε := ε) hδ hδhalf ha hr hrhalf hu
        (hAD hy).1 hσ (hAD hy).2 hPu hBD
      change _ ≤ (16 : ℝ≥0∞) ^ d *
        volume (V ∩ {v | |(radialCoordinates (Ψ y)).2 -
          ⟪v, (radialCoordinates (Ψ y)).1⟫| ≤ h}) at H
      rw [strip_volume_eq hh hVm hVf, ← mul_assoc] at H
      exact H
    _ ≤ ((16 : ℝ≥0∞) ^ d * ENNReal.ofReal h) *
        (K * (C₀ * (volume V) ^ (1 - 1 / q)) * (volume A) ^ (1 - 1 / q)) := by
      rw [lintegral_const_mul _ hG.enorm]
      exact mul_le_mul' le_rfl hG₁
    _ ≤ ((16 : ℝ≥0∞) ^ d * ENNReal.ofReal h) *
        (K * (C₀ * (J * volume B) ^ (1 - 1 / q)) * (volume A) ^ (1 - 1 / q)) :=
      mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hVb hq'))) le_rfl)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq']
      have he : ENNReal.ofReal h = ENNReal.ofReal (6 / σ ^ 4) * ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [h]
        ring
      rw [he]
      unfold C
      ac_rfl

end RestrictionWork
