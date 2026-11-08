import RestrictionWork.OriginalCapNormTransfer
import RestrictionWork.ShiftedSphericalGraphPhase

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace RestrictionWork

/-- The spherical subset represented by the quarter-sized graph domain. -/
def originalSmallCap {d : ℕ} (δ : ℝ) : Set (UnitSphere (d + 1)) :=
  (Subtype.val : UnitSphere (d + 1) → Ambient (d + 1)) ⁻¹'
    (capPoint δ '' Metric.ball 0 (1 / 4))

theorem measurableSet_originalSmallCap {d : ℕ} {δ : ℝ} (hδ : δ ≠ 0) :
    MeasurableSet (originalSmallCap (d := d) δ) :=
  ((cap_point_embedding hδ).2.2.measurableSet_image.mpr measurableSet_ball).preimage
    measurable_subtype_coe

/-- Every measurable input supported in the small cap is exactly the lift
of a compensated graph input, with a reverse input norm bound. -/
theorem original_cap_reverse {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {p : ℝ≥0∞} {f : UnitSphere (d + 1) → ℂ} (hfm : Measurable f)
    (hf : MemLp f p (sphereMeasure (d + 1)))
    (hfs : ∀ ω ∉ originalSmallCap δ, f ω = 0) :
    ∃ g : Ambient d → ℂ, Measurable g ∧ MemLp g p (patchMeasure d) ∧
      (∀ v ∉ Metric.ball (0 : Ambient d) (1 / 4), g v = 0) ∧
      capSphereLift δ g = f ∧
      eLpNorm g p (patchMeasure d) ≤
        2 * (ENNReal.ofReal (δ ^ d) ^ p.toReal⁻¹)⁻¹ *
          eLpNorm f p (sphereMeasure (d + 1)) := by
  let B : Set (Ambient d) := Metric.ball 0 (1 / 4)
  let W : Set (Ambient d) := Metric.ball 0 1
  let e : UnitSphere (d + 1) → Ambient (d + 1) := Subtype.val
  let F : Ambient (d + 1) → ℂ := Function.extend e f 0
  let H : Ambient d → ℂ := F ∘ capPoint δ
  let g : Ambient d → ℂ := B.indicator (fun v => (capHeight δ v : ℂ)⁻¹ * H v)
  have hBW : B ⊆ W := Metric.ball_subset_ball (by norm_num)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet
  have hC := (cap_point_embedding (d := d) hδ.ne').2.2
  have hFc : F ∘ e = f := Function.extend_comp he.injective _ _
  have hFm : Measurable F := he.measurable_extend hfm measurable_zero
  have hHm : Measurable H := hFm.comp hC.measurable
  have hgm : Measurable g := by
    unfold g
    apply Measurable.indicator _ measurableSet_ball
    have hh : Continuous (fun v : Ambient d => (capHeight δ v : ℂ)) := by
      unfold capHeight
      fun_prop
    exact hh.measurable.inv.mul hHm
  have hFs : ∀ x ∉ capPoint δ '' B, F x = 0 := by
    intro x hx
    by_cases hr : x ∈ range e
    · obtain ⟨ω, rfl⟩ := hr
      rw [show F (e ω) = f ω from congrFun hFc ω]
      exact hfs ω hx
    · exact Function.extend_apply' _ _ _ hr
  have hgfs : ∀ v ∉ B, g v = 0 := fun v hv => indicator_of_notMem hv _
  have hgcomp : capAmbientLift δ g = F := by
    funext x
    by_cases hx : x ∈ capPoint δ '' W
    · obtain ⟨v, hv, rfl⟩ := hx
      unfold capAmbientLift
      rw [indicator_of_mem (mem_image_of_mem _ hv)]
      unfold capProfileExtension
      rw [hC.injective.extend_apply]
      unfold capProfile
      by_cases hV : v ∈ B
      · unfold g
        rw [indicator_of_mem hV]
        have hheight : (capHeight δ v : ℂ) ≠ 0 := by
          exact_mod_cast ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
            (cap_chart_geometry hδ hδ₁ hv).1).ne'
        rw [← mul_assoc, mul_inv_cancel₀ hheight, one_mul]
        rfl
      · rw [hgfs v hV, mul_zero]
        exact (hFs _ (fun ⟨u, hu, heq⟩ => hV (hC.injective heq ▸ hu))).symm
    · unfold capAmbientLift
      rw [indicator_of_notMem hx]
      exact (hFs x fun h => hx ((image_mono hBW) h)).symm
  have hlift : capSphereLift δ g = f := by
    change capAmbientLift δ g ∘ e = f
    rw [hgcomp, hFc]
  have hFa : MemLp F p (ambientSphereMeasure (d + 1)) := by
    unfold ambientSphereMeasure
    rw [he.memLp_map_measure_iff, hFc]
    exact hf
  have hFnorm : eLpNorm F p (ambientSphereMeasure (d + 1)) =
      eLpNorm f p (sphereMeasure (d + 1)) := by
    unfold ambientSphereMeasure
    rw [he.eLpNorm_map_measure, hFc]
  have harea := cap_area_identity (d := d) hδ hδ₁
  change (capParameterMeasure d δ).map (capPoint δ) =
      (ambientSphereMeasure (d + 1)).restrict (capPoint δ '' W) at harea
  have hH : MemLp H p (capParameterMeasure d δ) := by
    rw [← hC.memLp_map_measure_iff, harea]
    exact hFa.restrict _
  have hHnorm : eLpNorm H p (capParameterMeasure d δ) ≤
      eLpNorm f p (sphereMeasure (d + 1)) := by
    change eLpNorm (F ∘ capPoint δ) p (capParameterMeasure d δ) ≤ _
    rw [← hC.eLpNorm_map_measure, harea, ← hFnorm]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hunit : ∀ᵐ v ∂patchMeasure d, v ∈ W := ae_restrict_mem measurableSet_ball
  have hdom : ENNReal.ofReal (δ ^ d) • patchMeasure d ≤ capParameterMeasure d δ := by
    unfold capParameterMeasure
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hunit] with v hv
    exact ENNReal.ofReal_le_ofReal (cap_chart_geometry hδ hδ₁ hv).2.2.2.1
  have hc0 : ENNReal.ofReal (δ ^ d) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hct : ENNReal.ofReal (δ ^ d) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdom' : patchMeasure d ≤ (ENNReal.ofReal (δ ^ d))⁻¹ • capParameterMeasure d δ := by
    have h : (ENNReal.ofReal (δ ^ d))⁻¹ •
          (ENNReal.ofReal (δ ^ d) • patchMeasure d) ≤
        (ENNReal.ofReal (δ ^ d))⁻¹ • capParameterMeasure d δ := by
      gcongr
    rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul] at h
  have hHb : MemLp H p (patchMeasure d) :=
    hH.of_measure_le_smul (ENNReal.inv_ne_top.mpr hc0) hdom'
  have hpoint : ∀ᵐ v ∂patchMeasure d, ‖g v‖ ≤ 2 * ‖H v‖ := by
    filter_upwards [hunit] with v hv
    by_cases hvB : v ∈ B
    · have hlo := (cap_chart_geometry hδ hδ₁ hv).1
      have hn : 0 < capHeight δ v := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hlo
      have hinv : (capHeight δ v)⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ hn]
        linarith
      unfold g
      rw [indicator_of_mem hvB, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hn]
      exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    · rw [hgfs v hvB, norm_zero]
      positivity
  have htwo : ∀ v : Ambient d, ‖(2 : ℂ) • H v‖ = 2 * ‖H v‖ := by
    intro v
    rw [norm_smul]
    norm_num
  have hgLp : MemLp g p (patchMeasure d) := by
    apply (hHb.const_smul (2 : ℂ)).mono hgm.aestronglyMeasurable
    filter_upwards [hpoint] with v hv
    exact (htwo v).symm ▸ hv
  refine ⟨g, hgm, hgLp, hgfs, hlift, ?_⟩
  have hnorm : eLpNorm g p (patchMeasure d) ≤ 2 * eLpNorm H p (patchMeasure d) := by
    have h := eLpNorm_mono_ae (p := p) hgm.aestronglyMeasurable
      (hpoint.mono fun v hv => (htwo v).symm ▸ hv)
    change eLpNorm g p (patchMeasure d) ≤ eLpNorm ((2 : ℂ) • H) p (patchMeasure d) at h
    rw [eLpNorm_const_smul] at h
    simpa [← ofReal_norm] using h
  have hHp : eLpNorm H p (patchMeasure d) ≤
      (ENNReal.ofReal (δ ^ d) ^ p.toReal⁻¹)⁻¹ * eLpNorm H p (capParameterMeasure d δ) := by
    refine (eLpNorm_mono_measure _ hdom').trans_eq ?_
    rw [eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr hct)]
    simp only [one_div, smul_eq_mul, ENNReal.inv_rpow, ENNReal.toReal_inv]
  calc
    _ ≤ 2 * eLpNorm H p (patchMeasure d) := hnorm
    _ ≤ 2 * ((ENNReal.ofReal (δ ^ d) ^ p.toReal⁻¹)⁻¹ *
        eLpNorm H p (capParameterMeasure d δ)) := mul_le_mul' le_rfl hHp
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hHnorm)

end RestrictionWork
