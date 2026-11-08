import RestrictionWork.UnitHemisphereArea
import RestrictionWork.CapParameterScaling
import RestrictionWork.CapChartGeometry

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace RestrictionWork

/-- The originally missing interface: the parametrized cap measure is
exactly the canonical surface measure restricted to the actual cap. -/
theorem cap_area_identity {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) :
    CapAreaIdentity d δ := by
  let B := Metric.ball (0 : Ambient d) 1
  let f : Ambient d → Ambient d := fun v => δ • v
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hpoint := cap_point_embedding (d := d) one_ne_zero
  have hh (v : Ambient d) : capHeight 1 (f v) = capHeight δ v := by
    simp only [capHeight, f, one_pow, norm_smul, Real.norm_eq_abs, abs_of_pos hδ,
      mul_pow, one_mul]
  have hcomp : capPoint (d := d) δ = (capPoint (d := d) 1) ∘ f := by
    funext v
    simp only [Function.comp_apply, capPoint, hh]
    congr 1
    funext i
    simp only [one_mul, f, PiLp.smul_apply, smul_eq_mul]
  have hb : f '' B = Metric.ball (0 : Ambient d) δ := by
    change δ • Metric.ball (0 : Ambient d) 1 = _
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hδ, mul_one] using
      (_root_.smul_ball hδ.ne' (0 : Ambient d) 1)
  have himg : capPoint δ '' B = capPoint 1 '' Metric.ball (0 : Ambient d) δ := by
    rw [hcomp, image_comp, hb]
  have hsub : Metric.ball (0 : Ambient d) δ ⊆ B :=
    Metric.ball_subset_ball (hδ₁.trans (by norm_num))
  have hrestrict :
      ((volume : Measure (Ambient d)).restrict (Metric.ball 0 δ)).withDensity
        (fun y => ENNReal.ofReal (capHeight 1 y)⁻¹) =
      (capParameterMeasure d 1).restrict (Metric.ball 0 δ) := by
    unfold capParameterMeasure patchMeasure capDensity
    simp only [one_pow, one_div]
    rw [restrict_withDensity measurableSet_ball,
      Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 hsub]
  have hm : ((capParameterMeasure d 1).restrict (Metric.ball 0 δ)).map (capPoint 1) =
      (capGraphMeasure d 1).restrict (capPoint 1 '' Metric.ball (0 : Ambient d) δ) := by
    rw [capGraphMeasure, hpoint.2.2.restrict_map, hpoint.2.1.preimage_image]
  have hs : MeasurableSet (capPoint 1 '' Metric.ball (0 : Ambient d) δ) :=
    hpoint.2.2.measurableSet_image.mpr measurableSet_ball
  have hpos : capPoint 1 '' Metric.ball (0 : Ambient d) δ ⊆
      {z : Ambient (d + 1) | 0 < z (Fin.last d)} := by
    rw [← himg]
    rintro z ⟨v, hv, rfl⟩
    have hv' : v ∈ Metric.ball (0 : Ambient d) 1 := hv
    have hheight := (cap_chart_geometry hδ hδ₁ hv').1
    have H : 0 < capHeight δ v := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hheight
    simpa only [mem_setOf_eq, capPoint, WithLp.equiv_symm_apply, PiLp.toLp_apply, Fin.snoc_last] using H
  unfold CapAreaIdentity capGraphMeasure
  rw [hcomp, ← Measure.map_map hpoint.1.measurable hf,
    cap_parameter_scaling hδ, hrestrict, hm, unit_hemisphere_area,
    Measure.restrict_restrict hs, inter_eq_left.2 hpos]
  rw [← himg]
  rw [← hcomp]

end RestrictionWork
