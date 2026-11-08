import RestrictionWork.HemisphereAreaMeasure
import RestrictionWork.CapPointEmbedding

set_option autoImplicit false
noncomputable section
open Set MeasureTheory OAI.MahlerStokes
open scoped ENNReal
namespace RestrictionWork

/-- The hemisphere area formula in the project's original Euclidean
parameter coordinates and original graph measure. -/
theorem unit_hemisphere_area (d : ℕ) :
    capGraphMeasure d 1 =
      ((sphereMeasure (d + 1)).map Subtype.val).restrict
        {z : Ambient (d + 1) | 0 < z (Fin.last d)} := by
  let e := (WithLp.equiv 2 (Fin d → ℝ)).symm
  let T : coordBall d 1 → Ambient d := fun y => e y
  let μ : Measure (coordBall d 1) := (volume : Measure (Fin d → ℝ)).comap Subtype.val
  let w : Ambient d → ℝ≥0∞ := fun y => ENNReal.ofReal (capHeight 1 y)⁻¹
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp (Fin d)
  have hT : Measurable T := hp.measurable.comp measurable_subtype_coe
  have hw : Measurable w := by
    unfold w capHeight
    fun_prop
  have hpre : e ⁻¹' Metric.ball (0 : Ambient d) 1 = coordBall d 1 := by
    ext y
    change dist (e y) 0 < 1 ↔ radiusSq y < 1 ^ 2
    rw [dist_zero_right, radiusSq_eq_euclidean_norm_sq]
    exact (sq_lt_sq₀ (norm_nonneg _) zero_le_one).symm
  have hμ0 : μ.map T = (volume : Measure (Ambient d)).restrict (Metric.ball 0 1) := by
    have hsub : μ.map Subtype.val = (volume : Measure (Fin d → ℝ)).restrict (coordBall d 1) := by
      simpa only [Subtype.range_coe] using
        (MeasurableEmbedding.subtype_coe (measurableSet_coordBall d 1)).map_comap
          (volume : Measure (Fin d → ℝ))
    calc
      μ.map T = (μ.map Subtype.val).map e := by
        rw [Measure.map_map hp.measurable measurable_subtype_coe]
        rfl
      _ = _ := by
        rw [hsub, ← hpre, ← Measure.restrict_map hp.measurable measurableSet_ball,
          hp.map_eq]
  have hh (y : coordBall d 1) : chord 1 (y : Fin d → ℝ) = capHeight 1 (T y) := by
    simp only [chord, capHeight, one_pow, one_mul, radiusSq_eq_euclidean_norm_sq]
    rfl
  have hweights : hemisphereParameterArea d = μ.withDensity (w ∘ T) := by
    unfold hemisphereParameterArea
    congr 1
    funext y
    rw [hh]
    rfl
  have htransport : (μ.withDensity (w ∘ T)).map T = (μ.map T).withDensity w := by
    ext s hs
    rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
      setLIntegral_map hs hw hT]
    rfl
  have hparam : (hemisphereParameterArea d).map T = capParameterMeasure d 1 := by
    rw [hweights, htransport, hμ0]
    unfold capParameterMeasure patchMeasure
    congr 1
    funext y
    simp [capDensity, w]
  have hchart : (capPoint (d := d) 1) ∘ T =
      fun y : coordBall d 1 => toLp 2 (hemisphereGraph (Fin.last d) y) := by
    funext y
    unfold Function.comp capPoint hemisphereGraph
    rw [Fin.insertNth_last']
    simp only [one_mul]
    rw [← hh]
    rfl
  rw [capGraphMeasure, ← hparam,
    Measure.map_map (cap_point_embedding (d := d) one_ne_zero).1.measurable hT,
    hchart]
  exact hemisphere_area_measure d (Fin.last d)

end RestrictionWork
