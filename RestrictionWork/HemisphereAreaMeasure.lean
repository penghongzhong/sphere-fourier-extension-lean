import RestrictionWork.Definitions
import SphereAreaReuse.HemisphereArea

set_option autoImplicit false
noncomputable section
open Set MeasureTheory OAI.MahlerStokes
namespace RestrictionWork

/-- The actual canonical sphere measure on an open hemisphere, expressed
in graph coordinates. The area identity is derived, never assumed. -/
theorem hemisphere_area_measure (d : ℕ) (i : Fin (d + 1)) :
    (hemisphereParameterArea d).map
      (fun y : coordBall d 1 => toLp 2 (hemisphereGraph i y)) =
      ((sphereMeasure (d + 1)).map Subtype.val).restrict
        {z : Ambient (d + 1) | 0 < z i} := by
  have hp := measurePreserving_hemisphereParam (n := d) i
  have hs : MeasurableSet {z : Ambient (d + 1) | 0 < z i} := by
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  rw [Measure.restrict_map measurable_subtype_coe hs]
  have hr : range (hemisphereParam (n := d) i) =
      Subtype.val ⁻¹' {z : Ambient (d + 1) | 0 < z i} :=
    hemisphereParam_range i
  rw [← hr]
  unfold sphereMeasure
  rw [← hp.map_eq,
    Measure.map_map measurable_subtype_coe hp.measurable]
  rfl

end RestrictionWork
