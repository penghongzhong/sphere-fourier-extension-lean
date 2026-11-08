import RestrictionWork.OriginalSphereNecessity
import RestrictionWork.OriginalClosureReduction

set_option autoImplicit false
noncomputable section
namespace RestrictionWork

/-- The original full conjecture is equivalent to finite-output sufficiency
on the allowed Knapp equality line. -/
theorem original_target_iff_finite_knapp :
    FullSphereRestrictionConjecture ↔ FiniteKnappBoundarySufficiency :=
  ⟨fun H ↦ (original_closure_reduction.mp H).2,
    fun H ↦ original_closure_reduction.mpr ⟨original_sphere_necessity, H⟩⟩

end RestrictionWork
