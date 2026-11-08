import RestrictionWork.OriginalRadialNecessary
import RestrictionWork.OriginalKnappNecessary

set_option autoImplicit false
noncomputable section
namespace RestrictionWork

/-- Both necessary exponent conditions for the literal original operator. -/
theorem original_sphere_necessity : SphereRestrictionNecessity := by
  intro n hn p q hp hq hE
  exact ⟨hp, hq, original_radial_necessary n hn p q hp hq hE,
    original_knapp_necessary hn hp hq hE⟩

end RestrictionWork
