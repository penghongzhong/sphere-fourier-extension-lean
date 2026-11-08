import RestrictionWork.ClosureObligations
import RestrictionWork.StrictAdmissibleSufficiency

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace RestrictionWork

/-- Exact equivalence for the unchanged original iff target. Strict
sufficiency and the infinite-output endpoint have already been discharged;
the two propositions on the right remain mathematical obligations. -/
theorem original_closure_reduction : FullSphereRestrictionConjecture ↔
    SphereRestrictionNecessity ∧ FiniteKnappBoundarySufficiency := by
  constructor
  · intro H
    constructor
    · intro n hn p q hp hq hb
      exact (H n hn p q hp hq).mp hb
    · intro n hn p q _ ha _
      exact (H n hn p q ha.1 ha.2.1).mpr ha
  · rintro ⟨HN, HB⟩ n hn p q hp hq
    constructor
    · exact HN n hn p q hp hq
    · intro ha
      by_cases hqt : q = ⊤
      · subst q
        exact extension_top_bound hp
      by_cases hs : (q⁻¹).toReal <
          (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal)
      · exact strict_admissible_sufficiency hn hp hq ha.2.2.1 hs
      · exact HB n hn p q hqt ha
          (le_antisymm ha.2.2.2 (le_of_not_gt hs))

end RestrictionWork
