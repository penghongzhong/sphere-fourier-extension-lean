import RestrictionWork.ClosureObligations

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace RestrictionWork

/-- The remaining radial threshold part of necessity. The separate Knapp
necessary inequality has been proved for the literal original operator. -/
def RadialRestrictionNecessity : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ p q : ℝ≥0∞, 1 ≤ p → 1 ≤ q →
    BoundedSphereExtension n p q →
      ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q

end RestrictionWork
