import RestrictionWork.Target

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace RestrictionWork

/-- Necessity for the original operator, with the original quantifiers. -/
def SphereRestrictionNecessity : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ p q : ℝ≥0∞, 1 ≤ p → 1 ≤ q →
    BoundedSphereExtension n p q → AdmissibleExponents n p q

/-- Only the finite-output allowed Knapp equality remains on the sufficient
side. This proposition is an explicit remaining obligation, not an axiom. -/
def FiniteKnappBoundarySufficiency : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ p q : ℝ≥0∞, q ≠ ⊤ → AdmissibleExponents n p q →
    (q⁻¹).toReal = (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal) →
    BoundedSphereExtension n p q

end RestrictionWork
