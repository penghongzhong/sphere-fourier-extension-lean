import RestrictionWork.Kernel
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace RestrictionWork

/-- Reciprocal-exponent form, including p or q equal to infinity. -/
def AdmissibleExponents (n : ℕ) (p q : ℝ≥0∞) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧
  ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q ∧
  (q⁻¹).toReal ≤ (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal)

def BoundedSphereExtension (n : ℕ) (p q : ℝ≥0∞) : Prop :=
  ∃ C : ℝ≥0, ∀ f : UnitSphere n → ℂ,
    MemLp f p (sphereMeasure n) →
    MemLp (extension f) q (volume : Measure (Ambient n)) ∧
    eLpNorm (extension f) q (volume : Measure (Ambient n)) ≤
      (C : ℝ≥0∞) * eLpNorm f p (sphereMeasure n)

/-- OPEN target JSP-001040. This is a proposition definition, not an axiom
    or a theorem asserting that the conjecture is true. -/
def FullSphereRestrictionConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ p q : ℝ≥0∞, 1 ≤ p → 1 ≤ q →
    (BoundedSphereExtension n p q ↔ AdmissibleExponents n p q)

end RestrictionWork
