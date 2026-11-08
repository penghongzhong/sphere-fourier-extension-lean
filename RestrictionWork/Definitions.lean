import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

/-!
Standard input for JSP-001040. These are classical elementary estimates,
not a proof of the open finite-q restriction conjecture.
-/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace RestrictionWork

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev UnitSphere (n : ℕ) := Metric.sphere (0 : Ambient n) 1

/-- Surface measure induced from Euclidean volume by polar coordinates. -/
def sphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (volume : Measure (Ambient n)).toSphere

def kernel {n : ℕ} (x : Ambient n) (ω : UnitSphere n) : ℂ :=
  Complex.exp (((2 * Real.pi * ⟪x, (ω : Ambient n)⟫ : ℝ) : ℂ) * Complex.I)

def extension {n : ℕ} (f : UnitSphere n → ℂ) (x : Ambient n) : ℂ :=
  ∫ ω, f ω * kernel x ω ∂sphereMeasure n

end RestrictionWork
