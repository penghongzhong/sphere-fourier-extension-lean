import RestrictionWork.PhaseExtensionDefinitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

def capHeight {d : ℕ} (δ : ℝ) (v : Ambient d) : ℝ :=
  Real.sqrt (1 - δ ^ 2 * ‖v‖ ^ 2)

def capPoint {d : ℕ} (δ : ℝ) (v : Ambient d) : Ambient (d + 1) :=
  (WithLp.equiv 2 (Fin (d + 1) → ℝ)).symm
    (Fin.snoc (α := fun _ : Fin (d + 1) => ℝ) (fun i => δ * v i) (capHeight δ v))

def capDensity {d : ℕ} (δ : ℝ) (v : Ambient d) : ℝ :=
  δ ^ d / capHeight δ v

def capParameterMeasure (d : ℕ) (δ : ℝ) : Measure (Ambient d) :=
  (patchMeasure d).withDensity (fun v => ENNReal.ofReal (capDensity δ v))

/-- The parametrized graph measure. Its equality with the canonical sphere
measure on a small cap is proved in CapAreaIdentity.lean. -/
def capGraphMeasure (d : ℕ) (δ : ℝ) : Measure (Ambient (d + 1)) :=
  (capParameterMeasure d δ).map (capPoint δ)

/-- The surface-area interface, stated with the original canonical measure.
The theorem cap_area_identity proves it for 0 < delta <= 1/2. -/
def CapAreaIdentity (d : ℕ) (δ : ℝ) : Prop :=
  capGraphMeasure d δ =
    ((sphereMeasure (d + 1)).map Subtype.val).restrict
      (capPoint δ '' Metric.ball (0 : Ambient d) 1)

def capProfile {d : ℕ} (δ : ℝ) (g : Ambient d → ℂ) (v : Ambient d) : ℂ :=
  (capHeight δ v : ℂ) * g v

def capPhysicalScale {d : ℕ} (δ : ℝ) (z : Ambient d × ℝ) : Ambient d × ℝ :=
  (δ⁻¹ • z.1, -2 * z.2 / δ ^ 2)

def capGraphExtension {d : ℕ} (δ : ℝ) (f : Ambient d → ℂ)
    (z : Ambient d × ℝ) : ℂ :=
  ∫ v, f v * Complex.exp (((⟪z.1, δ • v⟫ + z.2 * capHeight δ v : ℝ) : ℂ) * Complex.I)
    ∂capParameterMeasure d δ

end RestrictionWork
