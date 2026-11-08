import RestrictionWork.CapChartDefinitions
import RestrictionWork.AngularAlignment
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RestrictionWork

/-- Extend the compensated profile along the actual cap graph. -/
def capProfileExtension {d : ℕ} (δ : ℝ) (g : Ambient d → ℂ) : Ambient (d + 1) → ℂ :=
  Function.extend (capPoint δ) (capProfile δ g) (fun _ => 0)

/-- A concrete ambient function supported on the actual cap. -/
def capAmbientLift {d : ℕ} (δ : ℝ) (g : Ambient d → ℂ) : Ambient (d + 1) → ℂ :=
  (capPoint δ '' Metric.ball (0 : Ambient d) 1).indicator (capProfileExtension δ g)

/-- The same concrete input on the original sphere. -/
def capSphereLift {d : ℕ} (δ : ℝ) (g : Ambient d → ℂ) : UnitSphere (d + 1) → ℂ :=
  fun ω => capAmbientLift δ g ω

/-- Embed spatial coordinates and time into the original Euclidean space. -/
def physicalEmbed {d : ℕ} (z : Ambient d × ℝ) : Ambient (d + 1) :=
  (WithLp.equiv 2 (Fin (d + 1) → ℝ)).symm
    (Fin.snoc (α := fun _ : Fin (d + 1) => ℝ) (fun i => z.1 i) z.2)

end RestrictionWork
