import RestrictionWork.Definitions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- A genuine Bochner oscillatory integral, with a common linear phase. -/
def phaseExtension {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℂ) (linear phase : α → ℝ) (t : ℝ) : ℂ :=
  ∫ v, g v * Complex.exp (((linear v + t * phase v : ℝ) : ℂ) * Complex.I) ∂μ

def sphericalPhase (δ s : ℝ) : ℝ :=
  2 * (1 - Real.sqrt (1 - δ ^ 2 * s)) / δ ^ 2

def patchMeasure (d : ℕ) : Measure (Ambient d) :=
  volume.restrict (Metric.ball (0 : Ambient d) 1)

def graphExtension {d : ℕ} (g : Ambient d → ℂ) (phase : Ambient d → ℝ)
    (z : Ambient d × ℝ) : ℂ :=
  phaseExtension (patchMeasure d) g (fun v => ⟪z.1, v⟫) phase z.2

def sphericalPatchExtension {d : ℕ} (δ : ℝ) (g : Ambient d → ℂ)
    (z : Ambient d × ℝ) : ℂ :=
  graphExtension g (fun v => sphericalPhase δ (‖v‖ ^ 2)) z

def paraboloidExtension {d : ℕ} (g : Ambient d → ℂ) (z : Ambient d × ℝ) : ℂ :=
  graphExtension g (fun v => ‖v‖ ^ 2) z

/-- Explicit geometric constant, independent of the cap scale and radius. -/
def patchErrorConstant (d : ℕ) (p q : ENNReal) : ENNReal :=
  volume (Metric.ball (0 : Ambient d × ℝ) 1) ^ q.toReal⁻¹ *
    (patchMeasure d) Set.univ ^ (1 - p.toReal⁻¹)

end RestrictionWork
