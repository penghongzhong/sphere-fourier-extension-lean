import RestrictionWork.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

def ambientSphereMeasure (n : ℕ) : Measure (Ambient n) :=
  (sphereMeasure n).map Subtype.val

def angularExtension {n : ℕ} (g : Ambient n → ℂ) (y : Ambient n) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * ((⟪y, ω⟫ : ℝ) : ℂ)) * g ω
    ∂ambientSphereMeasure n

/-- The ambient angular-frequency operator used by the new source is the
same actual integral, after pullback to the sphere and the 2*pi dilation. -/
theorem angular_alignment {n : ℕ} (g : Ambient n → ℂ) (x : Ambient n) :
    extension (fun ω : UnitSphere n => g ω) x =
      angularExtension g ((2 * Real.pi) • x) := by
  unfold angularExtension ambientSphereMeasure
  rw [(MeasurableEmbedding.subtype_coe (Metric.isClosed_sphere.measurableSet)).integral_map]
  unfold extension kernel
  congr 1
  funext ω
  simp only [real_inner_smul_left, Complex.ofReal_mul]
  rw [mul_comm (g (ω : Ambient n))]
  congr 1
  congr 1
  ring

end RestrictionWork
