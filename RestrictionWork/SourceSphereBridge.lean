import RestrictionWork.Definitions
import CriticalTwoPi

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

/-- A concrete extension of sphere data to the ambient space. Its values
away from the sphere have no effect on the canonical sphere measure. -/
def sphereAmbientLift {n : ℕ} (f : UnitSphere n → ℂ) : Ambient n → ℂ :=
  Function.extend Subtype.val f (fun _ ↦ 0)

/-- Exact norm and operator agreement between the original subtype sphere
and the already verified ambient representation. No analytic bound is assumed. -/
theorem source_sphere_bridge {n : ℕ} {p : ℝ≥0∞} {f : UnitSphere n → ℂ}
    (hf : MemLp f p (sphereMeasure n)) :
    MemLp (sphereAmbientLift f) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ∧
    eLpNorm (sphereAmbientLift f) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      eLpNorm f p (sphereMeasure n) ∧
    ∀ x : Ambient n, CriticalReplay.sphericalExtensionTwoPi (sphereAmbientLift f) x =
      extension f x := by
  have he : MeasurableEmbedding (Subtype.val : UnitSphere n → Ambient n) :=
    MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet
  have hc : sphereAmbientLift f ∘ (Subtype.val : UnitSphere n → Ambient n) = f :=
    Function.extend_comp he.injective _ _
  have hn : eLpNorm (sphereAmbientLift f) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      eLpNorm f p (sphereMeasure n) := by
    change eLpNorm (sphereAmbientLift f) p ((sphereMeasure n).map Subtype.val) = _
    rw [he.eLpNorm_map_measure, hc]
  refine ⟨?_, hn, ?_⟩
  · change MemLp (sphereAmbientLift f) p ((sphereMeasure n).map Subtype.val)
    rw [he.memLp_map_measure_iff, hc]
    exact hf
  · intro x
    unfold CriticalReplay.sphericalExtensionTwoPi OAI.Analysis.Fourier.Restriction.sphereMeasure
    rw [he.integral_map]
    unfold extension kernel
    apply integral_congr_ae
    filter_upwards [] with ω
    have hv : sphereAmbientLift f (ω : Ambient n) = f ω := congrFun hc ω
    rw [hv, mul_comm (f ω)]
    congr 1
    congr 1
    push_cast
    ring

end RestrictionWork
