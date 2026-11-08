import RestrictionWork.CapLiftDefinitions
import RestrictionWork.CapAreaIdentity
import RestrictionWork.CapProfileLp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

/-- Actual input on the original sphere, with exact norm correspondence
and the uniform cap-scale bound. Only the given Lp input is required. -/
theorem cap_lift_lp {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {g : Ambient d → ℂ} {p : ℝ≥0∞} (hg : MemLp g p (patchMeasure d)) :
    MemLp (capSphereLift δ g) p (sphereMeasure (d + 1)) ∧
    eLpNorm (capSphereLift δ g) p (sphereMeasure (d + 1)) =
      eLpNorm (capProfile δ g) p (capParameterMeasure d δ) ∧
    eLpNorm (capSphereLift δ g) p (sphereMeasure (d + 1)) ≤
      ENNReal.ofReal (2 * δ ^ d) ^ p.toReal⁻¹ * eLpNorm g p (patchMeasure d) := by
  have he := (cap_point_embedding (d := d) hδ.ne').2.2
  have hs : MeasurableSet (capPoint δ '' Metric.ball (0 : Ambient d) 1) :=
    he.measurableSet_image.mpr measurableSet_ball
  have ha : (capParameterMeasure d δ).map (capPoint δ) =
      (ambientSphereMeasure (d + 1)).restrict (capPoint δ '' Metric.ball (0 : Ambient d) 1) :=
    cap_area_identity hδ hδ₁
  have hc : capProfileExtension δ g ∘ capPoint δ = capProfile δ g :=
    Function.extend_comp he.injective _ _
  have hp := cap_profile_lp_bound hδ hδ₁ hg
  have hf : MemLp (capProfileExtension δ g) p
      ((ambientSphereMeasure (d + 1)).restrict (capPoint δ '' Metric.ball (0 : Ambient d) 1)) := by
    rw [← ha, he.memLp_map_measure_iff, hc]
    exact hp.1
  have hl : MemLp (capAmbientLift δ g) p (ambientSphereMeasure (d + 1)) :=
    (memLp_indicator_iff_restrict hs).2 hf
  have hsub : MeasurableEmbedding (Subtype.val : UnitSphere (d + 1) → Ambient (d + 1)) :=
    MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet
  have hn : eLpNorm (capSphereLift δ g) p (sphereMeasure (d + 1)) =
      eLpNorm (capProfile δ g) p (capParameterMeasure d δ) := by
    calc
      _ = eLpNorm (capAmbientLift δ g) p (ambientSphereMeasure (d + 1)) :=
        hsub.eLpNorm_map_measure.symm
      _ = eLpNorm (capProfileExtension δ g) p
          ((ambientSphereMeasure (d + 1)).restrict (capPoint δ '' Metric.ball (0 : Ambient d) 1)) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hs
      _ = _ := by rw [← ha, he.eLpNorm_map_measure, hc]
  refine ⟨hsub.memLp_map_measure_iff.mp hl, hn, ?_⟩
  rw [hn]
  exact hp.2

end RestrictionWork
