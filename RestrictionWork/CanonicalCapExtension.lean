import RestrictionWork.CapLiftLp
import RestrictionWork.PhysicalCapInner
import RestrictionWork.KernelIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- The original sphere extension of a concrete lifted input is exactly
the graph integral, including its 2*pi normalization and integrability. -/
theorem canonical_cap_extension {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {g : Ambient d → ℂ} (hg : Integrable g (patchMeasure d)) (z : Ambient d × ℝ) :
    Integrable (fun ω => capSphereLift δ g ω *
      kernel ((2 * Real.pi)⁻¹ • physicalEmbed z) ω) (sphereMeasure (d + 1)) ∧
    extension (capSphereLift δ g) ((2 * Real.pi)⁻¹ • physicalEmbed z) =
      capGraphExtension δ (capProfile δ g) z := by
  have he := (cap_point_embedding (d := d) hδ.ne').2.2
  have hs : MeasurableSet (capPoint δ '' Metric.ball (0 : Ambient d) 1) :=
    he.measurableSet_image.mpr measurableSet_ball
  have ha : (capParameterMeasure d δ).map (capPoint δ) =
      (ambientSphereMeasure (d + 1)).restrict (capPoint δ '' Metric.ball (0 : Ambient d) 1) :=
    cap_area_identity hδ hδ₁
  have hsf : Integrable (capSphereLift δ g) (sphereMeasure (d + 1)) :=
    memLp_one_iff_integrable.mp (cap_lift_lp hδ hδ₁ (memLp_one_iff_integrable.mpr hg)).1
  refine ⟨integrable_kernel_product hsf _, ?_⟩
  have halign := angular_alignment (capAmbientLift δ g) ((2 * Real.pi)⁻¹ • physicalEmbed z)
  change extension (capSphereLift δ g) _ = _ at halign
  rw [halign, smul_smul, mul_inv_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_smul]
  unfold angularExtension
  have hi : (fun ω : Ambient (d + 1) =>
      Complex.exp (Complex.I * ((⟪physicalEmbed z, ω⟫ : ℝ) : ℂ)) * capAmbientLift δ g ω) =
      (capPoint δ '' Metric.ball (0 : Ambient d) 1).indicator
        (fun ω => Complex.exp (Complex.I * ((⟪physicalEmbed z, ω⟫ : ℝ) : ℂ)) *
          capProfileExtension δ g ω) := by
    funext ω
    by_cases hω : ω ∈ capPoint δ '' Metric.ball (0 : Ambient d) 1
    · simp [capAmbientLift, hω]
    · simp [capAmbientLift, hω]
  rw [hi, integral_indicator hs, ← ha, he.integral_map]
  unfold capGraphExtension
  apply integral_congr_ae
  filter_upwards [] with v
  rw [show capProfileExtension δ g (capPoint δ v) = capProfile δ g v from
    he.injective.extend_apply _ _ v]
  simp only [physical_cap_inner, mul_comm]

end RestrictionWork
