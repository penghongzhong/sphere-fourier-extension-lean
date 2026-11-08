import RestrictionWork.PhaseExtensionDefinitions
import RestrictionWork.PhaseExponentialLipschitz
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RestrictionWork

/-- Uniform phase error controls the difference of the actual integrals.
Integrability and measurable phases are explicit, so no undefined-integral
convention is used to bypass an analytical hypothesis. -/
theorem phase_extension_perturbation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℂ} (hg : Integrable g μ) {linear φ ψ : α → ℝ}
    (hlinear : Measurable linear) (hφ : Measurable φ) (hψ : Measurable ψ)
    {ε : ℝ} (_hε : 0 ≤ ε) (hclose : ∀ᵐ v ∂μ, |φ v - ψ v| ≤ ε) (t : ℝ) :
    ‖phaseExtension μ g linear φ t - phaseExtension μ g linear ψ t‖ ≤
      (|t| * ε) * ∫ v, ‖g v‖ ∂μ := by
  have hint (phase : α → ℝ) (hphase : Measurable phase) :
      Integrable (fun v => g v *
        Complex.exp (((linear v + t * phase v : ℝ) : ℂ) * Complex.I)) μ := by
    have hmeas : Measurable (fun v =>
        Complex.exp (((linear v + t * phase v : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    apply hg.mono (hg.aestronglyMeasurable.mul hmeas.aestronglyMeasurable)
    filter_upwards [] with v
    simp [norm_mul, Complex.norm_exp]
  unfold phaseExtension
  rw [← integral_sub (hint φ hφ) (hint ψ hψ)]
  calc
    _ ≤ ∫ v, (|t| * ε) * ‖g v‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hg.norm.const_mul (|t| * ε))
      filter_upwards [hclose] with v hv
      rw [← mul_sub, norm_mul]
      have H := phase_exponential_lipschitz (linear v + t * φ v) (linear v + t * ψ v)
      have heq : (linear v + t * φ v) - (linear v + t * ψ v) = t * (φ v - ψ v) := by ring
      rw [heq, abs_mul] at H
      have H' := mul_le_mul_of_nonneg_left hv (abs_nonneg t)
      have H'' := mul_le_mul_of_nonneg_left (H.trans H') (norm_nonneg (g v))
      simpa only [mul_comm ‖g v‖] using H''
    _ = _ := integral_const_mul (|t| * ε) (fun v => ‖g v‖)

end RestrictionWork
