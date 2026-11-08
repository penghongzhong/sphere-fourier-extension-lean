import RestrictionWork.SourceSphereBridge
import UnconditionalExtensionReplay

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- The literal original sphere extension has the critical local bound.
The local-smoothing and restriction estimates are no longer hypotheses. -/
theorem original_critical_local_input {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : UnitSphere n → ℂ,
      MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (sphereMeasure n) →
      MemLp (extension f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (Metric.ball 0 R)) ∧
      eLpNorm (extension f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (Metric.ball 0 R)) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (R ^ ε) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
            (sphereMeasure n) := by
  obtain ⟨D, hD, HD⟩ := CriticalReplay.twoPi_critical_local_extension hn hε
  refine ⟨D.toNNReal, ?_⟩
  intro R hR f hf
  obtain ⟨hl, hn, he⟩ := source_sphere_bridge hf
  have H := HD R hR (sphereAmbientLift f) hl
  have heq : CriticalReplay.sphericalExtensionTwoPi (sphereAmbientLift f) = extension f :=
    funext he
  rw [heq, hn] at H
  rw [ENNReal.coe_toNNReal hD]
  have hm : (volume : Measure (Ambient n)).restrict (Metric.ball 0 R) ≤
      volume.restrict (Metric.closedBall 0 R) :=
    Measure.restrict_mono Metric.ball_subset_closedBall le_rfl
  exact ⟨H.1.mono_measure hm, (eLpNorm_mono_measure _ hm).trans H.2⟩

end RestrictionWork
