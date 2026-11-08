import CriticalReplay
import CriticalTwoPi

open OAI.Analysis.Fourier.Wave OAI.Analysis.Fourier.Restriction
open MeasureTheory Set Metric
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace CriticalReplay

/-- The compiled producer discharges local smoothing in the angular local
extension estimate. This file is checked after the full producer replay. -/
theorem critical_local_extension
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ g : Space n → ℂ,
      MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (sphereMeasure n) →
      MemLp (sphericalExtension g)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (closedBall 0 R)) ∧
      eLpNorm (sphericalExtension g)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (closedBall 0 R)) ≤
        C * ENNReal.ofReal (R ^ ε) *
          eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
            (sphereMeasure n) :=
  localSmoothing_local_extension_critical
    OAI.Analysis.Fourier.LocalSmoothing.euclidean_local_smoothing hn hε

/-- The literal `2π` critical local extension estimate has no local-smoothing
or restriction estimate left as an analytic hypothesis. -/
theorem twoPi_critical_local_extension
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ g : Space n → ℂ,
      MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (sphereMeasure n) →
      MemLp (sphericalExtensionTwoPi g)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (closedBall 0 R)) ∧
      eLpNorm (sphericalExtensionTwoPi g)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (closedBall 0 R)) ≤
        D * ENNReal.ofReal (R ^ ε) *
          eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
            (sphereMeasure n) :=
  localSmoothing_twoPi_local_extension_critical
    OAI.Analysis.Fourier.LocalSmoothing.euclidean_local_smoothing hn hε

end CriticalReplay
