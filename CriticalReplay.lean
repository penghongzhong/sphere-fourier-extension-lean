import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.Fourier.Restriction.LocalCritical

open OAI.Analysis.Fourier.Wave OAI.Analysis.Fourier.Restriction
open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace CriticalReplay

/-- Independent replay of the published critical local restriction input.
No local smoothing premise is left in this declaration. -/
theorem critical_local_input
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f → MemLp f (ENNReal.ofReal (restrictionInputExponent n)) volume →
      (∀ x, R < ‖x‖ → f x = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume :=
  OAI.Analysis.Fourier.Restriction.localSmoothing_local_restriction_critical
    OAI.Analysis.Fourier.LocalSmoothing.euclidean_local_smoothing hn hε

end CriticalReplay

