import OAI.Analysis.Fourier.Restriction.Sparse.Bound
import OAI.Analysis.Fourier.Restriction.Extension
import OAI.Analysis.Fourier.Restriction.Diagonal
import CriticalReplay

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CriticalReplay
open OAI.Analysis.Fourier.Wave OAI.Analysis.Fourier.Restriction

/-- Global diagonal extension, with the local-smoothing premise discharged
by the independently replayed producer and no spatial support condition. -/
theorem global_diagonal_extension {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < s) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : Space n → ℂ,
      MemLp g (ENNReal.ofReal s) (sphereMeasure n) →
      MemLp (sphericalExtension g) (ENNReal.ofReal s) volume ∧
      eLpNorm (sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (sphereMeasure n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 < s := by
    have H := (OAI.MeasureTheory.Kakeya.criticalExponent_gt_two hn).trans hs
    linarith
  have hq1 : 1 ≤ s / (s - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < s - 1)).mpr
    linarith
  have hqc : s / (s - 1) < restrictionInputExponent n := by
    unfold restrictionInputExponent
    apply (div_lt_div_iff₀ (by linarith : 0 < s - 1)
      (by linarith : 0 < (n : ℝ) + 1)).mpr
    have H : 2 * (n : ℝ) < s * ((n : ℝ) - 1) := by
      exact (div_lt_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mp hs
    nlinarith
  obtain ⟨C, hC, HC⟩ := localSmoothing_global_restriction
    OAI.Analysis.Fourier.LocalSmoothing.euclidean_local_smoothing hn hq1 hqc
  refine ⟨C, hC, ?_⟩
  intro g hg
  exact sphericalExtension_bound_of_restriction hs1 hC (fun f hf _ ↦ HC f hf) hg

end CriticalReplay
