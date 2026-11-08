import CriticalLocalDual

open OAI.Analysis.Fourier.Wave OAI.Analysis.Fourier.Restriction
open MeasureTheory Set Metric
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace CriticalReplay

/-- Critical local extension in the actual angular-frequency convention,
with local smoothing still displayed as its only analytic premise. -/
theorem localSmoothing_local_extension_critical
    (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
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
            (sphereMeasure n) := by
  let p := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnplus : (n : ℝ) + 1 ≠ 0 := by linarith
  have hp : 1 < p := by
    dsimp [p, OAI.Analysis.Fourier.LocalSmoothing.criticalExponent]
    apply (lt_div_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mpr
    linarith
  have hq : p / (p - 1) = restrictionInputExponent n := by
    apply (div_eq_iff (by linarith : p - 1 ≠ 0)).mpr
    dsimp [p, OAI.Analysis.Fourier.LocalSmoothing.criticalExponent, restrictionInputExponent]
    field_simp [hn1, hnplus]
    <;> ring
  obtain ⟨C, hC, HC⟩ := localSmoothing_local_restriction_critical hls hn hε
  refine ⟨C, hC, ?_⟩
  intro R hR g hg
  apply local_extension_of_restriction hp (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) ?_ hg
  intro f hfm hfi hfp hfs
  rw [hq] at hfp ⊢
  exact HC R hR f hfm hfi hfp hfs

end CriticalReplay
