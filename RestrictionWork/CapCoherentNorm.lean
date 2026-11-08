import RestrictionWork.CapCoherentPointwise
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- A strictly positive lower Lq norm for the actual constant-data cap
extension, uniform over all small cap scales. -/
theorem cap_coherent_norm (d : ℕ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ b : ℝ≥0, 0 < b ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
      (b : ℝ≥0∞) ≤ eLpNorm (sphericalPatchExtension δ (fun _ : Ambient d ↦ (1 : ℂ))) q
        (volume.restrict (Metric.ball (0 : Ambient d × ℝ) 1)) := by
  haveI : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let M := (patchMeasure d).real Set.univ
  have hmass : 0 < (patchMeasure d) Set.univ := by
    rw [patchMeasure, Measure.restrict_apply_univ]
    exact Metric.measure_ball_pos volume _ zero_lt_one
  have hM : 0 < M := ENNReal.toReal_pos hmass.ne' (measure_ne_top _ _)
  let ν : Measure (Ambient d × ℝ) := volume.restrict (Metric.ball 0 (1/8 : ℝ))
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hνmass : 0 < ν Set.univ := by
    rw [Measure.restrict_apply_univ]
    exact Metric.measure_ball_pos volume _ (by norm_num)
  have hν : ν ≠ 0 := by
    intro H
    simpa only [H, Measure.coe_zero, Pi.zero_apply, lt_self_iff_false] using hνmass
  have hq0 : q ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hq).ne'
  let K := eLpNorm (fun _ : Ambient d × ℝ ↦ ((M / 2 : ℝ) : ℂ)) q ν
  have hK : K < ⊤ := memLp_const _
  have hK0 : 0 < K := by
    dsimp [K]
    rw [eLpNorm_const _ hq0 hν]
    apply ENNReal.mul_pos
    · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < M / 2)]
      exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < M / 2)).ne'
    · exact (ENNReal.rpow_pos hνmass (measure_ne_top _ _)).ne'
  refine ⟨K.toNNReal, ?_, ?_⟩
  · have H : (0 : ℝ≥0∞) < (K.toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_toNNReal hK.ne]
      exact hK0
    exact_mod_cast H
  · intro δ hδ hδ₁
    rw [ENNReal.coe_toNNReal hK.ne]
    have H : K ≤ eLpNorm (sphericalPatchExtension δ (fun _ : Ambient d ↦ (1 : ℂ))) q ν := by
      apply eLpNorm_mono_ae aestronglyMeasurable_const
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hzn : ‖z‖ ≤ 1/8 := by
        exact (show ‖z‖ < 1/8 by simpa only [Metric.mem_ball, dist_zero_right] using hz).le
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < M / 2)] using
        cap_coherent_pointwise hδ hδ₁ z hzn
    exact H.trans (eLpNorm_mono_measure _ (Measure.restrict_mono
      (Metric.ball_subset_ball (by norm_num : (1/8 : ℝ) ≤ 1)) le_rfl))

end RestrictionWork
