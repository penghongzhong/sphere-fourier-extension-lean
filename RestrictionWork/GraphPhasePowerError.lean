import RestrictionWork.PhaseIntegralError
import RestrictionWork.GraphExtensionContinuous
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

theorem patch_error_constant_lt_top {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (q : ℝ≥0∞) :
    patchErrorConstant d p q < ⊤ := by
  have : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have : Measure.IsAddHaarMeasure (volume : Measure (Ambient d × ℝ)) := by
    rw [Measure.volume_eq_prod (Ambient d) ℝ]
    infer_instance
  have hpinv : p.toReal⁻¹ ≤ 1 := by
    by_cases ht : p = ⊤
    · simp [ht]
    have H : (1 : ℝ) ≤ p.toReal := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ht hp
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) H
  apply (ENNReal.mul_ne_top _ _).lt_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_lt_top.ne
  · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _)

/-- An a.e. uniform phase difference controls the actual local output
norm. The radius power uses the full dimension of physical space. -/
theorem graph_phase_power_error {d : ℕ} {g : Ambient d → ℂ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hg : MemLp g p (patchMeasure d)) {φ ψ : Ambient d → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ) {τ R : ℝ} (hτ : 0 ≤ τ)
    (hclose : ∀ᵐ v ∂patchMeasure d, |φ v - ψ v| ≤ τ) (hR : 0 < R) (q : ℝ≥0∞) :
    patchErrorConstant d p q < ⊤ ∧
    eLpNorm (graphExtension g φ - graphExtension g ψ) q
      (volume.restrict (Metric.ball (0 : Ambient d × ℝ) R)) ≤
      patchErrorConstant d p q *
        ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * q.toReal⁻¹) * τ) *
          eLpNorm g p (patchMeasure d) := by
  have : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let T := Metric.ball (0 : Ambient d × ℝ) R
  have : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have : Measure.IsAddHaarMeasure (volume : Measure (Ambient d × ℝ)) := by
    rw [Measure.volume_eq_prod (Ambient d) ℝ]
    infer_instance
  have hgint := hg.integrable hp
  have hcont : Continuous (graphExtension g φ - graphExtension g ψ) :=
    (graph_extension_continuous hgint hφ).sub (graph_extension_continuous hgint hψ)
  have hpoint : ∀ᵐ z ∂volume.restrict T, ‖(graphExtension g φ - graphExtension g ψ) z‖ ≤
      (R * τ) * ∫ v, ‖g v‖ ∂patchMeasure d := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := T) measurableSet_ball] with z hz
    have hzR : ‖z‖ < R := by simpa only [T, Metric.mem_ball, dist_zero_right] using hz
    have ht : |z.2| ≤ R := by
      simpa only [Real.norm_eq_abs] using (norm_snd_le z).trans hzR.le
    have H := phase_extension_perturbation (linear := fun v => ⟪z.1, v⟫)
      hgint (by fun_prop) hφ hψ hτ hclose z.2
    exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht hτ)
      (integral_nonneg fun v => norm_nonneg (g v)))
  have hLp := eLpNorm_le_of_ae_bound (p := q) hcont.aestronglyMeasurable hpoint
  simp only [Measure.restrict_apply_univ, ENNReal.ofReal_mul (mul_nonneg hR.le hτ)] at hLp
  have hL1 : ENNReal.ofReal (∫ v, ‖g v‖ ∂patchMeasure d) ≤
      eLpNorm g p (patchMeasure d) * (patchMeasure d) Set.univ ^ (1 - p.toReal⁻¹) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hgint, ← eLpNorm_one_eq_lintegral_enorm]
    · simpa only [ENNReal.toReal_one, div_one, one_div] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg.aestronglyMeasurable
    · exact hg.aestronglyMeasurable
  have hball : volume T ^ q.toReal⁻¹ =
      ENNReal.ofReal (R ^ (((d : ℝ) + 1) * q.toReal⁻¹)) *
        volume (Metric.ball (0 : Ambient d × ℝ) 1) ^ q.toReal⁻¹ := by
    dsimp only [T]
    rw [Measure.addHaar_ball volume (0 : Ambient d × ℝ) hR.le,
      show Module.finrank ℝ (Ambient d × ℝ) = d + 1 by simp [Module.finrank_prod, Ambient],
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ q.toReal⁻¹),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, Nat.cast_add, Nat.cast_one]
  have hfactor : ENNReal.ofReal (R ^ (((d : ℝ) + 1) * q.toReal⁻¹)) * ENNReal.ofReal (R * τ) =
      ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * q.toReal⁻¹) * τ) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_add hR, Real.rpow_one]
    ring
  refine ⟨patch_error_constant_lt_top hp q, ?_⟩
  calc
    _ ≤ volume T ^ q.toReal⁻¹ * (ENNReal.ofReal (R * τ) *
        (eLpNorm g p (patchMeasure d) * (patchMeasure d) Set.univ ^ (1 - p.toReal⁻¹))) :=
      hLp.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hL1))
    _ = _ := by
      rw [hball, ← hfactor]
      unfold patchErrorConstant
      ring

end RestrictionWork
