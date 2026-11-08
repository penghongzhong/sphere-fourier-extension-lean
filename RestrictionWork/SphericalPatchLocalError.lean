import RestrictionWork.PhaseIntegralError
import RestrictionWork.GraphExtensionContinuous
import RestrictionWork.SphericalPhaseError
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

/-- Local L^p-to-L^q error between the centered spherical and paraboloid
extension operators. The measures and integrals are the actual ones.
The volume factors are kept exact, and no restriction estimate is assumed. -/
theorem spherical_patch_local_error {d : ℕ} {g : Ambient d → ℂ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hg : MemLp g p (patchMeasure d))
    {δ R : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) (hR : 0 ≤ R) (q : ℝ≥0∞) :
    MemLp (fun z => sphericalPatchExtension δ g z - paraboloidExtension g z) q
      (volume.restrict (Metric.ball (0 : Ambient d × ℝ) R)) ∧
    eLpNorm (fun z => sphericalPatchExtension δ g z - paraboloidExtension g z) q
      (volume.restrict (Metric.ball (0 : Ambient d × ℝ) R)) ≤
      volume (Metric.ball (0 : Ambient d × ℝ) R) ^ q.toReal⁻¹ *
        (ENNReal.ofReal (R * δ ^ 2) * (eLpNorm g p (patchMeasure d) *
          (patchMeasure d) Set.univ ^ (1 - p.toReal⁻¹))) := by
  haveI : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Ambient d × ℝ) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hgint : Integrable g (patchMeasure d) := MemLp.integrable hp hg
  have hφ : Measurable (fun v : Ambient d => sphericalPhase δ (‖v‖ ^ 2)) := by
    unfold sphericalPhase
    fun_prop
  have hψ : Measurable (fun v : Ambient d => ‖v‖ ^ 2) := by fun_prop
  have hclose : ∀ᵐ v ∂patchMeasure d, |sphericalPhase δ (‖v‖ ^ 2) - ‖v‖ ^ 2| ≤ δ ^ 2 := by
    have H : ∀ᵐ v ∂patchMeasure d, v ∈ Metric.ball (0 : Ambient d) 1 := by
      exact ae_restrict_mem measurableSet_ball
    filter_upwards [H] with v hv
    have hvnorm : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hv
    exact spherical_phase_quadratic_error δ (‖v‖ ^ 2) hδ hδ₁ (sq_nonneg _) (by nlinarith [norm_nonneg v])
  have hpoint (z : Ambient d × ℝ) :
      ‖sphericalPatchExtension δ g z - paraboloidExtension g z‖ ≤
        (|z.2| * δ ^ 2) * ∫ v, ‖g v‖ ∂patchMeasure d := by
    exact phase_extension_perturbation hgint (by fun_prop) hφ hψ (sq_nonneg δ) hclose z.2
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Ambient d × ℝ) R),
      ‖sphericalPatchExtension δ g z - paraboloidExtension g z‖ ≤
        (R * δ ^ 2) * ∫ v, ‖g v‖ ∂patchMeasure d := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have ht : |z.2| ≤ R := by
      simpa only [Real.norm_eq_abs] using (norm_snd_le z).trans hzR.le
    exact (hpoint z).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ht (sq_nonneg δ))
      (integral_nonneg fun v => norm_nonneg (g v)))
  have hcont : Continuous (fun z => sphericalPatchExtension δ g z - paraboloidExtension g z) :=
    (graph_extension_continuous hgint hφ).sub (graph_extension_continuous hgint hψ)
  refine ⟨MemLp.of_bound hcont.aestronglyMeasurable _ hbound, ?_⟩
  have Hnorm := eLpNorm_le_of_ae_bound (p := q) hcont.aestronglyMeasurable hbound
  simp only [Measure.restrict_apply_univ] at Hnorm
  have HL1 : ENNReal.ofReal (∫ v, ‖g v‖ ∂patchMeasure d) ≤
      eLpNorm g p (patchMeasure d) * (patchMeasure d) Set.univ ^ (1 - p.toReal⁻¹) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hgint, ← eLpNorm_one_eq_lintegral_enorm]
    simpa only [ENNReal.toReal_one, div_one, one_div] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg.aestronglyMeasurable
    exact hg.aestronglyMeasurable
  calc
    _ ≤ volume (Metric.ball (0 : Ambient d × ℝ) R) ^ q.toReal⁻¹ *
        ENNReal.ofReal ((R * δ ^ 2) * ∫ v, ‖g v‖ ∂patchMeasure d) := Hnorm
    _ = volume (Metric.ball (0 : Ambient d × ℝ) R) ^ q.toReal⁻¹ *
        (ENNReal.ofReal (R * δ ^ 2) * ENNReal.ofReal (∫ v, ‖g v‖ ∂patchMeasure d)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hR (sq_nonneg δ))]
    _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl HL1)

end RestrictionWork
