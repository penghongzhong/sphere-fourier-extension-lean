import RestrictionWork.Target
import RestrictionWork.ExtensionContinuous
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- The original extension maps every sphere Lp, p at least one, into
L-infinity, with a finite constant fixed before the input is chosen. -/
theorem extension_top_bound {n : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    BoundedSphereExtension n p ⊤ := by
  haveI : IsFiniteMeasure (sphereMeasure n) := by unfold sphereMeasure; infer_instance
  have hpinv : p.toReal⁻¹ ≤ 1 := by
    by_cases hpt : p = ⊤
    · simp [hpt]
    · have hr : (1 : ℝ) ≤ p.toReal := by
        simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hpt hp
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr
  let B := (sphereMeasure n) Set.univ ^ (1 - p.toReal⁻¹)
  have hB : B ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _)
  refine ⟨B.toNNReal, ?_⟩
  intro f hf
  have hfi : Integrable f (sphereMeasure n) :=
    memLp_one_iff_integrable.mp (hf.mono_exponent hp)
  have he : eLpNorm (extension f) ⊤ volume ≤ eLpNorm f 1 (sphereMeasure n) := by
    rw [eLpNorm_exponent_top (extension_continuous hfi).aestronglyMeasurable]
    calc
      _ ≤ ENNReal.ofReal (∫ ω, ‖f ω‖ ∂sphereMeasure n) :=
        eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall (extension_bound hfi))
      _ = _ := by
        rw [ofReal_integral_norm_eq_lintegral_enorm hfi,
          eLpNorm_one_eq_lintegral_enorm hfi.aestronglyMeasurable]
  have hi : eLpNorm f 1 (sphereMeasure n) ≤ eLpNorm f p (sphereMeasure n) * B := by
    simpa only [ENNReal.toReal_one, div_one, one_div] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
  have H : eLpNorm (extension f) ⊤ volume ≤ B * eLpNorm f p (sphereMeasure n) := by
    simpa only [mul_comm] using he.trans hi
  rw [ENNReal.coe_toNNReal hB]
  exact ⟨H.trans_lt (ENNReal.mul_lt_top hB.lt_top hf), H⟩

end RestrictionWork
