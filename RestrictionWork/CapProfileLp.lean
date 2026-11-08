import RestrictionWork.CapChartGeometry
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

/-- The compensated input has the correct cap scale in the explicitly
parametrized graph measure. No equality with canonical surface measure
is asserted here. The factor two is uniform in the cap radius. -/
theorem cap_profile_lp_bound {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {g : Ambient d → ℂ} {p : ℝ≥0∞} (hg : MemLp g p (patchMeasure d)) :
    MemLp (capProfile δ g) p (capParameterMeasure d δ) ∧
    eLpNorm (capProfile δ g) p (capParameterMeasure d δ) ≤
      ENNReal.ofReal (2 * δ ^ d) ^ p.toReal⁻¹ * eLpNorm g p (patchMeasure d) := by
  have hunit : ∀ᵐ v ∂patchMeasure d, v ∈ Metric.ball (0 : Ambient d) 1 :=
    ae_restrict_mem measurableSet_ball
  have hdom : capParameterMeasure d δ ≤ ENNReal.ofReal (2 * δ ^ d) • patchMeasure d := by
    unfold capParameterMeasure
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hunit] with v hv
    exact ENNReal.ofReal_le_ofReal (cap_chart_geometry hδ hδ₁ hv).2.2.2.2
  have hheight : Continuous (fun v : Ambient d => (capHeight δ v : ℂ)) := by
    unfold capHeight
    fun_prop
  have hbase : ∀ᵐ v ∂patchMeasure d, ‖capProfile δ g v‖ ≤ ‖g v‖ := by
    filter_upwards [hunit] with v hv
    obtain ⟨hwlo, hwhi, _⟩ := cap_chart_geometry hδ hδ₁ hv
    have hw0 : 0 ≤ capHeight δ v := le_trans (by norm_num) hwlo
    simpa [capProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0] using
      mul_le_mul_of_nonneg_right hwhi (norm_nonneg (g v))
  have hpbase : MemLp (capProfile δ g) p (patchMeasure d) :=
    hg.mono (hheight.aestronglyMeasurable.mul hg.aestronglyMeasurable) hbase
  have hc0 : ENNReal.ofReal (2 * δ ^ d) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  refine ⟨hpbase.of_measure_le_smul ENNReal.ofReal_ne_top hdom, ?_⟩
  calc
    _ ≤ eLpNorm (capProfile δ g) p (ENNReal.ofReal (2 * δ ^ d) • patchMeasure d) :=
      eLpNorm_mono_measure _ hdom
    _ = ENNReal.ofReal (2 * δ ^ d) ^ p.toReal⁻¹ * eLpNorm (capProfile δ g) p (patchMeasure d) := by
      rw [eLpNorm_smul_measure_of_ne_zero hc0]
      simp only [one_div, ENNReal.toReal_inv, smul_eq_mul]
    _ ≤ _ := mul_le_mul' le_rfl (eLpNorm_mono_ae hpbase.aestronglyMeasurable hbase)

end RestrictionWork
