import RestrictionWork.SphericalPatchLocalError
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

/-- The actual local approximation error with its radius power and a proved
finite constant independent of δ, R and g. Product physical space carries its
standard product norm. No global restriction input is assumed. -/
theorem spherical_patch_power_error {d : ℕ} {g : Ambient d → ℂ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hg : MemLp g p (patchMeasure d))
    {δ R : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) (hR : 0 < R) (q : ℝ≥0∞) :
    patchErrorConstant d p q < ⊤ ∧
    MemLp (fun z => sphericalPatchExtension δ g z - paraboloidExtension g z) q
      (volume.restrict (Metric.ball (0 : Ambient d × ℝ) R)) ∧
    eLpNorm (fun z => sphericalPatchExtension δ g z - paraboloidExtension g z) q
      (volume.restrict (Metric.ball (0 : Ambient d × ℝ) R)) ≤
      patchErrorConstant d p q *
        ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * q.toReal⁻¹) * δ ^ 2) *
          eLpNorm g p (patchMeasure d) := by
  haveI : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Ambient d × ℝ)) := by
    rw [Measure.volume_eq_prod (Ambient d) ℝ]
    infer_instance
  have hpinv : p.toReal⁻¹ ≤ 1 := by
    by_cases hpt : p = ⊤
    · simp [hpt]
    · have hr : (1 : ℝ) ≤ p.toReal := by
        simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hpt hp
      simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr
  have hC : patchErrorConstant d p q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_lt_top.ne
    · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _)
  obtain ⟨hmem, H⟩ := spherical_patch_local_error hp hg hδ hδ₁ hR.le q
  have hdim : Module.finrank ℝ (Ambient d × ℝ) = d + 1 := by
    simp [Module.finrank_prod, Ambient]
  have hpower : (R ^ (d + 1) : ℝ) ^ q.toReal⁻¹ =
      R ^ (((d : ℝ) + 1) * q.toReal⁻¹) := by
    calc
      _ = (R ^ ((d + 1 : ℕ) : ℝ)) ^ q.toReal⁻¹ := by rw [Real.rpow_natCast]
      _ = R ^ (((d + 1 : ℕ) : ℝ) * q.toReal⁻¹) :=
        (Real.rpow_mul hR.le ((d + 1 : ℕ) : ℝ) q.toReal⁻¹).symm
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]
  have hball : volume (Metric.ball (0 : Ambient d × ℝ) R) ^ q.toReal⁻¹ =
      ENNReal.ofReal (R ^ (((d : ℝ) + 1) * q.toReal⁻¹)) *
        volume (Metric.ball (0 : Ambient d × ℝ) 1) ^ q.toReal⁻¹ := by
    rw [Measure.addHaar_ball volume (0 : Ambient d × ℝ) hR.le, hdim,
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ q.toReal⁻¹),
      ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ R ^ (d + 1)) (by positivity), hpower]
  have hscalar : ENNReal.ofReal (R ^ (((d : ℝ) + 1) * q.toReal⁻¹)) *
      ENNReal.ofReal (R * δ ^ 2) =
      ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * q.toReal⁻¹) * δ ^ 2) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    congr 1
    rw [Real.rpow_add hR, Real.rpow_one]
    ring
  refine ⟨hC, hmem, ?_⟩
  rw [hball] at H
  calc
    _ ≤ _ := H
    _ = patchErrorConstant d p q *
        (ENNReal.ofReal (R ^ (((d : ℝ) + 1) * q.toReal⁻¹)) * ENNReal.ofReal (R * δ ^ 2)) *
          eLpNorm g p (patchMeasure d) := by unfold patchErrorConstant; ring
    _ = _ := by rw [hscalar]

end RestrictionWork
