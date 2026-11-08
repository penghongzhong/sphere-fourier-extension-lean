import RestrictionWork.CapProfileLp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- Exact oscillatory rescaling with the genuine weighted parameter measure.
The original canonical surface-area identification is not an assumption or
conclusion of this theorem. Integrability is part of the returned result. -/
theorem cap_rescaling_integral {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {g : Ambient d → ℂ} (hg : Integrable g (patchMeasure d)) (z : Ambient d × ℝ) :
    Integrable (fun v => capProfile δ g v * Complex.exp
      (((⟪(capPhysicalScale δ z).1, δ • v⟫ + (capPhysicalScale δ z).2 * capHeight δ v : ℝ) : ℂ) * Complex.I))
      (capParameterMeasure d δ) ∧
    capGraphExtension δ (capProfile δ g) (capPhysicalScale δ z) =
      ((δ ^ d : ℝ) : ℂ) * Complex.exp (((-2 * z.2 / δ ^ 2 : ℝ) : ℂ) * Complex.I) *
        sphericalPatchExtension δ g z := by
  have hprof : Integrable (capProfile δ g) (capParameterMeasure d δ) :=
    memLp_one_iff_integrable.mp (cap_profile_lp_bound hδ hδ₁ (memLp_one_iff_integrable.mpr hg)).1
  have hkernel : Measurable (fun v : Ambient d => Complex.exp
      (((⟪(capPhysicalScale δ z).1, δ • v⟫ + (capPhysicalScale δ z).2 * capHeight δ v : ℝ) : ℂ) * Complex.I)) := by
    unfold capHeight
    fun_prop
  have hint : Integrable (fun v => capProfile δ g v * Complex.exp
      (((⟪(capPhysicalScale δ z).1, δ • v⟫ + (capPhysicalScale δ z).2 * capHeight δ v : ℝ) : ℂ) * Complex.I))
      (capParameterMeasure d δ) := by
    apply hprof.mono (hprof.aestronglyMeasurable.mul hkernel.aestronglyMeasurable)
    filter_upwards [] with v
    simp [norm_mul, Complex.norm_exp]
  refine ⟨hint, ?_⟩
  have hphase (v : Ambient d) :
      ⟪(capPhysicalScale δ z).1, δ • v⟫ + (capPhysicalScale δ z).2 * capHeight δ v =
      -2 * z.2 / δ ^ 2 + (⟪z.1, v⟫ + z.2 * sphericalPhase δ (‖v‖ ^ 2)) := by
    simp only [capPhysicalScale, real_inner_smul_left, real_inner_smul_right]
    unfold capHeight sphericalPhase
    field_simp [hδ.ne']
    ring
  have hexp (v : Ambient d) :
      Complex.exp (((⟪(capPhysicalScale δ z).1, δ • v⟫ + (capPhysicalScale δ z).2 * capHeight δ v : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-2 * z.2 / δ ^ 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((⟪z.1, v⟫ + z.2 * sphericalPhase δ (‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I) := by
    rw [hphase, Complex.ofReal_add, add_mul, Complex.exp_add]
  unfold capGraphExtension capParameterMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun v : Ambient d => ENNReal.ofReal (capDensity δ v)) by
      unfold capDensity capHeight; fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold sphericalPatchExtension graphExtension phaseExtension
  rw [← integral_const_mul (((δ ^ d : ℝ) : ℂ) *
    Complex.exp (((-2 * z.2 / δ ^ 2 : ℝ) : ℂ) * Complex.I))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with v hv
  obtain ⟨hwlo, _, _, _, _⟩ := cap_chart_geometry hδ hδ₁ hv
  have hwpos : 0 < capHeight δ v := by linarith
  have hdnonneg : 0 ≤ capDensity δ v := by unfold capDensity; positivity
  have hcancel : (capDensity δ v : ℂ) * (capHeight δ v : ℂ) = ((δ ^ d : ℝ) : ℂ) := by
    have H : capDensity δ v * capHeight δ v = δ ^ d := div_mul_cancel₀ _ hwpos.ne'
    exact_mod_cast H
  rw [ENNReal.toReal_ofReal hdnonneg, Complex.real_smul, capProfile, hexp]
  calc
    _ = ((capDensity δ v : ℂ) * (capHeight δ v : ℂ)) *
        (Complex.exp (((-2 * z.2 / δ ^ 2 : ℝ) : ℂ) * Complex.I) *
          (g v * Complex.exp (((⟪z.1, v⟫ + z.2 * sphericalPhase δ (‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I))) := by ring
    _ = _ := by rw [hcancel]; ring

end RestrictionWork
