import RestrictionWork.PatchGraphMeasure
import RestrictionWork.ShiftedSphericalFourierDecay
import RestrictionWork.FourierMeasureExtension

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

instance patch_graph_measure_finite {d : ℕ} (φ : Ambient d → ℝ) :
    IsFiniteMeasure (patchGraphMeasure φ) := by
  have : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  unfold patchGraphMeasure
  infer_instance

/-- Uniform decay on the Euclidean frequency space used by the sparse-ball
restriction proof. -/
theorem shifted_spherical_measure_decay {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ x : Ambient (d + 1),
        ‖measureExtension (patchGraphMeasure (shiftedSphericalGraphPhase δ a r))
          (fun _ => 1) x‖ ≤ C * (1 + ‖x‖) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, hA, HA⟩ := shifted_spherical_kernel_decay hd
  refine ⟨2 * A, by positivity, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf x
  let φ := shiftedSphericalGraphPhase δ a r
  let e := euclideanSliceEquiv (Fin.last d)
  let z := e.symm x
  have hx : e z = x := e.apply_symm_apply x
  have hφ : Measurable φ := by
    unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hK : measureExtension (patchGraphMeasure φ) (fun _ => 1) x = patchGraphKernel φ z := by
    rw [← hx]
    unfold measureExtension
    simp only [mul_one, mul_comm Complex.I]
    exact patch_graph_measure_integral hφ z
  have hsize : ‖x‖ ≤ 2 * ‖z‖ := by
    rw [← hx]
    exact euclidean_slice_norm_le_product (Fin.last d) z
  have hroot : Real.sqrt (1 + ‖x‖) ≤ 2 * Real.sqrt (1 + ‖z‖) := by
    calc
      _ ≤ Real.sqrt (4 * (1 + ‖z‖)) := Real.sqrt_le_sqrt (by linarith [norm_nonneg z])
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hp : 0 < Real.sqrt (1 + ‖z‖) := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < Real.sqrt (1 + ‖x‖) := Real.sqrt_pos.2 (by positivity)
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  change ‖measureExtension (patchGraphMeasure φ) (fun _ => 1) x‖ ≤ _
  rw [hK]
  apply (le_div_iff₀ hq).mpr
  calc
    _ ≤ (A / Real.sqrt (1 + ‖z‖)) * (2 * Real.sqrt (1 + ‖z‖)) :=
      mul_le_mul (HA hδ hδhalf ha hr hrhalf z) hroot hq.le (by positivity)
    _ = _ := by field_simp [hp.ne']

end RestrictionWork
