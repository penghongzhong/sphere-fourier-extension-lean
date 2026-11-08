import RestrictionWork.GraphTubeAverage
import RestrictionWork.ShiftedGraphTubeGeometry
import RestrictionWork.ShiftedGraphLocalDual
import RestrictionWork.ShiftedSphericalMeasureDecay

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction
  (restrictionInputExponent restrictionInputExponent_bounds continuous_angularFourier)
namespace RestrictionWork

def patchTubeVolumeFactor (d : ℕ) : ℝ≥0∞ :=
  (patchTubeMassConstant d)⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ (d + 1)) *
    volume (ball (0 : Ambient (d + 1)) 1)

theorem patch_tube_volume_factor_finite (d : ℕ) :
    patchTubeVolumeFactor d ≠ ⊤ := by
  unfold patchTubeVolumeFactor
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (patch_tube_mass_constant_finite_positive d).1)
      ENNReal.ofReal_ne_top) measure_ball_lt_top.ne

theorem patch_tube_volume_ratio {d : ℕ} {h : ℝ} (hh : 0 < h) :
    (patchTubeMassConstant d * ENNReal.ofReal (h ^ d))⁻¹ *
      volume (ball (0 : Ambient (d + 1)) (2 * h)) =
    patchTubeVolumeFactor d * ENNReal.ofReal h := by
  let A := patchTubeMassConstant d
  let m := A * ENNReal.ofReal (h ^ d)
  let V := volume (ball (0 : Ambient (d + 1)) 1)
  obtain ⟨hA0, hAt⟩ := patch_tube_mass_constant_finite_positive d
  have hm0 : m ≠ 0 := mul_ne_zero hA0 (by positivity)
  have hmt : m ≠ ⊤ := ENNReal.mul_ne_top hAt ENNReal.ofReal_ne_top
  have he : m * (patchTubeVolumeFactor d * ENNReal.ofReal h) =
      volume (ball (0 : Ambient (d + 1)) (2 * h)) := by
    rw [Measure.addHaar_ball_of_pos volume _ (show 0 < 2 * h by positivity)]
    simp only [Ambient, finrank_euclideanSpace_fin]
    calc
      _ = (A * A⁻¹) * (ENNReal.ofReal ((2 : ℝ) ^ (d + 1)) *
            (ENNReal.ofReal (h ^ d) * ENNReal.ofReal h)) * V := by
        unfold m patchTubeVolumeFactor A V
        ring
      _ = _ := by
        rw [ENNReal.mul_inv_cancel hA0 hAt, one_mul, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← pow_succ, ← mul_pow]
  change m⁻¹ * _ = _
  rw [← he, ← mul_assoc, ENNReal.inv_mul_cancel hm0 hmt, one_mul]

/-- The real shifted graph has the codimension-one thin neighborhood gain,
uniform in the parent scale, the center and the subcap radius. -/
theorem shifted_graph_thin_restriction {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ R : ℝ, 1 ≤ R →
        ∀ f : Ambient (d + 1) → ℂ, Measurable f → Integrable f →
        (∀ x, R < ‖x‖ → f x = 0) → ∀ h : ℝ, 0 < h → h ≤ 1 →
          let p := restrictionInputExponent (d + 1)
          eLpNorm (angularFourier f) (ENNReal.ofReal p)
            (volume.restrict (patchGraphTube (shiftedSphericalGraphPhase δ a r) h)) ≤
            C * ENNReal.ofReal h ^ (1 / p) * ENNReal.ofReal (R ^ ε) *
              eLpNorm f (ENNReal.ofReal p) volume := by
  let p := restrictionInputExponent (d + 1)
  have hp : 0 < p := zero_lt_one.trans
    (restrictionInputExponent_bounds (show 2 ≤ d + 1 by omega)).1
  obtain ⟨A, hA, HA⟩ := shifted_graph_local_restriction_translated hd hε
  let D := (patchTubeVolumeFactor d) ^ (1 / p)
  have hD : D ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (patch_tube_volume_factor_finite d)
  refine ⟨D * A, ENNReal.mul_ne_top hD hA, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf R hR f hfm hfi hfs h hh hh1
  let φ := shiftedSphericalGraphPhase δ a r
  let m := patchTubeMassConstant d * ENNReal.ofReal (h ^ d)
  obtain ⟨hM0, hMt⟩ := patch_tube_mass_constant_finite_positive d
  have hm0 : m ≠ 0 := mul_ne_zero hM0 (by positivity)
  have hmt : m ≠ ⊤ := ENNReal.mul_ne_top hMt ENNReal.ofReal_ne_top
  have H := tube_norm_of_translated_bound (μ := patchGraphMeasure φ)
    (measurable_set_patch_graph_tube φ h) hm0 hmt
    (fun x hx => shifted_graph_tube_mass_lower hδ hδhalf ha hr hrhalf hh hh1 hx)
    hp (continuous_angularFourier hfi).measurable
    (HA hδ hδhalf ha hr hrhalf R hR f hfm hfi hfs)
  change _ ≤ ((patchTubeMassConstant d * ENNReal.ofReal (h ^ d))⁻¹ *
    volume (ball (0 : Ambient (d + 1)) (2 * h))) ^ (1 / p) * _ at H
  rw [patch_tube_volume_ratio hh, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at H
  apply H.trans_eq
  unfold D
  ring

end RestrictionWork
