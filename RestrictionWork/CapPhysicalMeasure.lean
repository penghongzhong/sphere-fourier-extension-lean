import RestrictionWork.CapChartDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RestrictionWork

/-- The exact pushforward of physical Lebesgue measure under the parabolic
coordinate change. The factor 1/2 is retained. -/
theorem cap_physical_measure {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (volume : Measure (Ambient d × ℝ)).map (capPhysicalScale δ) =
      ENNReal.ofReal (δ ^ (d + 2) / 2) • (volume : Measure (Ambient d × ℝ)) := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Ambient d × ℝ)) := by
    rw [Measure.volume_eq_prod (Ambient d) ℝ]
    infer_instance
  let A : (Ambient d × ℝ) →ₗ[ℝ] (Ambient d × ℝ) :=
    LinearMap.prodMap (δ⁻¹ • (LinearMap.id : Ambient d →ₗ[ℝ] Ambient d))
      ((-2 / δ ^ 2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  have hA : (A : (Ambient d × ℝ) → Ambient d × ℝ) = capPhysicalScale δ := by
    funext z
    apply Prod.ext
    · rfl
    · simp only [A, LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply,
        capPhysicalScale, smul_eq_mul]
      ring
  have hdet : LinearMap.det A = (δ⁻¹) ^ d * (-2 / δ ^ 2) := by
    simp [A, LinearMap.det_prodMap, LinearMap.det_smul, Ambient]
  have hdet₀ : LinearMap.det A ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hδ.ne')) (div_ne_zero (by norm_num) (pow_ne_zero _ hδ.ne'))
  have hinv : ((δ⁻¹) ^ d * (-2 / δ ^ 2))⁻¹ = -(δ ^ (d + 2) / 2) := by
    rw [inv_pow]
    field_simp [hδ.ne', pow_add]
    simp only [pow_add]
  have habs : |(LinearMap.det A)⁻¹| = δ ^ (d + 2) / 2 := by
    rw [hdet, hinv, abs_neg, abs_of_nonneg (by positivity)]
  have H := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Ambient d × ℝ)) hdet₀
  rw [hA, habs] at H
  exact H

end RestrictionWork
