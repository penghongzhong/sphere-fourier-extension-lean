import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Stereographic coordinates in the tangent vector space at the unit
pole. The scale compensates for a shrinking cap near the pole. -/
def sphereStereo (scale : ℝ) (pole point : E) : E :=
  scale • ((‖point - pole‖ ^ 2)⁻¹ • (point - pole) + (1 / 2 : ℝ) • pole)

private theorem unit_chord_inner {pole point : E} (hp : ‖pole‖ = 1) (hq : ‖point‖ = 1) :
    ⟪pole, point - pole⟫ = -(‖point - pole‖ ^ 2) / 2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real, hp, hq, real_inner_comm]
  ring

theorem sphere_stereo_tangent (scale : ℝ) {pole point : E}
    (hp : ‖pole‖ = 1) (hq : ‖point‖ = 1) (hne : point ≠ pole) :
    ⟪pole, sphereStereo scale pole point⟫ = 0 := by
  have ha : ‖point - pole‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [sphereStereo, real_inner_smul_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, unit_chord_inner hp hq,
    real_inner_self_eq_norm_sq, hp]
  field_simp [ha]
  ring

private theorem norm_inversion_sub {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y‖ = ‖x - y‖ / (‖x‖ * ‖y‖) := by
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hsq : ‖(‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y‖ ^ 2 =
      (‖x - y‖ / (‖x‖ * ‖y‖)) ^ 2 := by
    rw [div_pow, norm_sub_sq_real x y, norm_sub_sq_real, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (‖x‖ ^ 2)⁻¹),
      abs_of_nonneg (by positivity : 0 ≤ (‖y‖ ^ 2)⁻¹), real_inner_smul_left,
      real_inner_smul_right]
    field_simp [hx0, hy0]
    ring
  apply le_antisymm
  · exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq.le
  · exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq.symm.le

theorem sphere_stereo_distance {scale : ℝ} (hscale : 0 ≤ scale) {pole point other : E}
    (hp : point ≠ pole) (hq : other ≠ pole) :
    ‖sphereStereo scale pole point - sphereStereo scale pole other‖ =
      scale * ‖point - other‖ / (‖point - pole‖ * ‖other - pole‖) := by
  unfold sphereStereo
  rw [← smul_sub, add_sub_add_right_eq_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale,
    norm_inversion_sub (sub_ne_zero.mpr hp) (sub_ne_zero.mpr hq)]
  rw [show (point - pole) - (other - pole) = point - other by abel, mul_div_assoc]

theorem sphere_stereo_norm_sq (scale : ℝ) {pole point : E}
    (hp : ‖pole‖ = 1) (hq : ‖point‖ = 1) (hne : point ≠ pole) :
    ‖sphereStereo scale pole point‖ ^ 2 =
      scale ^ 2 / ‖point - pole‖ ^ 2 - scale ^ 2 / 4 := by
  have ha : ‖point - pole‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [sphereStereo, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (‖point - pole‖ ^ 2)⁻¹),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), real_inner_smul_left,
    real_inner_smul_right, real_inner_comm pole (point - pole),
    unit_chord_inner hp hq, hp]
  field_simp [ha]
  ring

/-- The polar hyperplane relation in stereographic coordinates, including
the exact factor away from the incidence set. -/
theorem sphere_stereo_incidence (scale : ℝ) {pole point other : E}
    (hp : ‖pole‖ = 1) (hq : ‖point‖ = 1) (ht : ‖other‖ = 1)
    (hne : point ≠ pole) (hne' : other ≠ pole) :
    ⟪sphereStereo scale pole point, sphereStereo scale pole other -
        sphereStereo scale pole point⟫ =
      scale ^ 2 * (⟪point - pole, other - pole⟫ - ‖other - pole‖ ^ 2) /
        (‖point - pole‖ ^ 2 * ‖other - pole‖ ^ 2) := by
  have ha : ‖point - pole‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hb : ‖other - pole‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne')
  have hdifference : sphereStereo scale pole other - sphereStereo scale pole point =
      scale • ((‖other - pole‖ ^ 2)⁻¹ • (other - pole) -
        (‖point - pole‖ ^ 2)⁻¹ • (point - pole)) := by
    unfold sphereStereo
    rw [← smul_sub, add_sub_add_right_eq_sub]
  rw [hdifference, sphereStereo, real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_sub_right, inner_sub_right]
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [unit_chord_inner hp hq, unit_chord_inner hp ht, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (‖point - pole‖ ^ 2)⁻¹)]
  field_simp [ha, hb]
  ring

end RestrictionWork
