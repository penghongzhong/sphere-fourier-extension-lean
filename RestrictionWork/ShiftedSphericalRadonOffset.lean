import RestrictionWork.ShiftedSphericalRadonPhase
import RestrictionWork.ShiftedSphericalStereoBounds

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- On a separated spherical collision strip, the normalized direction has
unit length in the tangent plane and the offset is in a fixed interval.
The error is expressed in the standard offset variable of the Radon transform. -/
theorem shifted_collision_radon_offset_strip {d : ℕ} {δ r σ ε : ℝ} {a u y w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖u + y - w‖ ≤ 1)
    (hσ : 0 < σ) (hsepY : σ ≤ ‖y - u‖) (hsepW : σ ≤ ‖w - u‖)
    (hε : |shiftedCollisionPhase δ a r u y w| ≤ ε) :
    let P := shiftedCapPoint δ a r
    let Y := sphereStereo (δ * r) (P u) (P y)
    let W := sphereStereo (δ * r) (P u) (P w)
    let θ := ‖Y‖⁻¹ • Y
    ‖θ‖ = 1 ∧ ⟪P u, θ⟫ = 0 ∧ ⟪P u, W⟫ = 0 ∧
      (1 / 8 : ℝ) ≤ ‖Y‖ ∧ ‖Y‖ ≤ 1 / σ ∧
      |‖Y‖ - ⟪W, θ⟫| ≤ 6 * ε / σ ^ 4 := by
  intro P Y W θ
  obtain ⟨hYt, hYlo, hYhi⟩ :=
    shifted_spherical_stereo_tangent_annulus hδ hδhalf ha hr hrhalf hu hy hσ hsepY
  obtain ⟨hWt, _, _⟩ :=
    shifted_spherical_stereo_tangent_annulus hδ hδhalf ha hr hrhalf hu hw hσ hsepW
  change ⟪P u, Y⟫ = 0 at hYt
  change ⟪P u, W⟫ = 0 at hWt
  change 1 / 8 ≤ ‖Y‖ at hYlo
  change ‖Y‖ ≤ 1 / σ at hYhi
  have hY0 : 0 < ‖Y‖ := by linarith
  have H := shifted_collision_radon_strip hδ hδhalf ha hr hrhalf hu hy hw hz hσ hsepY hsepW hε
  change |⟪Y, W - Y⟫| ≤ 3 * ε / (4 * σ ^ 4) at H
  refine ⟨?_, ?_, hWt, hYlo, hYhi, ?_⟩
  · dsimp only [θ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hY0.le), inv_mul_cancel₀ hY0.ne']
  · dsimp only [θ]
    rw [real_inner_smul_right, hYt, mul_zero]
  · have he : ‖Y‖ - ⟪W, θ⟫ = -‖Y‖⁻¹ * ⟪Y, W - Y⟫ := by
      dsimp only [θ]
      rw [real_inner_smul_right, real_inner_comm Y W, inner_sub_right, real_inner_self_eq_norm_sq]
      field_simp [hY0.ne']
      ring
    have hInv : ‖Y‖⁻¹ ≤ 8 := by
      rw [inv_eq_one_div, div_le_iff₀ hY0]
      linarith
    rw [he, abs_mul, abs_neg, abs_of_nonneg (inv_nonneg.mpr hY0.le)]
    calc
      _ ≤ 8 * (3 * ε / (4 * σ ^ 4)) :=
        mul_le_mul hInv H (abs_nonneg _) (by norm_num)
      _ = _ := by ring

end RestrictionWork
