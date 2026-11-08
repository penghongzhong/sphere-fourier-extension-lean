import RestrictionWork.ShiftedSphericalGraphPhase
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped Topology RealInnerProductSpace
namespace RestrictionWork

/-- The first and second derivatives of the normalized phase along a line. -/
theorem shifted_spherical_line_derivatives {d : ℕ} {δ r t : ℝ}
    (hδ : δ ≠ 0) (hr : r ≠ 0) (a v w : Ambient d)
    (ht : 0 < 1 - δ ^ 2 * ‖a + r • (v + t • w)‖ ^ 2) :
    let x := a + r • (v + t • w)
    let h := Real.sqrt (1 - δ ^ 2 * ‖x‖ ^ 2)
    let G := fun s : ℝ => shiftedSphericalGraphPhase δ a r (v + s • w)
    HasDerivAt G ((2 * ⟪x, w⟫ / h - ⟪sphericalGraphSlope δ a, w⟫) / r) t ∧
      HasDerivAt (deriv G) (2 * ‖w‖ ^ 2 / h + 2 * δ ^ 2 * ⟪x, w⟫ ^ 2 / h ^ 3) t := by
  intro x h phase
  let b := a + r • v
  let l := sphericalGraphSlope δ a
  let X : ℝ → Ambient d := fun s => a + r • (v + s • w)
  let J : ℝ → ℝ := fun s => ⟪X s, w⟫
  let F : ℝ → ℝ := fun s => 1 - δ ^ 2 * ‖X s‖ ^ 2
  let H : ℝ → ℝ := fun s => Real.sqrt (F s)
  let G : ℝ → ℝ := fun s => shiftedSphericalGraphPhase δ a r (v + s • w)
  let D : ℝ → ℝ := fun s => (2 * J s / H s - ⟪l, w⟫) / r
  have hX (s : ℝ) : X s = b + (s * r) • w := by
    simp only [X, b, smul_add, smul_smul, add_assoc, mul_comm r s]
  have hJ (s : ℝ) : J s = ⟪b, w⟫ + (s * r) * ‖w‖ ^ 2 := by
    rw [show J s = ⟪X s, w⟫ from rfl, hX, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  have hJderiv (s : ℝ) : HasDerivAt J (r * ‖w‖ ^ 2) s := by
    convert (hasDerivAt_const s ⟪b, w⟫).add
      ((hasDerivAt_id' s).mul_const (r * ‖w‖ ^ 2)) using 1
    · funext y
      rw [hJ]
      simp only [Pi.add_apply]
      ring
    · ring
  have hQderiv (s : ℝ) : HasDerivAt (fun y => ‖X y‖ ^ 2) (2 * r * J s) s := by
    convert ((hasDerivAt_const s (‖b‖ ^ 2)).add
      ((hasDerivAt_id' s).mul_const (2 * r * ⟪b, w⟫))).add
      (((hasDerivAt_id' s).pow 2).mul_const (r ^ 2 * ‖w‖ ^ 2)) using 1
    · funext y
      rw [hX, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      simp only [Pi.add_apply, Pi.pow_apply]
      ring
    · rw [hJ]
      norm_num
      ring
  have hFderiv (s : ℝ) : HasDerivAt F (-2 * δ ^ 2 * r * J s) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hQderiv s).const_mul (δ ^ 2)) using 1
    ring
  have hHderiv (s : ℝ) (hs : 0 < F s) :
      HasDerivAt H (-δ ^ 2 * r * J s / H s) s := by
    convert (hFderiv s).sqrt hs.ne' using 1
    change -δ ^ 2 * r * J s / H s = -2 * δ ^ 2 * r * J s / (2 * H s)
    field_simp [(Real.sqrt_pos.2 hs).ne']
  have hφderiv (s : ℝ) (hs : 0 < F s) :
      HasDerivAt (fun y => sphericalGraphPhase δ (X y)) (2 * r * J s / H s) s := by
    have Hd := (((hasDerivAt_const s (1 : ℝ)).sub (hHderiv s hs)).const_mul 2).div_const (δ ^ 2)
    change HasDerivAt (fun y => sphericalGraphPhase δ (X y))
      (2 * (0 - (-δ ^ 2 * r * J s / H s)) / δ ^ 2) s at Hd
    apply Hd.congr_deriv
    field_simp [hδ, (Real.sqrt_pos.2 hs).ne']
    ring
  have hD (s : ℝ) (hs : 0 < F s) : HasDerivAt G (D s) s := by
    have hlin : HasDerivAt (fun y : ℝ => r * ⟪l, v + y • w⟫) (r * ⟪l, w⟫) s := by
      convert ((hasDerivAt_const s ⟪l, v⟫).add
        ((hasDerivAt_id' s).mul_const ⟪l, w⟫)).const_mul r using 1
      · funext y
        simp only [inner_add_right, real_inner_smul_right, Pi.add_apply]
      · ring
    have Hd := (((hφderiv s hs).sub (hasDerivAt_const s (sphericalGraphPhase δ a))).sub
      hlin).div_const (r ^ 2)
    change HasDerivAt G ((2 * r * J s / H s - 0 - r * ⟪l, w⟫) / r ^ 2) s at Hd
    apply Hd.congr_deriv
    dsimp only [D]
    field_simp [hr, (Real.sqrt_pos.2 hs).ne']
    ring
  have htF : 0 < F t := ht
  have hDderiv : HasDerivAt D
      (2 * ‖w‖ ^ 2 / h + 2 * δ ^ 2 * ⟪x, w⟫ ^ 2 / h ^ 3) t := by
    convert ((((hJderiv t).const_mul 2).div (hHderiv t htF)
      (Real.sqrt_pos.2 htF).ne').sub (hasDerivAt_const t ⟪l, w⟫)).div_const r using 1
    change 2 * ‖w‖ ^ 2 / H t + 2 * δ ^ 2 * J t ^ 2 / H t ^ 3 =
      ((2 * (r * ‖w‖ ^ 2) * H t - 2 * J t * (-δ ^ 2 * r * J t / H t)) /
        (H t) ^ 2 - 0) / r
    field_simp [hr, (Real.sqrt_pos.2 htF).ne']
    ring
  refine ⟨hD t htF, ?_⟩
  change HasDerivAt (deriv G) _ t
  apply hDderiv.congr_of_eventuallyEq
  have hFc : Continuous F := by unfold F X; fun_prop
  filter_upwards [hFc.continuousAt (isOpen_Ioi.mem_nhds htF)] with s hs
  exact (hD s hs).deriv

/-- The Hessian along the line, with the same interface as the curvature proof. -/
theorem shifted_spherical_line_second_derivative {d : ℕ} {δ r t : ℝ}
    (hδ : δ ≠ 0) (hr : r ≠ 0) (a v w : Ambient d)
    (ht : 0 < 1 - δ ^ 2 * ‖a + r • (v + t • w)‖ ^ 2) :
    let x := a + r • (v + t • w)
    let h := Real.sqrt (1 - δ ^ 2 * ‖x‖ ^ 2)
    HasDerivAt (deriv (fun s : ℝ => shiftedSphericalGraphPhase δ a r (v + s • w)))
      (2 * ‖w‖ ^ 2 / h + 2 * δ ^ 2 * ⟪x, w⟫ ^ 2 / h ^ 3) t :=
  (shifted_spherical_line_derivatives hδ hr a v w ht).2

end RestrictionWork
