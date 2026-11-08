import RestrictionWork.ShiftedSphericalLineSlope
import RestrictionWork.ShiftedSphericalLineCurvature
import LeanOscillatory.VanDerCorput

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter
open scoped RealInnerProductSpace Interval Topology
namespace RestrictionWork

theorem shifted_spherical_affine_line_derivatives {d : ℕ} {δ r s c ξ τ : ℝ}
    {a v w : Ambient d} (hδ : δ ≠ 0) (hr : r ≠ 0)
    (hs : 0 < 1 - δ ^ 2 * ‖a + r • (v + s • w)‖ ^ 2) :
    let G := fun x : ℝ => shiftedSphericalGraphPhase δ a r (v + x • w)
    let F := fun x : ℝ => c + ξ * x + τ * G x
    ContDiffAt ℝ 2 F s ∧ HasDerivAt F (ξ + τ * deriv G s) s ∧
      HasDerivAt (deriv F) (τ * deriv (deriv G) s) s := by
  intro G F
  have hG : ContDiffAt ℝ 2 G s := shifted_spherical_line_contDiffAt hs
  have hF : ContDiffAt ℝ 2 F s := by dsimp only [F]; fun_prop
  have hDeriv (x : ℝ) (hx : 0 < 1 - δ ^ 2 * ‖a + r • (v + x • w)‖ ^ 2) :
      HasDerivAt F (ξ + τ * deriv G x) x := by
    have hGx : HasDerivAt G (deriv G x) x :=
      ((shifted_spherical_line_contDiffAt hx).differentiableAt (by norm_num)).hasDerivAt
    have hLin : HasDerivAt (fun y : ℝ => c + ξ * y) ξ x := by
      exact (hasDerivAt_const_mul (x := x) ξ).const_add c
    exact hLin.add (hGx.const_mul τ)
  refine ⟨hF, hDeriv s hs, ?_⟩
  have hG' : DifferentiableAt ℝ (deriv G) s :=
    (shifted_spherical_line_second_derivative hδ hr a v w hs).differentiableAt
  have hDeriv' : HasDerivAt (fun x : ℝ => ξ + τ * deriv G x)
      (τ * deriv (deriv G) s) s := by
    exact (hG'.hasDerivAt.const_mul τ).const_add ξ
  apply hDeriv'.congr_of_eventuallyEq
  have hCont : Continuous (fun x : ℝ => 1 - δ ^ 2 * ‖a + r • (v + x • w)‖ ^ 2) := by
    fun_prop
  filter_upwards [hCont.continuousAt (isOpen_Ioi.mem_nhds hs)] with x hx
  exact (hDeriv x hx).deriv

/-- Constant amplitude slice bounds. Curvature controls the normal-frequency
regime. A separated first derivative controls the tangential regime. -/
theorem shifted_spherical_slice_estimates {d : ℕ} {δ r α β c ξ τ : ℝ} {a v w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hab : α < β) (hτ : 0 ≤ τ)
    (hw : ‖w‖ = 1) (hU : ∀ x ∈ Icc α β, ‖v + x • w‖ ≤ 1) :
    let F := fun x : ℝ => c + ξ * x + τ * shiftedSphericalGraphPhase δ a r (v + x • w)
    let I := ∫ x in α..β, Complex.exp ((F x : ℂ) * Complex.I)
    ‖I‖ ≤ β - α ∧ (0 < τ → ‖I‖ ≤ 8 / Real.sqrt (2 * τ)) ∧
      (0 < |ξ| → 10 * τ ≤ |ξ| / 2 → ‖I‖ ≤ 6 / |ξ|) := by
  intro F I
  let G := fun x : ℝ => shiftedSphericalGraphPhase δ a r (v + x • w)
  have hJets (x : ℝ) (hx : x ∈ Icc α β) :
      ContDiffAt ℝ 2 F x ∧ HasDerivAt F (ξ + τ * deriv G x) x ∧
        HasDerivAt (deriv F) (τ * deriv (deriv G) x) x := by
    have hrad := spherical_radicand_lower_bound hδ.le hδhalf
      (rebase_point_norm_le_one ha hr.le hrhalf (hU x hx))
    exact shifted_spherical_affine_line_derivatives hδ.ne' hr.ne' (by linarith only [hrad])
  have hC : ContDiffOn ℝ 2 F (uIcc α β) := by
    rw [uIcc_of_le hab.le]
    exact fun x hx => (hJets x hx).1.contDiffWithinAt
  have hF2 (x : ℝ) (hx : x ∈ Icc α β) : 2 * τ ≤ deriv (deriv F) x := by
    have H := (shifted_spherical_line_curvature hδ hδhalf ha hr hrhalf (w := w) (hU x hx)).1
    rw [hw] at H
    rw [(hJets x hx).2.2.deriv]
    simpa only [one_pow, mul_one, mul_comm τ 2] using mul_le_mul_of_nonneg_left H hτ
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [I]
    calc
      _ ≤ 1 * |β - α| := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x _ => by simp [Complex.norm_exp])
      _ = β - α := by rw [one_mul, abs_of_pos (sub_pos.mpr hab)]
  · intro hτpos
    have hLower (x : ℝ) (hx : x ∈ uIcc α β) :
        2 * τ ≤ |iteratedDerivWithin 2 F (uIcc α β) x| := by
      have hx' : x ∈ Icc α β := by simpa only [uIcc_of_le hab.le] using hx
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hab.ne) (hJets x hx').1 hx]
      change 2 * τ ≤ |iteratedDeriv (1 + 1) F x|
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact (hF2 x hx').trans (le_abs_self _)
    have H := Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two'
      (k := 2) le_rfl hC hLower (mul_pos (by norm_num) hτpos)
    have hpow : (2 * τ) ^ (-(1 : ℝ) / (2 : ℕ)) = (Real.sqrt (2 * τ))⁻¹ := by
      push_cast
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
    rw [hpow] at H
    have hconstant : Oscillatory.VanDerCorput.c 2 = 8 := by
      norm_num [Oscillatory.VanDerCorput.c]
    rw [hconstant] at H
    simpa only [I, div_eq_mul_inv] using H
  · intro hξ hsep
    have hD (x : ℝ) (hx : x ∈ uIcc α β) : derivWithin F (uIcc α β) x = deriv F x := by
      have hx' : x ∈ Icc α β := by simpa only [uIcc_of_le hab.le] using hx
      exact ((hJets x hx').2.1.differentiableAt.derivWithin
        (uniqueDiffOn_uIcc hab.ne x hx))
    have hm : MonotoneOn (deriv F) (Icc α β) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun x hx => (hJets x hx).2.2.continuousAt.continuousWithinAt
      · exact fun x hx => (hJets x (interior_subset hx)).2.2.differentiableAt.differentiableWithinAt
      · intro x hx
        exact (by positivity : 0 ≤ 2 * τ).trans (hF2 x (interior_subset hx))
    have hm' : MonotoneOn (derivWithin F (uIcc α β)) (uIcc α β) := by
      intro x hx y hy hxy
      rw [hD x hx, hD y hy]
      exact hm (by simpa only [uIcc_of_le hab.le] using hx)
        (by simpa only [uIcc_of_le hab.le] using hy) hxy
    have hLower (x : ℝ) (hx : x ∈ uIcc α β) :
        |ξ| / 2 ≤ |derivWithin F (uIcc α β) x| := by
      have hx' : x ∈ Icc α β := by simpa only [uIcc_of_le hab.le] using hx
      have H := shifted_spherical_line_slope_bound hδ hδhalf ha hr hrhalf (w := w) (hU x hx')
      change |deriv G x| ≤ 10 * ‖w‖ at H
      rw [hw, mul_one] at H
      have hsmall : |τ * deriv G x| ≤ |ξ| / 2 := by
        rw [abs_mul, abs_of_nonneg hτ]
        exact (mul_le_mul_of_nonneg_left H hτ).trans (by linarith)
      have htri : |ξ| ≤ |ξ + τ * deriv G x| + |τ * deriv G x| := by
        have HH := abs_add_le (ξ + τ * deriv G x) (-(τ * deriv G x))
        rw [add_neg_cancel_right, abs_neg] at HH
        exact HH
      rw [hD x hx, (hJets x hx').2.1.deriv]
      linarith
    have H := Oscillatory.norm_integral_exp_mul_I_le_of_order_one'
      hC hLower hm' (half_pos hξ)
    have he : Oscillatory.VanDerCorput.c 1 * (|ξ| / 2)⁻¹ = 6 / |ξ| := by
      simp only [Oscillatory.VanDerCorput.c]
      field_simp [hξ.ne']
      norm_num
    exact H.trans_eq he

end RestrictionWork
