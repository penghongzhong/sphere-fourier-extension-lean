import RestrictionWork.ShiftedSphericalLineDerivatives

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- Every directional second derivative of the rebased phase is bounded
above and below by fixed multiples of the squared direction norm. -/
theorem shifted_spherical_line_curvature {d : ℕ} {δ r t : ℝ} {a v w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖v + t • w‖ ≤ 1) :
    let G := fun s : ℝ => shiftedSphericalGraphPhase δ a r (v + s • w)
    2 * ‖w‖ ^ 2 ≤ deriv (deriv G) t ∧ deriv (deriv G) t ≤ 8 * ‖w‖ ^ 2 := by
  intro G
  let x := a + r • (v + t • w)
  let h := Real.sqrt (1 - δ ^ 2 * ‖x‖ ^ 2)
  have hx : ‖x‖ ≤ 1 := by
    calc
      _ ≤ ‖a‖ + ‖r • (v + t • w)‖ := norm_add_le _ _
      _ = ‖a‖ + r * ‖v + t • w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ 1 := by nlinarith only [ha, hrhalf, mul_le_mul_of_nonneg_left hu hr.le]
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have harg : 3 / 4 ≤ 1 - δ ^ 2 * ‖x‖ ^ 2 := by
    nlinarith only [hδsq, mul_le_mul_of_nonneg_left hx2 (sq_nonneg δ)]
  have hh : 1 / 2 ≤ h := Real.le_sqrt_of_sq_le (by linarith only [harg])
  have hhpos : 0 < h := by linarith
  have hhone : h ≤ 1 := by
    calc
      h ≤ Real.sqrt 1 := Real.sqrt_le_sqrt
        (sub_le_self _ (by positivity : 0 ≤ δ ^ 2 * ‖x‖ ^ 2))
      _ = 1 := Real.sqrt_one
  have hh3 : 1 / 8 ≤ h ^ 3 := by
    calc
      _ = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hh 3
  have hin : ⟪x, w⟫ ^ 2 ≤ ‖w‖ ^ 2 := by
    have hC : |⟪x, w⟫| ≤ ‖w‖ := by
      calc
        _ ≤ ‖x‖ * ‖w‖ := by
          simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) x w)
        _ ≤ ‖w‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg w)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hC
  have he : deriv (deriv G) t = 2 * ‖w‖ ^ 2 / h + 2 * δ ^ 2 * ⟪x, w⟫ ^ 2 / h ^ 3 :=
    (shifted_spherical_line_second_derivative hδ.ne' hr.ne' a v w (by linarith only [harg])).deriv
  have hlo : 2 * ‖w‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 / h := by
    rw [le_div_iff₀ hhpos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hhone (by positivity : 0 ≤ 2 * ‖w‖ ^ 2)
  have hhi : 2 * ‖w‖ ^ 2 / h ≤ 4 * ‖w‖ ^ 2 := by
    rw [div_le_iff₀ hhpos]
    nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg ‖w‖)]
  have hpositive : 0 ≤ 2 * δ ^ 2 * ⟪x, w⟫ ^ 2 / h ^ 3 := by positivity
  have hsecond : 2 * δ ^ 2 * ⟪x, w⟫ ^ 2 / h ^ 3 ≤ 4 * ‖w‖ ^ 2 := by
    rw [div_le_iff₀ (pow_pos hhpos _)]
    calc
      _ ≤ (2 * (1 / 4)) * ‖w‖ ^ 2 :=
        mul_le_mul (by linarith) hin (sq_nonneg _) (by norm_num)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hh3 (sq_nonneg ‖w‖)]
  rw [he]
  constructor <;> linarith

end RestrictionWork
