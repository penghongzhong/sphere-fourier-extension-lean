import RestrictionWork.ShiftedSphericalLineDerivatives
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

theorem spherical_radicand_lower_bound {d : ℕ} {δ : ℝ} {v : Ambient d}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (hv : ‖v‖ ≤ 1) :
    3 / 4 ≤ 1 - δ ^ 2 * ‖v‖ ^ 2 := by
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hvsq : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  nlinarith only [hδsq, mul_le_mul_of_nonneg_left hvsq (sq_nonneg δ)]

theorem rebase_point_norm_le_one {d : ℕ} {a u : Ambient d} {r : ℝ}
    (ha : ‖a‖ ≤ 1 / 2) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) :
    ‖a + r • u‖ ≤ 1 := by
  calc
    _ ≤ ‖a‖ + ‖r • u‖ := norm_add_le _ _
    _ = ‖a‖ + r * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ 1 := by nlinarith only [ha, hrhalf, mul_le_mul_of_nonneg_left hu hr]

theorem shifted_spherical_line_contDiffAt {d : ℕ} {δ r t : ℝ}
    {a v w : Ambient d} (ht : 0 < 1 - δ ^ 2 * ‖a + r • (v + t • w)‖ ^ 2) :
    ContDiffAt ℝ 2 (fun s : ℝ => shiftedSphericalGraphPhase δ a r (v + s • w)) t := by
  unfold shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
  have hnorm : ContDiffAt ℝ 2 (fun s : ℝ => ‖a + r • (v + s • w)‖ ^ 2) t := by
    apply ContDiffAt.norm_sq (𝕜 := ℝ)
    fun_prop
  have harg : ContDiffAt ℝ 2 (fun s : ℝ => 1 - δ ^ 2 * ‖a + r • (v + s • w)‖ ^ 2) t := by
    fun_prop
  have hne : 1 - δ ^ 2 * ‖a + r • (v + t • w)‖ ^ 2 ≠ 0 := ht.ne'
  have hs := harg.sqrt hne
  simp only [inner_add_right, real_inner_smul_right]
  fun_prop

/-- The derivative after subtracting the tangent plane stays uniformly
bounded even as the subcap radius tends to zero. -/
theorem shifted_spherical_line_slope_bound {d : ℕ} {δ r t : ℝ} {a v w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖v + t • w‖ ≤ 1) :
    |deriv (fun s : ℝ => shiftedSphericalGraphPhase δ a r (v + s • w)) t| ≤ 10 * ‖w‖ := by
  let u := v + t • w
  let x := a + r • u
  let h := Real.sqrt (1 - δ ^ 2 * ‖x‖ ^ 2)
  let k := Real.sqrt (1 - δ ^ 2 * ‖a‖ ^ 2)
  have hx : ‖x‖ ≤ 1 := rebase_point_norm_le_one ha hr.le hrhalf hu
  have hxarg := spherical_radicand_lower_bound hδ.le hδhalf hx
  have haarg := spherical_radicand_lower_bound hδ.le hδhalf (ha.trans (by norm_num))
  have hh : 1 / 2 ≤ h := Real.le_sqrt_of_sq_le (by linarith only [hxarg])
  have hk : 1 / 2 ≤ k := Real.le_sqrt_of_sq_le (by linarith only [haarg])
  have hhpos : 0 < h := by linarith
  have hkpos : 0 < k := by linarith
  have hsum : 1 ≤ k + h := by linarith
  have hx2 : h ^ 2 = 1 - δ ^ 2 * ‖x‖ ^ 2 := Real.sq_sqrt (by linarith only [hxarg])
  have ha2 : k ^ 2 = 1 - δ ^ 2 * ‖a‖ ^ 2 := Real.sq_sqrt (by linarith only [haarg])
  have hA : |⟪a, u⟫| ≤ 1 / 2 := by
    calc
      _ ≤ ‖a‖ * ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) a u
      _ ≤ (1 / 2) * 1 := mul_le_mul ha hu (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hnorm_sq : ‖x‖ ^ 2 = ‖a‖ ^ 2 + 2 * r * ⟪a, u⟫ + r ^ 2 * ‖u‖ ^ 2 := by
    dsimp only [x]
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hdiff : (k - h) * (k + h) = δ ^ 2 * r * (2 * ⟪a, u⟫ + r * ‖u‖ ^ 2) := by
    calc
      _ = k ^ 2 - h ^ 2 := by ring
      _ = _ := by rw [ha2, hx2, hnorm_sq]; ring
  have hU : |2 * ⟪a, u⟫ + r * ‖u‖ ^ 2| ≤ 3 / 2 := by
    have hB : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    calc
      _ ≤ |2 * ⟪a, u⟫| + |r * ‖u‖ ^ 2| := abs_add_le _ _
      _ = 2 * |⟪a, u⟫| + r * ‖u‖ ^ 2 := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hr.le, abs_of_nonneg (sq_nonneg ‖u‖)]
      _ ≤ _ := by nlinarith only [hA, hrhalf, mul_le_mul_of_nonneg_left hB hr.le]
  have hdiff_abs : |k - h| ≤ r := by
    have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
    calc
      _ = |k - h| * 1 := by ring
      _ ≤ |k - h| * (k + h) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |(k - h) * (k + h)| := by rw [abs_mul, abs_of_pos (by linarith : 0 < k + h)]
      _ = (δ ^ 2 * r) * |2 * ⟪a, u⟫ + r * ‖u‖ ^ 2| := by
        rw [hdiff, abs_mul, abs_of_nonneg (by positivity : 0 ≤ δ ^ 2 * r)]
      _ ≤ ((1 / 4) * r) * (3 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hδsq hr.le) hU (abs_nonneg _) (by positivity)
      _ ≤ r := by linarith
  have hslope := (shifted_spherical_line_derivatives hδ.ne' hr.ne' a v w
    (t := t) (by linarith only [hxarg])).1.deriv
  change deriv (fun s : ℝ => shiftedSphericalGraphPhase δ a r (v + s • w)) t =
    (2 * ⟪x, w⟫ / h - ⟪sphericalGraphSlope δ a, w⟫) / r at hslope
  have he : (2 * ⟪x, w⟫ / h - ⟪sphericalGraphSlope δ a, w⟫) / r =
      2 * ⟪u, w⟫ / h + 2 * ⟪a, w⟫ * (k - h) / (r * h * k) := by
    have hℓ : ⟪sphericalGraphSlope δ a, w⟫ = 2 / k * ⟪a, w⟫ := by
      unfold sphericalGraphSlope
      rw [real_inner_smul_left]
    rw [hℓ, show ⟪x, w⟫ = ⟪a, w⟫ + r * ⟪u, w⟫ by
      dsimp only [x]
      rw [inner_add_left, real_inner_smul_left]]
    field_simp [hhpos.ne', hkpos.ne', hr.ne']
    ring
  have h1 : |2 * ⟪u, w⟫ / h| ≤ 4 * ‖w‖ := by
    have H : |⟪u, w⟫| ≤ ‖w‖ := by
      calc
        _ ≤ ‖u‖ * ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) u w
        _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hu (norm_nonneg w)
    rw [abs_div, abs_of_pos hhpos, div_le_iff₀ hhpos, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith only [H, mul_le_mul_of_nonneg_left hh (norm_nonneg w)]
  have h2 : |2 * ⟪a, w⟫ * (k - h) / (r * h * k)| ≤ 4 * ‖w‖ := by
    have H : |⟪a, w⟫| ≤ (1 / 2) * ‖w‖ := by
      calc
        _ ≤ ‖a‖ * ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) a w
        _ ≤ _ := mul_le_mul_of_nonneg_right ha (norm_nonneg w)
    have hdenom : 0 < r * h * k := by positivity
    have hquarter : 1 / 4 ≤ h * k := by
      calc
        _ = (1 / 2 : ℝ) * (1 / 2) := by norm_num
        _ ≤ _ := mul_le_mul hh hk (by norm_num) hhpos.le
    rw [abs_div, abs_of_pos hdenom, div_le_iff₀ hdenom, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (2 * ((1 / 2) * ‖w‖)) * r :=
        mul_le_mul (mul_le_mul_of_nonneg_left H (by norm_num)) hdiff_abs (abs_nonneg _) (by positivity)
      _ ≤ _ := by
        have Hq := mul_le_mul_of_nonneg_left hquarter (mul_nonneg hr.le (norm_nonneg w))
        nlinarith only [Hq]
  rw [hslope, he]
  exact (abs_add_le _ _).trans (by linarith [norm_nonneg w])

end RestrictionWork
