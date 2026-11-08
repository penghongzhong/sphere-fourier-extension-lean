import RestrictionWork.ShiftedSphericalChord
import RestrictionWork.SphereStereo

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- The normalized stereographic chart and its inverse are Lipschitz on a
subpatch separated from the pole. Neither bound costs a cap scale. -/
theorem shifted_spherical_stereo_distance_bounds {d : ℕ} {δ r σ : ℝ}
    {a u y w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hσ : 0 < σ) (hsepY : σ ≤ ‖y - u‖) (hsepW : σ ≤ ‖w - u‖) :
    let P := shiftedCapPoint δ a r
    let Y := sphereStereo (δ * r) (P u) (P y)
    let W := sphereStereo (δ * r) (P u) (P w)
    ‖y - w‖ / 16 ≤ ‖Y - W‖ ∧ ‖Y - W‖ ≤ 2 * ‖y - w‖ / σ ^ 2 := by
  intro P Y W
  let k := δ * r
  have hk : 0 < k := mul_pos hδ hr
  have hdist (v : Ambient d) (hv : ‖v‖ ≤ 1) (hsep : σ ≤ ‖v - u‖) :
      k * σ ≤ ‖P v - P u‖ ∧ ‖P v - P u‖ ≤ 4 * k := by
    obtain ⟨hl, hh⟩ := shifted_cap_chord_bounds hδ.le hδhalf ha hr.le hrhalf hv hu
    refine ⟨(mul_le_mul_of_nonneg_left hsep hk.le).trans hl, hh.trans ?_⟩
    have H : ‖v - u‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    nlinarith only [mul_le_mul_of_nonneg_left H (show 0 ≤ 2 * k by positivity)]
  obtain ⟨hy₁, hy₂⟩ := hdist y hy hsepY
  obtain ⟨hw₁, hw₂⟩ := hdist w hw hsepW
  have hypos : 0 < ‖P y - P u‖ := (mul_pos hk hσ).trans_le hy₁
  have hwpos : 0 < ‖P w - P u‖ := (mul_pos hk hσ).trans_le hw₁
  have hneY : P y ≠ P u := sub_ne_zero.mp (norm_pos_iff.mp hypos)
  have hneW : P w ≠ P u := sub_ne_zero.mp (norm_pos_iff.mp hwpos)
  have hden : 0 < ‖P y - P u‖ * ‖P w - P u‖ := mul_pos hypos hwpos
  obtain ⟨hlo, hhi⟩ := shifted_cap_chord_bounds hδ.le hδhalf ha hr.le hrhalf hy hw
  change k * ‖y - w‖ ≤ ‖P y - P w‖ at hlo
  change ‖P y - P w‖ ≤ 2 * k * ‖y - w‖ at hhi
  rw [show ‖Y - W‖ = k * ‖P y - P w‖ / (‖P y - P u‖ * ‖P w - P u‖) from
    sphere_stereo_distance hk.le hneY hneW]
  constructor
  · apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (‖y - w‖ / 16) * ((4 * k) * (4 * k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hy₂ hw₂ hwpos.le (by positivity)) (by positivity)
      _ = k * (k * ‖y - w‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hk.le
  · apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ k * (2 * k * ‖y - w‖) := mul_le_mul_of_nonneg_left hhi hk.le
      _ = (2 * ‖y - w‖ / σ ^ 2) * ((k * σ) * (k * σ)) := by
        field_simp [hσ.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul hy₁ hw₁ (by positivity) hypos.le) (by positivity)

/-- The image stays in a fixed annulus in the pole's tangent space, so polar
coordinates there incur only constants depending on the separation. -/
theorem shifted_spherical_stereo_tangent_annulus {d : ℕ} {δ r σ : ℝ}
    {a u v : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hσ : 0 < σ) (hsep : σ ≤ ‖v - u‖) :
    let P := shiftedCapPoint δ a r
    let V := sphereStereo (δ * r) (P u) (P v)
    ⟪P u, V⟫ = 0 ∧ (1 / 8 : ℝ) ≤ ‖V‖ ∧ ‖V‖ ≤ 1 / σ := by
  intro P V
  let k := δ * r
  let A := ‖P v - P u‖
  have hk : 0 < k := mul_pos hδ hr
  have hk₁ : k ≤ 1 / 4 := by
    dsimp only [k]
    have H := mul_le_mul hδhalf hrhalf hr.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  obtain ⟨hl, hh⟩ := shifted_cap_chord_bounds hδ.le hδhalf ha hr.le hrhalf hv hu
  change k * ‖v - u‖ ≤ A at hl
  change A ≤ 2 * k * ‖v - u‖ at hh
  have hAlo : k * σ ≤ A := (mul_le_mul_of_nonneg_left hsep hk.le).trans hl
  have hAhi : A ≤ 4 * k := by
    have H : ‖v - u‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ 2 * k)])
  have hApos : 0 < A := (mul_pos hk hσ).trans_le hAlo
  have hne : P v ≠ P u := sub_ne_zero.mp (norm_pos_iff.mp hApos)
  have hPu := shifted_cap_point_norm_one hδ.le hδhalf ha hr.le hrhalf hu
  have hPv := shifted_cap_point_norm_one hδ.le hδhalf ha hr.le hrhalf hv
  have hnorm : ‖V‖ ^ 2 = k ^ 2 / A ^ 2 - k ^ 2 / 4 := sphere_stereo_norm_sq k hPu hPv hne
  have hleft : (1 / 16 : ℝ) ≤ k ^ 2 / A ^ 2 := by
    apply (le_div_iff₀ (pow_pos hApos 2)).mpr
    nlinarith only [(sq_le_sq₀ hApos.le (by positivity)).mpr hAhi]
  have hright : k ^ 2 / A ^ 2 ≤ (1 / σ) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hApos 2) (pow_pos hσ 2)).mpr
    simpa only [one_pow, one_mul, mul_pow] using
      (sq_le_sq₀ (by positivity) hApos.le).mpr hAlo
  refine ⟨sphere_stereo_tangent k hPu hPv hne, ?_, ?_⟩
  · apply (sq_le_sq₀ (by norm_num) (norm_nonneg V)).mp
    rw [hnorm]
    nlinarith only [hleft, (sq_le_sq₀ hk.le (by norm_num)).mpr hk₁]
  · apply (sq_le_sq₀ (norm_nonneg V) (by positivity)).mp
    rw [hnorm]
    linarith only [hright, sq_nonneg k]

end RestrictionWork
