import RestrictionWork.ShiftedSphericalChord
import RestrictionWork.SphereStereo

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- The phase defect in the squared bilinear extension after eliminating
the horizontal frequency sum. -/
def shiftedCollisionPhase {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ)
    (u y w : Ambient d) : ℝ :=
  shiftedSphericalGraphPhase δ a r u + shiftedSphericalGraphPhase δ a r y -
    shiftedSphericalGraphPhase δ a r w - shiftedSphericalGraphPhase δ a r (u + y - w)

def shiftedCollisionHeightSum {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ)
    (u y w : Ambient d) : ℝ :=
  shiftedCapHeight δ a r u + shiftedCapHeight δ a r y - shiftedCapHeight δ a r w +
    shiftedCapHeight δ a r (u + y - w)

theorem shifted_collision_height_sum_bounds {d : ℕ} {δ r : ℝ} {a u y w : Ambient d}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖u + y - w‖ ≤ 1) :
    1 ≤ shiftedCollisionHeightSum δ a r u y w ∧
      shiftedCollisionHeightSum δ a r u y w ≤ 3 := by
  obtain ⟨hu₁, hu₂, _⟩ := shifted_cap_height_bounds hδ hδhalf ha hr hrhalf hu
  obtain ⟨hy₁, hy₂, _⟩ := shifted_cap_height_bounds hδ hδhalf ha hr hrhalf hy
  obtain ⟨hw₁, hw₂, _⟩ := shifted_cap_height_bounds hδ hδhalf ha hr hrhalf hw
  obtain ⟨hz₁, hz₂, _⟩ := shifted_cap_height_bounds hδ hδhalf ha hr hrhalf hz
  unfold shiftedCollisionHeightSum
  constructor <;> linarith

private theorem unit_three_point_sum_defect {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p q t : E}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (ht : ‖t‖ = 1) :
    ‖p + q - t‖ ^ 2 - 1 = 2 * (‖t - p‖ ^ 2 - ⟪q - p, t - p⟫) := by
  simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left, inner_sub_left,
    inner_sub_right, real_inner_self_eq_norm_sq, hp, hq, ht,
    real_inner_comm q p, real_inner_comm t p]
  ring

private theorem euclidean_slice_add {d : ℕ} (i : Fin (d + 1))
    (v w : Ambient d) (s t : ℝ) :
    euclideanSliceEquiv i (v, s) + euclideanSliceEquiv i (w, t) =
      euclideanSliceEquiv i (v + w, s + t) := by
  apply PiLp.ext
  intro j
  induction j using i.succAboveCases with
  | x => simp [euclidean_slice_apply]
  | p j => simp [euclidean_slice_apply]

/-- On the actual rebased spherical graph the four-frequency phase defect
factors exactly as a positive weight times a Euclidean hyperplane relation. -/
theorem shifted_collision_radon_factor {d : ℕ} {δ r : ℝ} {a u y w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖u + y - w‖ ≤ 1)
    (hyu : y ≠ u) (hwu : w ≠ u) :
    let P := shiftedCapPoint δ a r
    let k := δ * r
    let Y := sphereStereo k (P u) (P y)
    let W := sphereStereo k (P u) (P w)
    shiftedCollisionPhase δ a r u y w * shiftedCollisionHeightSum δ a r u y w =
      4 * (‖P y - P u‖ / k) ^ 2 * (‖P w - P u‖ / k) ^ 2 * ⟪Y, W - Y⟫ := by
  intro P k Y W
  let z := u + y - w
  let b := shiftedCapHeight δ a r
  let c := b u + b y - b w
  have hk : 0 < k := mul_pos hδ hr
  have hP (v : Ambient d) (hv : ‖v‖ ≤ 1) : ‖P v‖ = 1 :=
    shifted_cap_point_norm_one hδ.le hδhalf ha hr.le hrhalf hv
  have hPne (v : Ambient d) (hv : ‖v‖ ≤ 1) (hne : v ≠ u) : P v ≠ P u := by
    intro he
    have hh := (shifted_cap_chord_bounds hδ.le hδhalf ha hr.le hrhalf hv hu).1
    change k * ‖v - u‖ ≤ ‖P v - P u‖ at hh
    rw [he, sub_self, norm_zero] at hh
    exact (not_le_of_gt (mul_pos hk (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))) hh
  have hAy : ‖P y - P u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hPne y hy hyu))
  have hAw : ‖P w - P u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hPne w hw hwu))
  have hhorizontal : δ • (a + r • u) + δ • (a + r • y) - δ • (a + r • w) =
      δ • (a + r • z) := by
    simp only [z, smul_add, smul_sub]
    abel
  have hsum :
      P u + P y - P w = euclideanSliceEquiv (Fin.last d) (δ • (a + r • z), c) := by
    dsimp only [P]
    rw [shifted_cap_point_slice, shifted_cap_point_slice, shifted_cap_point_slice,
      euclidean_slice_add, euclidean_slice_sub, hhorizontal]
  have hnorm : ‖P u + P y - P w‖ ^ 2 - 1 = (c - b z) * (c + b z) := by
    have hh : ‖δ • (a + r • z)‖ ^ 2 + b z ^ 2 = 1 := by
      have he := congrArg (fun t : ℝ => t ^ 2) (hP z hz)
      dsimp only [P] at he
      rw [shifted_cap_point_slice, euclidean_slice_norm_sq] at he
      simpa only [b, one_pow] using he
    rw [hsum, euclidean_slice_norm_sq]
    linarith only [hh, show (c - b z) * (c + b z) = c ^ 2 - b z ^ 2 by ring]
  have hphase : shiftedCollisionPhase δ a r u y w = 2 * (b z - c) / k ^ 2 := by
    unfold shiftedCollisionPhase shiftedSphericalGraphPhase graphRebasePhase
      sphericalGraphPhase sphericalPhase
    change ((2 * (1 - b u) / δ ^ 2 - 2 * (1 - capHeight δ a) / δ ^ 2 -
      r * ⟪sphericalGraphSlope δ a, u⟫) / r ^ 2 +
      (2 * (1 - b y) / δ ^ 2 - 2 * (1 - capHeight δ a) / δ ^ 2 -
      r * ⟪sphericalGraphSlope δ a, y⟫) / r ^ 2 -
      (2 * (1 - b w) / δ ^ 2 - 2 * (1 - capHeight δ a) / δ ^ 2 -
      r * ⟪sphericalGraphSlope δ a, w⟫) / r ^ 2 -
      (2 * (1 - b z) / δ ^ 2 - 2 * (1 - capHeight δ a) / δ ^ 2 -
      r * ⟪sphericalGraphSlope δ a, z⟫) / r ^ 2) = _
    have hlin : ⟪sphericalGraphSlope δ a, z⟫ = ⟪sphericalGraphSlope δ a, u⟫ +
        ⟪sphericalGraphSlope δ a, y⟫ - ⟪sphericalGraphSlope δ a, w⟫ := by
      simp only [z, inner_add_right, inner_sub_right]
    rw [hlin]
    dsimp only [c, k]
    field_simp [hδ.ne', hr.ne']
    ring
  have hpolar := sphere_stereo_incidence k (hP u hu) (hP y hy) (hP w hw)
    (hPne y hy hyu) (hPne w hw hwu)
  change ⟪Y, W - Y⟫ = k ^ 2 *
    (⟪P y - P u, P w - P u⟫ - ‖P w - P u‖ ^ 2) /
      (‖P y - P u‖ ^ 2 * ‖P w - P u‖ ^ 2) at hpolar
  change shiftedCollisionPhase δ a r u y w * (c + b z) = _
  calc
    _ = (-2) * (‖P u + P y - P w‖ ^ 2 - 1) / k ^ 2 := by rw [hphase, hnorm]; ring
    _ = _ := by
      rw [unit_three_point_sum_defect (hP u hu) (hP y hy) (hP w hw), hpolar]
      field_simp [hk.ne', hAy, hAw]
      ring

/-- On separated supports a phase strip is contained in a hyperplane strip
with constants independent of the parent cap and the subcap scales. -/
theorem shifted_collision_radon_strip {d : ℕ} {δ r σ ε : ℝ} {a u y w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖u + y - w‖ ≤ 1)
    (hσ : 0 < σ) (hsepY : σ ≤ ‖y - u‖) (hsepW : σ ≤ ‖w - u‖)
    (hε : |shiftedCollisionPhase δ a r u y w| ≤ ε) :
    let P := shiftedCapPoint δ a r
    let Y := sphereStereo (δ * r) (P u) (P y)
    let W := sphereStereo (δ * r) (P u) (P w)
    |⟪Y, W - Y⟫| ≤ 3 * ε / (4 * σ ^ 4) := by
  intro P Y W
  let k := δ * r
  let A := ‖P y - P u‖ / k
  let B := ‖P w - P u‖ / k
  let D := shiftedCollisionPhase δ a r u y w
  let H := shiftedCollisionHeightSum δ a r u y w
  have hk : 0 < k := mul_pos hδ hr
  have hne (v : Ambient d) (hv : σ ≤ ‖v - u‖) : v ≠ u := by
    intro he
    rw [he, sub_self, norm_zero] at hv
    exact hσ.not_ge hv
  have hA : σ ≤ A := (le_div_iff₀ hk).mpr (by
    rw [mul_comm σ k]
    exact (mul_le_mul_of_nonneg_left hsepY hk.le).trans
      (shifted_cap_chord_bounds hδ.le hδhalf ha hr.le hrhalf hy hu).1)
  have hB : σ ≤ B := (le_div_iff₀ hk).mpr (by
    rw [mul_comm σ k]
    exact (mul_le_mul_of_nonneg_left hsepW hk.le).trans
      (shifted_cap_chord_bounds hδ.le hδhalf ha hr.le hrhalf hw hu).1)
  obtain ⟨hH1, hH3⟩ := shifted_collision_height_sum_bounds hδ.le hδhalf ha hr.le hrhalf hu hy hw hz
  change 1 ≤ H at hH1
  change H ≤ 3 at hH3
  have he : D * H = 4 * A ^ 2 * B ^ 2 * ⟪Y, W - Y⟫ :=
    shifted_collision_radon_factor hδ hδhalf ha hr hrhalf hu hy hw hz (hne y hsepY) (hne w hsepW)
  have hcoef : 4 * σ ^ 4 ≤ 4 * A ^ 2 * B ^ 2 := by
    rw [show 4 * σ ^ 4 = 4 * σ ^ 2 * σ ^ 2 by ring, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (pow_le_pow_left₀ hσ.le hA _) (pow_le_pow_left₀ hσ.le hB _)
        (by positivity) (by positivity)) (by norm_num)
  have habs : |D| * H = 4 * A ^ 2 * B ^ 2 * |⟪Y, W - Y⟫| := by
    simpa only [abs_mul, abs_of_nonneg (zero_le_one.trans hH1),
      abs_of_nonneg (by positivity : 0 ≤ 4 * A ^ 2 * B ^ 2)] using congrArg abs he
  apply (le_div_iff₀ (by positivity : 0 < 4 * σ ^ 4)).mpr
  calc
    _ = (4 * σ ^ 4) * |⟪Y, W - Y⟫| := mul_comm _ _
    _ ≤ (4 * A ^ 2 * B ^ 2) * |⟪Y, W - Y⟫| :=
      mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    _ = |D| * H := habs.symm
    _ ≤ ε * 3 := mul_le_mul hε hH3 (zero_le_one.trans hH1) ((abs_nonneg D).trans hε)
    _ = _ := mul_comm _ _

end RestrictionWork
