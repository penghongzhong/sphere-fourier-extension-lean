import RestrictionWork.CapChartDefinitions
import RestrictionWork.PatchGraphMeasure
import RestrictionWork.ShiftedSphericalLineSlope

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

def shiftedCapHeight {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ) (v : Ambient d) : ℝ :=
  capHeight δ (a + r • v)

def shiftedCapPoint {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ) (v : Ambient d) :
    Ambient (d + 1) :=
  capPoint δ (a + r • v)

theorem shifted_cap_point_slice {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ)
    (v : Ambient d) :
    shiftedCapPoint δ a r v =
      euclideanSliceEquiv (Fin.last d) (δ • (a + r • v), shiftedCapHeight δ a r v) := by
  apply PiLp.ext
  intro j
  induction j using (Fin.last d).succAboveCases with
  | x =>
    simp [shiftedCapPoint, shiftedCapHeight, capPoint, euclidean_slice_apply]
  | p j =>
    simp [shiftedCapPoint, shiftedCapHeight, capPoint, euclidean_slice_apply, Fin.succAbove_last, mul_add]

theorem shifted_cap_height_bounds {d : ℕ} {δ r : ℝ} {a v : Ambient d}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hv : ‖v‖ ≤ 1) :
    (3 / 4 : ℝ) ≤ shiftedCapHeight δ a r v ∧
      shiftedCapHeight δ a r v ≤ 1 ∧
      shiftedCapHeight δ a r v ^ 2 = 1 - δ ^ 2 * ‖a + r • v‖ ^ 2 := by
  have hrad := spherical_radicand_lower_bound hδ hδhalf (rebase_point_norm_le_one ha hr hrhalf hv)
  unfold shiftedCapHeight capHeight
  refine ⟨Real.le_sqrt_of_sq_le (by linarith only [hrad]), ?_,
    Real.sq_sqrt (by linarith only [hrad])⟩
  exact (Real.sqrt_le_sqrt (sub_le_self _ (by positivity))).trans_eq Real.sqrt_one

theorem shifted_cap_point_norm_one {d : ℕ} {δ r : ℝ} {a v : Ambient d}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hv : ‖v‖ ≤ 1) :
    ‖shiftedCapPoint δ a r v‖ = 1 := by
  apply le_antisymm <;> apply (sq_le_sq₀ (by positivity) (by positivity)).mp <;>
    rw [shifted_cap_point_slice, euclidean_slice_norm_sq, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hδ, mul_pow,
      (shifted_cap_height_bounds hδ hδhalf ha hr hrhalf hv).2.2] <;> linarith

/-- Chords of the actual sphere chart are comparable to parameter
differences, with the common physical scale retained. -/
theorem shifted_cap_chord_bounds {d : ℕ} {δ r : ℝ} {a v w : Ambient d}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (δ * r) * ‖v - w‖ ≤ ‖shiftedCapPoint δ a r v - shiftedCapPoint δ a r w‖ ∧
      ‖shiftedCapPoint δ a r v - shiftedCapPoint δ a r w‖ ≤ 2 * (δ * r) * ‖v - w‖ := by
  let X := a + r • v
  let Y := a + r • w
  let h := shiftedCapHeight δ a r v
  let k := shiftedCapHeight δ a r w
  have hX := rebase_point_norm_le_one ha hr hrhalf hv
  have hY := rebase_point_norm_le_one ha hr hrhalf hw
  obtain ⟨hh, _, hh2⟩ := shifted_cap_height_bounds hδ hδhalf ha hr hrhalf hv
  obtain ⟨hk, _, hk2⟩ := shifted_cap_height_bounds hδ hδhalf ha hr hrhalf hw
  change 3 / 4 ≤ h at hh
  change 3 / 4 ≤ k at hk
  change h ^ 2 = 1 - δ ^ 2 * ‖X‖ ^ 2 at hh2
  change k ^ 2 = 1 - δ ^ 2 * ‖Y‖ ^ 2 at hk2
  have hsum : 0 < h + k := by linarith
  have hxy : X - Y = r • (v - w) := by
    dsimp only [X, Y]
    rw [add_sub_add_left_eq_sub, smul_sub]
  have hxyNorm : ‖X - Y‖ = r * ‖v - w‖ := by
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have he : (h - k) * (h + k) = δ ^ 2 * ((‖Y‖ - ‖X‖) * (‖Y‖ + ‖X‖)) := by
    calc
      _ = h ^ 2 - k ^ 2 := by ring
      _ = _ := by rw [hh2, hk2]; ring
  have hδsum : δ * (‖Y‖ + ‖X‖) ≤ h + k := by
    have H := mul_le_mul hδhalf (show ‖Y‖ + ‖X‖ ≤ 2 by linarith) (by positivity)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hdiff : |h - k| ≤ δ * ‖X - Y‖ := by
    apply (mul_le_mul_iff_left₀ hsum).mp
    calc
      _ = |(h - k) * (h + k)| := by rw [abs_mul, abs_of_pos hsum]
      _ = δ ^ 2 * (|‖X‖ - ‖Y‖| * (‖Y‖ + ‖X‖)) := by
        rw [he, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg δ),
          abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), abs_sub_comm]
      _ ≤ δ ^ 2 * (‖X - Y‖ * (‖Y‖ + ‖X‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity))
          (sq_nonneg _)
      _ = (δ * ‖X - Y‖) * (δ * (‖Y‖ + ‖X‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hδsum (by positivity)
  have hsq : ‖shiftedCapPoint δ a r v - shiftedCapPoint δ a r w‖ ^ 2 =
      ((δ * r) * ‖v - w‖) ^ 2 + (h - k) ^ 2 := by
    rw [shifted_cap_point_slice, shifted_cap_point_slice, euclidean_slice_sub,
      euclidean_slice_norm_sq, ← smul_sub]
    change ‖δ • (X - Y)‖ ^ 2 + (h - k) ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ, hxyNorm, mul_assoc]
  have hdist : |h - k| ≤ (δ * r) * ‖v - w‖ := by
    simpa only [hxyNorm, mul_assoc] using hdiff
  have hdist2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hdist
  rw [sq_abs] at hdist2
  constructor
  · apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [hsq]
    linarith only [sq_nonneg (h - k)]
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hsq, show 2 * (δ * r) * ‖v - w‖ = 2 * ((δ * r) * ‖v - w‖) by ring]
    nlinarith only [hdist2, sq_nonneg ((δ * r) * ‖v - w‖)]

end RestrictionWork
