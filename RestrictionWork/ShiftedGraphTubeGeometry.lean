import RestrictionWork.PatchGraphCoordinates
import RestrictionWork.ShiftedSphericalLineSlope

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

theorem shifted_graph_phase_difference {d : ℕ} {δ r : ℝ} {a u v : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |shiftedSphericalGraphPhase δ a r u - shiftedSphericalGraphPhase δ a r v| ≤
      10 * ‖u - v‖ := by
  let w := u - v
  let g : ℝ → ℝ := fun s => shiftedSphericalGraphPhase δ a r (v + s • w)
  have hseg (s : ℝ) (hs : s ∈ Icc 0 1) : ‖v + s • w‖ ≤ 1 := by
    have he : v + s • w = (1 - s) • v + s • u := by
      dsimp only [w]
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [he]
    calc
      _ ≤ ‖(1 - s) • v‖ + ‖s • u‖ := norm_add_le _ _
      _ = (1 - s) * ‖v‖ + s * ‖u‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
      _ ≤ (1 - s) * 1 + s * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hs.2))
          (mul_le_mul_of_nonneg_left hu hs.1)
      _ = 1 := by ring
  have hC : Continuous g := by
    unfold g shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hD : DifferentiableOn ℝ g (Ioo 0 1) := by
    intro s hs
    have hrad := spherical_radicand_lower_bound hδ.le hδhalf
      (rebase_point_norm_le_one ha hr.le hrhalf (hseg s ⟨hs.1.le, hs.2.le⟩))
    exact ((shifted_spherical_line_contDiffAt (δ := δ) (r := r) (a := a)
      (v := v) (w := w) (t := s) (by linarith only [hrad])).differentiableAt
      (by norm_num)).differentiableWithinAt
  obtain ⟨s, hs, hderiv⟩ := exists_deriv_eq_slope g zero_lt_one hC.continuousOn hD
  have H : |deriv g s| ≤ 10 * ‖w‖ :=
    shifted_spherical_line_slope_bound hδ hδhalf ha hr hrhalf (hseg s ⟨hs.1.le, hs.2.le⟩)
  rw [hderiv] at H
  simpa [g, w] using H

theorem shifted_graph_point_dist_le {d : ℕ} {δ r : ℝ} {a u v : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    dist (patchGraphPoint (shiftedSphericalGraphPhase δ a r) u)
      (patchGraphPoint (shiftedSphericalGraphPhase δ a r) v) ≤ 20 * dist u v := by
  let φ := shiftedSphericalGraphPhase δ a r
  have H := shifted_graph_phase_difference hδ hδhalf ha hr hrhalf hu hv
  change |φ u - φ v| ≤ 10 * ‖u - v‖ at H
  rw [dist_eq_norm, dist_eq_norm, patchGraphPoint, patchGraphPoint, euclidean_slice_sub]
  calc
    _ ≤ 2 * ‖(u - v, φ u - φ v)‖ := euclidean_slice_norm_le_product _ _
    _ ≤ 2 * (10 * ‖u - v‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
      exact ⟨by linarith only [norm_nonneg (u - v)], H⟩
    _ = _ := by ring

theorem shifted_graph_tube_subset_ball {d : ℕ} {δ r h : ℝ} {a : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hh : h ≤ 1) :
    patchGraphTube (shiftedSphericalGraphPhase δ a r) h ⊆ ball (0 : Ambient (d + 1)) 21 := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := patch_graph_tube_mem_iff.mp hx
  have hv' : ‖v‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hv
  have hzero : patchGraphPoint (shiftedSphericalGraphPhase δ a r) (0 : Ambient d) = 0 := by
    rw [patchGraphPoint, euclidean_slice_apply]
    simp [shiftedSphericalGraphPhase, graphRebasePhase]
  have H := shifted_graph_point_dist_le hδ hδhalf ha hr hrhalf hv'.le
    (v := (0 : Ambient d)) (by simp)
  rw [hzero, dist_zero_right, dist_zero_right] at H
  have Hx : dist x (patchGraphPoint (shiftedSphericalGraphPhase δ a r) v) < h :=
    mem_ball.mp hxv
  rw [mem_ball]
  calc
    dist x 0 ≤ dist x (patchGraphPoint (shiftedSphericalGraphPhase δ a r) v) +
      dist (patchGraphPoint (shiftedSphericalGraphPhase δ a r) v) 0 :=
      dist_triangle _ _ _
    _ < 21 := by rw [dist_zero_right]; linarith

def patchTubeMassConstant (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 40 : ℝ) ^ d) * volume (ball (0 : Ambient d) 1)

theorem patch_tube_mass_constant_finite_positive (d : ℕ) :
    patchTubeMassConstant d ≠ 0 ∧ patchTubeMassConstant d ≠ ⊤ := by
  unfold patchTubeMassConstant
  exact ⟨mul_ne_zero (by positivity) (measure_ball_pos volume _ zero_lt_one).ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne⟩

/-- The hard parameter cutoff retains a uniform lower mass in the tube,
including points near the edge of the parameter ball. -/
theorem shifted_graph_tube_mass_lower {d : ℕ} {δ r h : ℝ} {a : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hh : 0 < h) (hh1 : h ≤ 1)
    {x : Ambient (d + 1)} (hx : x ∈ patchGraphTube (shiftedSphericalGraphPhase δ a r) h) :
    patchTubeMassConstant d * ENNReal.ofReal (h ^ d) ≤
      patchGraphMeasure (shiftedSphericalGraphPhase δ a r) (ball x (2 * h)) := by
  let φ := shiftedSphericalGraphPhase δ a r
  obtain ⟨v, hv, hxv⟩ := patch_graph_tube_mem_iff.mp hx
  have hv' : ‖v‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hv
  let s : ℝ := h / 40
  let c : Ambient d := (1 - s) • v
  have hs : 0 < s := div_pos hh (by norm_num)
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hc : ‖c‖ ≤ 1 - s := by
    dsimp only [c]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hs1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv'.le (by linarith : 0 ≤ 1 - s)
  have hcv : dist c v ≤ s := by
    rw [dist_eq_norm]
    have he : c - v = (-s) • v := by
      dsimp only [c]
      rw [sub_smul, one_smul, neg_smul]; abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv'.le hs.le
  have hinside : ball c s ⊆ ball (0 : Ambient d) 1 := by
    intro u hu
    rw [mem_ball, dist_zero_right]
    have H := dist_triangle u c 0
    rw [dist_zero_right, dist_zero_right] at H
    linarith [mem_ball.mp hu]
  have hpre : ball c s ⊆ patchGraphPoint φ ⁻¹' ball x (2 * h) := by
    intro u hu
    have hu' : ‖u‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hinside hu
    have huv : dist u v < 2 * s := (dist_triangle u c v).trans_lt (by linarith [mem_ball.mp hu])
    have H := shifted_graph_point_dist_le hδ hδhalf ha hr hrhalf hu'.le hv'.le
    have H' := H.trans_lt (mul_lt_mul_of_pos_left huv (by norm_num : 0 < (20 : ℝ)))
    change dist (patchGraphPoint φ u) x < 2 * h
    have hdist : dist x (patchGraphPoint φ v) < h := mem_ball.mp hxv
    have hdist' : dist (patchGraphPoint φ v) x < h := by rwa [dist_comm]
    exact (dist_triangle _ (patchGraphPoint φ v) _).trans_lt (by dsimp [s] at H'; linarith)
  have hm : Measurable φ := by
    unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  change _ ≤ (patchMeasure d).map (patchGraphPoint φ) (ball x (2 * h))
  rw [Measure.map_apply (measurable_patch_graph_point hm) measurableSet_ball]
  calc
    _ = volume (ball c s) := by
      rw [Measure.addHaar_ball_of_pos volume c hs, patchTubeMassConstant]
      simp only [Ambient, finrank_euclideanSpace_fin]
      have he : s ^ d = (1 / 40 : ℝ) ^ d * h ^ d := by
        rw [← mul_pow]; congr 1; dsimp [s]; ring
      rw [he, ENNReal.ofReal_mul (by positivity)]
      ring
    _ = patchMeasure d (ball c s) := by
      unfold patchMeasure
      rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hinside]
    _ ≤ _ := measure_mono hpre

end RestrictionWork
