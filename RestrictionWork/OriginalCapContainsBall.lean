import RestrictionWork.OriginalCapReverse
import RestrictionWork.EuclideanBallSlices

set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace RestrictionWork

/-- The quarter-sized cap chart contains a metric ball on the sphere. -/
theorem original_small_cap_contains_ball {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) :
    ∃ pole : UnitSphere (d + 1), Metric.ball pole (δ / 4) ⊆ originalSmallCap δ := by
  let E := euclideanSliceEquiv (Fin.last d)
  have hcenter : E (0, 1) ∈ UnitSphere (d + 1) := by
    rw [Metric.mem_sphere, dist_zero_right]
    have H := euclidean_slice_norm_sq (Fin.last d) (0 : Ambient d) 1
    have He : ‖E (0, 1)‖ ^ 2 = 1 := by simpa using H
    nlinarith [norm_nonneg (E (0, 1))]
  let pole : UnitSphere (d + 1) := ⟨E (0, 1), hcenter⟩
  refine ⟨pole, ?_⟩
  intro ω hω
  let w := (E.symm (ω : Ambient (d + 1))).1
  let s := (E.symm (ω : Ambient (d + 1))).2
  have hspl : E (w, s) = (ω : Ambient (d + 1)) := E.apply_symm_apply ω
  have hnorm : ‖E (w, s)‖ = 1 := by
    rw [hspl]
    exact (dist_zero_right _).symm.trans (Metric.mem_sphere.mp ω.property)
  have hnormsq : ‖w‖ ^ 2 + s ^ 2 = 1 := by
    rw [← euclidean_slice_norm_sq (Fin.last d), show euclideanSliceEquiv (Fin.last d) (w, s) =
      E (w, s) from rfl, hnorm, one_pow]
  have hdiff : E (w, s) - E (0, 1) = E (w, s - 1) := by
    apply PiLp.ext
    rw [Fin.forall_iff_castSucc]
    simp only [E, euclidean_slice_apply, Fin.insertNth_last', PiLp.sub_apply, PiLp.toLp_apply,
      Fin.snoc_last, Fin.snoc_castSucc, PiLp.zero_apply, sub_zero]
    exact ⟨trivial, fun _ => trivial⟩
  have hlt : ‖E (w, s - 1)‖ < δ / 4 := by
    rw [← hdiff, hspl]
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hω
  have hDsq : ‖E (w, s - 1)‖ ^ 2 = ‖w‖ ^ 2 + (s - 1) ^ 2 :=
    euclidean_slice_norm_sq (Fin.last d) w (s - 1)
  have hwle : ‖w‖ ≤ ‖E (w, s - 1)‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [hDsq]; linarith [sq_nonneg (s - 1)])
  have hsle : |s - 1| ≤ ‖E (w, s - 1)‖ := by
    apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs, hDsq]
    linarith [sq_nonneg ‖w‖]
  have hspos : 0 < s := by
    have H := (abs_lt.mp (hsle.trans_lt hlt)).1
    linarith
  let v := δ⁻¹ • w
  have hv : v ∈ Metric.ball (0 : Ambient d) (1 / 4) := by
    rw [Metric.mem_ball, dist_zero_right, show v = δ⁻¹ • w from rfl, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ), ← div_eq_inv_mul]
    exact (div_lt_iff₀ hδ).mpr (by linarith [hwle.trans_lt hlt])
  have hδv : δ • v = w := by simp [v, smul_smul, hδ.ne']
  have hheight : capHeight δ v = s := by
    have hh := congrArg norm hδv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at hh
    have hrad : 1 - δ ^ 2 * ‖v‖ ^ 2 = s ^ 2 := by
      rw [← mul_pow, hh]
      linarith
    rw [capHeight, hrad, Real.sqrt_sq hspos.le]
  have hC : capPoint δ v = E (w, s) := by
    have hw (i : Fin d) : δ * v i = w i := congrArg (fun x : Ambient d => x i) hδv
    simp only [capPoint, E, euclidean_slice_apply, Fin.insertNth_last', hw, hheight]
    rfl
  exact ⟨v, hv, hC.trans hspl⟩

end RestrictionWork
