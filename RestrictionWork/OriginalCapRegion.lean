import RestrictionWork.CapLiftDefinitions

set_option autoImplicit false
noncomputable section
namespace RestrictionWork

/-- The actual, normalized original-frequency image of a local product ball
is contained in a Euclidean ball at the parabolic scale. -/
theorem original_cap_region {d : ℕ} {δ R : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) (hR : 0 < R) :
    (fun z : Ambient d × ℝ => (2 * Real.pi)⁻¹ •
      physicalEmbed (capPhysicalScale δ z)) '' Metric.ball 0 R ⊆
      Metric.ball (0 : Ambient (d + 1)) (4 * R / δ ^ 2) := by
  have hP (w : Ambient d × ℝ) : ‖physicalEmbed w‖ ≤ ‖w.1‖ + |w.2| := by
    have HS : ‖physicalEmbed w‖ ^ 2 = ‖w.1‖ ^ 2 + |w.2| ^ 2 := by
      simp only [physicalEmbed, PiLp.norm_sq_eq_of_L2,
        WithLp.equiv_symm_apply, PiLp.toLp_apply, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last, Real.norm_eq_abs]
    nlinarith [norm_nonneg (physicalEmbed w), norm_nonneg w.1,
      abs_nonneg w.2, mul_nonneg (norm_nonneg w.1) (abs_nonneg w.2)]
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδinv : δ⁻¹ ≤ (δ ^ 2)⁻¹ := by
    have H : δ ^ 2 ≤ δ := by nlinarith
    simpa only [one_div] using one_div_le_one_div_of_le hδsq H
  have hπ : 0 < 2 * Real.pi := by positivity
  have hπinv : (2 * Real.pi)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hπ).mpr
    nlinarith [Real.two_le_pi]
  rintro y ⟨z, hz, rfl⟩
  have hzR : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hx : ‖z.1‖ ≤ R := (norm_fst_le z).trans hzR.le
  have ht : |z.2| ≤ R := by simpa only [Real.norm_eq_abs] using (norm_snd_le z).trans hzR.le
  have HX : δ⁻¹ * ‖z.1‖ ≤ R / δ ^ 2 := by
    calc
      _ ≤ (δ ^ 2)⁻¹ * R := mul_le_mul hδinv hx (norm_nonneg _) (inv_nonneg.mpr hδsq.le)
      _ = _ := by ring
  have HT : |(-2 * z.2) / δ ^ 2| ≤ 2 * R / δ ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hδsq]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) hδsq.le
  have HP : ‖physicalEmbed (capPhysicalScale δ z)‖ ≤ R / δ ^ 2 + 2 * R / δ ^ 2 := by
    apply (hP (capPhysicalScale δ z)).trans
    apply add_le_add _ HT
    simpa only [capPhysicalScale, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)] using HX
  have Hnorm : ‖(2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)‖ ≤
      ‖physicalEmbed (capPhysicalScale δ z)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hπ)]
    exact mul_le_of_le_one_left (norm_nonneg _) hπinv
  rw [Metric.mem_ball, dist_zero_right]
  apply Hnorm.trans_lt
  apply HP.trans_lt
  have Hpos : 0 < R / δ ^ 2 := div_pos hR hδsq
  have htwo : 2 * R / δ ^ 2 = 2 * (R / δ ^ 2) := by ring
  have hfour : 4 * R / δ ^ 2 = 4 * (R / δ ^ 2) := by ring
  rw [htwo, hfour]
  linarith

end RestrictionWork
