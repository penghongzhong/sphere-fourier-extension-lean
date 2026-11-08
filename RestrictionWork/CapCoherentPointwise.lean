import RestrictionWork.SphericalPatchLocalError

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- Constant cap data stay coherent on a fixed physical ball. The lower
bound and the physical ball are independent of the cap scale. -/
theorem cap_coherent_pointwise {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1/2)
    (z : Ambient d × ℝ) (hz : ‖z‖ ≤ 1/8) :
    (patchMeasure d).real Set.univ / 2 ≤
      ‖sphericalPatchExtension δ (fun _ : Ambient d ↦ (1 : ℂ)) z‖ := by
  haveI : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let M := (patchMeasure d).real Set.univ
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  let φ : Ambient d → ℝ := fun v ↦ sphericalPhase δ (‖v‖ ^ 2)
  let θ : Ambient d → ℝ := fun v ↦ ⟪z.1, v⟫ + z.2 * φ v
  have hφ : Measurable φ := by dsimp [φ]; unfold sphericalPhase; fun_prop
  have hθ : Measurable θ := by dsimp [θ]; fun_prop
  have hs : ‖z.1‖ ≤ 1/8 := (norm_fst_le z).trans hz
  have ht : |z.2| ≤ 1/8 := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le z).trans hz
  have hsmall : ∀ᵐ v ∂patchMeasure d, |θ v| ≤ 3/8 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with v hv
    have hvn : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hv
    have herr := spherical_phase_quadratic_error δ (‖v‖ ^ 2) hδ hδ₁
      (sq_nonneg _) (by nlinarith [norm_nonneg v])
    have hφb : |φ v| ≤ 2 := by
      have H : |φ v| ≤ δ ^ 2 + ‖v‖ ^ 2 := by
        calc
          _ = |(φ v - ‖v‖ ^ 2) + ‖v‖ ^ 2| := by congr 1; ring
          _ ≤ |φ v - ‖v‖ ^ 2| + |‖v‖ ^ 2| := abs_add_le _ _
          _ ≤ _ := by
            rw [abs_of_nonneg (sq_nonneg ‖v‖)]
            exact add_le_add herr le_rfl
      have hd : δ ^ 2 ≤ 1/4 := by nlinarith
      nlinarith [norm_nonneg v]
    have hlin : |⟪z.1, v⟫| ≤ 1/8 := by
      have H : |⟪z.1, v⟫| ≤ ‖z.1‖ * ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) z.1 v
      exact H.trans ((mul_le_of_le_one_right (norm_nonneg _) hvn.le).trans hs)
    dsimp [θ]
    calc
      _ ≤ |⟪z.1, v⟫| + |z.2 * φ v| := abs_add_le _ _
      _ = |⟪z.1, v⟫| + |z.2| * |φ v| := by rw [abs_mul]
      _ ≤ (1/8 : ℝ) + (1/8 : ℝ) * 2 :=
        add_le_add hlin (mul_le_mul ht hφb (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num
  have hint : Integrable (fun v ↦ Complex.exp ((θ v : ℂ) * Complex.I)) (patchMeasure d) := by
    apply Integrable.of_bound (C := 1)
    · fun_prop
    · filter_upwards [] with v
      simp [Complex.norm_exp]
  have hconst : (∫ _ : Ambient d, (1 : ℂ) ∂patchMeasure d) = (M : ℂ) := by
    simp [M]
  have he : sphericalPatchExtension δ (fun _ : Ambient d ↦ (1 : ℂ)) z =
      ∫ v, Complex.exp ((θ v : ℂ) * Complex.I) ∂patchMeasure d := by
    simp only [sphericalPatchExtension, graphExtension, phaseExtension, one_mul]
    rfl
  have Herr : ‖sphericalPatchExtension δ (fun _ : Ambient d ↦ (1 : ℂ)) z - (M : ℂ)‖ ≤
      (3/8 : ℝ) * M := by
    rw [he, ← hconst, ← integral_sub hint (integrable_const (1 : ℂ))]
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hsmall] with v hv
    have H := phase_exponential_lipschitz (θ v) 0
    have H' : ‖Complex.exp ((θ v : ℂ) * Complex.I) - 1‖ ≤ |θ v| := by
      simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] using H
    exact H'.trans hv
  have Hnorm := norm_sub_norm_le (M : ℂ)
    (sphericalPatchExtension δ (fun _ : Ambient d ↦ (1 : ℂ)) z)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM, norm_sub_rev] at Hnorm
  change M / 2 ≤ _
  linarith

end RestrictionWork
