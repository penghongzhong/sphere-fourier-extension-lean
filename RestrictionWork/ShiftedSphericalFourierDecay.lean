import RestrictionWork.EuclideanBallSlices
import RestrictionWork.ShiftedSphericalSliceOscillation

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace Interval ComplexConjugate
namespace RestrictionWork

/-- The Fourier kernel of the graph measure with the unit-ball cutoff,
in the angular-frequency convention used by `graphExtension`. -/
def patchGraphKernel {d : ℕ} (φ : Ambient d → ℝ) (z : Ambient d × ℝ) : ℂ :=
  graphExtension (fun _ => 1) φ z

theorem patch_graph_kernel_neg {d : ℕ} (φ : Ambient d → ℝ) (z : Ambient d × ℝ) :
    patchGraphKernel φ (-z) = conj (patchGraphKernel φ z) := by
  unfold patchGraphKernel graphExtension phaseExtension
  simp only [one_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [Prod.fst_neg, Prod.snd_neg, inner_neg_left, neg_mul, ← neg_add]
  rw [Complex.conj_exp_ofReal_mul_I, Complex.ofReal_neg, neg_mul]

private theorem shifted_spherical_coordinate_bound {d : ℕ} {δ r τ : ℝ} {a : Ambient (d + 1)}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hτ : 0 ≤ τ)
    (y : Ambient (d + 1)) (i : Fin (d + 1))
    (hi : ‖y‖ ≤ ((d : ℝ) + 1) * |y i|)
    {v : Ambient d} (hv : v ∈ Metric.ball (0 : Ambient d) 1) :
    let z := (y, τ)
    let φ := shiftedSphericalGraphPhase δ a r
    ‖∫ s in -ballSliceRadius v..ballSliceRadius v,
        Complex.exp (((⟪y, euclideanSliceEquiv i (v, s)⟫ +
          τ * φ (euclideanSliceEquiv i (v, s)) : ℝ) : ℂ) * Complex.I)‖ ≤
      320 * ((d : ℝ) + 1) / Real.sqrt (1 + ‖z‖) := by
  intro z φ
  let N : ℝ := (d : ℝ) + 1
  let ρ := ‖z‖
  let b := ballSliceRadius v
  let u := euclideanSliceEquiv i (v, 0)
  let w : Ambient (d + 1) := EuclideanSpace.single i 1
  let F : ℝ → ℝ := fun s => ⟪y, u⟫ + y i * s + τ * φ (u + s • w)
  let I := ∫ s in -b..b, Complex.exp ((F s : ℂ) * Complex.I)
  have hN : 1 ≤ N := by unfold N; linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hbpos : 0 < b := by
    have hv' : ‖v‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hv
    exact Real.sqrt_pos.2 (by nlinarith [norm_nonneg v])
  have hb : b ≤ 1 := by
    calc
      b ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (sub_le_self _ (sq_nonneg ‖v‖))
      _ = _ := Real.sqrt_one
  have hw : ‖w‖ = 1 := by simp [w]
  have hU (s : ℝ) (hs : s ∈ Icc (-b) b) : ‖u + s • w‖ ≤ 1 := by
    change ‖euclideanSliceEquiv i (v, 0) + s • EuclideanSpace.single i 1‖ ≤ 1
    rw [← euclidean_slice_affine]
    exact euclidean_slice_norm_le_one i hv hs
  have hphase (s : ℝ) :
      ⟪y, euclideanSliceEquiv i (v, s)⟫ + τ * φ (euclideanSliceEquiv i (v, s)) = F s := by
    rw [euclidean_slice_affine]
    dsimp only [F, u, w]
    rw [inner_add_right, real_inner_smul_right, EuclideanSpace.inner_single_right]
    simp
    ring
  simp_rw [hphase]
  change ‖I‖ ≤ 320 * N / Real.sqrt (1 + ρ)
  obtain ⟨htriv, hnormal, htangent⟩ := shifted_spherical_slice_estimates
    (c := ⟪y, u⟫) (ξ := y i) hδ hδhalf ha hr hrhalf
      (show -b < b by linarith) hτ hw hU
  change ‖I‖ ≤ b - -b at htriv
  have hroot : 0 < Real.sqrt (1 + ρ) := Real.sqrt_pos.2 (by unfold ρ; positivity)
  have hρ : ρ = max ‖y‖ τ := by simp [ρ, z, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hτ]
  apply (le_div_iff₀ hroot).mpr
  by_cases hsmall : ρ ≤ 1
  · have H : Real.sqrt (1 + ρ) ≤ 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> linarith
    calc
      _ ≤ 2 * 2 := mul_le_mul (htriv.trans (by linarith)) H hroot.le (by norm_num)
      _ ≤ _ := by linarith
  · have hlarge : 1 ≤ ρ := le_of_lt (lt_of_not_ge hsmall)
    by_cases hdom : ‖y‖ ≤ 40 * N * τ
    · have hdom' : ρ ≤ 40 * N * τ := by
        rw [hρ, max_le_iff]
        refine ⟨hdom, ?_⟩
        nlinarith only [mul_le_mul_of_nonneg_right hN hτ, hτ]
      have hτpos : 0 < τ := by
        by_contra! h
        have he : τ = 0 := le_antisymm h hτ
        rw [he, mul_zero] at hdom'
        linarith
      have htpos : 0 < Real.sqrt (2 * τ) := Real.sqrt_pos.2 (by positivity)
      have hroot' : Real.sqrt (1 + ρ) ≤ 40 * N * Real.sqrt (2 * τ) := by
        calc
          _ ≤ Real.sqrt ((40 * N) * (2 * τ)) := Real.sqrt_le_sqrt (by linarith)
          _ = Real.sqrt (40 * N) * Real.sqrt (2 * τ) := Real.sqrt_mul (by positivity) _
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ htpos.le
            exact Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
      calc
        _ ≤ (8 / Real.sqrt (2 * τ)) * (40 * N * Real.sqrt (2 * τ)) :=
          mul_le_mul (hnormal hτpos) hroot' hroot.le (by positivity)
        _ = _ := by field_simp [htpos.ne']; ring
    · have hdom' : 40 * N * τ ≤ ‖y‖ := le_of_lt (lt_of_not_ge hdom)
      have hty : τ ≤ ‖y‖ := by
        nlinarith only [hdom', mul_le_mul_of_nonneg_right hN hτ, hτ]
      have hy : ρ = ‖y‖ := hρ.trans (max_eq_left hty)
      have hν : 0 < |y i| := by
        by_contra! h
        have he : |y i| = 0 := le_antisymm h (abs_nonneg _)
        rw [he, mul_zero, ← hy] at hi
        linarith
      have hsep : 10 * τ ≤ |y i| / 2 := by
        apply le_of_mul_le_mul_left (a := N) _ (by linarith)
        nlinarith only [hdom', hi, mul_nonneg (show 0 ≤ N by linarith) hτ]
      have hroot' : Real.sqrt (1 + ρ) ≤ 2 * N * |y i| := by
        calc
          _ ≤ 1 + ρ := Real.sqrt_le_self_iff.mpr (Or.inr (by unfold ρ; linarith only [norm_nonneg z]))
          _ ≤ 2 * ρ := by linarith
          _ ≤ _ := by rw [hy, mul_assoc]; exact mul_le_mul_of_nonneg_left hi (by norm_num)
      calc
        _ ≤ (6 / |y i|) * (2 * N * |y i|) :=
          mul_le_mul (htangent hν hsep) hroot' hroot.le (by positivity)
        _ = 12 * N := by field_simp [hν.ne']; ring
        _ ≤ _ := by linarith

/-- A positive uniform Fourier decay power for the full shifted and
parabolically rescaled spherical graph family, on its actual parameter ball. -/
theorem shifted_spherical_kernel_decay_succ (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {δ r : ℝ} {a : Ambient (d + 1)}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ z : Ambient (d + 1) × ℝ,
        ‖patchGraphKernel (shiftedSphericalGraphPhase δ a r) z‖ ≤
          C / Real.sqrt (1 + ‖z‖) := by
  let C := 320 * ((d : ℝ) + 1) * (patchMeasure d).real univ
  refine ⟨C, by unfold C; positivity, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf
  let φ := shiftedSphericalGraphPhase δ a r
  have hpos (y : Ambient (d + 1)) (τ : ℝ) (hτ : 0 ≤ τ) :
      ‖patchGraphKernel φ (y, τ)‖ ≤ C / Real.sqrt (1 + ‖(y, τ)‖) := by
    obtain ⟨i, hi⟩ := exists_euclidean_large_coordinate y
    let f : Ambient (d + 1) → ℂ := fun u =>
      Complex.exp (((⟪y, u⟫ + τ * φ u : ℝ) : ℂ) * Complex.I)
    have : IsFiniteMeasure (patchMeasure (d + 1)) := by
      unfold patchMeasure
      exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have : IsFiniteMeasure (patchMeasure d) := by
      unfold patchMeasure
      exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hm : Measurable f := by
      unfold f φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
      fun_prop
    have hf : Integrable f (patchMeasure (d + 1)) :=
      (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
        (.of_forall fun u => (Complex.norm_exp_ofReal_mul_I _).le)
    unfold patchGraphKernel graphExtension phaseExtension
    simp only [one_mul]
    change ‖∫ u, f u ∂patchMeasure (d + 1)‖ ≤ _
    rw [euclidean_ball_integral_slices i hf]
    calc
      _ ≤ (320 * ((d : ℝ) + 1) / Real.sqrt (1 + ‖(y, τ)‖)) *
          (patchMeasure d).real univ := by
        apply norm_integral_le_of_norm_le_const
        have he : ∀ᵐ v ∂patchMeasure d, v ∈ Metric.ball (0 : Ambient d) 1 :=
          ae_restrict_mem measurableSet_ball
        filter_upwards [he] with v hv
        exact shifted_spherical_coordinate_bound hδ hδhalf ha hr hrhalf hτ y i hi hv
      _ = _ := by unfold C; ring
  intro z
  by_cases hz : 0 ≤ z.2
  · exact hpos z.1 z.2 hz
  · have H := hpos (-z.1) (-z.2) (by linarith)
    change ‖patchGraphKernel φ (-z)‖ ≤ C / Real.sqrt (1 + ‖-z‖) at H
    rwa [patch_graph_kernel_neg, Complex.norm_conj, norm_neg] at H

theorem shifted_spherical_kernel_decay {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ z : Ambient d × ℝ,
        ‖patchGraphKernel (shiftedSphericalGraphPhase δ a r) z‖ ≤
          C / Real.sqrt (1 + ‖z‖) := by
  cases d with
  | zero => omega
  | succ d => exact shifted_spherical_kernel_decay_succ d

end RestrictionWork
