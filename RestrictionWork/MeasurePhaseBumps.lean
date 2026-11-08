import OAI.Analysis.Fourier.Restriction.BumpBounds

-- Adapted from OpenAI's Apache-2.0 Lean restriction development.
-- Upstream revision 4eaee87548250b2682affda7d05d947c05554bae (see UPSTREAM_LICENSE).

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators RealInnerProductSpace
open OAI.Analysis.Fourier.Wave
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction

namespace RestrictionWork

def radiusBallBump {n : ℕ} (ρ : ℝ) : Space n → ℂ :=
  (ball 0 ρ).indicator (fun _ ↦ 1)

def radiusBallBumpSum {n : ℕ} (ρ : ℝ) (E : Finset (Space n)) (a : Space n → ℂ) : Space n → ℂ :=
  fun x ↦ ∑ z ∈ E, a z * radiusBallBump ρ (x - z)

theorem radius_ball_bump_translate {n : ℕ} (ρ : ℝ) (z x : Space n) :
    radiusBallBump ρ (x - z) = (ball z ρ).indicator (fun _ ↦ (1 : ℂ)) x := by
  have he : x - z ∈ ball (0 : Space n) ρ ↔ x ∈ ball z ρ := by
    simp only [mem_ball, dist_eq_norm, sub_zero]
  unfold radiusBallBump
  by_cases hx : x ∈ ball z ρ
  · rw [indicator_of_mem (he.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (fun h ↦ hx (he.mp h)), indicator_of_notMem hx]

theorem measurable_radius_ball_bump_translate {n : ℕ} (ρ : ℝ) (z : Space n) :
    Measurable (fun x ↦ radiusBallBump ρ (x - z)) := by
  simp_rw [radius_ball_bump_translate ρ]
  exact measurable_const.indicator measurableSet_ball

theorem integrable_radius_ball_bump_translate {n : ℕ} (ρ : ℝ) (z : Space n) :
    Integrable (fun x ↦ radiusBallBump ρ (x - z)) := by
  simp_rw [radius_ball_bump_translate ρ]
  have H : IntegrableOn (fun _ : Space n ↦ (1 : ℂ)) (ball z ρ) volume :=
    integrableOn_const (measure_ball_lt_top.ne)
  exact (integrable_indicator_iff measurableSet_ball).mpr H

theorem measurable_radius_ball_bump_sum {n : ℕ} (ρ : ℝ) (E : Finset (Space n)) (a : Space n → ℂ) :
    Measurable (radiusBallBumpSum ρ E a) := by
  apply Finset.measurable_sum
  intro z hz
  exact (measurable_radius_ball_bump_translate ρ z).const_mul (a z)

theorem integrable_radius_ball_bump_sum {n : ℕ} (ρ : ℝ) (E : Finset (Space n)) (a : Space n → ℂ) :
    Integrable (radiusBallBumpSum ρ E a) := by
  apply integrable_finsetSum
  intro z hz
  exact (integrable_radius_ball_bump_translate ρ z).const_mul (a z)

theorem radius_ball_bump_sum_eq_zero {n : ℕ} (ρ : ℝ) (E : Finset (Space n)) (a : Space n → ℂ)
    (x : Space n) (hx : ∀ z ∈ E, x ∉ ball z ρ) :
    radiusBallBumpSum ρ E a x = 0 := by
  apply Finset.sum_eq_zero
  intro z hz
  rw [radius_ball_bump_translate ρ, indicator_of_notMem (hx z hz), mul_zero]

theorem radius_ball_bump_sum_norm_le_one {n : ℕ} (ρ : ℝ) (hρ : ρ ≤ 1 / 4)
    (E : Finset (Space n)) (a : Space n → ℂ)
    (hsep : ∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w)
    (ha : ∀ z ∈ E, ‖a z‖ ≤ 1) (x : Space n) :
    ‖radiusBallBumpSum ρ E a x‖ ≤ 1 := by
  by_cases hx : ∃ z ∈ E, x ∈ ball z ρ
  · obtain ⟨z, hz, hxz⟩ := hx
    have he : radiusBallBumpSum ρ E a x = a z := by
      unfold radiusBallBumpSum
      rw [Finset.sum_eq_single z]
      · rw [radius_ball_bump_translate ρ, indicator_of_mem hxz, mul_one]
      · intro w hw hwz
        have hxw : x ∉ ball w ρ := by
          intro hxw
          have H := dist_triangle w x z
          have hwx : dist w x < ρ := by simpa only [mem_ball, dist_comm] using hxw
          have hxz' : dist x z < ρ := hxz
          have HS := hsep w hw z hz hwz
          linarith
        rw [radius_ball_bump_translate ρ, indicator_of_notMem hxw, mul_zero]
      · exact fun h ↦ (h hz).elim
    rw [he]
    exact ha z hz
  · have hz : ∀ z ∈ E, x ∉ ball z ρ := by simpa only [not_exists, not_and] using hx
    rw [radius_ball_bump_sum_eq_zero ρ E a x hz, norm_zero]
    norm_num

theorem angular_fourier_radius_ball_bump_sum {n : ℕ} (ρ : ℝ) (E : Finset (Space n))
    (a : Space n → ℂ) (ξ : Space n) :
    angularFourier (radiusBallBumpSum ρ E a) ξ =
      angularFourier (radiusBallBump ρ : Space n → ℂ) ξ * finitePhaseSum E a ξ := by
  change angularFourier (fun x ↦ ∑ z ∈ E, a z * radiusBallBump ρ (x - z)) ξ = _
  rw [angularFourier_sum E _
    (fun z _ ↦ (integrable_radius_ball_bump_translate ρ z).const_mul (a z))]
  simp_rw [angularFourier_const_mul, angularFourier_translate]
  rw [finitePhaseSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem eLpNorm_radius_ball_bump_sum_le {n : ℕ} (ρ : ℝ) {p : ℝ} (hp : 0 < p) (hρ : ρ ≤ 1 / 4)
    (E : Finset (Space n)) (a : Space n → ℂ)
    (hsep : ∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w)
    (ha : ∀ z ∈ E, ‖a z‖ ≤ 1) :
    eLpNorm (radiusBallBumpSum ρ E a) (ENNReal.ofReal p) volume ≤
      ((E.card : ℝ≥0∞) * volume (ball (0 : Space n) ρ)) ^ (1 / p) := by
  have H := eLpNorm_le_bound_mul_measure volume
    (measurable_radius_ball_bump_sum ρ E a).aestronglyMeasurable
    (E.measurableSet_biUnion (fun _ _ ↦ measurableSet_ball)) (by norm_num : (0 : ℝ) ≤ 1)
    (radius_ball_bump_sum_norm_le_one ρ hρ E a hsep ha)
    (E := ⋃ z ∈ E, ball z ρ)
    (by
      intro x hx
      apply radius_ball_bump_sum_eq_zero ρ
      simpa only [mem_iUnion, not_exists, not_and] using hx) hp
  simp only [ENNReal.ofReal_one, one_mul] at H
  exact H.trans (ENNReal.rpow_le_rpow (volume_finite_ball_union_le E _) (by positivity))

theorem radius_ball_fourier_lower {n : ℕ} {r K : ℝ} (hK : 0 ≤ K) (hr : r * K ≤ 1 / 4)
    {ξ : Space n} (hξ : ‖ξ‖ ≤ K) :
    volume.real (ball (0 : Space n) r) / 2 ≤
      ‖angularFourier ((ball (0 : Space n) r).indicator (fun _ ↦ (1 : ℂ))) ξ‖ := by
  let μ := (volume : Measure (Space n)).restrict (ball 0 r)
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball (0 : Space n) r) < ⊤)⟩
  have hm : Measurable (fun x : Space n ↦ -(inner ℝ x ξ)) := by fun_prop
  have hs : ∀ᵐ x ∂μ, |-(inner ℝ x ξ)| ≤ 1 / 4 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hx' : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using hx
    rw [abs_neg]
    calc
      _ ≤ ‖x‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x‖ * K := mul_le_mul_of_nonneg_left hξ (norm_nonneg _)
      _ ≤ r * K := mul_le_mul_of_nonneg_right hx'.le hK
      _ ≤ 1 / 4 := hr
  have H := small_phase_integral_lower_bound μ (fun x : Space n ↦ -(inner ℝ x ξ)) hm hs
  rw [angularFourier_indicator_ball]
  simpa only [Measure.real, μ, Measure.restrict_apply_univ, Complex.ofReal_neg, mul_neg, neg_mul] using H

theorem eLpNorm_finite_phase_sum_le_radius_bumps {n : ℕ} (μ : Measure (Space n))
    {ρ K : ℝ} (hK : 0 ≤ K) (hρK : ρ * K ≤ 1 / 4) (hsupp : ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ K)
    (E : Finset (Space n))
    (a : Space n → ℂ) (p : ℝ≥0∞) :
    ENNReal.ofReal (volume.real (ball (0 : Space n) ρ) / 2) *
        eLpNorm (finitePhaseSum E a) p μ ≤
      eLpNorm (angularFourier (radiusBallBumpSum ρ E a)) p μ := by
  let c := volume.real (ball (0 : Space n) ρ) / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have H : eLpNorm ((c : ℂ) • finitePhaseSum E a) p μ ≤
      eLpNorm (angularFourier (radiusBallBumpSum ρ E a)) p μ := by
    apply eLpNorm_mono_ae ((continuous_finitePhaseSum E a).const_smul (c : ℂ)).aestronglyMeasurable
    filter_upwards [hsupp] with ξ hξ
    have Hlow := radius_ball_fourier_lower hK hρK hξ
    rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
      angular_fourier_radius_ball_bump_sum,
      norm_mul]
    exact mul_le_mul_of_nonneg_right Hlow (norm_nonneg _)
  simpa only [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc] using H

end RestrictionWork
