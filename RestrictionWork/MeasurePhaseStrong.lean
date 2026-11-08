import OAI.Analysis.Fourier.Restriction.PhaseStrong

-- Adapted from OpenAI's Apache-2.0 Lean restriction development.
-- Upstream revision 4eaee87548250b2682affda7d05d947c05554bae (see UPSTREAM_LICENSE).

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators Topology
open OAI.Analysis.Fourier.Wave
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction

namespace RestrictionWork

theorem measure_finite_phase_sum_band_bound {n : ℕ} (μ : Measure (Space n)) (E : Finset (Space n))
    {p : ℝ≥0∞} {q s : ℝ} (hq : 0 < q) (hs : 0 ≤ s) {C : ℝ≥0∞}
    (hres : ∀ S : Finset (Space n), S ⊆ E → ∀ a : Space n → ℂ,
      (∀ z ∈ S, ‖a z‖ ≤ 1) → eLpNorm (finitePhaseSum S a) p μ ≤
        C * ENNReal.ofReal ((S.card : ℝ) ^ s))
    (a : Space n → ℂ) (hsum : (∑ z ∈ E, ‖a z‖ ^ q) ≤ 1)
    {l u : ℝ} (hl : 0 < l) (hu : 0 < u) :
    eLpNorm (finitePhaseSum E (amplitudeBand a l u)) p μ ≤
      C * ENNReal.ofReal (u * l ^ (-q * s)) := by
  classical
  let S := E.filter (fun z ↦ l < ‖a z‖)
  let b : Space n → ℂ := fun z ↦ (u : ℂ)⁻¹ * amplitudeBand a l u z
  have hb : ∀ z ∈ S, ‖b z‖ ≤ 1 := by
    intro z hz
    change ‖(u : ℂ)⁻¹ * amplitudeBand a l u z‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    calc
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left (norm_amplitudeBand_le_upper a l hu.le z) (by positivity)
      _ = 1 := inv_mul_cancel₀ hu.ne'
  have H := hres S (Finset.filter_subset _ _) b hb
  have hc := finite_card_norm_gt_le E a hq hl hsum
  have hpow : (S.card : ℝ) ^ s ≤ l ^ (-q * s) := by
    calc
      _ ≤ (l ^ (-q)) ^ s := Real.rpow_le_rpow (by positivity) hc hs
      _ = _ := (Real.rpow_mul hl.le _ _).symm
  have he : amplitudeBand a l u = (fun z ↦ (u : ℂ) * b z) := by
    funext z
    dsimp [b]
    rw [← mul_assoc, mul_inv_cancel₀ (show (u : ℂ) ≠ 0 by exact_mod_cast hu.ne'), one_mul]
  rw [finitePhaseSum_band_filter, he, finitePhaseSum_const_mul, eLpNorm_const_smul]
  have hnorm : ‖(u : ℂ)‖ₑ = ENNReal.ofReal u := by
    simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  rw [hnorm]
  calc
    _ ≤ ENNReal.ofReal u * (C * ENNReal.ofReal ((S.card : ℝ) ^ s)) := by gcongr
    _ ≤ ENNReal.ofReal u * (C * ENNReal.ofReal (l ^ (-q * s))) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hu.le]; ring

/-- Restricted finite exponential-sum bounds improve to strong bounds at
every smaller input exponent, uniformly in the finite set. -/
theorem measure_finite_phase_sum_normalized_bound {n : ℕ} (μ : Measure (Space n)) (E : Finset (Space n))
    {p q s : ℝ} (hp : 1 ≤ p) (hq : 0 < q) (hs : 0 ≤ s) (hqs : q * s < 1)
    {C : ℝ≥0∞}
    (hres : ∀ S : Finset (Space n), S ⊆ E → ∀ a : Space n → ℂ,
      (∀ z ∈ S, ‖a z‖ ≤ 1) →
        eLpNorm (finitePhaseSum S a) (ENNReal.ofReal p) μ ≤
          C * ENNReal.ofReal ((S.card : ℝ) ^ s))
    (a : Space n → ℂ) (hsum : (∑ z ∈ E, ‖a z‖ ^ q) ≤ 1) :
    eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) μ ≤
      (C * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-q * s))) *
        ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (1 + -q * s))⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have ha : ∀ z ∈ E, ‖a z‖ ≤ 1 :=
    fun z hz ↦ finite_norm_le_one_of_sum_rpow_le_one E a hq hsum hz
  let ρ : ℝ := (1 / 2 : ℝ) ^ (1 + -q * s)
  have hρ : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have Hk (k : ℕ) :
      eLpNorm (finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
        (ENNReal.ofReal p) μ ≤
      (C * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-q * s))) * ENNReal.ofReal (ρ ^ k) := by
    have H := measure_finite_phase_sum_band_bound μ E hq hs hres a hsum
      (l := (1 / 2 : ℝ) ^ (k + 1)) (u := (1 / 2 : ℝ) ^ k) (by positivity) (by positivity)
    have he : (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ (k + 1)) ^ (-q * s) =
        (1 / 2 : ℝ) ^ (-q * s) * ρ ^ k := by
      rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
      rw [show (1 / 2 : ℝ) ^ k * (((1 / 2 : ℝ) ^ k) ^ (-q * s) *
          (1 / 2 : ℝ) ^ (-q * s)) =
        (1 / 2 : ℝ) ^ (-q * s) * ((1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k) ^ (-q * s)) by ring]
      rw [pow_mul_rpow_band (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [he, ENNReal.ofReal_mul (by positivity)] at H
    simpa only [mul_assoc] using H
  have hlim : ∀ ξ, Tendsto (fun N : ℕ ↦
      finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N)) ξ)
      atTop (𝓝 (finitePhaseSum E a ξ)) := by
    intro ξ
    exact tendsto_finsetSum E (fun z hz ↦ (tendsto_amplitudeBand a z).mul tendsto_const_nhds)
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise μ
    (fun N ↦ (continuous_finitePhaseSum E _).aestronglyMeasurable)
    (continuous_finitePhaseSum E a).aestronglyMeasurable hlim hp0
  intro N
  rw [finitePhaseSum_low_decomposition E a ha N]
  have hsumNorm : eLpNorm (fun ξ ↦ ∑ k ∈ Finset.range N,
      finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) ξ)
      (ENNReal.ofReal p) μ ≤
      ∑ k ∈ Finset.range N, eLpNorm
        (finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
        (ENNReal.ofReal p) μ := by
    have he : (fun ξ ↦ ∑ k ∈ Finset.range N,
        finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) ξ) =
        ∑ k ∈ Finset.range N,
          finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) := by
      funext ξ
      simp only [Finset.sum_apply]
    rw [he]
    exact eLpNorm_sum_le hpE
  exact hsumNorm.trans ((Finset.sum_le_sum (fun k _ ↦ Hk k)).trans
    (sum_mul_ofReal_geometric_le _ (by dsimp [ρ]; positivity) hρ N))

theorem measure_finite_phase_sum_strong_bound {n : ℕ} (μ : Measure (Space n)) (E : Finset (Space n))
    {p q s : ℝ} (hp : 1 ≤ p) (hq : 0 < q) (hs : 0 ≤ s) (hqs : q * s < 1)
    {C : ℝ≥0∞}
    (hres : ∀ S : Finset (Space n), S ⊆ E → ∀ a : Space n → ℂ,
      (∀ z ∈ S, ‖a z‖ ≤ 1) →
        eLpNorm (finitePhaseSum S a) (ENNReal.ofReal p) μ ≤
          C * ENNReal.ofReal ((S.card : ℝ) ^ s)) (a : Space n → ℂ) :
    eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) μ ≤
      phaseInterpolationConstant q s C * ENNReal.ofReal ((∑ z ∈ E, ‖a z‖ ^ q) ^ (1 / q)) := by
  let S : ℝ := ∑ z ∈ E, ‖a z‖ ^ q
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun z _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hS : S = 0
  · have ha : ∀ z ∈ E, a z = 0 := by
      intro z hz
      have H : ‖a z‖ ^ q ≤ 0 := by
        calc
          _ ≤ S := Finset.single_le_sum (fun w _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hz
          _ = 0 := hS
      have Hzero : ‖a z‖ ^ q = 0 := le_antisymm H (Real.rpow_nonneg (norm_nonneg _) _)
      have hn : ‖a z‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) hq.ne').mp Hzero
      exact norm_eq_zero.mp hn
    have hP : finitePhaseSum E a = 0 := by
      funext ξ
      apply Finset.sum_eq_zero
      intro z hz
      rw [ha z hz, zero_mul]
    rw [hP, eLpNorm_zero]
    exact zero_le
  have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
  let N := S ^ (1 / q)
  have hNp : 0 < N := Real.rpow_pos_of_pos hSp _
  have hNq : N ^ q = S := by
    dsimp [N]
    rw [← Real.rpow_mul hSp.le, one_div_mul_cancel hq.ne', Real.rpow_one]
  let b : Space n → ℂ := fun z ↦ ((N⁻¹ : ℝ) : ℂ) * a z
  have hsum : (∑ z ∈ E, ‖b z‖ ^ q) ≤ 1 := by
    have he (z : Space n) : ‖b z‖ ^ q = (N ^ q)⁻¹ * ‖a z‖ ^ q := by
      dsimp [b]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNp),
        Real.mul_rpow (inv_nonneg.mpr hNp.le) (norm_nonneg _), Real.inv_rpow hNp.le]
    simp_rw [he]
    rw [← Finset.mul_sum, hNq]
    change S⁻¹ * S ≤ 1
    rw [inv_mul_cancel₀ hS]
  have H := measure_finite_phase_sum_normalized_bound μ E hp hq hs hqs hres b hsum
  have he : a = (fun z ↦ (N : ℂ) * b z) := by
    funext z
    dsimp [b]
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (show (N : ℂ) ≠ 0 by exact_mod_cast hNp.ne'), one_mul]
  have hPeq : finitePhaseSum E a = (N : ℂ) • finitePhaseSum E b := by
    conv_lhs => rw [he]
    exact finitePhaseSum_const_mul E b (N : ℂ)
  rw [hPeq, eLpNorm_const_smul]
  have hn : ‖(N : ℂ)‖ₑ = ENNReal.ofReal N := by
    simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp]
  rw [hn]
  calc
    _ ≤ ENNReal.ofReal N * phaseInterpolationConstant q s C := by
      gcongr
      exact H
    _ = _ := mul_comm _ _

end RestrictionWork
