import OAI.Analysis.Fourier.Restriction.WeakInterpolation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

private theorem measure_norm_tail_le {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {u : Y → ℂ} (hu : Measurable u) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    ν {y | t / 2 < ‖u y‖} ≤
      (2 : ℝ≥0∞) ^ r / ENNReal.ofReal t ^ r * ∫⁻ y, ‖u y‖ₑ ^ r ∂ν := by
  have ht' : 0 < t / 2 := by positivity
  have h₀ := (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr ht') hr).ne'
  have htfin : ENNReal.ofReal (t / 2) ^ r ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg hr (ENNReal.ofReal_ne_top)).ne
  calc
    _ ≤ ν {y | ENNReal.ofReal (t / 2) ^ r ≤ ‖u y‖ₑ ^ r} := by
      apply measure_mono
      intro y hy
      exact ENNReal.rpow_le_rpow (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hy.le) hr
    _ ≤ (∫⁻ y, ‖u y‖ₑ ^ r ∂ν) / ENNReal.ofReal (t / 2) ^ r :=
      meas_ge_le_lintegral_div (hu.enorm.pow_const r).aemeasurable h₀ htfin
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat,
        ENNReal.div_rpow_of_nonneg _ _ hr, div_eq_mul_inv,
        ENNReal.inv_div
          (Or.inl (ENNReal.rpow_lt_top_of_nonneg hr ENNReal.ofNat_ne_top).ne)
          (Or.inl (ENNReal.rpow_pos_of_nonneg (by norm_num) hr).ne'), div_eq_mul_inv]
      ac_rfl

set_option maxHeartbeats 650000 in
/-- Marcinkiewicz interpolation from the first and second moments of the
two outputs of each amplitude truncation. -/
theorem whitney_moment_le_of_truncated_outputs {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [SFinite μ] (ν : Measure Y)
    {f : X → ℂ} {u : Y → ℂ} (hf : Measurable f) (hu : Measurable u)
    {r : ℝ} (hr₁ : 1 < r) (hr₂ : r < 2) {C₁ C₂ : ℝ≥0∞}
    (hcut : ∀ t > 0, ∃ (v w : Y → ℂ), Measurable v ∧ Measurable w ∧
      (∀ y, u y = v y + w y) ∧
      (∫⁻ y, ‖v y‖ₑ ∂ν) ≤ C₁ * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ∂μ ∧
      (∫⁻ y, ‖w y‖ₑ ^ (2 : ℕ) ∂ν) ≤ C₂ * ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ (2 : ℕ) ∂μ) :
    (∫⁻ y, ‖u y‖ₑ ^ r ∂ν) ≤
      ((2 * C₁) * ENNReal.ofReal (r / (r - 1)) +
        (4 * C₂) * ENNReal.ofReal (r / (2 - r))) * ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  simp only [← ofReal_norm]
  apply OAI.Analysis.Fourier.Restriction.power_moment_le_of_two_truncations
    μ ν hf.norm hu.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hr₁ hr₂
  intro t ht
  obtain ⟨v, w, hv, hw, huv, h₁, h₂⟩ := hcut t ht
  have hsub : {y | t < ‖u y‖} ⊆ {y | t / 2 < ‖v y‖} ∪ {y | t / 2 < ‖w y‖} := by
    intro y hy
    by_contra! he
    obtain ⟨hv', hw'⟩ := not_or.mp he
    have H := norm_add_le (v y) (w y)
    rw [← huv y] at H
    change t < ‖u y‖ at hy
    have hv'' : ‖v y‖ ≤ t / 2 := le_of_not_gt hv'
    have hw'' : ‖w y‖ ≤ t / 2 := le_of_not_gt hw'
    linarith
  have hv' := measure_norm_tail_le ν hv (r := 1) zero_le_one ht
  have hw' := measure_norm_tail_le ν hw (r := 2) (by norm_num) ht
  simp only [ENNReal.rpow_one] at hv'
  simp only [ENNReal.rpow_two, show (2 : ℝ≥0∞) ^ (2 : ℕ) = 4 by norm_num] at hw'
  calc
    _ ≤ ν ({y | t / 2 < ‖v y‖} ∪ {y | t / 2 < ‖w y‖}) := measure_mono hsub
    _ ≤ ν {y | t / 2 < ‖v y‖} + ν {y | t / 2 < ‖w y‖} := measure_union_le _ _
    _ ≤ 2 / ENNReal.ofReal t * (C₁ * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ∂μ) +
        4 / ENNReal.ofReal t ^ (2 : ℕ) *
          (C₂ * ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ (2 : ℕ) ∂μ) :=
      add_le_add (hv'.trans (mul_le_mul' le_rfl h₁)) (hw'.trans (mul_le_mul' le_rfl h₂))
    _ = _ := by simp only [ENNReal.rpow_two, ofReal_norm, div_eq_mul_inv]; ac_rfl

end RestrictionWork
