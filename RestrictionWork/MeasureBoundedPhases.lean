import RestrictionWork.MeasurePhaseBumps
import RestrictionWork.MeasureUnitBallLoss

-- Adapted from OpenAI's Apache-2.0 Lean restriction development.
-- Upstream revision 4eaee87548250b2682affda7d05d947c05554bae (see UPSTREAM_LICENSE).

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators
open OAI.Analysis.Fourier.Wave
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction

namespace RestrictionWork

/-- The small-loss physical-space estimate controls finite exponential
sums on every unit-separated set, with no dependence on its cardinality
other than the displayed strict power. -/
theorem measure_bounded_phases_of_unit_ball_loss {n : ℕ} (𝓜 : Set (Measure (Space n)))
    {K : ℝ} (hK : 1 ≤ K) (hsupp : ∀ μ ∈ 𝓜, ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ K)
    {p ε : ℝ} (hp : 0 < p)
    (_ : 0 < ε) {A : ℝ≥0∞} (hAt : A ≠ ⊤)
    (hbound : ∀ μ ∈ 𝓜, ∀ E : Finset (Space n), ∀ M : ℕ, 1 ≤ M → E.card ≤ M →
      ∀ f : Space n → ℂ, Measurable f → Integrable f →
        (∀ x, (∀ e ∈ E, x ∉ ball e 1) → f x = 0) →
          eLpNorm (angularFourier f) (ENNReal.ofReal p) μ ≤
            A * ENNReal.ofReal ((M : ℝ) ^ ε) * eLpNorm f (ENNReal.ofReal p) volume) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ μ ∈ 𝓜, ∀ E : Finset (Space n),
      (∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w) →
      ∀ a : Space n → ℂ, (∀ z ∈ E, ‖a z‖ ≤ 1) →
        eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) μ ≤
          B * ENNReal.ofReal ((E.card : ℝ) ^ (ε + 1 / p)) := by
  let ρ : ℝ := (1 / 4) / K
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hρ0 : 0 < ρ := div_pos (by norm_num) hK0
  have hρK : ρ * K ≤ 1 / 4 := by
    dsimp [ρ]
    rw [div_mul_cancel₀ _ hK0.ne']
  have hρ : ρ ≤ 1 / 4 :=
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hK hρ0.le : ρ ≤ ρ * K).trans hρK
  let V := volume (ball (0 : Space n) ρ)
  let c := ENNReal.ofReal (V.toReal / 2)
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hVp : 0 < V := measure_ball_pos volume _ hρ0
  have hcp : 0 < c := ENNReal.ofReal_pos.mpr (by
    exact div_pos (ENNReal.toReal_pos hVp.ne' hVt) (by norm_num))
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨c⁻¹ * A * V ^ (1 / p), ?_, ?_⟩
  · apply ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hcp.ne') hAt)
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hVt
  intro μ hμ E hsep a ha
  by_cases he : E.Nonempty
  · have hM : 1 ≤ E.card := he.card_pos
    have HM : 0 < (E.card : ℝ) := by exact_mod_cast he.card_pos
    have H := hbound μ hμ E E.card hM le_rfl (radiusBallBumpSum ρ E a)
      (measurable_radius_ball_bump_sum ρ E a) (integrable_radius_ball_bump_sum ρ E a) (by
        intro x hx
        apply radius_ball_bump_sum_eq_zero
        intro z hz hxz
        exact hx z hz (ball_subset_ball (hρ.trans (by norm_num)) hxz))
    have HL := eLpNorm_finite_phase_sum_le_radius_bumps μ hK0.le hρK (hsupp μ hμ) E a (ENNReal.ofReal p)
    have HN := eLpNorm_radius_ball_bump_sum_le ρ hp hρ E a hsep ha
    have HP : ENNReal.ofReal ((E.card : ℝ) ^ ε) *
        ((E.card : ℝ≥0∞) * V) ^ (1 / p) =
        V ^ (1 / p) * ENNReal.ofReal ((E.card : ℝ) ^ (ε + 1 / p)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      have hcN : (E.card : ℝ≥0∞) = ENNReal.ofReal (E.card : ℝ) := by simp
      rw [hcN, ENNReal.ofReal_rpow_of_pos HM,
        Real.rpow_add HM, ENNReal.ofReal_mul (by positivity)]
      ring
    calc
      _ = c⁻¹ * (c * eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcp.ne' hct, one_mul]
      _ ≤ c⁻¹ * eLpNorm (angularFourier (radiusBallBumpSum ρ E a)) (ENNReal.ofReal p) μ := by
        gcongr
        exact HL
      _ ≤ c⁻¹ * (A * ENNReal.ofReal ((E.card : ℝ) ^ ε) *
          eLpNorm (radiusBallBumpSum ρ E a) (ENNReal.ofReal p) volume) := by gcongr
      _ ≤ c⁻¹ * (A * ENNReal.ofReal ((E.card : ℝ) ^ ε) *
          ((E.card : ℝ≥0∞) * V) ^ (1 / p)) := by gcongr
      _ = _ := by rw [mul_assoc A, HP]; ring
  · have he0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst E
    have hP : finitePhaseSum (∅ : Finset (Space n)) a = 0 := by
      funext x
      simp [finitePhaseSum]
    rw [hP, eLpNorm_zero]
    exact zero_le

end RestrictionWork
