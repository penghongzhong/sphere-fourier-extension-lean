import RestrictionWork.OriginalStrictTarget
import RestrictionWork.ExtensionTopBound

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped ENNReal
namespace RestrictionWork

/-- Sufficiency in the strict part of the exact original reciprocal-exponent
region, for arbitrary extended exponents and with no analytic premise. -/
theorem strict_admissible_sufficiency {n : ℕ} (hn : 3 ≤ n) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hrad : ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q)
    (hstrict : (q⁻¹).toReal <
      (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal)) :
    BoundedSphereExtension n p q := by
  by_cases hqt : q = ⊤
  · subst q
    exact extension_top_bound hp
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnplus : 0 < (n : ℝ) + 1 := by linarith
  have hnminus : 0 < (n : ℝ) - 1 := by linarith
  have hqr : 0 < q.toReal := by
    have H := ENNReal.toReal_mono hqt hq
    rw [ENNReal.toReal_one] at H
    linarith
  have hp1 : 1 < p := by
    rcases lt_or_eq_of_le hp with H | H
    · exact H
    · exfalso
      rw [← H] at hstrict
      simp only [inv_one, ENNReal.toReal_one, sub_self, mul_zero] at hstrict
      exact (not_lt_of_ge ENNReal.toReal_nonneg) hstrict
  have hradR : 2 * (n : ℝ) / ((n : ℝ) - 1) < q.toReal := by
    have H := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hqt).mpr hrad
    rwa [ENNReal.toReal_ofReal (by positivity)] at H
  have hline : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent p < q.toReal := by
    have H : 1 < (((n : ℝ) - 1) / ((n : ℝ) + 1)) *
        (1 - p.toReal⁻¹) * q.toReal := by
      apply (div_lt_iff₀ hqr).mp
      simpa only [ENNReal.toReal_inv, one_div] using hstrict
    by_cases hpt : p = ⊤
    · simp only [OAI.Analysis.Fourier.Restriction.conjugateExponent]
      rw [if_pos hpt, mul_one]
      simp only [hpt, ENNReal.toReal_top, inv_zero, sub_zero, mul_one] at H
      have H' := mul_lt_mul_of_pos_right H hnplus
      have he : ((((n : ℝ) - 1) / ((n : ℝ) + 1)) * q.toReal) *
          ((n : ℝ) + 1) = q.toReal * ((n : ℝ) - 1) := by
        field_simp
        <;> ring
      rw [one_mul, he] at H'
      exact (div_lt_iff₀ hnminus).mpr H'
    · have hpr : 1 < p.toReal :=
        OAI.Analysis.Fourier.Restriction.one_lt_toReal_of_one_lt hp1 hpt
      have hpr0 : 0 < p.toReal := by linarith
      have H' := mul_lt_mul_of_pos_right H (mul_pos hnplus hpr0)
      have he : ((((n : ℝ) - 1) / ((n : ℝ) + 1)) *
          (1 - p.toReal⁻¹) * q.toReal) * (((n : ℝ) + 1) * p.toReal) =
          q.toReal * ((n : ℝ) - 1) * (p.toReal - 1) := by
        field_simp
        <;> ring
      rw [one_mul, he] at H'
      simp only [OAI.Analysis.Fourier.Restriction.conjugateExponent]
      rw [if_neg hpt, div_mul_div_comm]
      apply (div_lt_iff₀ (mul_pos hnminus (sub_pos.mpr hpr))).mpr
      simpa only [mul_assoc] using H'
  have H := original_strict_target hn hp1 hradR hline
  simpa only [ENNReal.ofReal_toReal hqt] using H

end RestrictionWork
