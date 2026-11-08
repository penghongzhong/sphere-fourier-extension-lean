import OAI.Analysis.Fourier.Restriction.RadialModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
open Set
namespace RestrictionWork
open OAI.Analysis.Fourier.Restriction (radialOscillation radialOscillation_lipschitz)

/-- A nonzero sinusoid dominates a prescribed decaying error on a fixed
window of every sufficiently late period. -/
theorem oscillation_windows {A B C : ℝ} (hAB : 0 < A ^ 2 + B ^ 2) :
    ∃ s w a : ℝ, 1 ≤ s ∧ 0 < w ∧ w ≤ 2 * Real.pi ∧ 0 < a ∧
      ∀ k : ℕ, ∀ r ∈ Ioc (s + (k : ℝ) * (2 * Real.pi))
          (s + (k : ℝ) * (2 * Real.pi) + w),
        a + C / r ≤ |radialOscillation A B r| := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 < |radialOscillation A B t| := by
    by_cases hA : A = 0
    · refine ⟨Real.pi / 2, ?_⟩
      have hB : B ≠ 0 := by intro H; simp [hA, H] at hAB
      simpa [radialOscillation, hA] using abs_pos.mpr hB
    · exact ⟨0, by simpa [radialOscillation] using abs_pos.mpr hA⟩
  let P := 2 * Real.pi
  have hP : 0 < P := by dsimp [P]; positivity
  let m := |radialOscillation A B t|
  let L := |A| + |B|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let a := m / 4
  have ha : 0 < a := div_pos ht (by norm_num)
  let w := min P (a / (L + 1))
  have hL1 : 0 < L + 1 := by linarith
  have hw : 0 < w := lt_min hP (div_pos ha hL1)
  have hwP : w ≤ P := min_le_left _ _
  have hLw : L * w ≤ a := by
    have H := (le_div_iff₀ hL1).mp (min_le_right P (a / (L + 1)))
    change w * (L + 1) ≤ a at H
    nlinarith only [H, hw.le]
  obtain ⟨N, hN⟩ := exists_nat_gt ((max 1 (C / a) - t) / P)
  let s := t + (N : ℝ) * P
  have hs : max 1 (C / a) ≤ s := by
    have H := (div_lt_iff₀ hP).mp hN
    dsimp [s]
    linarith
  refine ⟨s, w, a, (le_max_left _ _).trans hs, hw, hwP, ha, ?_⟩
  intro k r hr
  let b := s + (k : ℝ) * P
  change b < r ∧ r ≤ b + w at hr
  have hb : s ≤ b := by
    dsimp [b]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hP.le)
  have hr1 : 1 ≤ r := (le_max_left 1 (C / a)).trans (hs.trans (hb.trans hr.1.le))
  have hCr : C / r ≤ a := by
    have H : C / a ≤ r := (le_max_right 1 (C / a)).trans (hs.trans (hb.trans hr.1.le))
    apply (div_le_iff₀ (by linarith : 0 < r)).mpr
    simpa only [mul_comm r a] using (div_le_iff₀ ha).mp H
  have hper : radialOscillation A B b = radialOscillation A B t := by
    have he : b = t + ((N + k : ℕ) : ℝ) * (2 * Real.pi) := by
      dsimp [b, s, P]
      push_cast
      ring
    rw [he]
    simp only [radialOscillation, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  have hd : |radialOscillation A B r - radialOscillation A B b| ≤ a := by
    apply (radialOscillation_lipschitz A B r b).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1.le)]
    exact (mul_le_mul_of_nonneg_left (by linarith [hr.2] : r - b ≤ w) hL).trans hLw
  have H := norm_sub_norm_le (radialOscillation A B b) (radialOscillation A B r)
  simp only [Real.norm_eq_abs] at H
  rw [abs_sub_comm, hper] at H
  rw [hper] at hd
  change m - |radialOscillation A B r| ≤ _ at H
  have hm : m = 4 * a := by dsimp [a]; ring
  linarith only [H, hd, hCr, hm, ha]

end RestrictionWork
