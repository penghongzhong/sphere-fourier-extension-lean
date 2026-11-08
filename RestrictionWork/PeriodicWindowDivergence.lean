import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace RestrictionWork

/-- A positive reciprocal lower bound on equally spaced windows of fixed
width forces divergence, including the logarithmic endpoint. -/
theorem periodic_window_divergence {F : ℝ → ℝ≥0∞} {s P w c : ℝ}
    (hs : 0 < s) (hw : 0 < w) (hwP : w ≤ P) (hc : 0 < c)
    (hlower : ∀ k : ℕ, ∀ r ∈ Ioc (s + (k : ℝ) * P) (s + (k : ℝ) * P + w),
      ENNReal.ofReal (c / r) ≤ F r) :
    (∫⁻ r in Ioi (0 : ℝ), F r) = ⊤ := by
  let S : ℕ → Set ℝ := fun k ↦ Ioc (s + (k : ℝ) * P) (s + (k : ℝ) * P + w)
  have hP : 0 < P := hw.trans_le hwP
  have hmeas (k : ℕ) : MeasurableSet (S k) := measurableSet_Ioc
  have horder {i j : ℕ} (hij : i < j) : Disjoint (S i) (S j) := by
    refine Set.disjoint_left.mpr fun r hi hj ↦ ?_
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have hmul := mul_le_mul_of_nonneg_right hcast hP.le
    change s + (i : ℝ) * P < r ∧ r ≤ s + (i : ℝ) * P + w at hi
    change s + (j : ℝ) * P < r ∧ r ≤ s + (j : ℝ) * P + w at hj
    nlinarith only [hmul, hi.2, hj.1, hwP]
  have hdisj : Pairwise (Disjoint on S) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with H | H
    · exact horder H
    · exact (horder H).symm
  have hpos {k : ℕ} {r : ℝ} (hr : r ∈ S k) : 0 < r := by
    have H : s + (k : ℝ) * P < r := hr.1
    nlinarith only [hs, H, mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hP.le]
  have hsub : (⋃ k, S k) ⊆ Ioi (0 : ℝ) := by
    intro r hr
    obtain ⟨k, hk⟩ := mem_iUnion.mp hr
    exact hpos hk
  let D := s + P + w
  have hD : 0 < D := by dsimp [D]; positivity
  have hcap {k : ℕ} {r : ℝ} (hr : r ∈ S k) : r ≤ D * ((k : ℝ) + 1) := by
    have H : r ≤ s + (k : ℝ) * P + w := hr.2
    dsimp [D]
    nlinarith only [H, hP.le, mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      (add_nonneg hs.le hw.le)]
  have hmass (k : ℕ) : ENNReal.ofReal (c * w / D) *
      ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ ∫⁻ r in S k, F r := by
    calc
      _ = ENNReal.ofReal (c / (D * ((k : ℝ) + 1))) * ENNReal.ofReal w := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      _ = ∫⁻ _ in S k, ENNReal.ofReal (c / (D * ((k : ℝ) + 1))) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        have H : volume (S k) = ENNReal.ofReal w := by
          dsimp [S]
          rw [Real.volume_Ioc]
          congr 1
          ring
        rw [H]
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (hmeas k)] with r hr
        exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hc.le (hpos hr)
          (hcap hr))).trans (hlower k r hr)
  have hharmonic : (∑' k : ℕ, ENNReal.ofReal (1 / ((k : ℝ) + 1))) = ⊤ := by
    by_contra H
    let a : ℕ → ℝ≥0 := fun k ↦ ((1 : ℝ) / ((k : ℝ) + 1)).toNNReal
    have ha : (∑' k, (a k : ℝ≥0∞)) ≠ ⊤ := by
      simpa only [a, ENNReal.ofReal] using H
    have hsum := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp ha
    apply Real.not_summable_one_div_natCast
    apply (summable_nat_add_iff (f := fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) 1).mp
    simpa only [a, Real.coe_toNNReal _ (by positivity : 0 ≤ (1 : ℝ) / ((_ : ℕ) + 1)),
      Nat.cast_add, Nat.cast_one] using hsum
  apply top_unique
  calc
    ⊤ = ∑' k : ℕ, ENNReal.ofReal (c * w / D) * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      rw [ENNReal.tsum_mul_left, hharmonic, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    _ ≤ ∑' k, ∫⁻ r in S k, F r := ENNReal.tsum_le_tsum hmass
    _ = ∫⁻ r in ⋃ k, S k, F r := (lintegral_iUnion hmeas hdisj F).symm
    _ ≤ _ := lintegral_mono_set hsub

end RestrictionWork
