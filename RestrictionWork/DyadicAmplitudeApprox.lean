import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Data.Int.Interval

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace RestrictionWork

/-- The part of the support on which the amplitude lies in one half-open
dyadic interval. -/
def dyadicAmplitudeSet {X : Type*} (S : Set X) (f : X → ℂ) (k : ℤ) : Set X :=
  S ∩ {x | (2 : ℝ) ^ k ≤ ‖f x‖ ∧ ‖f x‖ < (2 : ℝ) ^ (k + 1)}

def dyadicAmplitudePiece {X : Type*} (S : Set X) (f : X → ℂ) (k : ℤ) : X → ℂ :=
  (dyadicAmplitudeSet S f k).indicator f

def dyadicAmplitudeTrunc {X : Type*} (S : Set X) (f : X → ℂ) (N : ℕ) (x : X) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), dyadicAmplitudePiece S f k x

theorem measurableSet_dyadic_amplitude_set {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) {f : X → ℂ} (hf : Measurable f) (k : ℤ) :
    MeasurableSet (dyadicAmplitudeSet S f k) :=
  hS.inter ((measurableSet_le measurable_const hf.norm).inter
    (measurableSet_lt hf.norm measurable_const))

theorem pairwise_disjoint_dyadic_amplitude_set {X : Type*} (S : Set X) (f : X → ℂ) :
    Pairwise (fun j k => Disjoint (dyadicAmplitudeSet S f j) (dyadicAmplitudeSet S f k)) := by
  have H : ∀ ⦃j k : ℤ⦄, j < k → Disjoint (dyadicAmplitudeSet S f j) (dyadicAmplitudeSet S f k) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro x hj hk
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : j + 1 ≤ k)
    exact (hj.2.2.trans_le (h.trans hk.2.1)).false
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact H h
  · exact (H h).symm

theorem measurable_dyadic_amplitude_piece {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) {f : X → ℂ} (hf : Measurable f) (k : ℤ) :
    Measurable (dyadicAmplitudePiece S f k) :=
  hf.indicator (measurableSet_dyadic_amplitude_set hS hf k)

theorem norm_dyadic_amplitude_piece_le {X : Type*} (S : Set X) (f : X → ℂ)
    (k : ℤ) (x : X) :
    ‖dyadicAmplitudePiece S f k x‖ ≤
      (dyadicAmplitudeSet S f k).indicator (fun _ => (2 : ℝ) ^ (k + 1)) x := by
  by_cases hx : x ∈ dyadicAmplitudeSet S f k
  · simpa [dyadicAmplitudePiece, indicator_of_mem hx] using hx.2.2.le
  · simp [dyadicAmplitudePiece, indicator_of_notMem hx]

theorem dyadic_amplitude_sum_eq_indicator {X : Type*} (S : Set X) (f : X → ℂ)
    (I : Finset ℤ) (x : X) :
    (∑ k ∈ I, dyadicAmplitudePiece S f k x) =
      (⋃ k ∈ I, dyadicAmplitudeSet S f k).indicator f x := by
  classical
  by_cases hx : x ∈ ⋃ k ∈ I, dyadicAmplitudeSet S f k
  · obtain ⟨k, hk, hmem⟩ := mem_iUnion₂.mp hx
    rw [indicator_of_mem hx, Finset.sum_eq_single_of_mem k hk]
    · exact indicator_of_mem hmem _
    · intro j _ hj
      have hd := pairwise_disjoint_dyadic_amplitude_set S f hj
      exact indicator_of_notMem (fun h => disjoint_left.mp hd h hmem) _
  · rw [indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro k hk
    exact indicator_of_notMem (fun h => hx (mem_iUnion₂.mpr ⟨k, hk, h⟩)) _

theorem measurable_dyadic_amplitude_trunc {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) {f : X → ℂ} (hf : Measurable f) (N : ℕ) :
    Measurable (dyadicAmplitudeTrunc S f N) :=
  Finset.measurable_fun_sum _ (fun k _ => measurable_dyadic_amplitude_piece hS hf k)

theorem norm_dyadic_amplitude_trunc_le {X : Type*} (S : Set X) (f : X → ℂ)
    (N : ℕ) (x : X) : ‖dyadicAmplitudeTrunc S f N x‖ ≤ ‖f x‖ := by
  unfold dyadicAmplitudeTrunc
  rw [dyadic_amplitude_sum_eq_indicator]
  exact norm_indicator_le_norm_self _ _

/-- The finite truncation eventually includes the unique amplitude band of
each nonzero point of the support. -/
theorem tendsto_dyadic_amplitude_trunc {X : Type*} (S : Set X) (f : X → ℂ)
    (x : X) :
    Tendsto (fun N : ℕ => dyadicAmplitudeTrunc S f N x) atTop (𝓝 (S.indicator f x)) := by
  apply tendsto_const_nhds.congr'
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS]
    by_cases hx : f x = 0
    · filter_upwards [] with N
      rw [dyadicAmplitudeTrunc, dyadic_amplitude_sum_eq_indicator]
      by_cases hmem : x ∈ ⋃ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), dyadicAmplitudeSet S f k
      · rw [indicator_of_mem hmem]
      · rw [indicator_of_notMem hmem, hx]
    · obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr hx) (by norm_num : (1 : ℝ) < 2)
      refine eventually_atTop.mpr ⟨k.natAbs, fun N hN => ?_⟩
      have hkI : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        rw [Finset.mem_Icc]
        omega
      have hmem : x ∈ ⋃ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), dyadicAmplitudeSet S f k :=
        mem_iUnion₂.mpr ⟨k, hkI, hxS, hk⟩
      change f x = dyadicAmplitudeTrunc S f N x
      rw [dyadicAmplitudeTrunc, dyadic_amplitude_sum_eq_indicator, indicator_of_mem hmem]
  · rw [indicator_of_notMem hxS]
    filter_upwards [] with N
    rw [dyadicAmplitudeTrunc, dyadic_amplitude_sum_eq_indicator, indicator_of_notMem]
    intro hx
    obtain ⟨k, _, hk⟩ := mem_iUnion₂.mp hx
    exact hxS hk.1

/-- The lower dyadic amplitude times the band mass is bounded by the
corresponding portion of the actual input moment. -/
theorem dyadic_amplitude_mass_sum_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S) {f : X → ℂ} (hf : Measurable f)
    (I : Finset ℤ) {p : ℝ} (hp : 0 ≤ p) :
    (∑ k ∈ I, ENNReal.ofReal ((2 : ℝ) ^ k) ^ p * μ (dyadicAmplitudeSet S f k)) ≤
      ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  calc
    _ ≤ ∑ k ∈ I, ∫⁻ x in dyadicAmplitudeSet S f k, ‖f x‖ₑ ^ p ∂μ := by
      apply Finset.sum_le_sum
      intro k _
      rw [← setLIntegral_const]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_dyadic_amplitude_set hS hf k)] with x hx
      rw [← ofReal_norm]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx.2.1) hp
    _ = ∫⁻ x in ⋃ k ∈ I, dyadicAmplitudeSet S f k, ‖f x‖ₑ ^ p ∂μ := by
      rw [lintegral_biUnion_finset
        (fun _ _ _ _ h => pairwise_disjoint_dyadic_amplitude_set S f h)
        (fun k _ => measurableSet_dyadic_amplitude_set hS hf k)]
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

end RestrictionWork
