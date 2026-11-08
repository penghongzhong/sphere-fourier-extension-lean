import RestrictionWork.GraphWhitneyProjection
import RestrictionWork.WhitneyTruncationInterpolation
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter FourierTransform
open OAI.Analysis.Fourier.WavePackets
open scoped ENNReal Topology

namespace RestrictionWork

private theorem lintegral_count_pairs {d : ℕ} (j : ℕ)
    {F : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℝ≥0∞}
    (hF : ∀ p ∈ dyadicWhitneyPairs d j, Measurable (F p)) :
    let J := ↥(dyadicWhitneyPairs d j)
    (∫⁻ z : J × Ambient d, F z.1.val z.2 ∂Measure.count.prod volume) =
      ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x, F p x := by
  intro J
  rw [lintegral_prod _ (measurable_from_prod_countable_right (fun p => hF p.val p.property)).aemeasurable,
    lintegral_count, tsum_fintype]
  exact Finset.sum_coe_sort (dyadicWhitneyPairs d j) (fun p => ∫⁻ x, F p x)

private theorem integrable_kernel_mul_translate {d : ℕ} {k f : Ambient d → ℂ}
    (hk : Integrable k) (hf : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Ambient d) :
    Integrable (fun y => k y * f (x - y)) := by
  refine (hk.norm.mul_const M).mono' (hk.aestronglyMeasurable.mul
    (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
  filter_upwards [] with y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

set_option maxHeartbeats 1200000 in
private theorem graph_whitney_projection_integrable_moment {d : ℕ} {r : ℝ}
    (hr₁ : 1 < r) (hr₂ : r < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ)
      (F : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℂ),
      (∀ p ∈ dyadicWhitneyPairs d j, Measurable (F p)) →
      (∀ p ∈ dyadicWhitneyPairs d j, Integrable (F p)) →
      (∀ p ∈ dyadicWhitneyPairs d j, MemLp (F p) 2) →
      (∀ p ∈ dyadicWhitneyPairs d j, ∃ M : ℝ, ∀ x, ‖F p x‖ ≤ M) →
      (∫⁻ x, ‖graphWhitneyProjection j F x‖ₑ ^ r) ≤
        C * ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x, ‖F p x‖ₑ ^ r := by
  obtain ⟨C₁, hC₁, H₁⟩ := graph_whitney_projection_one (d := d)
  obtain ⟨_, _, HK⟩ := graph_whitney_cutoff_kernel_bound d
  let C₂ := ((7 ^ d * (2 * (2 * d + 2) + 1) ^ d : ℕ) : ℝ≥0∞)
  let C := (2 * C₁) * ENNReal.ofReal (r / (r - 1)) + (4 * C₂) * ENNReal.ofReal (r / (2 - r))
  have hC₂ : C₂ < ⊤ := (ENNReal.natCast_ne_top _).lt_top
  have hC : C < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC₁) ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC₂) ENNReal.ofReal_lt_top⟩
  refine ⟨C, hC, ?_⟩
  intro j F hF hFi hF₂ hFb
  let J := ↥(dyadicWhitneyPairs d j)
  let f : J × Ambient d → ℂ := fun z => F z.1.val z.2
  let μ := (Measure.count : Measure J).prod (volume : Measure (Ambient d))
  let : SFinite μ := by unfold μ; infer_instance
  have hf : Measurable f := measurable_from_prod_countable_right fun p => hF p.val p.property
  have hsum : (∫⁻ z, ‖f z‖ₑ ^ r ∂μ) =
      ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x, ‖F p x‖ₑ ^ r :=
    lintegral_count_pairs j (fun p hp => (hF p hp).enorm.pow_const r)
  rw [← hsum]
  apply whitney_moment_le_of_truncated_outputs μ volume hf
    (graph_whitney_projection_measurable j hF) hr₁ hr₂ (C₁ := C₁) (C₂ := C₂)
  intro t _ht
  let S (p : (Fin d → ℤ) × (Fin d → ℤ)) := {x | t < ‖F p x‖}
  let V (p : (Fin d → ℤ) × (Fin d → ℤ)) := (S p).indicator (F p)
  let W (p : (Fin d → ℤ) × (Fin d → ℤ)) := (S p)ᶜ.indicator (F p)
  have hS p (hp : p ∈ dyadicWhitneyPairs d j) : MeasurableSet (S p) :=
    measurableSet_lt measurable_const (hF p hp).norm
  have hV p hp : Measurable (V p) := (hF p hp).indicator (hS p hp)
  have hW p hp : Measurable (W p) := (hF p hp).indicator (hS p hp).compl
  refine ⟨graphWhitneyProjection j V, graphWhitneyProjection j W,
    graph_whitney_projection_measurable j hV, graph_whitney_projection_measurable j hW, ?_, ?_, ?_⟩
  · intro x
    unfold graphWhitneyProjection
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨M, hM⟩ := hFb p hp
    have hi := integrable_kernel_mul_translate (HK j p).1 (hV p hp)
      (fun x => (norm_indicator_le_norm_self _ _).trans (hM x)) x
    have hj := integrable_kernel_mul_translate (HK j p).1 (hW p hp)
      (fun x => (norm_indicator_le_norm_self _ _).trans (hM x)) x
    unfold complexConvolution
    rw [← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← mul_add]
    congr 1
    by_cases hx : x - y ∈ S p <;> simp [V, W, hx]
  · refine (H₁ j V hV).trans (mul_le_mul' le_rfl (le_of_eq ?_))
    rw [← lintegral_indicator (measurableSet_lt measurable_const hf.norm)]
    have h := lintegral_count_pairs j (fun p hp => (hV p hp).enorm)
    refine h.symm.trans (lintegral_congr ?_)
    intro z
    by_cases hz : z.2 ∈ S z.1.val
    · have ht : z ∈ {x | t < ‖f x‖} := hz
      rw [indicator_of_mem ht]
      change ‖(S z.1.val).indicator (F z.1.val) z.2‖ₑ = _
      rw [indicator_of_mem hz]
    · have ht : z ∉ {x | t < ‖f x‖} := hz
      rw [indicator_of_notMem ht]
      change ‖(S z.1.val).indicator (F z.1.val) z.2‖ₑ = _
      rw [indicator_of_notMem hz, enorm_zero]
  · refine (graph_whitney_projection_two j (fun p hp => (hFi p hp).indicator (hS p hp).compl)
      (fun p hp => (hF₂ p hp).indicator (hS p hp).compl)).trans (mul_le_mul' le_rfl (le_of_eq ?_))
    rw [← lintegral_indicator (measurableSet_le hf.norm measurable_const)]
    have h := lintegral_count_pairs j (fun p hp => (hW p hp).enorm.pow_const (2 : ℕ))
    refine h.symm.trans (lintegral_congr ?_)
    intro z
    by_cases hz : z.2 ∈ S z.1.val
    · have ht : t < ‖f z‖ := hz
      simp [W, hz, not_le.mpr ht]
    · have ht : ‖f z‖ ≤ t := le_of_not_gt hz
      simp [W, f, hz, ht]

set_option maxHeartbeats 1400000 in
/-- Strong same-layer moment bound for all bounded measurable test families
when the physical exponent lies strictly between one and two. -/
theorem graph_whitney_projection_moment_lt_two {d : ℕ} {r : ℝ}
    (hr₁ : 1 < r) (hr₂ : r < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ)
      (F : (Fin d → ℤ) × (Fin d → ℤ) → Ambient d → ℂ),
      (∀ p ∈ dyadicWhitneyPairs d j, Measurable (F p)) →
      (∀ p ∈ dyadicWhitneyPairs d j, ∃ M : ℝ, ∀ x, ‖F p x‖ ≤ M) →
      (∫⁻ x, ‖graphWhitneyProjection j F x‖ₑ ^ r) ≤
        C * ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x, ‖F p x‖ₑ ^ r := by
  obtain ⟨C, hC, H⟩ := graph_whitney_projection_integrable_moment (d := d) hr₁ hr₂
  obtain ⟨_, _, HK⟩ := graph_whitney_cutoff_kernel_bound d
  refine ⟨C, hC, ?_⟩
  intro j F hF hFb
  let B (n : ℕ) := Metric.ball (0 : Ambient d) (n : ℝ)
  let Fn (n : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) := (B n).indicator (F p)
  have hm n p hp : Measurable (Fn n p) := (hF p hp).indicator measurableSet_ball
  have hb n p (hp : p ∈ dyadicWhitneyPairs d j) : ∃ M : ℝ, ∀ x, ‖Fn n p x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hFb p hp
    exact ⟨M, fun x => (norm_indicator_le_norm_self _ _).trans (hM x)⟩
  have hLp n p (hp : p ∈ dyadicWhitneyPairs d j) (q : ℝ≥0∞) : MemLp (Fn n p) q := by
    change MemLp ((B n).indicator (F p)) q volume
    rw [memLp_indicator_iff_restrict measurableSet_ball]
    let : IsFiniteMeasure (volume.restrict (B n)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    obtain ⟨M, hM⟩ := hFb p hp
    exact MemLp.of_bound (hF p hp).aestronglyMeasurable M (.of_forall hM)
  have hpw (x : Ambient d) :
      Tendsto (fun n => graphWhitneyProjection j (Fn n) x) atTop
        (𝓝 (graphWhitneyProjection j F x)) := by
    unfold graphWhitneyProjection
    apply tendsto_finsetSum
    intro p hp
    let k := 𝓕⁻ (graphWhitneyCutoff j p)
    have hk := (HK j p).1
    obtain ⟨M, hM⟩ := hFb p hp
    unfold complexConvolution
    apply tendsto_integral_of_dominated_convergence (fun y => ‖k y‖ * M)
    · intro n
      exact hk.aestronglyMeasurable.mul
        ((hm n p hp).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact hk.norm.mul_const M
    · intro n
      filter_upwards [] with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((norm_indicator_le_norm_self _ _).trans (hM (x - y))) (norm_nonneg _)
    · filter_upwards [] with y
      have he : ∀ᶠ n : ℕ in atTop, x - y ∈ B n := by
        simpa only [B, Metric.mem_ball, dist_zero_right] using
          (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop ‖x - y‖)
      apply (tendsto_congr' (he.mono fun n hn => ?_)).mpr tendsto_const_nhds
      rw [show Fn n p (x - y) = F p (x - y) from indicator_of_mem hn _]
  have hbound n : (∫⁻ x, ‖graphWhitneyProjection j (Fn n) x‖ₑ ^ r) ≤
      C * ∑ p ∈ dyadicWhitneyPairs d j, ∫⁻ x, ‖F p x‖ₑ ^ r := by
    refine (H j (Fn n) (hm n) (fun p hp => memLp_one_iff_integrable.mp (hLp n p hp 1))
      (fun p hp => hLp n p hp 2) (hb n)).trans (mul_le_mul' le_rfl (Finset.sum_le_sum ?_))
    intro p _
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ B n <;> simp [Fn, hx, ENNReal.zero_rpow_of_pos (show 0 < r by linarith)]
  have hlim (x : Ambient d) :
      liminf (fun n => ‖graphWhitneyProjection j (Fn n) x‖ₑ ^ r) atTop =
        ‖graphWhitneyProjection j F x‖ₑ ^ r :=
    ((ENNReal.continuous_rpow_const.tendsto _).comp
      (continuous_enorm.tendsto _ |>.comp (hpw x))).liminf_eq
  simp_rw [← hlim]
  refine (lintegral_liminf_le (fun n =>
    (graph_whitney_projection_measurable j (hm n)).enorm.pow_const r)).trans ?_
  exact (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hbound))

end RestrictionWork
