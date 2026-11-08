import RestrictionWork.PhaseExtensionDefinitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace Interval
namespace RestrictionWork

/-- Insertion of one real coordinate, with product Lebesgue measure. -/
def euclideanSliceEquiv {d : ℕ} (i : Fin (d + 1)) : Ambient d × ℝ ≃ᵐ Ambient (d + 1) :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
      (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodComm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) i).symm.trans
      (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)))

theorem euclidean_slice_measure_preserving {d : ℕ} (i : Fin (d + 1)) :
    MeasurePreserving (euclideanSliceEquiv i) volume volume := by
  have h1 := (PiLp.volume_preserving_ofLp (Fin d)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have h2 : MeasurePreserving (Prod.swap : ((Fin d → ℝ) × ℝ) → ℝ × (Fin d → ℝ))
      volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure (Fin d → ℝ)))
        (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) i).symm
  exact (PiLp.volume_preserving_toLp (Fin (d + 1))).comp (h3.comp (h2.comp h1))

theorem euclidean_slice_apply {d : ℕ} (i : Fin (d + 1)) (v : Ambient d) (s : ℝ) :
    euclideanSliceEquiv i (v, s) =
      WithLp.toLp 2 (i.insertNth s (WithLp.ofLp v)) := rfl

theorem euclidean_slice_affine {d : ℕ} (i : Fin (d + 1)) (v : Ambient d) (s : ℝ) :
    euclideanSliceEquiv i (v, s) =
      euclideanSliceEquiv i (v, 0) + s • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  induction j using i.succAboveCases with
  | x =>
    simp [euclidean_slice_apply]
  | p j =>
    simp [euclidean_slice_apply, Fin.succAbove_ne]

theorem euclidean_slice_norm_sq {d : ℕ} (i : Fin (d + 1)) (v : Ambient d) (s : ℝ) :
    ‖euclideanSliceEquiv i (v, s)‖ ^ 2 = ‖v‖ ^ 2 + s ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succAbove _ i]
  simp [euclidean_slice_apply, add_comm]

def ballSliceRadius {d : ℕ} (v : Ambient d) : ℝ := Real.sqrt (1 - ‖v‖ ^ 2)

theorem euclidean_slice_mem_ball {d : ℕ} (i : Fin (d + 1)) (v : Ambient d) (s : ℝ) :
    euclideanSliceEquiv i (v, s) ∈ Metric.ball 0 1 ↔
      s ∈ Ioo (-ballSliceRadius v) (ballSliceRadius v) := by
  rw [Metric.mem_ball, dist_zero_right,
    ← sq_lt_sq₀ (norm_nonneg (euclideanSliceEquiv i (v, s))) (by norm_num : (0 : ℝ) ≤ 1),
    euclidean_slice_norm_sq]
  by_cases hv : ‖v‖ < 1
  · have hpos : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
    have hr : ballSliceRadius v ^ 2 = 1 - ‖v‖ ^ 2 := Real.sq_sqrt hpos
    have hn : 0 ≤ ballSliceRadius v := Real.sqrt_nonneg _
    rw [mem_Ioo, ← abs_lt, ← sq_lt_sq₀ (abs_nonneg s) hn, sq_abs, hr]
    constructor <;> intro h <;> nlinarith only [h]
  · have hnon : 1 - ‖v‖ ^ 2 ≤ 0 := by nlinarith [le_of_not_gt hv, norm_nonneg v]
    have he : ballSliceRadius v = 0 := Real.sqrt_eq_zero_of_nonpos hnon
    rw [he, neg_zero, Ioo_self]
    simp only [mem_empty_iff_false, iff_false]
    nlinarith [sq_nonneg s]

theorem euclidean_slice_norm_le_one {d : ℕ} (i : Fin (d + 1)) {v : Ambient d} {s : ℝ}
    (hv : v ∈ Metric.ball (0 : Ambient d) 1)
    (hs : s ∈ Icc (-ballSliceRadius v) (ballSliceRadius v)) :
    ‖euclideanSliceEquiv i (v, s)‖ ≤ 1 := by
  have hv' : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hv
  have hr : ballSliceRadius v ^ 2 = 1 - ‖v‖ ^ 2 :=
    Real.sq_sqrt (by nlinarith [norm_nonneg v])
  have hs' : s ^ 2 ≤ ballSliceRadius v ^ 2 := by
    have hrnon : 0 ≤ ballSliceRadius v := Real.sqrt_nonneg _
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hrnon).mpr (abs_le.mpr hs)
  rw [← sq_le_sq₀ (norm_nonneg (euclideanSliceEquiv i (v, s))) (by norm_num : (0 : ℝ) ≤ 1),
    euclidean_slice_norm_sq]
  linarith

/-- Fubini in an arbitrary coordinate of the actual Euclidean unit ball. -/
theorem euclidean_ball_integral_slices {d : ℕ} (i : Fin (d + 1))
    {f : Ambient (d + 1) → ℂ} (hf : Integrable f (patchMeasure (d + 1))) :
    (∫ u, f u ∂patchMeasure (d + 1)) =
      ∫ v, (∫ s in -ballSliceRadius v..ballSliceRadius v,
        f (euclideanSliceEquiv i (v, s))) ∂patchMeasure d := by
  let B := Metric.ball (0 : Ambient (d + 1)) 1
  let F := B.indicator f
  let e := euclideanSliceEquiv i
  have he := euclidean_slice_measure_preserving i
  have hF : Integrable F := (integrable_indicator_iff measurableSet_ball).mpr hf
  have hFe : Integrable (fun x : Ambient d × ℝ => F (e x))
      ((volume : Measure (Ambient d)).prod volume) :=
    (he.integrable_comp_emb e.measurableEmbedding).2 hF
  change (∫ u in B, f u) = _
  rw [← integral_indicator measurableSet_ball]
  change (∫ u, F u) = _
  rw [← he.integral_comp' F, Measure.volume_eq_prod (Ambient d) ℝ]
  change (∫ p, F (e p) ∂((volume : Measure (Ambient d)).prod volume)) = _
  rw [integral_prod _ hFe]
  unfold patchMeasure
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with v
  have hpoint : (fun s : ℝ => F (e (v, s))) =
      (Ioo (-ballSliceRadius v) (ballSliceRadius v)).indicator
        (fun s => f (e (v, s))) := by
    funext s
    have H : e (v, s) ∈ B ↔ s ∈ Ioo (-ballSliceRadius v) (ballSliceRadius v) :=
      euclidean_slice_mem_ball i v s
    by_cases hs : s ∈ Ioo (-ballSliceRadius v) (ballSliceRadius v)
    · rw [show F (e (v, s)) = f (e (v, s)) from indicator_of_mem (H.mpr hs) _,
        indicator_of_mem hs]
    · rw [show F (e (v, s)) = 0 from indicator_of_notMem (mt H.mp hs) _,
        indicator_of_notMem hs]
  have hinterval : -ballSliceRadius v ≤ ballSliceRadius v :=
    neg_le_self (Real.sqrt_nonneg _)
  rw [hpoint, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hinterval]
  by_cases hv : v ∈ Metric.ball (0 : Ambient d) 1
  · rw [indicator_of_mem hv]
  · rw [indicator_of_notMem hv]
    have hnorm : 1 ≤ ‖v‖ := le_of_not_gt (by simpa [Metric.mem_ball, dist_zero_right] using hv)
    have hrad : ballSliceRadius v = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith)
    simp [hrad]

theorem exists_euclidean_large_coordinate {d : ℕ} (y : Ambient (d + 1)) :
    ∃ i : Fin (d + 1), ‖y‖ ≤ ((d : ℝ) + 1) * |y i| := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (d + 1)))
    (fun j => |y j|) Finset.univ_nonempty
  refine ⟨i, (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow]
  calc
    _ ≤ ∑ _ : Fin (d + 1), |y i| ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (hi j hj)
    _ = ((d : ℝ) + 1) * |y i| ^ 2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [Nat.cast_nonneg (α := ℝ) d]

end RestrictionWork
