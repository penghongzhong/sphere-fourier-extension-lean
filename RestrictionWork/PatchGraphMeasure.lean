import RestrictionWork.EuclideanBallSlices
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

/-- The graph over the actual unit parameter ball, pushed into Euclidean
frequency space with its parameter measure. -/
def patchGraphMeasure {d : ℕ} (φ : Ambient d → ℝ) : Measure (Ambient (d + 1)) :=
  (patchMeasure d).map (fun v => euclideanSliceEquiv (Fin.last d) (v, φ v))

theorem euclidean_slice_sub {d : ℕ} (i : Fin (d + 1)) (v u : Ambient d) (s t : ℝ) :
    euclideanSliceEquiv i (v, s) - euclideanSliceEquiv i (u, t) =
      euclideanSliceEquiv i (v - u, s - t) := by
  apply PiLp.ext
  intro j
  induction j using i.succAboveCases with
  | x => simp [euclidean_slice_apply]
  | p j => simp [euclidean_slice_apply]

theorem euclidean_slice_inner {d : ℕ} (i : Fin (d + 1)) (v u : Ambient d) (s t : ℝ) :
    ⟪euclideanSliceEquiv i (v, s), euclideanSliceEquiv i (u, t)⟫ = ⟪v, u⟫ + s * t := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succAbove _ i]
  simp [euclidean_slice_apply, RCLike.inner_apply, mul_comm, add_comm]

theorem euclidean_slice_norm_le_product {d : ℕ} (i : Fin (d + 1)) (z : Ambient d × ℝ) :
    ‖euclideanSliceEquiv i z‖ ≤ 2 * ‖z‖ := by
  have hv : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have ht : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖euclideanSliceEquiv i (z.1, z.2)‖ ^ 2 ≤ (2 * ‖z‖) ^ 2
  rw [euclidean_slice_norm_sq]
  have h1 := (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg z)).mpr hv
  have h2 := (sq_le_sq₀ (norm_nonneg z.2) (norm_nonneg z)).mpr ht
  rw [Real.norm_eq_abs, sq_abs] at h2
  nlinarith only [h1, h2, sq_nonneg ‖z‖]

/-- The mass growth needed for the sparse-ball argument, with a constant
independent of the graph function. -/
theorem patch_graph_measure_ball_upper {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    (x : Ambient (d + 1)) {R : ℝ} (hR : 0 < R) :
    patchGraphMeasure φ (Metric.ball x R) ≤
      ENNReal.ofReal (R ^ d) * volume (Metric.ball (0 : Ambient d) 1) := by
  let e := euclideanSliceEquiv (Fin.last d)
  let z := e.symm x
  let G : Ambient d → Ambient (d + 1) := fun v => e (v, φ v)
  have hG : Measurable G := e.measurable.comp (measurable_id.prodMk hφ)
  have hx : e (z.1, z.2) = x := e.apply_symm_apply x
  have hproj : G ⁻¹' Metric.ball x R ⊆ Metric.ball z.1 R := by
    intro v hv
    have H : ‖G v - x‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hv
    have hdiff : ‖G v - x‖ ^ 2 = ‖v - z.1‖ ^ 2 + (φ v - z.2) ^ 2 := by
      rw [← hx]
      change ‖euclideanSliceEquiv (Fin.last d) (v, φ v) -
        euclideanSliceEquiv (Fin.last d) (z.1, z.2)‖ ^ 2 = _
      rw [euclidean_slice_sub, euclidean_slice_norm_sq]
    have hle : ‖v - z.1‖ ≤ ‖G v - x‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [hdiff]
      exact le_add_of_nonneg_right (sq_nonneg _)
    simpa [Metric.mem_ball, dist_eq_norm] using hle.trans_lt H
  change (patchMeasure d).map G (Metric.ball x R) ≤ _
  rw [Measure.map_apply hG measurableSet_ball]
  calc
    _ ≤ (patchMeasure d) (Metric.ball z.1 R) := measure_mono hproj
    _ ≤ volume (Metric.ball z.1 R) := Measure.restrict_apply_le _ _
    _ = _ := by
      rw [Measure.addHaar_ball_of_pos volume z.1 hR]
      simp only [Ambient, finrank_euclideanSpace_fin]

/-- Exact agreement between the pushed-forward kernel and the graph integral. -/
theorem patch_graph_measure_integral {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    (z : Ambient d × ℝ) :
    (∫ x, Complex.exp ((⟪euclideanSliceEquiv (Fin.last d) z, x⟫ : ℝ) * Complex.I)
      ∂patchGraphMeasure φ) = graphExtension (fun _ => 1) φ z := by
  let e := euclideanSliceEquiv (Fin.last d)
  let G : Ambient d → Ambient (d + 1) := fun v => e (v, φ v)
  have hG : Measurable G := e.measurable.comp (measurable_id.prodMk hφ)
  have hf : Measurable (fun x : Ambient (d + 1) =>
      Complex.exp ((⟪e z, x⟫ : ℝ) * Complex.I)) := by fun_prop
  change (∫ x, Complex.exp ((⟪e z, x⟫ : ℝ) * Complex.I) ∂(patchMeasure d).map G) = _
  rw [integral_map hG.aemeasurable hf.aestronglyMeasurable]
  unfold graphExtension phaseExtension
  simp only [one_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  change Complex.exp ((⟪e (z.1, z.2), e (v, φ v)⟫ : ℝ) * Complex.I) = _
  rw [euclidean_slice_inner]

end RestrictionWork
