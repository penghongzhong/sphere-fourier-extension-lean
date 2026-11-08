import RestrictionWork.GraphExtensionContinuous
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace RestrictionWork

private def graphPhaseFactor {d : ℕ} (φ : Ambient d → ℝ) (z : Ambient d × ℝ)
    (u : Ambient d) : ℂ :=
  Complex.exp (((inner ℝ z.1 u + z.2 * φ u : ℝ) : ℂ) * Complex.I)

private theorem graph_phase_factor_norm {d : ℕ} (φ : Ambient d → ℝ)
    (z : Ambient d × ℝ) (u : Ambient d) : ‖graphPhaseFactor φ z u‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem graph_phase_factor_measurable {d : ℕ} {φ : Ambient d → ℝ}
    (hφ : Measurable φ) (z : Ambient d × ℝ) :
    Measurable (graphPhaseFactor φ z) := by
  unfold graphPhaseFactor
  fun_prop

theorem graph_extension_norm_le_integral_norm {d : ℕ} (f : Ambient d → ℂ)
    (φ : Ambient d → ℝ) (z : Ambient d × ℝ) :
    ‖graphExtension f φ z‖ ≤ ∫ u, ‖f u‖ ∂patchMeasure d := by
  change ‖∫ u, f u * graphPhaseFactor φ z u ∂patchMeasure d‖ ≤ _
  simpa only [norm_mul, graph_phase_factor_norm, mul_one] using
    (norm_integral_le_integral_norm (μ := patchMeasure d) (fun u => f u * graphPhaseFactor φ z u))

theorem graph_extension_const_mul {d : ℕ} (c : ℂ) (f : Ambient d → ℂ)
    (φ : Ambient d → ℝ) (z : Ambient d × ℝ) :
    graphExtension (fun u => c * f u) φ z = c * graphExtension f φ z := by
  change (∫ u, (c * f u) * graphPhaseFactor φ z u ∂patchMeasure d) =
    c * ∫ u, f u * graphPhaseFactor φ z u ∂patchMeasure d
  simp only [mul_assoc, integral_const_mul]

theorem graph_extension_congr_ae {d : ℕ} {f g : Ambient d → ℂ}
    (hfg : f =ᵐ[patchMeasure d] g) (φ : Ambient d → ℝ) (z : Ambient d × ℝ) :
    graphExtension f φ z = graphExtension g φ z := by
  unfold graphExtension phaseExtension
  apply integral_congr_ae
  filter_upwards [hfg] with u hu
  rw [hu]

theorem graph_extension_finsetSum {d : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → Ambient d → ℂ} (hf : ∀ i ∈ s, Integrable (f i) (patchMeasure d))
    {φ : Ambient d → ℝ} (hφ : Measurable φ) (z : Ambient d × ℝ) :
    graphExtension (fun u => ∑ i ∈ s, f i u) φ z = ∑ i ∈ s, graphExtension (f i) φ z := by
  change (∫ u, (∑ i ∈ s, f i u) * graphPhaseFactor φ z u ∂patchMeasure d) =
    ∑ i ∈ s, ∫ u, f i u * graphPhaseFactor φ z u ∂patchMeasure d
  simp_rw [Finset.sum_mul]
  apply integral_finsetSum
  intro i hi
  refine (hf i hi).mono ((hf i hi).aestronglyMeasurable.mul
    (graph_phase_factor_measurable hφ z).aestronglyMeasurable) ?_
  filter_upwards [] with u
  simp only [norm_mul, graph_phase_factor_norm, mul_one, le_refl]

theorem graph_extension_tendsto_of_dominated {d : ℕ} {f : Ambient d → ℂ}
    (hf : Integrable f (patchMeasure d)) {F : ℕ → Ambient d → ℂ}
    (hF : ∀ n, AEStronglyMeasurable (F n) (patchMeasure d))
    (hbound : ∀ n u, ‖F n u‖ ≤ ‖f u‖)
    (hlim : ∀ u, Tendsto (fun n => F n u) atTop (𝓝 (f u)))
    {φ : Ambient d → ℝ} (hφ : Measurable φ) (z : Ambient d × ℝ) :
    Tendsto (fun n => graphExtension (F n) φ z) atTop (𝓝 (graphExtension f φ z)) := by
  change Tendsto (fun n => ∫ u, F n u * graphPhaseFactor φ z u ∂patchMeasure d) atTop
    (𝓝 (∫ u, f u * graphPhaseFactor φ z u ∂patchMeasure d))
  apply tendsto_integral_of_dominated_convergence (fun u => ‖f u‖)
  · exact fun n => (hF n).mul (graph_phase_factor_measurable hφ z).aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact .of_forall fun u => by
      simpa only [norm_mul, graph_phase_factor_norm, mul_one] using hbound n u
  · exact .of_forall fun u => (hlim u).mul_const _

/-- Pointwise dominated approximation on each side of the extension pairing. -/
theorem graph_extension_pairing_tendsto {d : ℕ} {f : Ambient d → ℂ}
    (hf : Integrable f (patchMeasure d)) {F : ℕ → Ambient d → ℂ}
    (hF : ∀ n, AEStronglyMeasurable (F n) (patchMeasure d))
    (hFb : ∀ n u, ‖F n u‖ ≤ ‖f u‖)
    (hFl : ∀ u, Tendsto (fun n => F n u) atTop (𝓝 (f u)))
    {g : Ambient d × ℝ → ℂ} (hg : Integrable g) {G : ℕ → Ambient d × ℝ → ℂ}
    (hG : ∀ n, AEStronglyMeasurable (G n) volume) (hGb : ∀ n z, ‖G n z‖ ≤ ‖g z‖)
    (hGl : ∀ z, Tendsto (fun n => G n z) atTop (𝓝 (g z)))
    {φ : Ambient d → ℝ} (hφ : Measurable φ) :
    Tendsto (fun n => ∫ z, G n z * graphExtension (F n) φ z) atTop
      (𝓝 (∫ z, g z * graphExtension f φ z)) := by
  let M := ∫ u, ‖f u‖ ∂patchMeasure d
  have hFi n : Integrable (F n) (patchMeasure d) := hf.mono (hF n) (.of_forall (hFb n))
  have hM (n : ℕ) (z : Ambient d × ℝ) : ‖graphExtension (F n) φ z‖ ≤ M :=
    (graph_extension_norm_le_integral_norm (F n) φ z).trans
      (integral_mono (hFi n).norm hf.norm (hFb n))
  apply tendsto_integral_of_dominated_convergence (fun z => ‖g z‖ * M)
  · exact fun n => (hG n).mul (graph_extension_continuous (hFi n) hφ).aestronglyMeasurable
  · exact hg.norm.mul_const M
  · intro n
    exact .of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul (hGb n z) (hM n z) (norm_nonneg _) (norm_nonneg _)
  · exact .of_forall fun z => (hGl z).mul
      (graph_extension_tendsto_of_dominated hf hF hFb hFl hφ z)

/-- The finite input and test decompositions expand the actual pairing. -/
theorem graph_extension_pairing_finset_le {d : ℕ} {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) {f : ι → Ambient d → ℂ}
    {g : κ → Ambient d × ℝ → ℂ}
    (hf : ∀ i ∈ I, Integrable (f i) (patchMeasure d))
    (hg : ∀ k ∈ J, Integrable (g k)) {φ : Ambient d → ℝ} (hφ : Measurable φ) :
    ‖∫ z, (∑ k ∈ J, g k z) * graphExtension (fun u => ∑ i ∈ I, f i u) φ z‖ₑ ≤
      ∑ i ∈ I, ∑ k ∈ J, ‖∫ z, g k z * graphExtension (f i) φ z‖ₑ := by
  have hi i (hi : i ∈ I) k (hk : k ∈ J) :
      Integrable (fun z => g k z * graphExtension (f i) φ z) := by
    refine ((hg k hk).norm.mul_const (∫ u, ‖f i u‖ ∂patchMeasure d)).mono'
      ((hg k hk).aestronglyMeasurable.mul (graph_extension_continuous (hf i hi) hφ).aestronglyMeasurable) ?_
    filter_upwards [] with z
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (graph_extension_norm_le_integral_norm (f i) φ z) (norm_nonneg _)
  simp_rw [graph_extension_finsetSum I hf hφ, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum I (fun i h => integrable_finsetSum J (hi i h))]
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i h
  rw [integral_finsetSum J (hi i h)]
  exact enorm_sum_le _ _

end RestrictionWork
