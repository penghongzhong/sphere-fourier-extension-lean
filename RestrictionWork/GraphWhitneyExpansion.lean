import RestrictionWork.DyadicWhitneyPairs
import RestrictionWork.GraphExtensionContinuous
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Function
open scoped RealInnerProductSpace

namespace RestrictionWork

/-- A finite sum of products of the actual cell-restricted graph extensions. -/
def graphWhitneyLayer {d : ℕ} (j : ℕ) (φ : Ambient d → ℝ)
    (f g : Ambient d → ℂ) (z : Ambient d × ℝ) : ℂ :=
  ∑ p ∈ dyadicWhitneyPairs d j,
    graphExtension ((dyadicParameterCell (j + 1) p.1).indicator f) φ z *
      graphExtension ((dyadicParameterCell (j + 1) p.2).indicator g) φ z

theorem ae_mem_iUnion_dyadic_whitney_regions (d : ℕ) (hd : 1 ≤ d) :
    ∀ᵐ w ∂(patchMeasure d).prod (patchMeasure d), w ∈ ⋃ j, dyadicWhitneyRegion d j := by
  let : NeZero d := ⟨by omega⟩
  let : SFinite (patchMeasure d) := by unfold patchMeasure; infer_instance
  have hmem : ∀ᵐ u ∂patchMeasure d, u ∈ Metric.ball (0 : Ambient d) 1 :=
    ae_restrict_mem measurableSet_ball
  have hmeas : MeasurableSet (⋃ j, dyadicWhitneyRegion d j) :=
    MeasurableSet.iUnion (measurable_dyadic_whitney_region d)
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [hmem] with u hu
  have hne : ∀ᵐ v ∂patchMeasure d, v ≠ u := by
    unfold patchMeasure
    exact (volume.restrict (Metric.ball (0 : Ambient d) 1)).ae_ne u
  filter_upwards [hmem, hne] with v hv hvu
  exact mem_iUnion_dyadic_whitney_regions_of_patch hu hv hvu.symm

private def oscillatoryData {d : ℕ} (φ : Ambient d → ℝ) (z : Ambient d × ℝ)
    (f : Ambient d → ℂ) (u : Ambient d) : ℂ :=
  f u * Complex.exp (((⟪z.1, u⟫ + z.2 * φ u : ℝ) : ℂ) * Complex.I)

private theorem integrable_oscillatory_data {d : ℕ} {φ : Ambient d → ℝ}
    (hφ : Measurable φ) (z : Ambient d × ℝ) {f : Ambient d → ℂ}
    (hf : Integrable f (patchMeasure d)) :
    Integrable (oscillatoryData φ z f) (patchMeasure d) := by
  have hmeas : Measurable (fun u : Ambient d =>
      Complex.exp (((⟪z.1, u⟫ + z.2 * φ u : ℝ) : ℂ) * Complex.I)) := by fun_prop
  refine hf.mono (hf.aestronglyMeasurable.mul hmeas.aestronglyMeasurable) ?_
  filter_upwards [] with u
  simp [oscillatoryData, Complex.norm_exp]

private theorem setIntegral_oscillatory_data {d : ℕ} (φ : Ambient d → ℝ)
    (z : Ambient d × ℝ) (f : Ambient d → ℂ) {s : Set (Ambient d)} (hs : MeasurableSet s) :
    ∫ u in s, oscillatoryData φ z f u ∂patchMeasure d =
      graphExtension (s.indicator f) φ z := by
  rw [← integral_indicator hs]
  unfold graphExtension phaseExtension
  congr 1
  funext u
  by_cases hu : u ∈ s <;> simp [oscillatoryData, hu]

/-- The Whitney decomposition of the genuine product converges pointwise
in the physical variables for integrable data on the patch. -/
theorem graph_extension_whitney_hasSum {d : ℕ} (hd : 1 ≤ d)
    {φ : Ambient d → ℝ} (hφ : Measurable φ) {f g : Ambient d → ℂ}
    (hf : Integrable f (patchMeasure d)) (hg : Integrable g (patchMeasure d))
    (z : Ambient d × ℝ) :
    HasSum (fun j => graphWhitneyLayer j φ f g z)
      (graphExtension f φ z * graphExtension g φ z) := by
  let μ := patchMeasure d
  let : SFinite μ := by unfold μ patchMeasure; infer_instance
  let F := oscillatoryData φ z f
  let G := oscillatoryData φ z g
  let K : Ambient d × Ambient d → ℂ := fun w => F w.1 * G w.2
  have hK : Integrable K (μ.prod μ) :=
    (integrable_oscillatory_data hφ z hf).mul_prod (integrable_oscillatory_data hφ z hg)
  have hrect (j : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
      ∫ w in dyadicWhitneyRectangle j p, K w ∂μ.prod μ =
        graphExtension ((dyadicParameterCell (j + 1) p.1).indicator f) φ z *
          graphExtension ((dyadicParameterCell (j + 1) p.2).indicator g) φ z := by
    rw [dyadicWhitneyRectangle, setIntegral_prod_mul F G,
      setIntegral_oscillatory_data φ z f (measurable_dyadic_parameter_cell _ _),
      setIntegral_oscillatory_data φ z g (measurable_dyadic_parameter_cell _ _)]
  have hlayer (j : ℕ) :
      (∫ w in dyadicWhitneyRegion d j, K w ∂μ.prod μ) = graphWhitneyLayer j φ f g z := by
    unfold dyadicWhitneyRegion graphWhitneyLayer
    rw [integral_biUnion_finset _ (fun p _ => measurable_dyadic_whitney_rectangle j p)
      ((pairwise_disjoint_dyadic_whitney_rectangles d j).set_pairwise _)
      (fun _ _ => hK.integrableOn)]
    simp_rw [hrect]
  have htotal : (∫ w in ⋃ j, dyadicWhitneyRegion d j, K w ∂μ.prod μ) =
      graphExtension f φ z * graphExtension g φ z := by
    rw [Measure.restrict_eq_self_of_ae_mem (ae_mem_iUnion_dyadic_whitney_regions d hd)]
    exact integral_prod_mul F G
  simpa only [hlayer, htotal] using
    (hasSum_integral_iUnion (measurable_dyadic_whitney_region d)
      (pairwise_disjoint_dyadic_whitney_regions d) hK.integrableOn)

end RestrictionWork
