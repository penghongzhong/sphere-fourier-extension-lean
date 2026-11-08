import RestrictionWork.GraphWhitneyMoment
import OAI.Analysis.Fourier.LocalSmoothing.DyadicReconstruction

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace RestrictionWork

/-- Minkowski and the verified pointwise Whitney expansion reduce the
actual extension product norm to the sum of its layer norms. -/
theorem graph_extension_product_eLpNorm_le_whitney_sum {d : ℕ} (hd : 1 ≤ d)
    {φ : Ambient d → ℝ} (hφ : Measurable φ) {f g : Ambient d → ℂ}
    (hf : Integrable f (patchMeasure d)) (hg : Integrable g (patchMeasure d))
    {P : ℝ≥0∞} (hP : 1 ≤ P) :
    eLpNorm (graphExtension f φ * graphExtension g φ) P volume ≤
      ∑' j, eLpNorm (graphWhitneyLayer j φ f g) P volume := by
  have hL (j : ℕ) : Continuous (graphWhitneyLayer j φ f g) :=
    continuous_finsetSum _ fun p _ =>
      (graph_extension_continuous (hf.indicator (measurable_dyadic_parameter_cell _ _)) hφ).mul
        (graph_extension_continuous (hg.indicator (measurable_dyadic_parameter_cell _ _)) hφ)
  have hPcont : Continuous (graphExtension f φ * graphExtension g φ) :=
    (graph_extension_continuous hf hφ).mul (graph_extension_continuous hg hφ)
  have hlim (z : Ambient d × ℝ) :
      Tendsto (fun N : ℕ => (0 : ℂ) + ∑ j ∈ Finset.range N, graphWhitneyLayer j φ f g z)
        atTop (𝓝 ((graphExtension f φ * graphExtension g φ) z)) := by
    simpa only [zero_add, Pi.mul_apply] using
      (graph_extension_whitney_hasSum hd hφ hf hg z).tendsto_sum_nat
  simpa only [eLpNorm_zero, zero_add] using
    OAI.Analysis.Fourier.LocalSmoothing.eLpNorm_le_base_add_tsum_of_tendsto
      (aestronglyMeasurable_zero (μ := volume)) (fun j => (hL j).aestronglyMeasurable)
      hPcont.aestronglyMeasurable hP hlim

set_option maxHeartbeats 750000 in
/-- The norm version of the same-layer estimate, in the form used by
the Whitney mass summation. -/
theorem graph_whitney_layer_eLpNorm_lt_two {d : ℕ} {R : ℝ}
    (hR₁ : 1 < R) (hR₂ : R < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (j : ℕ) {φ : Ambient d → ℝ},
      Measurable φ → ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g →
      Integrable f → Integrable g →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0) →
      (∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0) →
      eLpNorm (graphWhitneyLayer j φ f g) (ENNReal.ofReal R) volume ≤
        C * (∑ p ∈ dyadicWhitneyPairs d j,
          eLpNorm (graphWhitneyTerm j p φ f g) (ENNReal.ofReal R) volume ^ R) ^ (1 / R) := by
  obtain ⟨C, hC, H⟩ := graph_whitney_layer_moment_lt_two (d := d) hR₁ hR₂
  have hR : 0 < R := zero_lt_one.trans hR₁
  have hRinv : 0 ≤ 1 / R := by positivity
  refine ⟨C ^ (1 / R), ENNReal.rpow_lt_top_of_nonneg hRinv hC.ne, ?_⟩
  intro j φ hφ f g hf hg hfi hgi hfs hgs
  have hterm p : Continuous (graphWhitneyTerm j p φ f g) :=
    (graph_extension_continuous
      (hfi.indicator (measurable_dyadic_parameter_cell _ _)).restrict hφ).mul
      (graph_extension_continuous
        (hgi.indicator (measurable_dyadic_parameter_cell _ _)).restrict hφ)
  have hL : Continuous (graphWhitneyLayer j φ f g) :=
    continuous_finsetSum _ fun p _ => hterm p
  have hpow := H j hφ hf hg hfi hgi hfs hgs
  simp_rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hR
    hL.aestronglyMeasurable,
    ← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hR
      (hterm _).aestronglyMeasurable] at hpow
  have h := ENNReal.rpow_le_rpow hpow hRinv
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hRinv, ← ENNReal.rpow_mul,
    mul_one_div_cancel hR.ne', ENNReal.rpow_one] using h

end RestrictionWork
