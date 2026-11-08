import OAI.Analysis.Fourier.Restriction.LatticeLimit

-- Adapted from OpenAI's Apache-2.0 Lean restriction development.
-- Upstream revision 4eaee87548250b2682affda7d05d947c05554bae (see UPSTREAM_LICENSE).

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators
open OAI.Analysis.Fourier.Wave
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction

namespace RestrictionWork

theorem eLpNorm_measure_lattice_average_le {n : ℕ} (μ : Measure (Space n)) [SFinite μ] {q : ℝ} (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) μ ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    (E : Finset (Fin n → ℤ)) {f : Space n → ℂ} (hf : Measurable f) :
    eLpNorm (latticeAverage E f) (ENNReal.ofReal q) μ ≤
      C * eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  let F : Space n × Space n → ℂ := fun z ↦
    Complex.exp (-Complex.I * ((inner ℝ z.2 z.1 : ℝ) : ℂ)) *
      latticePhaseSum E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + z.2)) z.1
  have hFm : Measurable F := measurable_latticeAverage_integrand E hf
  have Havg := eLpNorm_average_rpow_le μ
    (volume.restrict (OAI.Analysis.Fourier.WavePackets.unitCell n)) hFm hq
  have Hslice (y : Space n) :
      eLpNorm (fun ξ ↦ F (ξ, y)) (ENNReal.ofReal q) μ ^ q ≤
      C ^ q * ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q := by
    have he : eLpNorm (fun ξ ↦ F (ξ, y)) (ENNReal.ofReal q) μ =
        eLpNorm (latticePhaseSum E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)))
          (ENNReal.ofReal q) μ := by
      apply eLpNorm_congr_norm_ae
        (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (by
          rw [← finitePhaseSum_integerVector]
          exact (continuous_finitePhaseSum _ _).aestronglyMeasurable)
      filter_upwards [] with ξ
      simp [F, Complex.norm_exp]
    rw [he]
    have H := ENNReal.rpow_le_rpow (hbound E (fun k ↦ f (OAI.Analysis.Fourier.WavePackets.integerVector k + y))) hq0.le
    have hs0 : 0 ≤ ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ ^ q := by positivity
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
      ← Real.rpow_mul hs0, one_div_mul_cancel hq0.ne', Real.rpow_one] at H
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ Real.rpow_nonneg (norm_nonneg _) _)] at H
    have heq (z : ℂ) : ENNReal.ofReal (‖z‖ ^ q) = ‖z‖ₑ ^ q := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hq0.le, ofReal_norm]
    simpa only [heq] using H
  have Hmass : (∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
      ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q) ≤ ∫⁻ x, ‖f x‖ₑ ^ q := by
    rw [MeasureTheory.lintegral_finsetSum _ (fun k _ ↦ by fun_prop)]
    rw [OAI.Analysis.Fourier.WavePackets.lintegral_eq_tsum_unitCell (fun x ↦ ‖f x‖ₑ ^ q)]
    exact ENNReal.sum_le_tsum E
  have Hpow : eLpNorm (latticeAverage E f) (ENNReal.ofReal q) μ ^ q ≤
      C ^ q * eLpNorm f (ENNReal.ofReal q) volume ^ q := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hq0 hf.aestronglyMeasurable]
    calc
      _ ≤ ∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
          eLpNorm (fun ξ ↦ F (ξ, y)) (ENNReal.ofReal q) μ ^ q := Havg
      _ ≤ ∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n, C ^ q *
          ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q := lintegral_mono Hslice
      _ = C ^ q * ∫⁻ y in OAI.Analysis.Fourier.WavePackets.unitCell n,
          ∑ k ∈ E, ‖f (OAI.Analysis.Fourier.WavePackets.integerVector k + y)‖ₑ ^ q := by
        apply lintegral_const_mul''
        fun_prop
      _ ≤ _ := mul_le_mul le_rfl Hmass zero_le zero_le
  have H := ENNReal.rpow_le_rpow Hpow (one_div_nonneg.mpr hq0.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] using H

/-- A uniform lattice restriction bound gives the genuine Euclidean
restriction bound, by probability-cell averaging and an absolutely
convergent tiling limit. -/
theorem measure_restriction_of_lattice_bound_measurable {n : ℕ} (μ : Measure (Space n)) [SFinite μ] {q : ℝ}
    (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) μ ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    {f : Space n → ℂ} (hfm : Measurable f) (hfi : Integrable f) :
    eLpNorm (angularFourier f) (ENNReal.ofReal q) μ ≤
      C * eLpNorm f (ENNReal.ofReal q) volume := by
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise μ
    (fun N ↦ (measurable_latticeAverage (latticeBox n N) hfm).aestronglyMeasurable)
    (continuous_angularFourier hfi).aestronglyMeasurable
    (tendsto_latticeAverage hfi) (by linarith)
  intro N
  exact eLpNorm_measure_lattice_average_le μ hq hbound _ hfm

theorem measure_restriction_of_lattice_bound {n : ℕ} (μ : Measure (Space n)) [SFinite μ] {q : ℝ}
    (hq : 1 ≤ q) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) μ ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    {f : Space n → ℂ} (hfi : Integrable f) :
    eLpNorm (angularFourier f) (ENNReal.ofReal q) μ ≤
      C * eLpNorm f (ENNReal.ofReal q) volume := by
  let g := hfi.aestronglyMeasurable.mk f
  have heq : f =ᵐ[volume] g := hfi.aestronglyMeasurable.ae_eq_mk
  have H := measure_restriction_of_lattice_bound_measurable μ hq hbound
    hfi.aestronglyMeasurable.measurable_mk (hfi.congr heq)
  have hF : angularFourier f = angularFourier g := funext (angularFourier_congr_ae heq)
  rwa [← hF, ← eLpNorm_congr_ae heq] at H

end RestrictionWork
