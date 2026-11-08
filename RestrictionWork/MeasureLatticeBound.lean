import OAI.Analysis.Fourier.Restriction.LatticeExponent

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

theorem measure_lattice_phase_sum_bound_of_separated {n : ℕ} (μ : Measure (Space n)) {p : ℝ≥0∞} {q : ℝ} {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Space n),
      (∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w) → ∀ a : Space n → ℂ,
        eLpNorm (finitePhaseSum E a) p μ ≤
          C * ENNReal.ofReal ((∑ z ∈ E, ‖a z‖ ^ q) ^ (1 / q)))
    (E : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    eLpNorm (latticePhaseSum E a) p μ ≤
      C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)) := by
  classical
  have H := hbound (E.image OAI.Analysis.Fourier.WavePackets.integerVector) (integerVector_image_separated E)
    (Function.extend OAI.Analysis.Fourier.WavePackets.integerVector a (fun _ ↦ 0))
  rw [finitePhaseSum_integerVector] at H
  have he : (∑ z ∈ E.image OAI.Analysis.Fourier.WavePackets.integerVector,
      ‖Function.extend OAI.Analysis.Fourier.WavePackets.integerVector a (fun _ ↦ 0) z‖ ^ q) =
      ∑ k ∈ E, ‖a k‖ ^ q := by
    rw [Finset.sum_image]
    · simp only [OAI.Analysis.Fourier.WavePackets.integerVector_injective.extend_apply]
    · intro i hi j hj hij
      exact OAI.Analysis.Fourier.WavePackets.integerVector_injective hij
  rwa [he] at H

theorem measure_lattice_bound_lower_output {n : ℕ} (μ : Measure (Space n)) {p q : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal p) μ ≤
        C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)))
    (E : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) μ ≤
      (C * (μ Set.univ) ^ (1 / q - 1 / p)) *
        ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)) := by
  have hp : 0 < p := hq.trans_le hqp
  have hm : AEStronglyMeasurable (latticePhaseSum E a) μ := by
    rw [← finitePhaseSum_integerVector]
    exact (continuous_finitePhaseSum _ _).aestronglyMeasurable
  have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hqp) hm
  have H' : eLpNorm (latticePhaseSum E a) (ENNReal.ofReal q) μ ≤
      eLpNorm (latticePhaseSum E a) (ENNReal.ofReal p) μ *
        (μ Set.univ) ^ (1 / q - 1 / p) := by
    simpa only [ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hp.le] using H
  calc
    _ ≤ _ := H'
    _ ≤ (C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q))) *
        (μ Set.univ) ^ (1 / q - 1 / p) := by gcongr; exact hbound E a
    _ = _ := by ring

end RestrictionWork
