import RestrictionWork.MeasureBoundedPhases
import RestrictionWork.MeasurePhaseStrong
import RestrictionWork.MeasureLatticeBound
import RestrictionWork.MeasureLatticeLimit

-- The lattice argument adapts OpenAI's Apache-2.0 restriction development
-- at revision 4eaee87548250b2682affda7d05d947c05554bae (see UPSTREAM_LICENSE).
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal BigOperators
open OAI.Analysis.Fourier.Wave
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction (latticePhaseSum phaseInterpolationConstant
  phaseInterpolationConstant_ne_top)
namespace RestrictionWork

/-- Sparse-to-lattice epsilon removal with one constant for the entire family. -/
theorem measure_sparse_bound_implies_lattice_bound {n : ℕ}
    (𝓜 : Set (Measure (Space n))) {K : ℝ} (hK : 1 ≤ K)
    (hsupp : ∀ μ ∈ 𝓜, ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ K)
    {p q : ℝ} (hq : 1 ≤ q) (hqp : q < p) {D : ℕ} (hD : 0 < D)
    (hSparse : ∀ α > (0 : ℝ), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ μ ∈ 𝓜, SparseMeasureFourierBound μ (ENNReal.ofReal p) α D C) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ μ ∈ 𝓜,
      ∀ E : Finset (Fin n → ℤ), ∀ a : (Fin n → ℤ) → ℂ,
        eLpNorm (latticePhaseSum E a) (ENNReal.ofReal p) μ ≤
          C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp : 1 ≤ p := hq.trans hqp.le
  have hp0 : 0 < p := hq0.trans hqp
  have hgap : 0 < 1 / q - 1 / p := sub_pos.mpr (one_div_lt_one_div_of_lt hq0 hqp)
  let ε : ℝ := (1 / q - 1 / p) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hs : 0 ≤ ε + 1 / p := by positivity
  have hqs : q * (ε + 1 / p) < 1 := by
    have H : ε + 1 / p < 1 / q := by dsimp [ε]; linarith
    simpa only [mul_one_div_cancel hq0.ne'] using mul_lt_mul_of_pos_left H hq0
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  obtain ⟨A, hAt, hA⟩ := measure_unit_ball_small_loss_of_sparse 𝓜 hpE hD hSparse hε
  obtain ⟨B, hBt, hB⟩ := measure_bounded_phases_of_unit_ball_loss 𝓜 hK hsupp hp0 hε hAt hA
  refine ⟨phaseInterpolationConstant q (ε + 1 / p) B,
    phaseInterpolationConstant_ne_top hBt, ?_⟩
  intro μ hμ
  apply measure_lattice_phase_sum_bound_of_separated
  intro E hsep a
  apply measure_finite_phase_sum_strong_bound μ E hp hq0 hs hqs _ a
  intro S hSE b hb
  exact hB μ hμ S (fun z hz w hw hzw => hsep z (hSE hz) w (hSE hw) hzw) b hb

/-- A uniform sparse bound and common support and mass bounds imply the
global Euclidean restriction estimate at every smaller diagonal exponent. -/
theorem measure_sparse_bound_implies_restriction {n : ℕ}
    (𝓜 : Set (Measure (Space n))) {K : ℝ} (hK : 1 ≤ K)
    (hsupp : ∀ μ ∈ 𝓜, ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ K)
    {V : ℝ≥0∞} (hV : V ≠ ⊤) (hmass : ∀ μ ∈ 𝓜, μ univ ≤ V)
    {p q : ℝ} (hq : 1 ≤ q) (hqp : q < p) {D : ℕ} (hD : 0 < D)
    (hSparse : ∀ α > (0 : ℝ), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ μ ∈ 𝓜, SparseMeasureFourierBound μ (ENNReal.ofReal p) α D C) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ μ ∈ 𝓜, ∀ f : Space n → ℂ, Integrable f →
      eLpNorm (angularFourier f) (ENNReal.ofReal q) μ ≤
        C * eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨C, hCt, hC⟩ :=
    measure_sparse_bound_implies_lattice_bound 𝓜 hK hsupp hq hqp hD hSparse
  have hexp : 0 ≤ 1 / q - 1 / p := sub_nonneg.mpr (one_div_le_one_div_of_le hq0 hqp.le)
  refine ⟨C * V ^ (1 / q - 1 / p),
    ENNReal.mul_ne_top hCt (ENNReal.rpow_ne_top_of_nonneg hexp hV), ?_⟩
  intro μ hμ f hf
  let : IsFiniteMeasure μ := ⟨(hmass μ hμ).trans_lt hV.lt_top⟩
  apply measure_restriction_of_lattice_bound μ hq _ hf
  intro E a
  exact (measure_lattice_bound_lower_output μ hq0 hqp.le (hC μ hμ) E a).trans
    (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hmass μ hμ) hexp)) le_rfl)

end RestrictionWork
