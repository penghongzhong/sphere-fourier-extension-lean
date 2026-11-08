import RestrictionWork.MeasureEpsilonRemoval
import RestrictionWork.ShiftedGraphSparseRestriction
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction (restrictionInputExponent)
namespace RestrictionWork

/-- Finset form of the uniform sparse-ball estimate used in the covering step. -/
theorem shifted_graph_sparse_measure_fourier_bound {d : ℕ} (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 →
        SparseMeasureFourierBound (patchGraphMeasure (shiftedSphericalGraphPhase δ a r))
          (ENNReal.ofReal (restrictionInputExponent (d + 1))) ε (16 * (d + 1)) C := by
  classical
  obtain ⟨C, hC, HC⟩ := shifted_graph_sparse_restriction_indexed hd hε
  refine ⟨C, hC, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf R hR T hsep f hfm hfi hfs
  let e : Fin T.card ≃ ↥T := T.equivFin.symm
  let z : Fin T.card → Ambient (d + 1) := fun i => (e i).val
  refine HC hδ hδhalf ha hr hrhalf T.card R hR z ?_ f hfm hfi ?_
  · intro i j hij
    apply hsep (z i) (e i).property (z j) (e j).property
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  · intro x hx
    apply hfs x
    intro y hy
    have H := hx (T.equivFin ⟨y, hy⟩)
    simpa only [z, e, Equiv.symm_apply_apply] using H

/-- Uniform lossless global diagonal restriction on the actual shifted graph. -/
theorem shifted_graph_global_restriction {d : ℕ} (hd : 1 ≤ d)
    {q : ℝ} (hq : 1 ≤ q) (hqp : q < restrictionInputExponent (d + 1)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ f : Ambient (d + 1) → ℂ, Integrable f →
        eLpNorm (angularFourier f) (ENNReal.ofReal q)
          (patchGraphMeasure (shiftedSphericalGraphPhase δ a r)) ≤
            C * eLpNorm f (ENNReal.ofReal q) volume := by
  let 𝓜 : Set (Measure (Ambient (d + 1))) := {μ |
    ∃ (δ : ℝ) (a : Ambient d) (r : ℝ), 0 < δ ∧ δ ≤ 1 / 2 ∧ ‖a‖ ≤ 1 / 2 ∧
      0 < r ∧ r ≤ 1 / 2 ∧ μ = patchGraphMeasure (shiftedSphericalGraphPhase δ a r)}
  have hφ (δ : ℝ) (a : Ambient d) (r : ℝ) : Measurable (shiftedSphericalGraphPhase δ a r) := by
    unfold shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hsupport : ∀ μ ∈ 𝓜, ∀ᵐ ξ ∂μ, ‖ξ‖ ≤ (21 : ℝ) := by
    rintro μ ⟨δ, a, r, hδ, hδhalf, ha, hr, hrhalf, rfl⟩
    filter_upwards [ae_patch_graph_point (hφ δ a r)] with ξ hξ
    obtain ⟨v, hv, rfl⟩ := hξ
    have H := shifted_graph_tube_subset_ball hδ hδhalf ha hr hrhalf (h := 1) le_rfl
      (patch_graph_tube_mem_iff.mpr ⟨v, hv, mem_ball_self zero_lt_one⟩)
    exact (by simpa only [mem_ball, dist_zero_right] using H :
      ‖patchGraphPoint (shiftedSphericalGraphPhase δ a r) v‖ < 21).le
  let V := volume (ball (0 : Ambient d) 1)
  have hmass : ∀ μ ∈ 𝓜, μ univ ≤ V := by
    rintro μ ⟨δ, a, r, _, _, _, _, _, rfl⟩
    change (patchMeasure d).map (patchGraphPoint (shiftedSphericalGraphPhase δ a r)) univ ≤ V
    rw [Measure.map_apply (measurable_patch_graph_point (hφ δ a r)) MeasurableSet.univ,
      preimage_univ, patchMeasure, Measure.restrict_apply_univ]
  have hSparse : ∀ ε > (0 : ℝ), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ μ ∈ 𝓜, SparseMeasureFourierBound μ (ENNReal.ofReal (restrictionInputExponent (d + 1)))
        ε (16 * (d + 1)) C := by
    intro ε hε
    obtain ⟨C, hC, HC⟩ := shifted_graph_sparse_measure_fourier_bound hd hε
    refine ⟨C, hC, ?_⟩
    rintro μ ⟨δ, a, r, hδ, hδhalf, ha, hr, hrhalf, rfl⟩
    exact HC hδ hδhalf ha hr hrhalf
  obtain ⟨C, hC, HC⟩ := measure_sparse_bound_implies_restriction 𝓜
    (by norm_num) hsupport (V := V) measure_ball_lt_top.ne hmass hq hqp
    (by omega : 0 < 16 * (d + 1)) hSparse
  refine ⟨C, hC, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf f hf
  exact HC _ ⟨δ, a, r, hδ, hδhalf, ha, hr, hrhalf, rfl⟩ f hf

end RestrictionWork
