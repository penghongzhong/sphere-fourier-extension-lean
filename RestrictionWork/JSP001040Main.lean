import RestrictionWork.SphericalGraphKnappPairing
import RestrictionWork.GraphExtensionUnitPairing
import RestrictionWork.KnappGraphToOriginal

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RestrictionWork

/-- The strong extension estimate on the inner patch at the exact finite
Knapp exponents, with a constant uniform in the spherical scale. -/
theorem spherical_graph_knapp_strong {d : ℕ} (hd : 2 ≤ d) {y : ℝ}
    (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
      ∀ f : Ambient d → ℂ, Measurable f →
      MemLp f (ENNReal.ofReal (knappProductInput d y)⁻¹) (patchMeasure d) →
      (∀ v ∉ Metric.ball (0 : Ambient d) (1 / 4), f v = 0) →
      eLpNorm (graphExtension f (sphericalGraphPhase δ)) (ENNReal.ofReal (2 / y)) volume ≤
        C * eLpNorm f (ENNReal.ofReal (knappProductInput d y)⁻¹) (patchMeasure d) := by
  have hy₁ : y < 1 := hyD.trans ((div_lt_one (by positivity)).mpr (by linarith))
  have hgain : 0 < knappProductInput d y - y / 2 := by
    rw [knapp_input_sub_diagonal (by omega : 0 < d) y]
    positivity
  have hx : 0 < knappProductInput d y := by linarith
  have hp : 1 ≤ (knappProductInput d y)⁻¹ := by
    apply (one_le_inv₀ hx).mpr
    unfold knappProductInput
    linarith [show 0 ≤ (((d : ℝ) + 2) / (2 * d)) * y by positivity]
  have hq : 1 < 2 / y := (lt_div_iff₀ hy).mpr (by linarith)
  have hs : (2 / y) / (2 / y - 1) = (1 - y / 2)⁻¹ := by
    have h : 0 < 1 - y / 2 := by linarith
    have he : 2 / y - 1 = (2 / y) * (1 - y / 2) := by field_simp
    rw [he, div_mul_eq_div_div, div_self (by positivity : 2 / y ≠ 0), one_div]
  obtain ⟨C, hC, H⟩ := spherical_graph_knapp_unit_pairing hd hy hyD
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ₁ f hf hfp hfs
  have hφ : Measurable (sphericalGraphPhase δ (d := d)) := by
    unfold sphericalGraphPhase sphericalPhase
    fun_prop
  refine graph_extension_le_of_unit_pairing hp hq hφ ?_ hf hfp hfs
  intro F G hF hFi hFs hFN hG hGi hGN
  rw [hs] at hGN
  exact H hδ hδ₁ hF hFi hFs hFN hG hGi hGN

/-- JSP-001040 for the unit sphere, all dimensions n ≥ 3 and the full
admissible range of p and q. -/
theorem fullSphereRestrictionConjecture : FullSphereRestrictionConjecture :=
  fullSphereRestriction_of_graph_strong fun _ hd _ hy hyD => by
    obtain ⟨C, hC, H⟩ := spherical_graph_knapp_strong hd hy hyD
    exact ⟨C, hC, H (by norm_num : (0 : ℝ) < 1 / 2) le_rfl⟩

/-- Exact sufficiency on the finite Knapp boundary of the original sphere. -/
theorem finiteKnappBoundarySufficiency : FiniteKnappBoundarySufficiency :=
  original_target_iff_finite_knapp.mp fullSphereRestrictionConjecture

end RestrictionWork
