import RestrictionWork.KnappInterpolationGeometry
import RestrictionWork.OriginalSphereFromGraph
import RestrictionWork.OriginalTargetFiniteKnapp

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RestrictionWork

/-- The exact finite Knapp line in the original extended-exponent formulation
has the real parameter used by the graph analysis. -/
theorem admissible_finite_knapp_reparam {d : ℕ} (hd : 2 ≤ d)
    {p q : ℝ≥0∞} (hqfin : q ≠ ⊤) (hadm : AdmissibleExponents (d + 1) p q)
    (hline : (q⁻¹).toReal =
      ((((d + 1 : ℕ) : ℝ) - 1) / (((d + 1 : ℕ) : ℝ) + 1)) * (1 - (p⁻¹).toReal)) :
    ∃ y : ℝ, 0 < y ∧ y < (d : ℝ) / ((d : ℝ) + 1) ∧
      p = ENNReal.ofReal (knappProductInput d y)⁻¹ ∧ q = ENNReal.ofReal (2 / y) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  have hd1 : 0 < (d : ℝ) + 1 := by linarith
  have hd2 : 0 < (d : ℝ) + 2 := by linarith
  have hqr : 0 < q.toReal := by
    have h := ENNReal.toReal_mono hqfin hadm.2.1
    rw [ENNReal.toReal_one] at h
    linarith
  have hrad : ENNReal.ofReal (2 * ((d : ℝ) + 1) / d) < q := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hadm.2.2.1
  have hradR : 2 * ((d : ℝ) + 1) / d < q.toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hqfin).mpr hrad
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  let y := 2 / q.toReal
  have hy : 0 < y := div_pos (by norm_num) hqr
  have hyD : y < (d : ℝ) / ((d : ℝ) + 1) := by
    apply (div_lt_div_iff₀ hqr hd1).mpr
    simpa only [mul_comm q.toReal (d : ℝ)] using (div_lt_iff₀ hdpos).mp hradR
  have hline' : q.toReal⁻¹ = (d : ℝ) / ((d : ℝ) + 2) * (1 - p.toReal⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      show (d : ℝ) + 1 + 1 = (d : ℝ) + 2 by ring, ENNReal.toReal_inv] using hline
  have H : ((d : ℝ) + 2) * q.toReal⁻¹ = (d : ℝ) * (1 - p.toReal⁻¹) := by
    rw [hline']
    field_simp
  have hw : (((d : ℝ) + 2) / (2 * d)) * y = 1 - p.toReal⁻¹ := by
    calc
      _ = (((d : ℝ) + 2) * q.toReal⁻¹) / d := by
        unfold y
        field_simp [hdpos.ne', hqr.ne']
      _ = _ := by
        rw [H, mul_comm (d : ℝ), mul_div_cancel_right₀ _ hdpos.ne']
  have hK : knappProductInput d y = p.toReal⁻¹ := by
    unfold knappProductInput
    rw [hw]
    ring
  have hKpos : 0 < knappProductInput d y := by
    have h := knapp_input_sub_diagonal (d := d) (by omega) y
    have hh : 0 < ((d : ℝ) + 1) / d * ((d : ℝ) / ((d : ℝ) + 1) - y) :=
      mul_pos (div_pos hd1 hdpos) (sub_pos.mpr hyD)
    linarith
  have hpfin : p ≠ ⊤ := by
    intro h
    rw [h, ENNReal.toReal_top, inv_zero] at hK
    exact hKpos.ne' hK
  refine ⟨y, hy, hyD, ?_, ?_⟩
  · rw [hK, inv_inv, ENNReal.ofReal_toReal hpfin]
  · have he : 2 / y = q.toReal := by
      unfold y
      field_simp
    rw [he, ENNReal.ofReal_toReal hqfin]

/-- Strong graph bounds throughout the real-parameter Knapp line imply
the exact original restriction conjecture, via the proved cap transfer,
sphere cover, strict range and necessity results. -/
theorem fullSphereRestriction_of_graph_strong
    (hstrong : ∀ d : ℕ, 2 ≤ d → ∀ y : ℝ, 0 < y → y < (d : ℝ) / ((d : ℝ) + 1) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ g : Ambient d → ℂ, Measurable g →
        MemLp g (ENNReal.ofReal (knappProductInput d y)⁻¹) (patchMeasure d) →
        (∀ v ∉ Metric.ball (0 : Ambient d) (1 / 4), g v = 0) →
        eLpNorm (graphExtension g (sphericalGraphPhase (1 / 2))) (ENNReal.ofReal (2 / y)) volume ≤
          C * eLpNorm g (ENNReal.ofReal (knappProductInput d y)⁻¹) (patchMeasure d)) :
    FullSphereRestrictionConjecture := by
  apply original_target_iff_finite_knapp.mpr
  apply finiteKnappBoundary_of_quarter_graph
  intro d hd p q hqfin hadm hline
  obtain ⟨y, hy, hyD, hp, hq⟩ := admissible_finite_knapp_reparam hd hqfin hadm hline
  rw [hp, hq]
  exact hstrong d hd y hy hyD

end RestrictionWork
