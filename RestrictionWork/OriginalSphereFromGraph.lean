import RestrictionWork.OriginalCapContainsBall
import RestrictionWork.OriginalSmallCapBound
import RestrictionWork.SphereFiniteCover
import RestrictionWork.ClosureObligations

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RestrictionWork

/-- A strong estimate for one quarter-sized spherical graph patch gives
the strong bound for the original global sphere extension. -/
theorem boundedSphereExtension_of_quarter_graph {d : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) {C : ℝ≥0∞} (hC : C < ⊤)
    (hgraph : ∀ g : Ambient d → ℂ, Measurable g →
      MemLp g p (patchMeasure d) →
      (∀ v ∉ Metric.ball (0 : Ambient d) (1 / 4), g v = 0) →
      eLpNorm (graphExtension g (sphericalGraphPhase δ)) q volume ≤
        C * eLpNorm g p (patchMeasure d)) :
    BoundedSphereExtension (d + 1) p q := by
  obtain ⟨K, hK, hcap⟩ := original_small_cap_bound_of_graph hδ hδ₁ hp hC hgraph
  obtain ⟨pole, hpole⟩ := original_small_cap_contains_ball (d := d) hδ hδ₁
  apply boundedSphereExtension_of_ball_bound hp hq pole (by positivity : 0 < δ / 4) hK
  intro f hfm hf hfs
  exact hcap f hfm hf (fun ω hω => hfs ω (fun hmem => hω (hpole hmem)))

/-- Reduces the exact finite Knapp boundary target to strong estimates
on a single quarter-sized chart at the fixed cap radius one half. -/
theorem finiteKnappBoundary_of_quarter_graph
    (hgraph : ∀ d : ℕ, 2 ≤ d → ∀ p q : ℝ≥0∞, q ≠ ⊤ →
      AdmissibleExponents (d + 1) p q →
      (q⁻¹).toReal = (((d + 1 : ℕ) : ℝ) - 1) / (((d + 1 : ℕ) : ℝ) + 1) *
        (1 - (p⁻¹).toReal) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ g : Ambient d → ℂ, Measurable g →
        MemLp g p (patchMeasure d) →
        (∀ v ∉ Metric.ball (0 : Ambient d) (1 / 4), g v = 0) →
        eLpNorm (graphExtension g (sphericalGraphPhase (1 / 2))) q volume ≤
          C * eLpNorm g p (patchMeasure d)) :
    FiniteKnappBoundarySufficiency := by
  intro n hn p q hqfin hadm hline
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨C, hC, hlocal⟩ := hgraph d (by omega) p q hqfin hadm hline
  exact boundedSphereExtension_of_quarter_graph (δ := 1 / 2)
    (by norm_num) le_rfl hadm.1 hadm.2.1 hC hlocal

end RestrictionWork
