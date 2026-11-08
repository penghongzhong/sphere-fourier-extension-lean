import RestrictionWork.ShiftedGraphRestrictedKnapp

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

/-- The exact Knapp power for restricted data on a fixed inner graph patch. -/
def SphericalGraphRestrictedKnapp (d : ℕ) (y : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 → ∀ {A : Set (Ambient d)}, MeasurableSet A →
    A ⊆ Metric.ball 0 (1 / 4) → ∀ {f : Ambient d → ℂ}, Measurable f →
    (∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
    eLpNorm (graphExtension f (sphericalGraphPhase δ) * graphExtension f (sphericalGraphPhase δ))
      (ENNReal.ofReal y)⁻¹ volume ≤ C * (volume A) ^ (2 * knappProductInput d y)

theorem restricted_graph_data {d : ℕ} {A : Set (Ambient d)} (hA : MeasurableSet A)
    (hAb : A ⊆ Metric.ball 0 (1 / 4)) {f : Ambient d → ℂ} (hf : Measurable f)
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) :
    Integrable f ∧ (∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0) ∧ ∀ u, ‖f u‖ ≤ 1 := by
  have hAt : volume A < ⊤ := (measure_mono hAb).trans_lt measure_ball_lt_top
  have h1 : Integrable (A.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hAt.ne).integrable_indicator hA
  refine ⟨h1.mono' hf.aestronglyMeasurable (.of_forall hfb), ?_, ?_⟩
  · intro u hu
    have hn : u ∉ A := fun h => hu ((Metric.ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)) (hAb h))
    have H := hfb u
    rw [indicator_of_notMem hn] at H
    exact norm_eq_zero.mp (le_antisymm H (norm_nonneg _))
  · intro u
    exact (hfb u).trans (by by_cases hu : u ∈ A <;> simp [hu])

theorem graph_extension_enorm_le_restricted_mass {d : ℕ} {A : Set (Ambient d)}
    (hA : MeasurableSet A) {f : Ambient d → ℂ}
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u)
    (φ : Ambient d → ℝ) (z : Ambient d × ℝ) :
    ‖graphExtension f φ z‖ₑ ≤ volume A := by
  unfold graphExtension phaseExtension
  calc
    _ ≤ ∫⁻ u, ‖f u * Complex.exp (((inner ℝ z.1 u + z.2 * φ u : ℝ) : ℂ) * Complex.I)‖ₑ
          ∂patchMeasure d := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, A.indicator (fun _ => (1 : ℝ≥0∞)) u ∂patchMeasure d := by
      apply lintegral_mono
      intro u
      change ‖f u * Complex.exp (((inner ℝ z.1 u + z.2 * φ u : ℝ) : ℂ) * Complex.I)‖ₑ ≤ _
      rw [enorm_mul, ← ofReal_norm (Complex.exp _), Complex.norm_exp_ofReal_mul_I,
        ENNReal.ofReal_one, mul_one]
      have H := ENNReal.ofReal_le_ofReal (hfb u)
      by_cases hu : u ∈ A <;> simpa [hu] using H
    _ = patchMeasure d A := by rw [lintegral_indicator hA]; simp
    _ ≤ _ := Measure.restrict_le_self A

end RestrictionWork
