import RestrictionWork.GraphRestrictedKnappSummation
import RestrictionWork.GraphRestrictedKnappHigh

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RestrictionWork

/-- The exact restricted Knapp estimate for all finite admissible
outputs on the inner spherical graph patch. -/
theorem spherical_graph_restricted_knapp {d : ℕ} (hd : 2 ≤ d) {y : ℝ}
    (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SphericalGraphRestrictedKnapp d y C := by
  by_cases h : 1 / 2 ≤ y
  · exact spherical_graph_restricted_knapp_at_le_two hd h hyD
  · have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hhalf : (1 / 2 : ℝ) < (d : ℝ) / ((d : ℝ) + 1) :=
      (lt_div_iff₀ (by positivity)).mpr (by linarith)
    obtain ⟨C, hCt, hC⟩ := spherical_graph_restricted_knapp_at_le_two hd le_rfl hhalf
    exact ⟨C ^ (2 * y), ENNReal.rpow_lt_top_of_nonneg (by positivity) hCt.ne,
      spherical_graph_restricted_knapp_below_half hd hy (lt_of_not_ge h) hC⟩

set_option maxHeartbeats 650000 in
/-- The linear form of the restricted estimate with the exact power
of the supporting set, uniformly for the spherical graph parameter. -/
theorem spherical_graph_restricted_knapp_linear {d : ℕ} (hd : 2 ≤ d) {y : ℝ}
    (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
      ∀ {A : Set (Ambient d)}, MeasurableSet A → A ⊆ Metric.ball 0 (1 / 4) →
      ∀ {f : Ambient d → ℂ}, Measurable f →
      (∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
      eLpNorm (graphExtension f (sphericalGraphPhase δ)) (ENNReal.ofReal (2 / y)) volume ≤
        C * (volume A) ^ knappProductInput d y := by
  obtain ⟨C, hC, H⟩ := spherical_graph_restricted_knapp hd hy hyD
  refine ⟨C ^ (1 / 2 : ℝ), ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne, ?_⟩
  intro δ hδ hδ₁ A hA hAb f hf hfb
  let φ := sphericalGraphPhase δ (d := d)
  let U := graphExtension f φ
  let q := (ENNReal.ofReal y)⁻¹
  have hφ : Measurable φ := by unfold φ sphericalGraphPhase sphericalPhase; fun_prop
  have hU : Continuous U :=
    graph_extension_continuous (restricted_graph_data hA hAb hf hfb).1.restrict hφ
  have he : eLpNorm (U * U) q volume =
      eLpNorm (fun z => ‖U z‖ ^ (2 : ℝ)) q volume := by
    apply eLpNorm_congr_norm_ae (hU.mul hU).aestronglyMeasurable
      ((Real.continuous_rpow_const (by norm_num)).comp hU.norm).aestronglyMeasurable
    filter_upwards [] with z
    simp [norm_mul, pow_two]
  have hq : q * ENNReal.ofReal 2 = ENNReal.ofReal (2 / y) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_inv_of_pos hy]
    exact mul_comm _ _
  have hb := H hδ hδ₁ hA hAb hf hfb
  change eLpNorm (U * U) q volume ≤ C * volume A ^ (2 * knappProductInput d y) at hb
  rw [he, eLpNorm_norm_rpow U hU.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2), hq] at hb
  have hs := ENNReal.rpow_le_rpow hb (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
    ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
    show (2 * knappProductInput d y) * (1 / 2) = knappProductInput d y by ring] using hs

end RestrictionWork
