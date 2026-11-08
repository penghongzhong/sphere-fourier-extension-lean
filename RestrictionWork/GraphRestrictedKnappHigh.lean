import RestrictionWork.GraphRestrictedKnappData
import RestrictionWork.GraphWhitneyLayerHigh

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

/-- Interpolating the already summed quadratic estimate with the global
supremum bound gives the exact Knapp mass power for output exponents R > 2. -/
theorem spherical_graph_restricted_knapp_below_half {d : ℕ} (hd : 2 ≤ d)
    {y : ℝ} (hy : 0 < y) (hy₂ : y < 1 / 2) {C : ℝ≥0∞}
    (hC : SphericalGraphRestrictedKnapp d (1 / 2) C) :
    SphericalGraphRestrictedKnapp d y (C ^ (2 * y)) := by
  intro δ hδ hδ₂ A hA hAb f hf hfb
  let φ : Ambient d → ℝ := sphericalGraphPhase δ
  let F := graphExtension f φ * graphExtension f φ
  have hφ : Measurable φ := by
    unfold φ sphericalGraphPhase sphericalPhase
    fun_prop
  have hfi : Integrable f (patchMeasure d) := (restricted_graph_data hA hAb hf hfb).1.restrict
  have hF : AEStronglyMeasurable F volume :=
    ((graph_extension_continuous hfi hφ).mul (graph_extension_continuous hfi hφ)).aestronglyMeasurable
  have hquadratic :
      eLpNorm F (ENNReal.ofReal (1 / 2))⁻¹ volume ≤
        C * (volume A) ^ (2 * knappProductInput d (1 / 2)) :=
    hC hδ hδ₂ hA hAb hf hfb
  have htop : eLpNorm F ⊤ volume ≤ (volume A) ^ (2 : ℝ) := by
    simpa only [ENNReal.rpow_two, pow_two] using
      graph_extension_product_eLpNorm_top_le_mass hA hA hφ hfi hfi hfb hfb
  let θ := 2 * y
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ₁ : θ < 1 := by dsimp [θ]; linarith
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁.le
  have hscale : θ * (1 / 2 : ℝ) + (1 - θ) * 0 = y := by
    dsimp [θ]
    ring
  have hinterp := eLpNorm_reciprocal_interpolate hF
    (s := 1 / 2) (t := 0) (by norm_num) le_rfl hθ hθ₁
  rw [hscale, ENNReal.ofReal_zero, ENNReal.inv_zero] at hinterp
  have hbase : 0 ≤ 2 * knappProductInput d (1 / 2) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hdiv : ((d : ℝ) + 2) / (2 * d) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith
    unfold knappProductInput
    linarith
  have hmass :
      2 * knappProductInput d (1 / 2) * θ + 2 * (1 - θ) = 2 * knappProductInput d y := by
    unfold θ knappProductInput
    ring
  change eLpNorm F (ENNReal.ofReal y)⁻¹ volume ≤ C ^ θ * (volume A) ^ (2 * knappProductInput d y)
  calc
    _ ≤ (C * (volume A) ^ (2 * knappProductInput d (1 / 2))) ^ θ *
          ((volume A) ^ (2 : ℝ)) ^ (1 - θ) :=
      hinterp.trans (mul_le_mul' (ENNReal.rpow_le_rpow hquadratic hθ.le)
        (ENNReal.rpow_le_rpow htop hθ'))
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hbase hθ.le)
          (mul_nonneg (by norm_num) hθ'), hmass]

end RestrictionWork
