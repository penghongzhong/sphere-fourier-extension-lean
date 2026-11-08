import RestrictionWork.GraphRestrictedKnappData
import RestrictionWork.GraphWhitneyPairRestricted
import RestrictionWork.GraphWhitneyLayerHigh
import RestrictionWork.WhitneyLayerMassFactor
import RestrictionWork.WhitneySummationExponent

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

set_option maxHeartbeats 1300000 in
/-- Summing the actual Whitney terms gives the exact restricted Knapp
bound, including the physical L² endpoint for the product. -/
theorem spherical_graph_restricted_knapp_at_le_two {d : ℕ} (hd : 2 ≤ d)
    {y : ℝ} (hy₂ : 1 / 2 ≤ y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SphericalGraphRestrictedKnapp d y C := by
  have hy : 0 < y := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hy₂
  have hy₁ : y < 1 := hyD.trans ((div_lt_one (by positivity)).mpr (by linarith))
  have hyk : y < 2 * knappProductInput d y :=
    (le_max_left y (1 - y)).trans_lt (whitney_sequence_reciprocal_lt_knapp_mass hd hy hyD).2
  obtain ⟨x, hx, P, hP, HP⟩ := spherical_graph_whitney_term_bound hd hy hyD
  obtain ⟨L, hL, HL⟩ := graph_whitney_layer_eLpNorm (d := d) hy₂ hy₁
  have hkx : 2 * knappProductInput d y < 2 * x := by linarith
  obtain ⟨S, hS, HS⟩ := dyadic_whitney_mass_tsum_le (d := d) (by omega) hy hyk hkx
  refine ⟨L * P * S, ENNReal.mul_lt_top (ENNReal.mul_lt_top hL hP) hS, ?_⟩
  intro δ hδ hδ₁ A hA hAb f hf hfb
  let φ := sphericalGraphPhase δ (d := d)
  let q := (ENNReal.ofReal y)⁻¹
  let b := (2 : ℝ≥0∞)⁻¹ ^ d
  let α := 2 * x
  let k := 2 * knappProductInput d y
  let m := dyadicWhitneyMass A
  have hφ : Measurable φ := by unfold φ sphericalGraphPhase sphericalPhase; fun_prop
  obtain ⟨hfi, hfs, hfm⟩ := restricted_graph_data hA hAb hf hfb
  by_cases hAz : volume A = 0
  · have he : graphExtension f φ = 0 := by
      funext z
      apply enorm_eq_zero.mp
      exact le_antisymm ((graph_extension_enorm_le_restricted_mass hA hfb φ z).trans_eq hAz) bot_le
    change eLpNorm (graphExtension f φ * graphExtension f φ) q volume ≤ _
    simp [he]
  have hAf : volume A < ⊤ := (measure_mono hAb).trans_lt measure_ball_lt_top
  have hq : 1 ≤ q := by
    change 1 ≤ (ENNReal.ofReal y)⁻¹
    rw [← ENNReal.ofReal_inv_of_pos hy, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_inv₀ hy).mpr hy₁.le)
  let W (j : ℕ) : ℝ≥0∞ :=
    (b ^ j) ^ (-(α - k)) * (∑ p ∈ dyadicWhitneyPairs d j, m j p ^ (α / y)) ^ y
  have hpiece (j : ℕ) :
      eLpNorm (graphWhitneyLayer j φ f f) q volume ≤ (L * P) * W j := by
    refine (HL j hφ hf hf hfi hfi hfs hfs hfm).trans ?_
    have hterms (p : (Fin d → ℤ) × (Fin d → ℤ)) (hp : p ∈ dyadicWhitneyPairs d j) :
        eLpNorm (graphWhitneyTerm j p φ f f) q volume ≤
          (P * (b ^ j) ^ (-(α - k))) * m j p ^ α := by
      have H := HP hδ hδ₁ hA hAb hf hfb j hp
      have he : α - k = 2 * (x - knappProductInput d y) := by unfold α k; ring
      rw [he]
      exact H
    have H := whitney_layer_mass_factor (dyadicWhitneyPairs d j) hy hterms
    exact (mul_le_mul' le_rfl H).trans_eq (by dsimp only [W]; ac_rfl)
  change eLpNorm (graphExtension f φ * graphExtension f φ) q volume ≤ _
  calc
    _ ≤ ∑' j, eLpNorm (graphWhitneyLayer j φ f f) q volume :=
      graph_extension_product_eLpNorm_le_whitney_sum (by omega) hφ hfi.restrict hfi.restrict hq
    _ ≤ ∑' j, (L * P) * W j := ENNReal.tsum_le_tsum hpiece
    _ = (L * P) * ∑' j, W j := ENNReal.tsum_mul_left
    _ ≤ (L * P) * (S * (volume A) ^ k) :=
      mul_le_mul' le_rfl (HS A (pos_iff_ne_zero.mpr hAz) hAf)
    _ = _ := by rw [mul_assoc (L * P) S]

end RestrictionWork
