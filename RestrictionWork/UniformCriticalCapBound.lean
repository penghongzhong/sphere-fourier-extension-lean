import RestrictionWork.TwoScaleCapBound
import RestrictionWork.BalancedCapScale
import RestrictionWork.LargeCapScaleLoss

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- The actual centered spherical cap family satisfies the critical local
estimate with a constant independent of the cap scale. -/
theorem uniform_critical_cap_bound {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → ∀ R : ℝ, 1 ≤ R →
      ∀ g : Ambient d → ℂ, MemLp g (capCriticalExponent d) (patchMeasure d) →
      MemLp (sphericalPatchExtension δ g) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ∧
      eLpNorm (sphericalPatchExtension δ g) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (R ^ ε) *
        eLpNorm g (capCriticalExponent d) (patchMeasure d) := by
  let p := capCriticalExponent d
  let κ : ℝ := 1 + ((d : ℝ) + 1) * p.toReal⁻¹
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  let η : ℝ := ε / (1 + κ)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηκ : η * (1 + κ) = ε := by
    dsimp [η]
    exact div_mul_cancel₀ ε (by linarith)
  obtain ⟨A₁, H₁⟩ := critical_cap_local_bound hd hη
  obtain ⟨A₂, H₂⟩ := two_scale_cap_bound hd hη
  let B := patchErrorConstant d p p
  have hB : B < ⊤ :=
    (H₂ (1/2) (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) 1 le_rfl 0 MemLp.zero).1
  let k := ENNReal.ofReal ((2 : ℝ) ^ (2 * η))
  let D : ℝ≥0∞ := (A₁ : ℝ≥0∞) + ((A₂ : ℝ≥0∞) * k + 2 * B)
  have hD : D ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨ENNReal.coe_ne_top, ENNReal.add_ne_top.mpr ⟨?_, ?_⟩⟩
    · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) hB.ne
  refine ⟨D.toNNReal, ?_⟩
  intro δ hδ hδ₁ R hR g hg
  have hR0 : 0 < R := by linarith
  have hQ : 1 ≤ ENNReal.ofReal (R ^ ε) :=
    ENNReal.one_le_ofReal.mpr (Real.one_le_rpow hR hε.le)
  have hA₁ : (A₁ : ℝ≥0∞) ≤ D := by exact le_self_add
  have hA₂ : (A₂ : ℝ≥0∞) * k + 2 * B ≤ D := by
    calc
      _ ≤ ((A₂ : ℝ≥0∞) * k + 2 * B) + (A₁ : ℝ≥0∞) := le_self_add
      _ = D := by dsimp [D]; ring
  rw [ENNReal.coe_toNNReal hD]
  refine ⟨(H₁ δ hδ hδ₁ R hR g hg).1, ?_⟩
  by_cases hsmall : R ^ κ * δ ^ 2 ≤ 1
  · obtain ⟨σ, hσ, hσ₁, hσerr, hσloss⟩ := balanced_cap_scale (η := η) hκ hR
    have herr : R ^ κ * (δ ^ 2 + σ ^ 2) ≤ 2 := by nlinarith
    have hloss : ENNReal.ofReal (R ^ η * σ ^ (-2 * η)) =
        k * ENNReal.ofReal (R ^ ε) := by
      rw [hσloss, hηκ, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    have he : ENNReal.ofReal (R ^ κ * (δ ^ 2 + σ ^ 2)) ≤ 2 := by
      simpa using ENNReal.ofReal_le_ofReal herr
    have H := (H₂ δ σ hδ hδ₁ hσ hσ₁ R hR g hg).2.2
    change eLpNorm (sphericalPatchExtension δ g) p _ ≤
      ((A₂ : ℝ≥0∞) * ENNReal.ofReal (R ^ η * σ ^ (-2 * η)) +
        B * ENNReal.ofReal (R ^ κ * (δ ^ 2 + σ ^ 2))) * eLpNorm g p _ at H
    rw [hloss] at H
    calc
      _ ≤ _ := H
      _ ≤ ((A₂ : ℝ≥0∞) * (k * ENNReal.ofReal (R ^ ε)) + B * 2) *
          eLpNorm g p (patchMeasure d) :=
        mul_le_mul' (add_le_add le_rfl (mul_le_mul' le_rfl he)) le_rfl
      _ ≤ ((A₂ : ℝ≥0∞) * (k * ENNReal.ofReal (R ^ ε)) +
          (B * 2) * ENNReal.ofReal (R ^ ε)) * eLpNorm g p (patchMeasure d) := by
        apply mul_le_mul' _ le_rfl
        apply add_le_add le_rfl
        simpa using mul_le_mul' (le_refl (B * 2)) hQ
      _ = (((A₂ : ℝ≥0∞) * k + 2 * B) * ENNReal.ofReal (R ^ ε)) *
          eLpNorm g p (patchMeasure d) := by ring
      _ ≤ _ := mul_le_mul' (mul_le_mul' hA₂ le_rfl) le_rfl
  · have hloss : R ^ η * δ ^ (-2 * η) ≤ R ^ ε := by
      have H := large_cap_scale_loss hη.le hR hδ (le_of_lt (lt_of_not_ge hsmall))
      simpa only [hηκ] using H
    calc
      _ ≤ _ := (H₁ δ hδ hδ₁ R hR g hg).2
      _ ≤ (A₁ : ℝ≥0∞) * ENNReal.ofReal (R ^ ε) *
          eLpNorm g p (patchMeasure d) :=
        mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hloss)) le_rfl
      _ ≤ _ := mul_le_mul' (mul_le_mul' hA₁ le_rfl) le_rfl

end RestrictionWork
