import RestrictionWork.ShiftedSphericalLocalBound
import RestrictionWork.GraphPhasePowerError

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- The critical local estimate for actual translated isotropic spherical
subcaps, uniform in the parent scale, center, and subcap radius. -/
theorem uniform_shifted_spherical_subcap_bound {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ a : Ambient d, ‖a‖ ≤ 1 / 2 →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ R : ℝ, 1 ≤ R →
      ∀ g : Ambient d → ℂ, MemLp g (capCriticalExponent d) (patchMeasure d) →
      MemLp (graphExtension g (shiftedSphericalGraphPhase δ a r)) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ∧
      eLpNorm (graphExtension g (shiftedSphericalGraphPhase δ a r)) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (R ^ ε) * eLpNorm g (capCriticalExponent d) (patchMeasure d) := by
  let p := capCriticalExponent d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hp : 1 ≤ p := by
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ hd0).mpr
    linarith
  let κ : ℝ := 1 + ((d : ℝ) + 1) * p.toReal⁻¹
  have hκ : 0 ≤ 2 * κ := by dsimp only [κ]; positivity
  let η : ℝ := ε / (1 + 2 * κ)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηκ : η * (1 + 2 * κ) = ε := by
    dsimp only [η]
    exact div_mul_cancel₀ ε (by linarith)
  obtain ⟨A, HA⟩ := shifted_spherical_local_bound hd hη
  let B := patchErrorConstant d p p
  have hB : B < ⊤ := patch_error_constant_lt_top hp p
  let k := ENNReal.ofReal ((2 : ℝ) ^ (2 * η))
  let D : ℝ≥0∞ := (A : ℝ≥0∞) * k + 140 * B
  have hk : 1 ≤ k :=
    ENNReal.one_le_ofReal.mpr (Real.one_le_rpow (by norm_num) (by positivity))
  have hD : D ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (by norm_num) hB.ne⟩
  have hA : (A : ℝ≥0∞) ≤ D := by
    calc
      _ ≤ (A : ℝ≥0∞) * k := by simpa only [mul_one] using mul_le_mul' (le_refl (A : ℝ≥0∞)) hk
      _ ≤ _ := le_self_add
  refine ⟨D.toNNReal, ?_⟩
  intro δ hδ hδhalf a ha r hr hrhalf R hR g hg
  have hR0 : 0 < R := by linarith
  let Q := ENNReal.ofReal (R ^ ε)
  have hQ : 1 ≤ Q := ENNReal.one_le_ofReal.mpr (Real.one_le_rpow hR hε.le)
  have hsquare (t : ℝ) : R ^ (2 * κ) * t ^ 2 = (R ^ κ * t) ^ 2 := by
    rw [mul_comm (2 : ℝ) κ, Real.rpow_mul hR0.le, Real.rpow_two, mul_pow]
  rw [ENNReal.coe_toNNReal hD]
  refine ⟨(HA δ hδ hδhalf a ha r hr hrhalf R hR g hg).1, ?_⟩
  by_cases hsmall : R ^ κ * r ≤ 1
  · obtain ⟨σ, hσ, hσhalf, hσsquare, hσloss⟩ := balanced_cap_scale (η := η) hκ hR
    rw [hsquare] at hσsquare
    have hσsmall : R ^ κ * σ ≤ 1 := by
      nlinarith [sq_nonneg (R ^ κ * σ - 1)]
    let φ := shiftedSphericalGraphPhase δ a r
    let ψ := shiftedSphericalGraphPhase δ a σ
    let T := Metric.ball (0 : Ambient d × ℝ) R
    let τ := 70 * δ ^ 2 * (r + σ)
    have hφ : Measurable φ := by
      unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
      fun_prop
    have hψ : Measurable ψ := by
      unfold ψ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
      fun_prop
    have hclose : ∀ᵐ u ∂patchMeasure d, |φ u - ψ u| ≤ τ := by
      have H : ∀ᵐ u ∂patchMeasure d, u ∈ Metric.ball (0 : Ambient d) 1 :=
        ae_restrict_mem measurableSet_ball
      filter_upwards [H] with u hu
      exact shifted_spherical_graph_scale_difference hδ hδhalf ha hr hrhalf hσ hσhalf
        (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hu))
    have hτ : 0 ≤ τ := by dsimp only [τ]; positivity
    have herr : R ^ κ * τ ≤ 140 := by
      have hsum : R ^ κ * (r + σ) ≤ 2 := by rw [mul_add]; linarith
      have hδsq : δ ^ 2 ≤ 1 := by nlinarith
      calc
        _ = 70 * (δ ^ 2 * (R ^ κ * (r + σ))) := by unfold τ; ring
        _ ≤ 70 * (1 * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hδsq hsum (by positivity) zero_le_one) (by norm_num)
        _ = _ := by norm_num
    have he : ENNReal.ofReal (R ^ κ * τ) ≤ 140 := by simpa using ENNReal.ofReal_le_ofReal herr
    have herror := (graph_phase_power_error hp hg hφ hψ hτ hclose hR0 p).2
    have Hσ := (HA δ hδ hδhalf a ha σ hσ hσhalf R hR g hg).2
    have hloss : ENNReal.ofReal (R ^ η * σ ^ (-2 * η)) = k * Q := by
      rw [hσloss, hηκ, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    rw [hloss] at Hσ
    change eLpNorm (graphExtension g φ) p (volume.restrict T) ≤
      D * Q * eLpNorm g p (patchMeasure d)
    have htriangle :
        eLpNorm (graphExtension g φ) p (volume.restrict T) ≤
          eLpNorm (graphExtension g ψ) p (volume.restrict T) +
          eLpNorm (graphExtension g φ - graphExtension g ψ) p (volume.restrict T) := by
      calc
        _ = eLpNorm (graphExtension g ψ + (graphExtension g φ - graphExtension g ψ)) p
            (volume.restrict T) := by rw [add_comm, sub_add_cancel]
        _ ≤ _ := eLpNorm_add_le hp
    calc
      _ ≤ _ := htriangle
      _ ≤ (A : ℝ≥0∞) * (k * Q) * eLpNorm g p (patchMeasure d) +
          B * ENNReal.ofReal (R ^ κ * τ) * eLpNorm g p (patchMeasure d) := add_le_add Hσ herror
      _ ≤ (A : ℝ≥0∞) * (k * Q) * eLpNorm g p (patchMeasure d) +
          B * (140 * Q) * eLpNorm g p (patchMeasure d) := by
        apply add_le_add le_rfl (mul_le_mul' (mul_le_mul' le_rfl _) le_rfl)
        exact he.trans (by simpa only [mul_one] using mul_le_mul' (le_refl (140 : ℝ≥0∞)) hQ)
      _ = _ := by unfold D; ring
  · have hbig : 1 ≤ R ^ (2 * κ) * r ^ 2 := by
      rw [hsquare]
      nlinarith [lt_of_not_ge hsmall, sq_nonneg (R ^ κ * r - 1)]
    have hloss : R ^ η * r ^ (-2 * η) ≤ R ^ ε := by
      simpa only [hηκ] using large_cap_scale_loss hη.le hR hr hbig
    calc
      _ ≤ _ := (HA δ hδ hδhalf a ha r hr hrhalf R hR g hg).2
      _ ≤ (A : ℝ≥0∞) * ENNReal.ofReal (R ^ ε) * eLpNorm g p (patchMeasure d) :=
        mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hloss)) le_rfl
      _ ≤ _ := mul_le_mul' (mul_le_mul' hA le_rfl) le_rfl

end RestrictionWork
