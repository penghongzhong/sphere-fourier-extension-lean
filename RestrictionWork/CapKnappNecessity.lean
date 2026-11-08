import RestrictionWork.CapCoherentNorm
import RestrictionWork.CapJacobianPower
import RestrictionWork.SmallPowerNecessity
import RestrictionWork.OriginalCapLocalInput
import RestrictionWork.Target

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- Knapp necessity follows from the actual original extension estimate,
the coherent cap lower bound and the exact cap norm transfer. -/
theorem cap_knapp_necessity {d : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hE : BoundedSphereExtension (d + 1) p q) :
    (q⁻¹).toReal ≤ ((d : ℝ) / ((d : ℝ) + 2)) * (1 - (p⁻¹).toReal) := by
  haveI : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨C, HC⟩ := hE
  obtain ⟨b, hb, Hb⟩ := cap_coherent_norm d hq
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  let G := eLpNorm (fun _ : Ambient d ↦ (1 : ℂ)) p (patchMeasure d)
  have hG : G < ⊤ := memLp_const _
  let K : ℝ := ((2 * Real.pi) ^ (d + 1) / 2) ^ q.toReal⁻¹ * (2 : ℝ) ^ p.toReal⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let e : ℝ := ((d : ℝ) + 2) * q.toReal⁻¹ + (d : ℝ) * p.toReal⁻¹
  let A : ℝ := K * (C : ℝ) * G.toReal
  have Hscalar : ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
      δ ^ (d : ℝ) ≤ (A / (b : ℝ)) * δ ^ e := by
    intro δ hδ hδ₁
    have H := original_cap_local_input (R := 1) (η := 0) hδ hδ₁ le_rfl hp
      (g := fun _ : Ambient d ↦ (1 : ℂ)) (memLp_const _) C (fun L _ f hf ↦ by
        simpa only [Real.rpow_zero, ENNReal.ofReal_one, mul_one] using
          (eLpNorm_mono_measure (f := extension f) (p := q)
            Measure.restrict_le_self).trans (HC f hf).2)
    have H' : ENNReal.ofReal (δ ^ d) * (b : ℝ≥0∞) ≤
        ENNReal.ofReal (K * δ ^ e) * (C : ℝ≥0∞) * G := by
      calc
        _ ≤ ENNReal.ofReal (δ ^ d) *
            eLpNorm (sphericalPatchExtension δ (fun _ : Ambient d ↦ (1 : ℂ))) q
              (volume.restrict (Metric.ball 0 1)) := mul_le_mul' le_rfl (Hb δ hδ hδ₁)
        _ ≤ _ := H
        _ = (ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^ q.toReal⁻¹ *
            ENNReal.ofReal (2 * δ ^ d) ^ p.toReal⁻¹) * (C : ℝ≥0∞) * G := by
          simp only [Real.rpow_zero, ENNReal.ofReal_one, mul_one]
          ring
        _ = _ := by rw [cap_jacobian_power d p q hδ]
    have hfinite : ENNReal.ofReal (K * δ ^ e) * (C : ℝ≥0∞) * G ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) hG.ne
    have Hr := ENNReal.toReal_mono hfinite H'
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at Hr
    rw [ENNReal.toReal_ofReal (pow_pos hδ d).le,
      ENNReal.toReal_ofReal (mul_pos hK (Real.rpow_pos_of_pos hδ e)).le] at Hr
    rw [Real.rpow_natCast]
    calc
      δ ^ d ≤ (A * δ ^ e) / (b : ℝ) := by
        apply (le_div_iff₀ hbR).mpr
        dsimp [A]
        convert Hr using 1 <;> ring
      _ = _ := by ring
  have H := small_power_necessity Hscalar
  simp only [ENNReal.toReal_inv]
  have he : ((d : ℝ) / ((d : ℝ) + 2)) * (1 - p.toReal⁻¹) =
      ((d : ℝ) - (d : ℝ) * p.toReal⁻¹) / ((d : ℝ) + 2) := by ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < (d : ℝ) + 2)).mpr
  dsimp [e] at H
  nlinarith only [H]

end RestrictionWork
