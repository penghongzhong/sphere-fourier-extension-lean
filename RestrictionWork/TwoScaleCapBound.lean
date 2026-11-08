import RestrictionWork.CriticalCapLocalBound
import RestrictionWork.SphericalPatchPowerError
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- Actual cap estimates at two independently chosen scales, compared
through the same paraboloid. All coefficients are independent of both scales. -/
theorem two_scale_cap_bound {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ≥0, ∀ δ σ : ℝ, 0 < δ → δ ≤ 1/2 → 0 < σ → σ ≤ 1/2 →
      ∀ R : ℝ, 1 ≤ R → ∀ g : Ambient d → ℂ,
      MemLp g (capCriticalExponent d) (patchMeasure d) →
      patchErrorConstant d (capCriticalExponent d) (capCriticalExponent d) < ⊤ ∧
      MemLp (sphericalPatchExtension δ g) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ∧
      eLpNorm (sphericalPatchExtension δ g) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ≤
      ((A : ℝ≥0∞) * ENNReal.ofReal (R ^ η * σ ^ (-2 * η)) +
        patchErrorConstant d (capCriticalExponent d) (capCriticalExponent d) *
          ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * (capCriticalExponent d).toReal⁻¹) *
            (δ ^ 2 + σ ^ 2))) * eLpNorm g (capCriticalExponent d) (patchMeasure d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hp : 1 ≤ capCriticalExponent d := by
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ hd0).mpr
    linarith
  obtain ⟨A, HA⟩ := critical_cap_local_bound hd hη
  refine ⟨A, ?_⟩
  intro δ σ hδ hδ₁ hσ hσ₁ R hR g hg
  have hR0 : 0 < R := by linarith
  obtain ⟨hB, hmδ, Hδ⟩ := spherical_patch_power_error hp hg hδ hδ₁ hR0 (capCriticalExponent d)
  obtain ⟨_, hmσ, Hσ⟩ := spherical_patch_power_error hp hg hσ hσ₁ hR0 (capCriticalExponent d)
  refine ⟨hB, (HA δ hδ hδ₁ R hR g hg).1, ?_⟩
  let F := sphericalPatchExtension δ g
  let H := sphericalPatchExtension σ g
  let P := paraboloidExtension g
  let μ := volume.restrict (Metric.ball (0 : Ambient d × ℝ) R)
  let p := capCriticalExponent d
  have he : F = H + ((F - P) - (H - P)) := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have ht : eLpNorm F p μ ≤ eLpNorm H p μ + eLpNorm (F - P) p μ + eLpNorm (H - P) p μ := by
    calc
      _ = eLpNorm (H + ((F - P) - (H - P))) p μ := congrArg (fun f ↦ eLpNorm f p μ) he
      _ ≤ eLpNorm H p μ + eLpNorm ((F - P) - (H - P)) p μ :=
        eLpNorm_add_le (f := H) (g := (F - P) - (H - P)) (μ := μ) hp
      _ ≤ eLpNorm H p μ + (eLpNorm (F - P) p μ + eLpNorm (H - P) p μ) :=
        add_le_add le_rfl (eLpNorm_sub_le (f := F - P) (g := H - P) (μ := μ) hp)
      _ = _ := (add_assoc _ _ _).symm
  have h := ht.trans (add_le_add (add_le_add (HA σ hσ hσ₁ R hR g hg).2 Hδ) Hσ)
  have hr : ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * p.toReal⁻¹) * δ ^ 2) +
      ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * p.toReal⁻¹) * σ ^ 2) =
      ENNReal.ofReal (R ^ (1 + ((d : ℝ) + 1) * p.toReal⁻¹) * (δ ^ 2 + σ ^ 2)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  change eLpNorm F p μ ≤ _
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [← hr]
      ring

end RestrictionWork
