import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RestrictionWork

/-- Log convexity of the output norm in reciprocal coordinates, including
the endpoint with reciprocal exponent zero. -/
theorem eLpNorm_reciprocal_interpolate {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E} (hf : AEStronglyMeasurable f μ)
    {s t θ : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hθ : 0 < θ) (hθ1 : θ < 1) :
    eLpNorm f (ENNReal.ofReal (θ * s + (1 - θ) * t))⁻¹ μ ≤
      eLpNorm f (ENNReal.ofReal s)⁻¹ μ ^ θ *
        eLpNorm f (ENNReal.ofReal t)⁻¹ μ ^ (1 - θ) := by
  let P := (ENNReal.ofReal (θ * s))⁻¹
  let Q := (ENNReal.ofReal ((1 - θ) * t))⁻¹
  let R := (ENNReal.ofReal (θ * s + (1 - θ) * t))⁻¹
  have hθ' : 0 < 1 - θ := sub_pos.mpr hθ1
  let : ENNReal.HolderTriple P Q R := ⟨by
    simp only [P, Q, R, inv_inv]
    exact (ENNReal.ofReal_add (mul_nonneg hθ.le hs) (mul_nonneg hθ'.le ht)).symm⟩
  let g : X → ℝ := fun x => ‖f x‖ ^ θ
  let h : X → ℝ := fun x => ‖f x‖ ^ (1 - θ)
  have hg : AEStronglyMeasurable g μ :=
    (Real.continuous_rpow_const hθ.le).comp_aestronglyMeasurable hf.norm
  have hh : AEStronglyMeasurable h μ :=
    (Real.continuous_rpow_const hθ'.le).comp_aestronglyMeasurable hf.norm
  have hprod : g • h = fun x => ‖f x‖ := by
    funext x
    change ‖f x‖ ^ θ * ‖f x‖ ^ (1 - θ) = ‖f x‖
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) hθ.le hθ'.le, add_sub_cancel, Real.rpow_one]
  have hexp (z a : ℝ) (ha : 0 < a) :
      (ENNReal.ofReal (a * z))⁻¹ * ENNReal.ofReal a = (ENNReal.ofReal z)⁻¹ := by
    have ha₀ : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
    rw [ENNReal.ofReal_mul ha.le, ENNReal.mul_inv (Or.inl ha₀)
      (Or.inl ENNReal.ofReal_ne_top), mul_right_comm,
      ENNReal.inv_mul_cancel ha₀ ENNReal.ofReal_ne_top, one_mul]
  have H := eLpNorm_smul_le_mul_eLpNorm (p := P) (q := Q) (r := R) hg hh
  rw [hprod, eLpNorm_norm f hf] at H
  change eLpNorm f R μ ≤ eLpNorm (fun x => ‖f x‖ ^ θ) P μ *
    eLpNorm (fun x => ‖f x‖ ^ (1 - θ)) Q μ at H
  rw [eLpNorm_norm_rpow f hf hθ, eLpNorm_norm_rpow f hf hθ',
    show P * ENNReal.ofReal θ = (ENNReal.ofReal s)⁻¹ from hexp s θ hθ,
    show Q * ENNReal.ofReal (1 - θ) = (ENNReal.ofReal t)⁻¹ from hexp t (1 - θ) hθ'] at H
  exact H

end RestrictionWork
