import RestrictionWork.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace RestrictionWork

def capCriticalExponent (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * ((d : ℝ) + 1) / (d : ℝ))

/-- The full input and output Jacobian factors at the actual critical
exponent cancel the cap-scale power, with the `2π` factor retained. -/
theorem critical_cap_scaling {d : ℕ} (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^
        (capCriticalExponent d).toReal⁻¹ *
      ENNReal.ofReal (2 * δ ^ d) ^ (capCriticalExponent d).toReal⁻¹ =
    ENNReal.ofReal ((2 * Real.pi) ^ ((d : ℝ) / 2) * δ ^ d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpc : 0 < 2 * ((d : ℝ) + 1) / (d : ℝ) := by positivity
  have hp : (capCriticalExponent d).toReal⁻¹ = (d : ℝ) / (2 * ((d : ℝ) + 1)) := by
    rw [capCriticalExponent, ENNReal.toReal_ofReal hpc.le, inv_div]
  rw [hp, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  have hb : ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) * (2 * δ ^ d) =
      (2 * Real.pi) ^ (d + 1) * δ ^ (2 * d + 2) := by
    have he : d + 2 + d = 2 * d + 2 := by omega
    rw [← he, pow_add δ (d + 2) d]
    ring
  rw [hb, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have hfirst : ((2 * Real.pi) ^ (d + 1)) ^ ((d : ℝ) / (2 * ((d : ℝ) + 1))) =
      (2 * Real.pi) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    field_simp
    <;> ring
  have hsecond : (δ ^ (2 * d + 2)) ^ ((d : ℝ) / (2 * ((d : ℝ) + 1))) = δ ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
    <;> ring
  rw [hfirst, hsecond]

end RestrictionWork
