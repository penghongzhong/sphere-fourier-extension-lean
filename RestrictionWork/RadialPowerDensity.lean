import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace RestrictionWork

/-- A normalized amplitude lower bound gives a reciprocal lower bound for
the radial power density throughout the subcritical and critical range. -/
theorem radial_power_density {r a u β q : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (ha : 0 < a) (hq : 0 ≤ q)
    (hweight : β * q ≤ (m : ℝ) + 1) (hamp : a ≤ r ^ β * u) :
    a ^ q / r ≤ r ^ m * u ^ q := by
  have hr0 : 0 < r := by linarith
  have hrβ : 0 < r ^ β := Real.rpow_pos_of_pos hr0 β
  have hl : a / r ^ β ≤ u := by
    apply (div_le_iff₀ hrβ).mpr
    simpa only [mul_comm u (r ^ β)] using hamp
  have hpow := Real.rpow_le_rpow (div_nonneg ha.le hrβ.le) hl hq
  have hweight' : (-1 : ℝ) ≤ (m : ℝ) - β * q := by linarith
  calc
    _ = a ^ q * r ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hr0.le, Real.rpow_one, div_eq_mul_inv]
    _ ≤ a ^ q * r ^ ((m : ℝ) - β * q) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr hweight')
        (Real.rpow_nonneg ha.le q)
    _ = r ^ m * (a / r ^ β) ^ q := by
      rw [Real.rpow_sub hr0, Real.rpow_natCast, Real.div_rpow ha.le hrβ.le,
        ← Real.rpow_mul hr0.le]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (pow_nonneg hr0.le m)

end RestrictionWork
