import RestrictionWork.CapKnappNecessity

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace RestrictionWork

/-- The Knapp half of necessity for the unchanged original sphere operator,
in all original dimensions and for all extended input/output exponents. -/
theorem original_knapp_necessary {n : ℕ} (hn : 3 ≤ n) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hE : BoundedSphereExtension n p q) :
    (q⁻¹).toReal ≤ (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have H := cap_knapp_necessity hp hq hE
  simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    add_assoc, one_add_one_eq_two] using H

end RestrictionWork
