import RestrictionWork.JSP001040Main

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RestrictionWork

/-- The sphere restriction conjecture in the catalog’s Hölder conjugate form. -/
theorem jsp001040_catalog_statement
    (n : ℕ) (hn : 3 ≤ n) (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    BoundedSphereExtension n p q ↔
      ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q ∧
      ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹ ≤ q := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let a : ℝ := ((n : ℝ) - 1) / ((n : ℝ) + 1)
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  let B : ℝ≥0∞ := ENNReal.ofReal a * (1 - p⁻¹)
  have hp' : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp
  have hq' : q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le hq).ne'
  have hBt : B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((tsub_le_self.trans_lt ENNReal.one_lt_top).ne)
  have hBr : B.toReal = a * (1 - (p⁻¹).toReal) := by
    dsimp [B]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
      ENNReal.toReal_sub_of_le hp' ENNReal.one_ne_top, ENNReal.toReal_one]
  have hBinv : B⁻¹ =
      ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹ := by
    have hA0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
    dsimp [B]
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_inv_of_pos ha]
    simp only [a, inv_div]
  have H := fullSphereRestrictionConjecture n hn p q hp hq
  unfold AdmissibleExponents at H
  rw [← hBinv, ← ENNReal.inv_le_iff_inv_le,
    ← ENNReal.toReal_le_toReal hq' hBt, hBr]
  simpa [hp, hq, a] using H

end RestrictionWork
