import RestrictionWork.KnappInterpolationGeometry

set_option autoImplicit false
noncomputable section

namespace RestrictionWork

/-- Reciprocal of the sequence exponent min(R,R') for the Whitney layer
when the reciprocal of the physical output exponent R is y. -/
def whitneySequenceReciprocal (y : ℝ) : ℝ := max y (1 - y)

/-- The Knapp mass power leaves a strictly positive fine-scale gain for
both branches of the same-layer almost orthogonality estimate. -/
theorem whitney_sequence_reciprocal_lt_knapp_mass {d : ℕ} (hd : 2 ≤ d)
    {y : ℝ} (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    0 < whitneySequenceReciprocal y ∧
      whitneySequenceReciprocal y < 2 * knappProductInput d y := by
  have hd₁ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd₂ : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hy₁ : y < 1 := hyD.trans ((div_lt_one (by positivity)).mpr (by linarith))
  have hgain := knapp_input_sub_diagonal (by omega : 0 < d) y
  have hpos : 0 < ((d : ℝ) + 1) / d * ((d : ℝ) / ((d : ℝ) + 1) - y) :=
    mul_pos (by positivity) (sub_pos.mpr hyD)
  refine ⟨hy.trans_le (le_max_left _ _), max_lt (by linarith) ?_⟩
  have hy₂ : 2 * y < (d : ℝ) := by linarith
  have hdiff : 2 * knappProductInput d y - (1 - y) = 1 - (2 * y) / d := by
    unfold knappProductInput
    field_simp [hd₁.ne']
    ring
  have h : (2 * y) / (d : ℝ) < 1 := (div_lt_one hd₁).mpr hy₂
  linarith

end RestrictionWork
