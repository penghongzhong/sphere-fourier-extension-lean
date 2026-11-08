import RestrictionWork.KnappInterpolationGeometry

set_option autoImplicit false
noncomputable section

namespace RestrictionWork

/-- In the interior radial range, two nearby points on the Knapp line
admit the same pair of positive Hölder weights for restricted pairing. -/
theorem exists_restricted_strong_nearby {d : ℕ} (hd : 2 ≤ d)
    {y : ℝ} (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < y - ε ∧ y + ε < (d : ℝ) / ((d : ℝ) + 1) ∧
      0 < b ∧ b < 1 ∧ (y - ε) / 2 ≤ b ∧ (y + ε) / 2 ≤ b ∧
      b ≤ knappProductInput d (y - ε) ∧ b ≤ knappProductInput d (y + ε) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  let D : ℝ := (d : ℝ) / ((d : ℝ) + 1)
  let a : ℝ := ((d : ℝ) + 2) / (2 * d)
  let g : ℝ := knappProductInput d y - y / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hg : 0 < g := by
    dsimp only [g]
    rw [knapp_input_sub_diagonal (by omega : 0 < d)]
    exact mul_pos (by positivity) (sub_pos.mpr hyD)
  let ε : ℝ := min (y / 2) (min ((D - y) / 2) (g / (2 * (a + 1))))
  let b : ℝ := y / 2 + g / 2
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by
    have : 0 < D - y := sub_pos.mpr hyD
    positivity) (by positivity))
  have hεy : ε ≤ y / 2 := min_le_left _ _
  have hεD : ε ≤ (D - y) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεg : ε ≤ g / (2 * (a + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hεg' := (le_div_iff₀ (by positivity : 0 < 2 * (a + 1))).mp hεg
  have hεa : a * ε ≤ g / 2 := by nlinarith only [hεg', hε]
  have hεle : ε ≤ g := by nlinarith only [hεg', hε, mul_nonneg ha.le hε.le]
  have hb : 0 < b := by dsimp [b]; positivity
  have hy₁ : y < 1 := hyD.trans ((div_lt_iff₀ (by positivity)).mpr (by linarith))
  have hky : knappProductInput d y < 1 := by
    change 1 - a * y < 1
    linarith [mul_pos ha hy]
  have hb₁ : b < 1 := by dsimp only [b, g]; linarith
  have hplus : y + ε < D := by linarith only [hεD, (show y < D from hyD)]
  have hKplus : b ≤ knappProductInput d (y + ε) := by
    change b ≤ 1 - a * (y + ε)
    have hg' : g = 1 - a * y - y / 2 := rfl
    dsimp only [b]
    rw [mul_add]
    linarith
  have hKmono : knappProductInput d (y + ε) ≤ knappProductInput d (y - ε) := by
    change 1 - a * (y + ε) ≤ 1 - a * (y - ε)
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (by linarith) ha.le) _
  refine ⟨ε, b, hε, by linarith, hplus, hb, hb₁, ?_, ?_, hKplus.trans hKmono, hKplus⟩
  all_goals dsimp only [b]; linarith

end RestrictionWork
