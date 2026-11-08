import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace RestrictionWork

/-- The input reciprocal on the Knapp line at bilinear output reciprocal y. -/
def knappProductInput (d : ℕ) (y : ℝ) : ℝ :=
  1 - ((d : ℝ) + 2) / (2 * d) * y

/-- The radial boundary meets the diagonal line x = y / 2. -/
theorem knapp_input_sub_diagonal {d : ℕ} (hd : 0 < d) (y : ℝ) :
    knappProductInput d y - y / 2 =
      ((d : ℝ) + 1) / d * ((d : ℝ) / ((d : ℝ) + 1) - y) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast hd
  unfold knappProductInput
  field_simp [hd₀.ne', show (d : ℝ) + 1 ≠ 0 by positivity]
  ring

/-- Moving the diagonal endpoint into its strict range still leaves an
input gain at any prescribed intermediate output reciprocal. -/
theorem knapp_diagonal_interpolation {d : ℕ} (hd : 2 ≤ d) {x y : ℝ}
    (hx : knappProductInput d (1 / 2) < x)
    (hy : 1 / 2 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ θ z : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < z ∧ z < (d : ℝ) / ((d : ℝ) + 1) ∧
      θ * (1 / 2) + (1 - θ) * z = y ∧
      knappProductInput d y < θ * x + (1 - θ) * (z / 2) := by
  let D : ℝ := (d : ℝ) / ((d : ℝ) + 1)
  let k : ℝ := ((d : ℝ) + 1) / d
  let g : ℝ := x - 1 / 4
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hk : 0 < k := by unfold k; positivity
  have hD : (1 / 2 : ℝ) < D := hy.trans hyD
  have hD₀ : 0 < D - 1 / 2 := sub_pos.mpr hD
  have hy₀ : 0 < D - y := sub_pos.mpr hyD
  have hdiff (z : ℝ) : knappProductInput d z - z / 2 = k * (D - z) :=
    knapp_input_sub_diagonal (by omega) z
  have hg : k * (D - 1 / 2) < g := by
    have H := hdiff (1 / 2)
    dsimp only [g]
    linarith
  have hg₀ : 0 < g := (mul_pos hk hD₀).trans hg
  let a : ℝ := k * (D - y) / g
  let b : ℝ := (D - y) / (D - 1 / 2)
  have ha : 0 < a := div_pos (mul_pos hk hy₀) hg₀
  have hab : a < b := by
    apply (div_lt_div_iff₀ hg₀ hD₀).mpr
    calc
      k * (D - y) * (D - 1 / 2) = (D - y) * (k * (D - 1 / 2)) := by ring
      _ < (D - y) * g := mul_lt_mul_of_pos_left hg hy₀
  have hb : b < 1 := (div_lt_iff₀ hD₀).mpr (by linarith)
  obtain ⟨θ, haθ, hθb⟩ := exists_between hab
  have hθ : 0 < θ := ha.trans haθ
  have hθ₁ : θ < 1 := hθb.trans hb
  have hθ' : 0 < 1 - θ := sub_pos.mpr hθ₁
  let z := (y - θ * (1 / 2)) / (1 - θ)
  have hz : 0 < z := div_pos (by linarith) hθ'
  have hzD : z < D := by
    apply (div_lt_iff₀ hθ').mpr
    have H := (lt_div_iff₀ hD₀).mp hθb
    nlinarith only [H]
  have hy_eq : θ * (1 / 2) + (1 - θ) * z = y := by
    unfold z
    field_simp [hθ'.ne']; ring
  have hgain : k * (D - y) < θ * g := (div_lt_iff₀ hg₀).mp haθ
  refine ⟨θ, z, hθ, hθ₁, hz, hzD, hy_eq, ?_⟩
  dsimp only [g] at hgain
  nlinarith only [hgain, hy_eq, hdiff y]

end RestrictionWork
