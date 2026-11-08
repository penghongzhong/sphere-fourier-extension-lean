import RestrictionWork.PhaseExtensionDefinitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace RestrictionWork

/-- The spherical height after subtracting its affine part and dividing by the
square of the subcap radius. -/
def shiftedSphericalHeight (δ r s A B : ℝ) : ℝ :=
  (sphericalPhase δ (s + 2 * r * A + r ^ 2 * B) - sphericalPhase δ s -
    2 * r * A / Real.sqrt (1 - δ ^ 2 * s)) / r ^ 2

/-- Quadratic tangent phase at squared radius (s). -/
def sphericalTangentHeight (δ s A B : ℝ) : ℝ :=
  B / Real.sqrt (1 - δ ^ 2 * s) +
    (δ ^ 2 / Real.sqrt (1 - δ ^ 2 * s)) *
      (A / Real.sqrt (1 - δ ^ 2 * s)) ^ 2

/-- Exact rationalization of the translated phase gives a uniform remainder
bound linear in the subcap radius. -/
theorem shifted_spherical_height_error {δ r s A B : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hr : 0 < r) (hrone : r ≤ 1)
    (hs : s ≤ 1) (hs' : s + 2 * r * A + r ^ 2 * B ≤ 1)
    (hA : |A| ≤ 1) (hB : 0 ≤ B) (hB₁ : B ≤ 1) :
    |shiftedSphericalHeight δ r s A B - sphericalTangentHeight δ s A B| ≤
      70 * δ ^ 2 * r := by
  let h := Real.sqrt (1 - δ ^ 2 * s)
  let k := Real.sqrt (1 - δ ^ 2 * (s + 2 * r * A + r ^ 2 * B))
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have harg : 3 / 4 ≤ 1 - δ ^ 2 * s := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg δ)]
  have harg' : 3 / 4 ≤ 1 - δ ^ 2 * (s + 2 * r * A + r ^ 2 * B) := by
    nlinarith only [hδsq, mul_le_mul_of_nonneg_left hs' (sq_nonneg δ)]
  have hh : 1 / 2 ≤ h := Real.le_sqrt_of_sq_le (by linarith only [harg])
  have hk : 1 / 2 ≤ k := Real.le_sqrt_of_sq_le (by linarith only [harg'])
  have hhpos : 0 < h := by linarith
  have hhk : 1 ≤ h + k := by linarith
  have hhkpos : 0 < h + k := by linarith
  have hh2 : h ^ 2 = 1 - δ ^ 2 * s := Real.sq_sqrt (by linarith)
  have hk2 : k ^ 2 = 1 - δ ^ 2 * (s + 2 * r * A + r ^ 2 * B) :=
    Real.sq_sqrt (by linarith)
  let U := (2 * A + r * B) / (h + k)
  let V := A / h
  have hsplit : (h - k) * (h + k) = δ ^ 2 * r * (2 * A + r * B) := by
    nlinarith only [hh2, hk2]
  have hdiff : h - k = δ ^ 2 * r * U := by
    dsimp only [U]
    apply (eq_div_iff hhkpos.ne').mpr at hsplit
    rw [hsplit, mul_div_assoc]
  have hrat : 2 * h * (h - k) = δ ^ 2 * r * (2 * A + r * B) + (h - k) ^ 2 := by
    nlinarith only [hsplit]
  have hphase : shiftedSphericalHeight δ r s A B = B / h + (δ ^ 2 / h) * U ^ 2 := by
    calc
      _ = (2 * h * (h - k) - 2 * δ ^ 2 * r * A) / (δ ^ 2 * r ^ 2 * h) := by
        unfold shiftedSphericalHeight sphericalPhase
        change ((2 * (1 - k) / δ ^ 2 - 2 * (1 - h) / δ ^ 2 -
          2 * r * A / h) / r ^ 2) = _
        field_simp [hδ.ne', hr.ne', hhpos.ne']
        ring
      _ = _ := by
        rw [hrat, hdiff]
        field_simp [hδ.ne', hr.ne', hhpos.ne']
        ring
  have hrB : r * B ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hB₁ hr.le
  have hU : |U| ≤ 3 := by
    dsimp only [U]
    rw [abs_div, abs_of_pos hhkpos, div_le_iff₀ hhkpos]
    calc
      _ ≤ |2 * A| + |r * B| := abs_add_le _ _
      _ = 2 * |A| + r * B := by rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos hr, abs_of_nonneg hB]
      _ ≤ 3 * (h + k) := by linarith
  have hV : |V| ≤ 2 := by
    dsimp only [V]
    rw [abs_div, abs_of_pos hhpos, div_le_iff₀ hhpos]
    linarith
  have hdiff₁ : |h - k| ≤ 3 * r := by
    rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg δ) hr.le)]
    calc
      _ ≤ (δ ^ 2 * r) * 3 := mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ 3 * r := by nlinarith [mul_le_mul_of_nonneg_right hδsq hr.le]
  have hdenom : 0 < h * (h + k) := mul_pos hhpos hhkpos
  have hdenom₁ : 1 / 2 ≤ h * (h + k) := by
    simpa only [mul_one] using
      mul_le_mul hh hhk (by norm_num : (0 : ℝ) ≤ 1) hhpos.le
  have hsub : U - V = r * B / (h + k) + A * (h - k) / (h * (h + k)) := by
    dsimp only [U, V]
    field_simp [hhpos.ne', hhkpos.ne']
    ring
  have hterm₁ : |r * B / (h + k)| ≤ r := by
    rw [abs_div, abs_of_nonneg (mul_nonneg hr.le hB), abs_of_pos hhkpos,
      div_le_iff₀ hhkpos]
    exact hrB.trans (le_mul_of_one_le_right hr.le hhk)
  have hterm₂ : |A * (h - k) / (h * (h + k))| ≤ 6 * r := by
    rw [abs_div, abs_mul, abs_of_pos hdenom, div_le_iff₀ hdenom]
    calc
      _ ≤ 1 * (3 * r) := mul_le_mul hA hdiff₁ (abs_nonneg _) zero_le_one
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hdenom₁ hr.le]
  have hUV : |U - V| ≤ 7 * r := by
    rw [hsub]
    linarith only [abs_add_le (r * B / (h + k)) (A * (h - k) / (h * (h + k))),
      hterm₁, hterm₂]
  have hUV' : |U + V| ≤ 5 := (abs_add_le U V).trans (by linarith)
  have hcoeff : δ ^ 2 / h ≤ 2 * δ ^ 2 := by
    rw [div_le_iff₀ hhpos]
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg δ)]
  rw [hphase]
  change |B / h + (δ ^ 2 / h) * U ^ 2 - (B / h + (δ ^ 2 / h) * V ^ 2)| ≤ _
  rw [show B / h + (δ ^ 2 / h) * U ^ 2 - (B / h + (δ ^ 2 / h) * V ^ 2) =
    (δ ^ 2 / h) * ((U - V) * (U + V)) by ring, abs_mul, abs_mul,
    abs_of_nonneg (div_nonneg (sq_nonneg δ) hhpos.le)]
  calc
    _ ≤ (2 * δ ^ 2) * ((7 * r) * 5) :=
      mul_le_mul hcoeff (mul_le_mul hUV hUV' (abs_nonneg _) (by positivity))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
    _ = _ := by ring

end RestrictionWork
