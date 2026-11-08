import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace RestrictionWork

/-- Integer coordinate of a half-open dyadic interval. -/
def dyadicIndex (j : ℕ) (x : ℝ) : ℤ := ⌊(2 : ℝ) ^ j * x⌋

/-- Two grid cells are neighbors if every pair of coordinate indices differs
by at most one. -/
def DyadicNear {ι : Type*} (j : ℕ) (u v : ι → ℝ) : Prop :=
  ∀ i, |dyadicIndex j (u i) - dyadicIndex j (v i)| ≤ 1

/-- Whitney level j uses separated cells at level j+1 with neighboring
parents at level j. -/
def DyadicWhitneyLevel {ι : Type*} (j : ℕ) (u v : ι → ℝ) : Prop :=
  DyadicNear j u v ∧ ¬ DyadicNear (j + 1) u v

private theorem dyadic_index_parent (j : ℕ) (x : ℝ) :
    dyadicIndex (j + 1) x / 2 = dyadicIndex j x := by
  unfold dyadicIndex
  have H := (Int.floor_div_natCast ((2 : ℝ) ^ (j + 1) * x) 2).symm
  norm_num only [Nat.cast_ofNat] at H
  rw [H]
  congr 1
  rw [pow_succ]
  ring

private theorem dyadic_near_antitone {ι : Type*} (u v : ι → ℝ) :
    Antitone (fun j => DyadicNear j u v) := by
  apply antitone_nat_of_succ_le
  intro j h i
  rw [← dyadic_index_parent j (u i), ← dyadic_index_parent j (v i)]
  obtain ⟨hl, hu⟩ := abs_le.mp (h i)
  exact abs_le.mpr ⟨by omega, by omega⟩

private theorem abs_sub_lt_two_of_floor_near {x z : ℝ}
    (h : |⌊x⌋ - ⌊z⌋| ≤ 1) : |x - z| < 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hl' : -1 ≤ (⌊x⌋ : ℝ) - (⌊z⌋ : ℝ) := by exact_mod_cast hl
  have hu' : (⌊x⌋ : ℝ) - (⌊z⌋ : ℝ) ≤ 1 := by exact_mod_cast hu
  exact abs_lt.mpr ⟨by linarith [Int.floor_le x, Int.lt_floor_add_one z],
    by linarith [Int.floor_le z, Int.lt_floor_add_one x]⟩

/-- An off-diagonal pair in neighboring root cells belongs to exactly
one Whitney level. -/
theorem exists_unique_dyadic_whitney_level {ι : Type*} {u v : ι → ℝ}
    (h₀ : DyadicNear 0 u v) (huv : u ≠ v) : ∃! j : ℕ, DyadicWhitneyLevel j u v := by
  classical
  have hcoord : ∃ i, u i ≠ v i := by
    by_contra! H
    exact huv (funext H)
  obtain ⟨i, hi⟩ := hcoord
  have hp : 0 < |u i - v i| := abs_pos.mpr (sub_ne_zero.mpr hi)
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / |u i - v i|)
  have hj' : (j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast j.lt_two_pow_self.le
  have hfar : 2 < (2 : ℝ) ^ j * |u i - v i| :=
    (div_lt_iff₀ hp).mp (hj.trans_le hj')
  have hnot : ¬ DyadicNear j u v := by
    intro H
    have h := abs_sub_lt_two_of_floor_near (H i)
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)] at h
    exact (not_lt_of_ge hfar.le) h
  have hex : ∃ j, ¬ DyadicNear j u v := ⟨j, hnot⟩
  let n := Nat.find hex
  have hnf : ¬ DyadicNear n u v := Nat.find_spec hex
  have hn : 0 < n := Nat.pos_of_ne_zero fun he => hnf (he ▸ h₀)
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hnear : DyadicNear (n - 1) u v := by
    by_contra hnfar
    have h := Nat.find_min' hex hnfar
    change n ≤ n - 1 at h
    omega
  refine ⟨n - 1, ⟨hnear, hn' ▸ hnf⟩, ?_⟩
  intro k hk
  have hnk : n ≤ k + 1 := Nat.find_min' hex hk.2
  have hkn : k < n := by
    by_contra! h
    exact hnf ((dyadic_near_antitone u v h) hk.1)
  omega

/-- The finest indices of a Whitney pair have bounded coordinate distance
and at least one coordinate with index gap two or greater. -/
theorem dyadic_whitney_index_bounds {ι : Type*} {u v : ι → ℝ} {j : ℕ}
    (h : DyadicWhitneyLevel j u v) :
    (∀ i, |dyadicIndex (j + 1) (u i) - dyadicIndex (j + 1) (v i)| ≤ 3) ∧
      ∃ i, 1 < |dyadicIndex (j + 1) (u i) - dyadicIndex (j + 1) (v i)| := by
  refine ⟨?_, ?_⟩
  · intro i
    have H := h.1 i
    rw [← dyadic_index_parent j (u i), ← dyadic_index_parent j (v i)] at H
    obtain ⟨hl, hu⟩ := abs_le.mp H
    exact abs_le.mpr ⟨by omega, by omega⟩
  · classical
    by_contra! hnear
    exact h.2 hnear

/-- The layer test is constant on a product of two cells at the fine level. -/
theorem dyadic_whitney_level_congr {ι : Type*} {u v u' v' : ι → ℝ} {j : ℕ}
    (hu : ∀ i, dyadicIndex (j + 1) (u i) = dyadicIndex (j + 1) (u' i))
    (hv : ∀ i, dyadicIndex (j + 1) (v i) = dyadicIndex (j + 1) (v' i)) :
    DyadicWhitneyLevel j u v ↔ DyadicWhitneyLevel j u' v' := by
  have hU (i : ι) : dyadicIndex j (u i) = dyadicIndex j (u' i) := by
    rw [← dyadic_index_parent j (u i), ← dyadic_index_parent j (u' i), hu i]
  have hV (i : ι) : dyadicIndex j (v i) = dyadicIndex j (v' i) := by
    rw [← dyadic_index_parent j (v i), ← dyadic_index_parent j (v' i), hv i]
  unfold DyadicWhitneyLevel DyadicNear
  simp_rw [hU, hV, hu, hv]

/-- Each Whitney pair has a coordinate separation of at least its fine
dyadic side length. -/
theorem dyadic_whitney_coordinate_gap {ι : Type*} {u v : ι → ℝ} {j : ℕ}
    (h : DyadicWhitneyLevel j u v) :
    ∃ i, ((2 : ℝ) ^ (j + 1))⁻¹ ≤ |u i - v i| := by
  obtain ⟨i, hi⟩ := (dyadic_whitney_index_bounds h).2
  let x := (2 : ℝ) ^ (j + 1) * u i
  let z := (2 : ℝ) ^ (j + 1) * v i
  have hgap : 1 ≤ |x - z| := by
    by_contra! H
    obtain ⟨hl, hu⟩ := abs_lt.mp H
    have hl' : -2 < (⌊x⌋ : ℝ) - (⌊z⌋ : ℝ) := by
      linarith [Int.floor_le x, Int.lt_floor_add_one x, Int.floor_le z]
    have hu' : (⌊x⌋ : ℝ) - (⌊z⌋ : ℝ) < 2 := by
      linarith [Int.floor_le x, Int.lt_floor_add_one z, Int.floor_le z]
    have hl'' : -2 < ⌊x⌋ - ⌊z⌋ := by exact_mod_cast hl'
    have hu'' : ⌊x⌋ - ⌊z⌋ < 2 := by exact_mod_cast hu'
    change 1 < |⌊x⌋ - ⌊z⌋| at hi
    exact (not_lt_of_ge (abs_le.mpr ⟨by omega, by omega⟩)) hi
  have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  refine ⟨i, ?_⟩
  unfold x z at hgap
  rw [← mul_sub, abs_mul, abs_of_pos hp, mul_comm] at hgap
  rw [← one_div]
  exact (div_le_iff₀ hp).mpr hgap

end RestrictionWork
