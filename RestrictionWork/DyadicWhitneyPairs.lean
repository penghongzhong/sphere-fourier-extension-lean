import RestrictionWork.DyadicWhitneyCells
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

set_option autoImplicit false
noncomputable section

open Set

namespace RestrictionWork

/-- Fine cells whose coordinate intervals lie in the root box `[-1,1)`. -/
def dyadicRootIndices (d n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Ico (-((2 : ℤ) ^ n)) ((2 : ℤ) ^ n))

/-- Ordered cell pairs at a Whitney level, within the root box. -/
def dyadicWhitneyPairs (d j : ℕ) : Finset ((Fin d → ℤ) × (Fin d → ℤ)) := by
  classical
  exact ((dyadicRootIndices d (j + 1)) ×ˢ (dyadicRootIndices d (j + 1))).filter
    (fun p => (∀ i, |p.1 i / 2 - p.2 i / 2| ≤ 1) ∧ ¬ (∀ i, |p.1 i - p.2 i| ≤ 1))

def dyadicWhitneyRectangle {d : ℕ} (j : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Set (Ambient d × Ambient d) :=
  dyadicParameterCell (j + 1) p.1 ×ˢ dyadicParameterCell (j + 1) p.2

def dyadicWhitneyRegion (d j : ℕ) : Set (Ambient d × Ambient d) :=
  ⋃ p ∈ dyadicWhitneyPairs d j, dyadicWhitneyRectangle j p

private theorem parent_index (j : ℕ) (x : ℝ) :
    dyadicIndex (j + 1) x / 2 = dyadicIndex j x := by
  unfold dyadicIndex
  have H := (Int.floor_div_natCast ((2 : ℝ) ^ (j + 1) * x) 2).symm
  norm_num only [Nat.cast_ofNat] at H
  rw [H]
  congr 1
  rw [pow_succ]
  ring

private theorem mem_pairs_iff {d j : ℕ} {p : (Fin d → ℤ) × (Fin d → ℤ)} :
    p ∈ dyadicWhitneyPairs d j ↔
      (p.1 ∈ dyadicRootIndices d (j + 1) ∧ p.2 ∈ dyadicRootIndices d (j + 1)) ∧
        (∀ i, |p.1 i / 2 - p.2 i / 2| ≤ 1) ∧ ¬ (∀ i, |p.1 i - p.2 i| ≤ 1) := by
  classical
  simp only [dyadicWhitneyPairs, Finset.mem_filter, Finset.mem_product]

theorem dyadic_whitney_pair_index_gap {d j : ℕ} {p : (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : p ∈ dyadicWhitneyPairs d j) (i : Fin d) : |p.1 i - p.2 i| ≤ 3 := by
  obtain ⟨hl, hu⟩ := abs_le.mp ((mem_pairs_iff.mp hp).2.1 i)
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem measurable_dyadic_whitney_rectangle {d : ℕ} (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : MeasurableSet (dyadicWhitneyRectangle j p) :=
  (measurable_dyadic_parameter_cell (j + 1) p.1).prod
    (measurable_dyadic_parameter_cell (j + 1) p.2)

theorem measurable_dyadic_whitney_region (d j : ℕ) :
    MeasurableSet (dyadicWhitneyRegion d j) := by
  exact MeasurableSet.biUnion (dyadicWhitneyPairs d j).finite_toSet.countable
    (fun p _ => measurable_dyadic_whitney_rectangle j p)

theorem pairwise_disjoint_dyadic_whitney_rectangles (d j : ℕ) :
    Pairwise (fun p q : (Fin d → ℤ) × (Fin d → ℤ) =>
      Disjoint (dyadicWhitneyRectangle j p) (dyadicWhitneyRectangle j q)) := by
  intro p q hpq
  apply disjoint_left.mpr
  intro w hp hq
  exact hpq (Prod.ext
    (funext fun i => (mem_dyadic_parameter_cell.mp hp.1 i).symm.trans
      (mem_dyadic_parameter_cell.mp hq.1 i))
    (funext fun i => (mem_dyadic_parameter_cell.mp hp.2 i).symm.trans
      (mem_dyadic_parameter_cell.mp hq.2 i)))

private theorem whitney_level_of_mem_rectangle {d j : ℕ}
    {p : (Fin d → ℤ) × (Fin d → ℤ)} {w : Ambient d × Ambient d}
    (hp : p ∈ dyadicWhitneyPairs d j) (hw : w ∈ dyadicWhitneyRectangle j p) :
    DyadicWhitneyLevel j (WithLp.ofLp w.1) (WithLp.ofLp w.2) := by
  have h₁ := mem_dyadic_parameter_cell.mp hw.1
  have h₂ := mem_dyadic_parameter_cell.mp hw.2
  have h := (mem_pairs_iff.mp hp).2
  refine ⟨fun i => ?_, fun H => h.2 fun i => ?_⟩
  · change |dyadicIndex j (w.1 i) - dyadicIndex j (w.2 i)| ≤ 1
    rw [← parent_index j (w.1 i), ← parent_index j (w.2 i), h₁ i, h₂ i]
    exact h.1 i
  · have Hi := H i
    change |dyadicIndex (j + 1) (w.1 i) - dyadicIndex (j + 1) (w.2 i)| ≤ 1 at Hi
    rwa [h₁ i, h₂ i] at Hi

private theorem near_antitone {ι : Type*} (u v : ι → ℝ) :
    Antitone (fun j => DyadicNear j u v) := by
  apply antitone_nat_of_succ_le
  intro j h i
  rw [← parent_index j (u i), ← parent_index j (v i)]
  obtain ⟨hl, hu⟩ := abs_le.mp (h i)
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem pairwise_disjoint_dyadic_whitney_regions (d : ℕ) :
    Pairwise (fun j k => Disjoint (dyadicWhitneyRegion d j) (dyadicWhitneyRegion d k)) := by
  intro j k hjk
  apply disjoint_left.mpr
  intro w hwj hwk
  simp only [dyadicWhitneyRegion, mem_iUnion, exists_prop] at hwj hwk
  obtain ⟨p, hp, hw₁⟩ := hwj
  obtain ⟨q, hq, hw₂⟩ := hwk
  have H := whitney_level_of_mem_rectangle hp hw₁
  have K := whitney_level_of_mem_rectangle hq hw₂
  have hroot := near_antitone (WithLp.ofLp w.1) (WithLp.ofLp w.2) (Nat.zero_le j) H.1
  have hne : WithLp.ofLp w.1 ≠ WithLp.ofLp w.2 := by
    intro he
    exact H.2 (fun i => by simp [he])
  exact hjk ((exists_unique_dyadic_whitney_level hroot hne).unique H K)

private theorem patch_coordinate_bounds {d : ℕ} {u : Ambient d}
    (hu : u ∈ Metric.ball (0 : Ambient d) 1) (i : Fin d) :
    -1 ≤ u i ∧ u i < 1 := by
  have hnorm : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hu
  have habs : |u i| < 1 := (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i :
    |u i| ≤ ‖u‖).trans_lt hnorm
  exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2⟩

private theorem root_indices_of_patch {d : ℕ} (n : ℕ) {u : Ambient d}
    (hu : u ∈ Metric.ball (0 : Ambient d) 1) :
    (fun i => dyadicIndex n (u i)) ∈ dyadicRootIndices d n := by
  rw [dyadicRootIndices, Fintype.mem_piFinset]
  intro i
  obtain ⟨hl, hh⟩ := patch_coordinate_bounds hu i
  simp only [Finset.mem_Ico, dyadicIndex]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  · apply Int.floor_lt.mpr
    push_cast
    simpa only [mul_one] using mul_lt_mul_of_pos_left hh (by positivity : 0 < (2 : ℝ) ^ n)

theorem mem_iUnion_dyadic_whitney_regions_of_patch {d : ℕ} {u v : Ambient d}
    (hu : u ∈ Metric.ball (0 : Ambient d) 1) (hv : v ∈ Metric.ball (0 : Ambient d) 1)
    (hne : u ≠ v) : (u, v) ∈ ⋃ j, dyadicWhitneyRegion d j := by
  have hU := Fintype.mem_piFinset.mp (root_indices_of_patch 0 hu)
  have hV := Fintype.mem_piFinset.mp (root_indices_of_patch 0 hv)
  have hroot : DyadicNear 0 (WithLp.ofLp u) (WithLp.ofLp v) := by
    intro i
    have hu' := Finset.mem_Ico.mp (hU i)
    have hv' := Finset.mem_Ico.mp (hV i)
    simp only [pow_zero] at hu' hv'
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hne' : WithLp.ofLp u ≠ WithLp.ofLp v := fun h => hne (WithLp.ofLp_injective _ h)
  obtain ⟨j, H, _⟩ := exists_unique_dyadic_whitney_level hroot hne'
  let p := ((fun i : Fin d => dyadicIndex (j + 1) (u i)),
    (fun i : Fin d => dyadicIndex (j + 1) (v i)))
  refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩
  · refine mem_pairs_iff.mpr ⟨⟨root_indices_of_patch _ hu, root_indices_of_patch _ hv⟩, ?_, H.2⟩
    intro i
    simpa only [p, parent_index] using H.1 i
  · exact ⟨mem_dyadic_parameter_cell.mpr (fun _ => rfl),
      mem_dyadic_parameter_cell.mpr (fun _ => rfl)⟩

end RestrictionWork
