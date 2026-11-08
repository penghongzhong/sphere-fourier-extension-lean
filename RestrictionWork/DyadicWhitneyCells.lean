import RestrictionWork.DyadicWhitneyLevel
import RestrictionWork.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

/-- A genuine half-open dyadic cell in the Euclidean parameter space. -/
def dyadicParameterCell {d : ℕ} (j : ℕ) (k : Fin d → ℤ) : Set (Ambient d) :=
  WithLp.ofLp ⁻¹' univ.pi (fun i => Ico ((k i : ℝ) / (2 : ℝ) ^ j)
    (((k i : ℝ) + 1) / (2 : ℝ) ^ j))

theorem mem_dyadic_parameter_cell {d j : ℕ} {k : Fin d → ℤ} {u : Ambient d} :
    u ∈ dyadicParameterCell j k ↔ ∀ i, dyadicIndex j (u i) = k i := by
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  simp only [dyadicParameterCell, mem_preimage, mem_univ_pi, mem_Ico, dyadicIndex,
    Int.floor_eq_iff, div_le_iff₀ hp, lt_div_iff₀ hp]
  simp_rw [mul_comm ((2 : ℝ) ^ j)]

theorem measurable_dyadic_parameter_cell {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    MeasurableSet (dyadicParameterCell j k) := by
  unfold dyadicParameterCell
  exact (MeasurableSet.pi (to_countable _) fun _ _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem volume_dyadic_parameter_cell {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    volume (dyadicParameterCell j k) = (ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹)) ^ d := by
  have hm : MeasurableSet (univ.pi (fun i : Fin d => Ico ((k i : ℝ) / (2 : ℝ) ^ j)
      (((k i : ℝ) + 1) / (2 : ℝ) ^ j))) :=
    MeasurableSet.pi (to_countable _) fun _ _ => measurableSet_Ico
  rw [dyadicParameterCell, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hm.nullMeasurableSet,
    Real.volume_pi_Ico]
  have hlen (i : Fin d) :
      ((k i : ℝ) + 1) / (2 : ℝ) ^ j - (k i : ℝ) / (2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := by
    rw [← sub_div, add_sub_cancel_left, one_div]
  simp_rw [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A Whitney cell pair has the required separation in the Euclidean norm
at every pair of points in those two actual cells. -/
theorem dyadic_whitney_cells_separated {d j : ℕ} {u v : Ambient d}
    (h : DyadicWhitneyLevel j (WithLp.ofLp u) (WithLp.ofLp v))
    {u' v' : Ambient d}
    (hu : u' ∈ dyadicParameterCell (j + 1) (fun i => dyadicIndex (j + 1) (u i)))
    (hv : v' ∈ dyadicParameterCell (j + 1) (fun i => dyadicIndex (j + 1) (v i))) :
    ((2 : ℝ) ^ (j + 1))⁻¹ ≤ ‖u' - v'‖ := by
  have H := (dyadic_whitney_level_congr (mem_dyadic_parameter_cell.mp hu)
    (mem_dyadic_parameter_cell.mp hv)).mpr h
  obtain ⟨i, hi⟩ := dyadic_whitney_coordinate_gap H
  refine hi.trans ?_
  simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (u' - v') i

end RestrictionWork
