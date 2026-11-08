/-
Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae.
Apache-2.0; see UPSTREAM_LICENSE and verification/reuse_sphere_area_sources.json.
Modified locally: minimal dependency extraction and Lean 4.19/Mathlib c44e API port.
The mathematical conclusion is retained; no measure identity is assumed.
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace MahlerStokes

/-- The squared Euclidean radius, in real coordinates with standard Lebesgue measure. -/
def radiusSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2
/-- An actual Euclidean ball in coordinates; the ambient Pi norm is irrelevant. -/
def coordBall (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) := {x | radiusSq x < R ^ 2}
def chord {n : ℕ} (R : ℝ) (y : Fin n → ℝ) : ℝ := Real.sqrt (R ^ 2 - radiusSq y)

lemma radiusSq_insertNth {n : ℕ} (i : Fin (n+1)) (t : ℝ) (y : Fin n → ℝ) :
    radiusSq (i.insertNth t y) = t ^ 2 + radiusSq y := by
  unfold radiusSq
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma measurableSet_coordBall (n : ℕ) (R : ℝ) : MeasurableSet (coordBall n R) := by
  apply IsOpen.measurableSet
  exact isOpen_lt (by unfold radiusSq; fun_prop) continuous_const


abbrev toLp {n : ℕ} (p : ℝ≥0∞) (x : Fin n → ℝ) : WithLp p (Fin n → ℝ) :=
  (WithLp.equiv p (Fin n → ℝ)).symm x

abbrev ofLp {n : ℕ} {p : ℝ≥0∞} (x : WithLp p (Fin n → ℝ)) : Fin n → ℝ :=
  WithLp.equiv p (Fin n → ℝ) x

theorem radiusSq_eq_euclidean_norm_sq {n : ℕ} (x : Fin n → ℝ) :
    radiusSq x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2 := by
  simpa only [radiusSq, toLp, WithLp.equiv_symm_apply, WithLp.ofLp_toLp,
    Real.norm_eq_abs, sq_abs] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) (toLp 2 x)).symm

end MahlerStokes
end
end OAI

