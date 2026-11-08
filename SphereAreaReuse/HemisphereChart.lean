/-
Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae.
Apache-2.0; see UPSTREAM_LICENSE and verification/reuse_sphere_area_sources.json.
Modified locally: minimal dependency extraction and Lean 4.19/Mathlib c44e API port.
The mathematical conclusion is retained; no measure identity is assumed.
-/
import SphereAreaReuse.Coordinates
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Convert

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

lemma radiusSq_smul {n : ℕ} (r : ℝ) (x : Fin n → ℝ) :
    radiusSq (r • x) = r^2 * radiusSq x := by
  simp only [radiusSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma chord_pos {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    0 < chord 1 y := Real.sqrt_pos.2 (sub_pos.mpr hy)

lemma chord_sq {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    (chord 1 y)^2 = 1 - radiusSq y := by
  simp only [chord, one_pow]
  apply Real.sq_sqrt
  have h : radiusSq y < 1 := by simpa [coordBall] using hy
  linarith

/-- Upper hemisphere graph, in the precise coordinate order used by Stokes. -/
def hemisphereGraph {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
  i.insertNth (chord 1 y) y

lemma radiusSq_hemisphereGraph {n : ℕ} (i : Fin (n+1)) {y : Fin n → ℝ}
    (hy : y ∈ coordBall n 1) : radiusSq (hemisphereGraph i y) = 1 := by
  rw [hemisphereGraph, radiusSq_insertNth, chord_sq hy]
  ring

/-- Radial coordinates on the open upper half-ball. The i-th domain
coordinate is radius; all remaining coordinates parametrize the hemisphere. -/
def hemisphereCone {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  x i • hemisphereGraph i (i.removeNth x)

def hemisphereConeDomain {n : ℕ} (i : Fin (n+1)) : Set (Fin (n+1) → ℝ) :=
  {x | x i ∈ Ioo (0 : ℝ) 1 ∧ i.removeNth x ∈ coordBall n 1}

lemma radiusSq_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) : radiusSq (hemisphereCone i x) = (x i)^2 := by
  rw [hemisphereCone, radiusSq_smul, radiusSq_hemisphereGraph i hx.2, mul_one]

lemma hemisphereCone_injOn {n : ℕ} (i : Fin (n+1)) :
    InjOn (hemisphereCone i) (hemisphereConeDomain i) := by
  intro x hx y hy h
  have hr : x i = y i := (sq_eq_sq₀ hx.1.1.le hy.1.1.le).mp
    ((radiusSq_hemisphereCone i hx).symm.trans ((congrArg radiusSq h).trans
      (radiusSq_hemisphereCone i hy)))
  have hv : i.removeNth x = i.removeNth y := by
    funext j
    have hj := congrFun h (i.succAbove j)
    simp only [hemisphereCone, hemisphereGraph, Pi.smul_apply, smul_eq_mul,
      Fin.insertNth_apply_succAbove] at hj
    rw [hr] at hj
    exact mul_left_cancel₀ hy.1.1.ne' hj
  apply funext
  rw [i.forall_iff_succAbove]
  exact ⟨hr, fun k => congrFun hv k⟩

/-- Real dot product as a continuous linear functional on coordinate space. -/
def coordinateDot {n : ℕ} (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, y j • ContinuousLinearMap.proj j

lemma coordinateDot_apply {n : ℕ} (y v : Fin n → ℝ) :
    coordinateDot y v = ∑ j, y j * v j := by
  simp [coordinateDot]

lemma hasFDerivAt_radiusSq {n : ℕ} (y : Fin n → ℝ) :
    HasFDerivAt radiusSq (2 • coordinateDot y) y := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := y)).mul
      ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := y)))
  have he : radiusSq (n := n) = fun z => ∑ j, z j * z j := by
    funext z
    simp [radiusSq, pow_two]
  have hd : (∑ j : Fin n, ((y j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) +
      (y j) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) =
      2 • coordinateDot y := by
    ext v
    simp [coordinateDot, Finset.mul_sum, two_mul, Finset.sum_add_distrib]
  rw [he]
  simpa only [ContinuousLinearMap.proj_apply, hd, Pi.mul_apply] using h

def chordDerivative {n : ℕ} (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  -(chord 1 y)⁻¹ • coordinateDot y

lemma hasFDerivAt_chord {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    HasFDerivAt (chord 1) (chordDerivative y) y := by
  have h := ((hasFDerivAt_radiusSq y).const_sub (1^2)).sqrt (sub_pos.mpr hy).ne'
  have hd : (1 / (2 * Real.sqrt (1 ^ 2 - radiusSq y))) • -(2 • coordinateDot y) =
      chordDerivative y := by
    ext v
    simp [chordDerivative, chord, div_eq_mul_inv]
    ring
  rw [hd] at h
  exact h

/-- Derivative of the hemisphere graph. -/
def hemisphereGraphDerivative {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (i.insertNth (chordDerivative y) (fun j => ContinuousLinearMap.proj j))

lemma hasFDerivAt_hemisphereGraph {n : ℕ} (i : Fin (n+1)) {y : Fin n → ℝ}
    (hy : y ∈ coordBall n 1) :
    HasFDerivAt (hemisphereGraph i) (hemisphereGraphDerivative i y) y := by
  apply hasFDerivAt_pi.2
  rw [i.forall_iff_succAbove]
  constructor
  · simpa [hemisphereGraph, hemisphereGraphDerivative] using hasFDerivAt_chord hy
  · intro j
    simp only [hemisphereGraph, Fin.insertNth_apply_succAbove]
    exact hasFDerivAt_apply j y

def removeCoordinate {n : ℕ} (i : Fin (n+1)) :
    (Fin (n+1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (i.succAbove j))

def hemisphereConeDerivative {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  x i • (hemisphereGraphDerivative i (i.removeNth x)).comp (removeCoordinate i) +
    (ContinuousLinearMap.proj i).smulRight (hemisphereGraph i (i.removeNth x))

lemma hasFDerivAt_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) :
    HasFDerivAt (hemisphereCone i) (hemisphereConeDerivative i x) x := by
  exact (ContinuousLinearMap.proj i : (Fin (n+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.smul
    ((hasFDerivAt_hemisphereGraph i hx.2).comp x (removeCoordinate i).hasFDerivAt)

end MahlerStokes

end

end OAI

