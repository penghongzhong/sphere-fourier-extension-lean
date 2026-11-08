
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

section


universe u

open scoped Topology
open Filter Asymptotics Set

open ContinuousLinearMap (toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {c : 𝕜 → 𝕜'} {c' : 𝕜'}

section Inverse

@[to_fun]
theorem HasDerivWithinAt.inv' (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x := by
  convert! (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring

@[to_fun]
theorem HasDerivAt.inv' (hc : HasDerivAt c c' x) (hx : c x ≠ 0) :
    HasDerivAt (c⁻¹) (-c' / c x ^ 2) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hc.inv' hx

theorem derivWithin_fun_inv'' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (fun x => (c x)⁻¹) s x = -derivWithin c s x / c x ^ 2 := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hc.hasDerivWithinAt.inv' hx).derivWithin hsx
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hsx]

theorem derivWithin_inv'' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : c x ≠ 0) :
    derivWithin (c⁻¹) s x = -derivWithin c s x / c x ^ 2 :=
  derivWithin_fun_inv'' hc hx

@[simp]
theorem deriv_fun_inv''' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv' hx).deriv

@[simp]
theorem deriv_inv''' (hc : DifferentiableAt 𝕜 c x) (hx : c x ≠ 0) :
    deriv (c⁻¹) x = -deriv c x / c x ^ 2 :=
  (hc.hasDerivAt.inv' hx).deriv

end Inverse
