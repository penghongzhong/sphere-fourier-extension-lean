import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
open Set
namespace RestrictionWork

/-- The imaginary exponential has global Lipschitz constant exactly one. -/
theorem phase_exponential_lipschitz (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤
      |a - b| := by
  have hderiv (x : ℝ) : HasDerivAt
      (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
      (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x := by
    simpa using (((hasDerivAt_id (x : ℂ)).comp_ofReal).mul_const Complex.I).cexp
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ)) (C := 1)
    (fun x _ => (hderiv x).hasDerivWithinAt)
    (fun x _ => by simp [norm_mul, Complex.norm_exp_ofReal_mul_I])
    (convex_univ) (mem_univ b) (mem_univ a)
  simpa only [one_mul, Real.norm_eq_abs] using H

end RestrictionWork
