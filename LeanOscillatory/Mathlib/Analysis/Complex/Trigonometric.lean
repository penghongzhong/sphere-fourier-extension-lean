
import Mathlib.Analysis.Complex.Trigonometric

section

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

variable (x y : ℂ)

theorem conj_exp_ofReal_mul_I (x : ℝ) : conj (exp (x * I)) = exp (-(x * I)) := by simp [← exp_conj]

end Complex

end
