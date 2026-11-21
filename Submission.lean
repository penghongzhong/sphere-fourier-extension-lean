import ManuscriptStatement

/-!
# JSP-001040: MathDB Lean submission entry point

Author: Pang-hung Chung
Manuscript: The sharp Fourier extension estimate for the sphere
arXiv: https://arxiv.org/abs/2611.11060

This file exposes the exact sphere Fourier extension target and its finite
Knapp boundary theorem. Both are derived from the existing proof dependency
closure; no replacement hypothesis, additional analytic assumption, or
unproved target is introduced in this submission wrapper.

The full source build, axiom checks and kernel replay are performed by
`python3 scripts/verify.py --jobs 2` using the pinned Lean/Mathlib toolchain.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace JSP001040Submission

/-- The complete strong-type sphere Fourier extension range, n >= 3. -/
theorem fullRange (n : ℕ) (hn : 3 ≤ n) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    RestrictionWork.BoundedSphereExtension n p q ↔
      ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q ∧
      ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹ ≤ q := by
  exact RestrictionWork.jsp001040_catalog_statement n hn p q hp hq

/-- The finite strong-type Knapp boundary used in the manuscript's main proof. -/
theorem finiteKnappBoundary (n : ℕ) (hn : 3 ≤ n) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hrad : ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q)
    (hline : q = ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹)
    (hqfin : q < ⊤) :
    RestrictionWork.BoundedSphereExtension n p q := by
  exact JSP001040Manuscript.finiteKnappBoundary n hn p q hp hq hrad hline hqfin

end JSP001040Submission

#check @JSP001040Submission.fullRange
#print axioms JSP001040Submission.fullRange
#check @JSP001040Submission.finiteKnappBoundary
#print axioms JSP001040Submission.finiteKnappBoundary
