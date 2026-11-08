import RestrictionWork.ShiftedSphericalGraphPhase
import RestrictionWork.GraphRebaseInput
import RestrictionWork.GraphRebasePhysical
import RestrictionWork.GraphExtensionContinuous
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

/-- Exact modulus identity under parabolic rebasing. The input Jacobian
is retained, and the affine part of the graph contributes a unit phase. -/
theorem graph_rebase_integral_norm {d : ℕ} (φ : Ambient d → ℝ) {a l : Ambient d} {r : ℝ}
    (hr : 0 < r) (ha : ‖a‖ ≤ 1 / 2) (hrhalf : r ≤ 1 / 2) (g : Ambient d → ℂ)
    (z : Ambient d × ℝ) :
    ‖graphExtension (graphRebaseInput a r g) φ (graphPhysicalMap l r z)‖ =
      r ^ d * ‖graphExtension g (graphRebasePhase φ a l r) z‖ := by
  let L := graphParameterMap a r
  let S := Metric.ball a r
  let ν : Measure (Ambient d) := volume.restrict S
  let c := ENNReal.ofReal (r ^ d)
  let w := graphPhysicalMap l r z
  let b : ℝ := ⟪w.1, a⟫ + w.2 * φ a
  let H : Ambient d → ℂ := fun v =>
    g (graphParameterInverse a r v) *
      Complex.exp (((⟪w.1, v⟫ + w.2 * φ v : ℝ) : ℂ) * Complex.I)
  have hL := graph_parameter_embedding a hr
  have hc₀ : c ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have hc_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hν : ν = c • (patchMeasure d).map L := by
    rw [graph_parameter_map_measure a hr, smul_smul, ENNReal.mul_inv_cancel hc₀ hc_top, one_smul]
  have hrestr : (patchMeasure d).restrict S = ν := graph_rebase_restrict ha hrhalf
  have hphase (u : Ambient d) :
      ⟪w.1, L u⟫ + w.2 * φ (L u) =
        b + (⟪z.1, u⟫ + z.2 * graphRebasePhase φ a l r u) := by
    dsimp only [b, w, L, graphParameterMap, graphPhysicalMap, graphRebasePhase]
    simp only [inner_add_right, real_inner_smul_right, inner_sub_left, real_inner_smul_left]
    field_simp [hr.ne']
    ring
  have hind (v : Ambient d) :
      graphRebaseInput a r g v *
        Complex.exp (((⟪w.1, v⟫ + w.2 * φ v : ℝ) : ℂ) * Complex.I) =
        S.indicator H v := by
    by_cases hv : v ∈ Metric.ball a r
    · simp [graphRebaseInput, S, H, hv]
    · simp [graphRebaseInput, S, hv]
  have hcomp (u : Ambient d) :
      H (L u) = Complex.exp ((b : ℂ) * Complex.I) *
        (g u * Complex.exp
          (((⟪z.1, u⟫ + z.2 * graphRebasePhase φ a l r u : ℝ) : ℂ) * Complex.I)) := by
    change g (graphParameterInverse a r (L u)) * _ = _
    have hinv : graphParameterInverse a r (L u) = u := graph_parameter_left_inverse a hr u
    rw [hinv, hphase, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  have hint :
      graphExtension (graphRebaseInput a r g) φ w =
        (r ^ d : ℝ) • (Complex.exp ((b : ℂ) * Complex.I) *
          graphExtension g (graphRebasePhase φ a l r) z) := by
    calc
      _ = ∫ v, S.indicator H v ∂patchMeasure d := by
        unfold graphExtension phaseExtension
        exact integral_congr_ae (.of_forall hind)
      _ = ∫ v, H v ∂ν := by rw [integral_indicator measurableSet_ball, hrestr]
      _ = (r ^ d : ℝ) • ∫ u, H (L u) ∂patchMeasure d := by
        rw [hν, integral_smul_measure, hL.integral_map, ENNReal.toReal_ofReal (pow_pos hr _).le]
      _ = _ := by
        simp only [hcomp, integral_const_mul, graphExtension, phaseExtension]
  change ‖graphExtension (graphRebaseInput a r g) φ w‖ = _
  rw [hint, norm_smul, norm_mul, Complex.norm_exp, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)]
  simp [Complex.mul_re]

end RestrictionWork
