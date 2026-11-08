import RestrictionWork.CapChartDefinitions
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RestrictionWork

/-- The cap graph is a global Borel embedding whenever its horizontal
scale is nonzero; no surface measure identity is used here. -/
theorem cap_point_embedding {d : ℕ} {δ : ℝ} (hδ : δ ≠ 0) :
    Continuous (capPoint (d := d) δ) ∧ Function.Injective (capPoint (d := d) δ) ∧
      MeasurableEmbedding (capPoint (d := d) δ) := by
  have hc : Continuous (capPoint (d := d) δ) := by
    have hh : Continuous (capHeight (d := d) δ) := by
      unfold capHeight
      fun_prop
    have hcoords : Continuous (fun v : Ambient d =>
        Fin.snoc (α := fun _ : Fin (d + 1) => ℝ)
          (fun i => δ * v i) (capHeight δ v)) := by
      rw [continuous_pi_iff, Fin.forall_iff_castSucc]
      constructor
      · simpa only [Fin.snoc_last] using hh
      · intro i
        simpa only [Fin.snoc_castSucc, Pi.mul_def] using
          (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i) :
            Continuous (fun v : Ambient d => δ * v i))
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => ℝ)).symm.continuous).comp hcoords
  have hi : Function.Injective (capPoint (d := d) δ) := by
    intro x y h
    apply (WithLp.equiv 2 (Fin d → ℝ)).injective
    funext i
    have H := congrArg (fun z : Ambient (d + 1) => z i.castSucc) h
    simp only [capPoint, WithLp.equiv_symm_apply, PiLp.toLp_apply, Fin.snoc_castSucc] at H
    exact mul_left_cancel₀ hδ H
  exact ⟨hc, hi, hc.measurable.measurableEmbedding hi⟩

end RestrictionWork
