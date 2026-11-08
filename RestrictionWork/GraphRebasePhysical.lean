import RestrictionWork.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

def graphPhysicalMap {d : ℕ} (l : Ambient d) (r : ℝ) (z : Ambient d × ℝ) :
    Ambient d × ℝ :=
  (r⁻¹ • z.1 - (z.2 / r ^ 2) • l, z.2 / r ^ 2)

theorem graph_physical_embedding {d : ℕ} (l : Ambient d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (graphPhysicalMap l r) := by
  have hm : Measurable (graphPhysicalMap l r) := by unfold graphPhysicalMap; fun_prop
  apply hm.measurableEmbedding
  intro z w h
  have ht : z.2 = w.2 := by
    have H := congrArg Prod.snd h
    change z.2 / r ^ 2 = w.2 / r ^ 2 at H
    exact (div_left_inj' (pow_ne_zero _ hr.ne')).mp H
  have hx : r⁻¹ • z.1 = r⁻¹ • w.1 := by
    have H := congrArg Prod.fst h
    simpa only [graphPhysicalMap, ht, sub_left_inj] using H
  apply Prod.ext _ ht
  have H := congrArg (fun x : Ambient d => r • x) hx
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using H

theorem graph_physical_map_measure {d : ℕ} (l : Ambient d) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Ambient d × ℝ)).map (graphPhysicalMap l r) =
      ENNReal.ofReal (r ^ (d + 2)) • volume := by
  have : Measure.IsAddHaarMeasure (volume : Measure (Ambient d × ℝ)) := by
    rw [Measure.volume_eq_prod (Ambient d) ℝ]
    infer_instance
  let D : (Ambient d × ℝ) →ₗ[ℝ] (Ambient d × ℝ) :=
    LinearMap.prodMap (r⁻¹ • (LinearMap.id : Ambient d →ₗ[ℝ] Ambient d))
      ((r ^ 2)⁻¹ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  let S : Ambient d × ℝ → Ambient d × ℝ := fun z => (z.1 - z.2 • l, z.2)
  have hD : Measurable D := D.continuous_of_finiteDimensional.measurable
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hshear : (volume : Measure (Ambient d × ℝ)).map S = volume := by
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_map hf hS, Measure.volume_eq_prod (Ambient d) ℝ]
    change (∫⁻ z, (f ∘ S) z ∂((volume : Measure (Ambient d)).prod volume)) = _
    rw [lintegral_prod_symm' _ (hf.comp hS), lintegral_prod_symm' _ hf]
    apply lintegral_congr
    intro t
    have hT := measurePreserving_add_right (volume : Measure (Ambient d)) (-(t • l))
    have hf_t : Measurable (fun x : Ambient d => f (x, t)) := by fun_prop
    change (∫⁻ x : Ambient d, f (x - t • l, t)) = ∫⁻ x : Ambient d, f (x, t)
    simp_rw [sub_eq_add_neg]
    rw [← lintegral_map hf_t hT.measurable, hT.map_eq]
  have hdet : LinearMap.det D = (r ^ (d + 2))⁻¹ := by
    simp [D, LinearMap.det_prodMap, LinearMap.det_smul, Ambient, pow_add, mul_comm]
  have hdiag : (volume : Measure (Ambient d × ℝ)).map D =
      ENNReal.ofReal (r ^ (d + 2)) • volume := by
    have hdet₀ : LinearMap.det D ≠ 0 := by rw [hdet]; positivity
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet₀, hdet, inv_inv,
      abs_of_pos (pow_pos hr _)]
  have hcomp : graphPhysicalMap l r = S ∘ D := by
    funext z
    simp [S, D, graphPhysicalMap, div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map hS hD, hdiag, Measure.map_smul, hshear]
  exact hS.aemeasurable

theorem graph_physical_ball_image {d : ℕ} {l : Ambient d} {r R : ℝ} (hr : 0 < r)
    (hrone : r ≤ 1) (hl : ‖l‖ ≤ 4) (hR : 0 < R) :
    graphPhysicalMap l r '' Metric.ball (0 : Ambient d × ℝ) R ⊆
      Metric.ball 0 (5 * R / r ^ 2) := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hx : ‖z.1‖ < R := (norm_fst_le z).trans_lt hz'
  have ht : |z.2| < R := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le z).trans_lt hz'
  have hs : |z.2 / r ^ 2| < R / r ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos hr _)]
    exact div_lt_div_of_pos_right ht (pow_pos hr _)
  have hx' : ‖r⁻¹ • z.1‖ < R / r ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div]
    apply (div_lt_div_of_pos_right hx hr).trans_le
    exact div_le_div_of_nonneg_left hR.le (pow_pos hr _) (by nlinarith [mul_le_mul_of_nonneg_left hrone hr.le])
  have hl' : ‖(z.2 / r ^ 2) • l‖ ≤ 4 * (R / r ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul hl hs.le (abs_nonneg _) (by norm_num)
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
  constructor
  · change ‖r⁻¹ • z.1 - (z.2 / r ^ 2) • l‖ < 5 * R / r ^ 2
    calc
      _ ≤ ‖r⁻¹ • z.1‖ + ‖(z.2 / r ^ 2) • l‖ := norm_sub_le _ _
      _ < R / r ^ 2 + 4 * (R / r ^ 2) := add_lt_add_of_lt_of_le hx' hl'
      _ = _ := by ring
  · change ‖z.2 / r ^ 2‖ < 5 * R / r ^ 2
    rw [Real.norm_eq_abs]
    exact hs.trans_le (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))

end RestrictionWork
