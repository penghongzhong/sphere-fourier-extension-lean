import RestrictionWork.CapChartDefinitions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace RestrictionWork

/-- Exact transport of the weighted cap parameter measure to a small
Euclidean ball. This retains the geometric density and its full power. -/
theorem cap_parameter_scaling {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (capParameterMeasure d δ).map (fun v : Ambient d => δ • v) =
      ((volume : Measure (Ambient d)).restrict (Metric.ball 0 δ)).withDensity
        (fun y => ENNReal.ofReal (capHeight 1 y)⁻¹) := by
  let B := Metric.ball (0 : Ambient d) 1
  let f : Ambient d → Ambient d := fun v => δ • v
  let w : Ambient d → ℝ≥0∞ := fun y => ENNReal.ofReal (capHeight 1 y)⁻¹
  let c : ℝ≥0∞ := ENNReal.ofReal (δ ^ d)
  let k : ℝ≥0∞ := ENNReal.ofReal ((δ ^ d)⁻¹)
  let μ : Measure (Ambient d) := volume.restrict B
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hi : Function.Injective f := by
    intro x y h
    have H := congrArg (fun z : Ambient d => δ⁻¹ • z) h
    simpa [f, smul_smul, hδ.ne'] using H
  have he : MeasurableEmbedding f := hf.measurableEmbedding hi
  have hw : Measurable w := by
    unfold w capHeight
    fun_prop
  have hb : f '' B = Metric.ball (0 : Ambient d) δ := by
    change δ • Metric.ball (0 : Ambient d) 1 = _
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hδ, mul_one] using
      (_root_.smul_ball hδ.ne' (0 : Ambient d) 1)
  have hm : μ.map f = k • ((volume : Measure (Ambient d)).restrict (Metric.ball 0 δ)) := by
    calc
      μ.map f = ((volume : Measure (Ambient d)).map f).restrict (f '' B) := by
        rw [he.restrict_map, hi.preimage_image]
      _ = _ := by
        rw [hb, Measure.map_addHaar_smul volume hδ.ne', Measure.restrict_smul]
        have hdim : Module.finrank ℝ (Ambient d) = d := by simp [Ambient]
        rw [hdim]
        rw [abs_of_pos (inv_pos.2 (pow_pos hδ d))]
  have hh (v : Ambient d) : capHeight 1 (f v) = capHeight δ v := by
    simp only [capHeight, f, one_pow, norm_smul, Real.norm_eq_abs, abs_of_pos hδ,
      mul_pow, one_mul]
  have hd : capParameterMeasure d δ = c • μ.withDensity (w ∘ f) := by
    unfold capParameterMeasure patchMeasure
    have H : (fun v : Ambient d => ENNReal.ofReal (capDensity δ v)) = c • (w ∘ f) := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, c, w, hh,
        capDensity, div_eq_mul_inv]
      rw [ENNReal.ofReal_mul (pow_pos hδ d).le]
    rw [H, withDensity_smul c (hw.comp hf)]
  have htransport : (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
    ext s hs
    rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
      setLIntegral_map hs hw hf]
    rfl
  have hck : c * k = 1 := by
    rw [← ENNReal.ofReal_mul (pow_pos hδ d).le]
    simp [c, k, hδ.ne']
  rw [hd, Measure.map_smul, htransport, hm, withDensity_smul_measure,
    smul_smul, hck, one_smul]
  exact hf.aemeasurable

end RestrictionWork
