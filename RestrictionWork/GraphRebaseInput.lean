import RestrictionWork.PhaseExtensionDefinitions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace RestrictionWork

def graphParameterMap {d : ℕ} (a : Ambient d) (r : ℝ) (u : Ambient d) : Ambient d :=
  a + r • u

def graphParameterInverse {d : ℕ} (a : Ambient d) (r : ℝ) (v : Ambient d) : Ambient d :=
  r⁻¹ • (v - a)

def graphRebaseInput {d : ℕ} (a : Ambient d) (r : ℝ) (g : Ambient d → ℂ) :
    Ambient d → ℂ :=
  (Metric.ball a r).indicator (g ∘ graphParameterInverse a r)

theorem graph_parameter_left_inverse {d : ℕ} (a : Ambient d) {r : ℝ} (hr : 0 < r) :
    Function.LeftInverse (graphParameterInverse a r) (graphParameterMap a r) := by
  intro u
  simp [graphParameterInverse, graphParameterMap, smul_smul, hr.ne']

theorem graph_parameter_embedding {d : ℕ} (a : Ambient d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (graphParameterMap a r) := by
  have hm : Measurable (graphParameterMap a r) := by unfold graphParameterMap; fun_prop
  exact hm.measurableEmbedding (graph_parameter_left_inverse a hr).injective

theorem graph_parameter_map_measure {d : ℕ} (a : Ambient d) {r : ℝ} (hr : 0 < r) :
    (patchMeasure d).map (graphParameterMap a r) =
      (ENNReal.ofReal (r ^ d))⁻¹ • (volume.restrict (Metric.ball a r)) := by
  let B := Metric.ball (0 : Ambient d) 1
  let L := graphParameterMap a r
  have hL := graph_parameter_embedding a hr
  have hb : L '' B = Metric.ball a r := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h := Metric.mem_ball.mp hu
      change dist (a + r • u) a < r
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have hn : ‖u‖ < 1 := by simpa only [dist_zero_right] using h
      simpa only [mul_one] using mul_lt_mul_of_pos_left hn hr
    · intro hv
      have hvn : ‖v - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hv
      refine ⟨graphParameterInverse a r v, ?_, ?_⟩
      · change dist (r⁻¹ • (v - a)) 0 < 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        simpa [hr.ne'] using mul_lt_mul_of_pos_left hvn (inv_pos.mpr hr)
      · simp [L, graphParameterMap, graphParameterInverse, smul_smul, hr.ne']
  have hmap : (volume : Measure (Ambient d)).map L = (ENNReal.ofReal (r ^ d))⁻¹ • volume := by
    have hs : Measurable (fun v : Ambient d => r • v) := by fun_prop
    have ht := measurePreserving_add_left (volume : Measure (Ambient d)) a
    change (volume : Measure (Ambient d)).map ((fun v : Ambient d => a + v) ∘
      (fun v : Ambient d => r • v)) = _
    rw [← Measure.map_map ht.measurable hs, Measure.map_addHaar_smul volume hr.ne',
      show Module.finrank ℝ (Ambient d) = d by simp [Ambient],
      abs_of_pos (inv_pos.mpr (pow_pos hr _)), Measure.map_smul, ht.map_eq,
      ENNReal.ofReal_inv_of_pos (pow_pos hr _)]
    exact ht.measurable.aemeasurable
  change ((volume : Measure (Ambient d)).restrict B).map L = _
  calc
    _ = ((volume : Measure (Ambient d)).map L).restrict (L '' B) := by
      rw [hL.restrict_map, hL.injective.preimage_image]
    _ = _ := by rw [hb, hmap, Measure.restrict_smul]

theorem graph_rebase_restrict {d : ℕ} {a : Ambient d} {r : ℝ}
    (ha : ‖a‖ ≤ 1 / 2) (hrhalf : r ≤ 1 / 2) :
    (patchMeasure d).restrict (Metric.ball a r) = volume.restrict (Metric.ball a r) := by
  have hsub : Metric.ball a r ⊆ Metric.ball (0 : Ambient d) 1 := by
    intro v hv
    have hvn : ‖v - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hv
    have H : ‖v‖ ≤ ‖v - a‖ + ‖a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (v - a) a
    simpa only [Metric.mem_ball, dist_zero_right] using (show ‖v‖ < 1 by linarith)
  unfold patchMeasure
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hsub]

theorem graph_rebase_input_norm {d : ℕ} {a : Ambient d} {r : ℝ} (hr : 0 < r)
    (ha : ‖a‖ ≤ 1 / 2) (hrhalf : r ≤ 1 / 2) {p : ℝ≥0∞} {g : Ambient d → ℂ}
    (hg : MemLp g p (patchMeasure d)) :
    MemLp (graphRebaseInput a r g) p (patchMeasure d) ∧
      eLpNorm (graphRebaseInput a r g) p (patchMeasure d) =
        ENNReal.ofReal (r ^ d) ^ p.toReal⁻¹ * eLpNorm g p (patchMeasure d) := by
  let L := graphParameterMap a r
  let c := ENNReal.ofReal (r ^ d)
  let S := Metric.ball a r
  let ν : Measure (Ambient d) := volume.restrict S
  let G := g ∘ graphParameterInverse a r
  have hL := graph_parameter_embedding a hr
  have hmap : (patchMeasure d).map L = c⁻¹ • ν := graph_parameter_map_measure a hr
  have hcomp : G ∘ L = g := funext fun u => by
    simp only [Function.comp_apply, L, G, graph_parameter_left_inverse a hr u]
  have hzero : c ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have htop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hν : ν = c • (patchMeasure d).map L := by
    rw [hmap, smul_smul, ENNReal.mul_inv_cancel hzero htop, one_smul]
  have hrestr : (patchMeasure d).restrict S = ν := graph_rebase_restrict ha hrhalf
  have hG : MemLp G p ((patchMeasure d).map L) :=
    hL.memLp_map_measure_iff.mpr (hcomp ▸ hg)
  have hGν : MemLp G p ν := hν ▸ hG.smul_measure htop
  change MemLp (S.indicator G) p (patchMeasure d) ∧ _
  refine ⟨memLp_indicator_iff_restrict measurableSet_ball |>.mpr (hrestr ▸ hGν), ?_⟩
  change eLpNorm (S.indicator G) p (patchMeasure d) = c ^ p.toReal⁻¹ * eLpNorm g p _
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball, hrestr, hν,
    eLpNorm_smul_measure_of_ne_zero hzero, hL.eLpNorm_map_measure, hcomp]
  simp only [one_div, ENNReal.toReal_inv, smul_eq_mul]

end RestrictionWork
