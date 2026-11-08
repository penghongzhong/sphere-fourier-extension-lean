import RestrictionWork.GraphRebaseIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

/-- Exact output-norm transfer on the image of any physical region. -/
theorem graph_rebase_norm_transfer {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {a l : Ambient d} {r : ℝ} (hr : 0 < r) (ha : ‖a‖ ≤ 1 / 2) (hrhalf : r ≤ 1 / 2)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Ambient d → ℂ} (hg : MemLp g p (patchMeasure d))
    (q : ℝ≥0∞) (T : Set (Ambient d × ℝ)) :
    ENNReal.ofReal (r ^ d) *
      eLpNorm (graphExtension g (graphRebasePhase φ a l r)) q (volume.restrict T) =
      ENNReal.ofReal (r ^ (d + 2)) ^ q.toReal⁻¹ *
        eLpNorm (graphExtension (graphRebaseInput a r g) φ) q
          (volume.restrict (graphPhysicalMap l r '' T)) := by
  let P := graphPhysicalMap l r
  let F := graphExtension (graphRebaseInput a r g) φ
  let G := graphExtension g (graphRebasePhase φ a l r)
  let ν : Measure (Ambient d × ℝ) := volume.restrict T
  have : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hψ : Measurable (graphRebasePhase φ a l r) := by
    unfold graphRebasePhase
    fun_prop
  have hG : Continuous G := graph_extension_continuous (hg.integrable hp) hψ
  have hF : Continuous F := graph_extension_continuous
    ((graph_rebase_input_norm hr ha hrhalf hg).1.integrable hp) hφ
  have hP := graph_physical_embedding l hr
  have hmap : ν.map P =
      ENNReal.ofReal (r ^ (d + 2)) • volume.restrict (P '' T) := by
    calc
      _ = ((volume : Measure (Ambient d × ℝ)).map P).restrict (P '' T) := by
        rw [hP.restrict_map, hP.injective.preimage_image]
      _ = _ := by rw [graph_physical_map_measure l hr, Measure.restrict_smul]
  have hJ : ENNReal.ofReal (r ^ (d + 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  change ENNReal.ofReal (r ^ d) * eLpNorm G q ν = _
  calc
    _ = eLpNorm ((r ^ d : ℝ) • G) q ν := by
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)]
    _ = eLpNorm (F ∘ P) q ν := by
      refine eLpNorm_congr_norm_ae (hG.const_smul _).aestronglyMeasurable
        ((hF.measurable.comp hP.measurable).aestronglyMeasurable) ?_
      refine .of_forall fun z => ?_
      have H := graph_rebase_integral_norm φ hr ha hrhalf g (l := l) z
      simpa only [P, G, F, Function.comp_apply, Pi.smul_apply, norm_smul,
        Real.norm_eq_abs, abs_of_pos (pow_pos hr d)] using H.symm
    _ = eLpNorm F q (ν.map P) := hP.eLpNorm_map_measure.symm
    _ = _ := by
      rw [hmap, eLpNorm_smul_measure_of_ne_zero hJ]
      simp only [one_div, ENNReal.toReal_inv, smul_eq_mul, P, F]

end RestrictionWork
