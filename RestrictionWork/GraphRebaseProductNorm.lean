import RestrictionWork.GraphRebaseNormTransfer

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RestrictionWork

/-- Exact global product-norm transfer for the same parabolic change of
variables in both factors. -/
theorem graph_rebase_product_norm_transfer {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {a l : Ambient d} {r y : ℝ} (hr : 0 < r) (ha : ‖a‖ ≤ 1 / 2) (hrhalf : r ≤ 1 / 2)
    (hy : 0 ≤ y) {f g : Ambient d → ℂ}
    (hf : MemLp f 1 (patchMeasure d)) (hg : MemLp g 1 (patchMeasure d)) :
    ENNReal.ofReal (r ^ d * r ^ d) *
      eLpNorm (graphExtension f (graphRebasePhase φ a l r) *
        graphExtension g (graphRebasePhase φ a l r)) (ENNReal.ofReal y)⁻¹ volume =
      ENNReal.ofReal (r ^ (d + 2)) ^ y *
        eLpNorm (graphExtension (graphRebaseInput a r f) φ *
          graphExtension (graphRebaseInput a r g) φ) (ENNReal.ofReal y)⁻¹ volume := by
  let q := (ENNReal.ofReal y)⁻¹
  let P := graphPhysicalMap l r
  let ψ := graphRebasePhase φ a l r
  let F := graphExtension (graphRebaseInput a r f) φ *
    graphExtension (graphRebaseInput a r g) φ
  let G := graphExtension f ψ * graphExtension g ψ
  let c := r ^ d * r ^ d
  have hψ : Measurable ψ := by unfold ψ graphRebasePhase; fun_prop
  have hG : Continuous G :=
    (graph_extension_continuous (memLp_one_iff_integrable.mp hf) hψ).mul
      (graph_extension_continuous (memLp_one_iff_integrable.mp hg) hψ)
  have hF : Continuous F :=
    (graph_extension_continuous
      (memLp_one_iff_integrable.mp (graph_rebase_input_norm hr ha hrhalf hf).1) hφ).mul
      (graph_extension_continuous
        (memLp_one_iff_integrable.mp (graph_rebase_input_norm hr ha hrhalf hg).1) hφ)
  have hc : 0 < c := mul_pos (pow_pos hr _) (pow_pos hr _)
  have hP := graph_physical_embedding l hr
  have hJ : ENNReal.ofReal (r ^ (d + 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  change ENNReal.ofReal c * eLpNorm G q volume = _
  calc
    _ = eLpNorm (c • G) q volume := by
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos hc]
    _ = eLpNorm (F ∘ P) q volume := by
      apply eLpNorm_congr_norm_ae (hG.const_smul c).aestronglyMeasurable
        (hF.measurable.comp hP.measurable).aestronglyMeasurable
      refine .of_forall fun z => ?_
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
        Function.comp_apply, F, G, Pi.mul_apply, norm_mul, ψ,
        graph_rebase_integral_norm φ hr ha hrhalf]
      unfold c
      ring
    _ = eLpNorm F q ((volume : Measure (Ambient d × ℝ)).map P) :=
      hP.eLpNorm_map_measure.symm
    _ = _ := by
      rw [graph_physical_map_measure l hr, eLpNorm_smul_measure_of_ne_zero hJ]
      simp only [q, one_div, inv_inv, ENNReal.toReal_ofReal hy,
        smul_eq_mul, F]

end RestrictionWork
