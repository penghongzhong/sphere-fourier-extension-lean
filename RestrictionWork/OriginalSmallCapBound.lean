import RestrictionWork.OriginalCapReverse

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace RestrictionWork

/-- A strong graph bound on the quarter-sized patch gives the corresponding
bound for arbitrary measurable data supported in the actual spherical cap. -/
theorem original_small_cap_bound_of_graph {d : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) {p q : ℝ≥0∞} (hp : 1 ≤ p)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hgraph : ∀ g : Ambient d → ℂ, Measurable g →
      MemLp g p (patchMeasure d) →
      (∀ v ∉ Metric.ball (0 : Ambient d) (1 / 4), g v = 0) →
      eLpNorm (graphExtension g (sphericalGraphPhase δ)) q volume ≤
        C * eLpNorm g p (patchMeasure d)) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ f : UnitSphere (d + 1) → ℂ, Measurable f →
      MemLp f p (sphereMeasure (d + 1)) →
      (∀ ω ∉ originalSmallCap δ, f ω = 0) →
      eLpNorm (extension f) q volume ≤ K * eLpNorm f p (sphereMeasure (d + 1)) := by
  let c := ENNReal.ofReal (δ ^ d)
  let J := ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2)
  let Q := J ^ q.toReal⁻¹
  let P := c ^ p.toReal⁻¹
  let K := Q⁻¹ * c * C * 2 * P⁻¹
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hJ0 : J ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hJt : J ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ0 : Q ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hJ0) hJt).ne'
  have hP0 : P ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hct).ne'
  have hQt : Q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hJt
  refine ⟨K, ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hQ0)) hct.lt_top) hC) (by norm_num))
    (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hP0)), ?_⟩
  intro f hfm hf hfs
  obtain ⟨g, hgm, hg, hgs, hlift, hgnorm⟩ := original_cap_reverse hδ hδ₁ hfm hf hfs
  let : IsFiniteMeasure (patchMeasure d) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : IsFiniteMeasure (sphereMeasure (d + 1)) := by unfold sphereMeasure; infer_instance
  have hcont := extension_continuous (hf.integrable hp)
  let Ψ : Ambient d × ℝ → Ambient (d + 1) :=
    fun z => (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)
  have hΨ : Measurable Ψ := by
    have hD : Measurable (fun x : Ambient (d + 1) => (2 * Real.pi)⁻¹ • x) := by fun_prop
    have hA : Measurable (capPhysicalScale (d := d) δ) := by unfold capPhysicalScale; fun_prop
    exact hD.comp ((physical_embed_measure d).measurable.comp hA)
  have hmap : (volume : Measure (Ambient d × ℝ)).map Ψ =
      J • (volume : Measure (Ambient (d + 1))) := original_cap_physical_measure hδ
  have hnorm : eLpNorm (extension f ∘ Ψ) q volume =
      Q * eLpNorm (extension f) q volume := by
    rw [← eLpNorm_map_measure hcont.aestronglyMeasurable hΨ.aemeasurable,
      hmap, eLpNorm_smul_measure_of_ne_zero hJ0]
    simp only [Q, one_div, smul_eq_mul, ENNReal.toReal_inv]
  have heq : Q * eLpNorm (extension f) q volume =
      c * eLpNorm (graphExtension g (sphericalGraphPhase δ)) q volume := by
    rw [← hnorm, ← hlift]
    exact original_cap_norm hδ hδ₁ (hg.integrable hp) q volume
  calc
    _ = Q⁻¹ * (Q * eLpNorm (extension f) q volume) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hQ0 hQt, one_mul]
    _ = Q⁻¹ * (c * eLpNorm (graphExtension g (sphericalGraphPhase δ)) q volume) := by
      rw [heq]
    _ ≤ Q⁻¹ * (c * (C * eLpNorm g p (patchMeasure d))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (hgraph g hgm hg hgs))
    _ ≤ _ := by
      dsimp only [K]
      simpa only [mul_assoc] using
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hgnorm)) :
          Q⁻¹ * (c * (C * eLpNorm g p (patchMeasure d))) ≤
            Q⁻¹ * (c * (C * (2 * P⁻¹ * eLpNorm f p (sphereMeasure (d + 1))))))

end RestrictionWork
