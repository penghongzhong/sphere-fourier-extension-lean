import RestrictionWork.OriginalCapNorm
import RestrictionWork.OriginalCapPhysicalMeasure
import RestrictionWork.ExtensionContinuous

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

/-- Exact local output norm transfer to the original sphere operator on
the image of any physical region. No restriction estimate is assumed. -/
theorem original_cap_norm_transfer {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2)
    {g : Ambient d → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hg : MemLp g p (patchMeasure d)) (q : ℝ≥0∞)
    (S : Set (Ambient d × ℝ)) :
    MemLp (capSphereLift δ g) p (sphereMeasure (d + 1)) ∧
    eLpNorm (capSphereLift δ g) p (sphereMeasure (d + 1)) =
      eLpNorm (capProfile δ g) p (capParameterMeasure d δ) ∧
    eLpNorm (capSphereLift δ g) p (sphereMeasure (d + 1)) ≤
      ENNReal.ofReal (2 * δ ^ d) ^ p.toReal⁻¹ * eLpNorm g p (patchMeasure d) ∧
    ENNReal.ofReal (δ ^ d) * eLpNorm (sphericalPatchExtension δ g) q (volume.restrict S) =
      ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ^ q.toReal⁻¹ *
        eLpNorm (extension (capSphereLift δ g)) q
          (volume.restrict ((fun z => (2 * Real.pi)⁻¹ •
            physicalEmbed (capPhysicalScale δ z)) '' S)) := by
  haveI : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hgint : Integrable g (patchMeasure d) := MemLp.integrable hp hg
  have hinput := cap_lift_lp hδ hδ₁ hg
  refine ⟨hinput.1, hinput.2.1, hinput.2.2, ?_⟩
  have hsf : Integrable (capSphereLift δ g) (sphereMeasure (d + 1)) :=
    memLp_one_iff_integrable.mp (cap_lift_lp hδ hδ₁ (memLp_one_iff_integrable.mpr hgint)).1
  have hcont := extension_continuous hsf
  have hA : Measurable (capPhysicalScale (d := d) δ) := by
    unfold capPhysicalScale
    fun_prop
  have hΨ : Measurable (fun z : Ambient d × ℝ =>
      (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)) := by
    have hD : Measurable (fun x : Ambient (d + 1) => (2 * Real.pi)⁻¹ • x) := by fun_prop
    exact hD.comp ((physical_embed_measure d).measurable.comp hA)
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hiP : Function.Injective (physicalEmbed (d := d)) := by
    intro x y h
    apply Prod.ext
    · apply PiLp.ext
      intro i
      have H := congrArg (fun v : Ambient (d + 1) => v i.castSucc) h
      simpa only [physicalEmbed, WithLp.equiv_symm_apply, PiLp.toLp_apply, Fin.snoc_castSucc] using H
    · have H := congrArg (fun v : Ambient (d + 1) => v (Fin.last d)) h
      simpa only [physicalEmbed, WithLp.equiv_symm_apply, PiLp.toLp_apply, Fin.snoc_last] using H
  have hiΨ : Function.Injective (fun z : Ambient d × ℝ =>
      (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)) := by
    intro z w h
    have HD := congrArg (fun v : Ambient (d + 1) => (2 * Real.pi) • v) h
    simp only [smul_smul, mul_inv_cancel₀ hπ.ne', one_smul] at HD
    have HA := hiP HD
    apply Prod.ext
    · have H := congrArg (fun y : Ambient d × ℝ => y.1) HA
      have HC := congrArg (fun v : Ambient d => δ • v) H
      simpa only [capPhysicalScale, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul] using HC
    · have H := congrArg (fun y : Ambient d × ℝ => y.2) HA
      dsimp only [capPhysicalScale] at H
      field_simp [hδ.ne'] at H
      linarith
  have heΨ := hΨ.measurableEmbedding hiΨ
  have hmap : ((volume : Measure (Ambient d × ℝ)).restrict S).map
      (fun z => (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) •
        (volume.restrict ((fun z => (2 * Real.pi)⁻¹ •
          physicalEmbed (capPhysicalScale δ z)) '' S)) := by
    calc
      _ = ((volume : Measure (Ambient d × ℝ)).map
          (fun z => (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z))).restrict
          ((fun z => (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)) '' S) := by
        rw [heΨ.restrict_map, hiΨ.preimage_image]
      _ = _ := by rw [original_cap_physical_measure hδ, Measure.restrict_smul]
  have hc0 : ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  calc
    _ = eLpNorm (fun z => extension (capSphereLift δ g)
        ((2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z))) q (volume.restrict S) :=
      (original_cap_norm hδ hδ₁ hgint q (volume.restrict S)).symm
    _ = eLpNorm (extension (capSphereLift δ g)) q
        (((volume : Measure (Ambient d × ℝ)).restrict S).map
          (fun z => (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z))) :=
      (eLpNorm_map_measure hcont.aestronglyMeasurable hΨ.aemeasurable).symm
    _ = _ := by
      rw [hmap, eLpNorm_smul_measure_of_ne_zero hc0]
      simp only [one_div, ENNReal.toReal_inv, smul_eq_mul]

end RestrictionWork
