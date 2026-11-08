import RestrictionWork.PhysicalEmbedMeasure
import RestrictionWork.CapPhysicalMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RestrictionWork

/-- Exact Lebesgue pushforward under the full original-frequency cap
rescaling. Both the 2*pi normalization and the factor 1/2 are retained. -/
theorem original_cap_physical_measure {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (volume : Measure (Ambient d × ℝ)).map
        (fun z => (2 * Real.pi)⁻¹ • physicalEmbed (capPhysicalScale δ z)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) •
        (volume : Measure (Ambient (d + 1))) := by
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hA : Measurable (capPhysicalScale (d := d) δ) := by
    unfold capPhysicalScale
    fun_prop
  have hP := physical_embed_measure d
  have hD : Measurable (fun x : Ambient (d + 1) => (2 * Real.pi)⁻¹ • x) := by
    fun_prop
  have hd : (volume : Measure (Ambient (d + 1))).map
      (fun x => (2 * Real.pi)⁻¹ • x) =
      ENNReal.ofReal ((2 * Real.pi) ^ (d + 1)) • (volume : Measure (Ambient (d + 1))) := by
    have H := Measure.map_addHaar_smul (volume : Measure (Ambient (d + 1)))
      (inv_ne_zero hπ.ne')
    have hdim : Module.finrank ℝ (Ambient (d + 1)) = d + 1 := by simp [Ambient]
    rw [hdim, inv_pow, inv_inv, abs_of_pos (pow_pos hπ (d + 1))] at H
    exact H
  have hc : ENNReal.ofReal (δ ^ (d + 2) / 2) * ENNReal.ofReal ((2 * Real.pi) ^ (d + 1)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (d + 1) * δ ^ (d + 2) / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    _ = (((volume : Measure (Ambient d × ℝ)).map (capPhysicalScale δ)).map
        physicalEmbed).map (fun x => (2 * Real.pi)⁻¹ • x) := by
      rw [Measure.map_map hD hP.measurable,
        Measure.map_map (hD.comp hP.measurable) hA]
      rfl
    _ = _ := by
      rw [cap_physical_measure hδ, Measure.map_smul _ hP.measurable.aemeasurable, hP.map_eq,
        Measure.map_smul _ hD.aemeasurable, hd, smul_smul, hc]

end RestrictionWork
