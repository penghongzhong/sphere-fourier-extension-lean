import RestrictionWork.CapLiftDefinitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RestrictionWork

/-- Concatenating space and time preserves the actual Lebesgue measure;
the product's max norm is never identified with the Euclidean norm. -/
theorem physical_embed_measure (d : ℕ) :
    MeasurePreserving (physicalEmbed (d := d)) volume volume := by
  have hp := PiLp.volume_preserving_ofLp (Fin d)
  have h1 : MeasurePreserving
      (Prod.map (WithLp.equiv 2 (Fin d → ℝ)) (id : ℝ → ℝ))
      (volume : Measure (Ambient d × ℝ)) (volume : Measure ((Fin d → ℝ) × ℝ)) := by
    change MeasurePreserving (Prod.map (@WithLp.ofLp 2 (Fin d → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (Ambient d)).prod volume)
      ((volume : Measure (Fin d → ℝ)).prod volume)
    exact hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  have h2 : MeasurePreserving (Prod.swap : ((Fin d → ℝ) × ℝ) → ℝ × (Fin d → ℝ))
      volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure (Fin d → ℝ))) (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)).symm
  have H := (PiLp.volume_preserving_toLp (Fin (d + 1))).comp (h3.comp (h2.comp h1))
  convert H using 1
  funext z
  change (WithLp.equiv 2 (Fin (d + 1) → ℝ)).symm
      (Fin.snoc (α := fun _ : Fin (d + 1) => ℝ) (fun i => z.1 i) z.2) =
    (WithLp.equiv 2 (Fin (d + 1) → ℝ)).symm
      ((Fin.last d).insertNth z.2 (WithLp.equiv 2 (Fin d → ℝ) z.1))
  rw [Fin.insertNth_last']
  rfl

end RestrictionWork
