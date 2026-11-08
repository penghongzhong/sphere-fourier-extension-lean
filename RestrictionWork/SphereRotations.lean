import RestrictionWork.ExtensionContinuous
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false

noncomputable section
open MeasureTheory Set
open scoped Pointwise RealInnerProductSpace ENNReal

namespace RestrictionWork

private theorem isometry_mem_unitSphere {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n)
    (w : UnitSphere n) : e (w : Ambient n) ∈ UnitSphere n := by
  change e (w : Ambient n) ∈ Metric.sphere 0 1
  rw [Metric.mem_sphere, dist_zero_right, e.norm_map]
  simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using w.property

/-- The restriction of an ambient linear isometric equivalence to the unit sphere. -/
def sphereIsometry {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n) :
    UnitSphere n ≃ᵐ UnitSphere n where
  toFun w := ⟨e (w : Ambient n), isometry_mem_unitSphere e w⟩
  invFun w := ⟨e.symm (w : Ambient n), isometry_mem_unitSphere e.symm w⟩
  left_inv w := Subtype.ext (e.symm_apply_apply (w : Ambient n))
  right_inv w := Subtype.ext (e.apply_symm_apply (w : Ambient n))
  measurable_toFun := (e.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (e.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

@[simp] theorem sphere_isometry_coe {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n) (w : UnitSphere n) :
    ((sphereIsometry e w : UnitSphere n) : Ambient n) = e (w : Ambient n) := rfl

theorem sphere_isometry_isometry {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n) :
    Isometry (sphereIsometry e : UnitSphere n → UnitSphere n) := by
  rw [isometry_iff_dist_eq]
  intro x y
  exact e.isometry.dist_eq (x : Ambient n) (y : Ambient n)

/-- Canonical surface measure is invariant under ambient linear isometries. -/
theorem sphere_isometry_measurePreserving {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n) :
    MeasurePreserving (sphereIsometry e) (sphereMeasure n) (sphereMeasure n) := by
  refine ⟨(sphereIsometry e).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereIsometry e).measurable hs, sphereMeasure,
    Measure.toSphere_apply' _ ((sphereIsometry e).measurable hs), Measure.toSphere_apply' _ hs]
  congr 1
  let C : Set ℝ := Ioo 0 1
  let L : Set (Ambient n) := C • (Subtype.val '' ((sphereIsometry e) ⁻¹' s))
  let R : Set (Ambient n) := C • (Subtype.val '' s)
  have hcone : e '' L = R := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨a, ha, v, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_smul.mp hu
      rw [e.map_smul]
      exact Set.smul_mem_smul ha ⟨sphereIsometry e w, hw, rfl⟩
    · intro hz
      obtain ⟨a, ha, v, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_smul.mp hz
      let y := (sphereIsometry e).symm w
      have hy : y ∈ (sphereIsometry e) ⁻¹' s := by
        simpa only [Set.mem_preimage, y, MeasurableEquiv.apply_symm_apply] using hw
      refine ⟨a • (y : Ambient n), Set.smul_mem_smul ha (Set.mem_image_of_mem _ hy), ?_⟩
      rw [e.map_smul, ← sphere_isometry_coe]
      simp only [y, MeasurableEquiv.apply_symm_apply]
  change (volume : Measure (Ambient n)) L = (volume : Measure (Ambient n)) R
  calc
    volume L = ((volume : Measure (Ambient n)).map e) (e '' L) := by
      change volume L = (volume.map e.toMeasurableEquiv) (e.toMeasurableEquiv '' L)
      rw [e.toMeasurableEquiv.measurableEmbedding.map_apply,
        e.toMeasurableEquiv.injective.preimage_image]
    _ = volume R := by rw [e.measurePreserving.map_eq, hcone]

/-- Orthogonal covariance of the actual integral, with the same isometry on frequencies. -/
theorem extension_comp_sphereIsometry {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n)
    (f : UnitSphere n → ℂ) : extension (f ∘ sphereIsometry e) = extension f ∘ e := by
  funext x
  change (∫ w, f (sphereIsometry e w) * kernel x w ∂sphereMeasure n) =
    ∫ w, f w * kernel (e x) w ∂sphereMeasure n
  rw [← (sphere_isometry_measurePreserving e).integral_comp' (fun w => f w * kernel (e x) w)]
  congr 1
  funext w
  simp only [kernel, sphere_isometry_coe, e.inner_map_map]

theorem eLpNorm_extension_comp_sphereIsometry {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n)
    {f : UnitSphere n → ℂ} (hf : Integrable f (sphereMeasure n)) (q : ℝ≥0∞) :
    eLpNorm (extension (f ∘ sphereIsometry e)) q volume =
      eLpNorm (extension f) q volume := by
  rw [extension_comp_sphereIsometry]
  exact eLpNorm_comp_measurePreserving (extension_continuous hf).aestronglyMeasurable
    e.measurePreserving

/-- A single reflection takes any chosen unit vector to any other. -/
theorem exists_sphere_isometry_apply {n : ℕ} (v w : UnitSphere n) :
    ∃ e : Ambient n ≃ₗᵢ[ℝ] Ambient n, sphereIsometry e v = w := by
  have hv : ‖(v : Ambient n)‖ = 1 := by
    simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using v.property
  have hw : ‖(w : Ambient n)‖ = 1 := by
    simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using w.property
  exact ⟨_, Subtype.ext (Submodule.reflection_sub (hv.trans hw.symm))⟩

end RestrictionWork
