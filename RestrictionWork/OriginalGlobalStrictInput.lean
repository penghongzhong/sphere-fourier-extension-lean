import RestrictionWork.SourceSphereBridge
import GlobalMixedExtension

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- Global extension in the strict mixed range for the literal original
subtype sphere, its canonical measure and the original `2π` kernel. -/
theorem original_global_strict_input {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞}
    (hp : 1 < p) {q : ℝ}
    (hq : 2 * (n : ℝ) / ((n : ℝ) - 1) < q)
    (hpq : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent p < q) :
    ∃ C : ℝ≥0, ∀ f : UnitSphere n → ℂ, MemLp f p (sphereMeasure n) →
      MemLp (extension f) (ENNReal.ofReal q) volume ∧
      eLpNorm (extension f) (ENNReal.ofReal q) volume ≤
        (C : ℝ≥0∞) * eLpNorm f p (sphereMeasure n) := by
  obtain ⟨A, _, HA⟩ := CriticalReplay.global_mixed_extension n hn p hp q hq hpq
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  let K : ℝ≥0∞ := ENNReal.ofReal |(c ^ n)⁻¹| ^ (ENNReal.ofReal q).toReal⁻¹
  have hK : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
    (inv_nonneg.mpr ENNReal.toReal_nonneg) ENNReal.ofReal_ne_top
  let D : ℝ≥0∞ := K * ENNReal.ofReal A
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top
  refine ⟨D.toNNReal, ?_⟩
  intro f hf
  obtain ⟨hl, hnrm, he⟩ := source_sphere_bridge hf
  have hgi : Integrable (sphereAmbientLift f)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    memLp_one_iff_integrable.mp (hl.mono_exponent hp.le)
  have hsurj : Function.Surjective (fun x : Ambient n ↦ c • x) := by
    intro y
    refine ⟨c⁻¹ • y, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hnorm : eLpNorm (extension f) (ENNReal.ofReal q) volume =
      K * eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension (sphereAmbientLift f))
        (ENNReal.ofReal q) volume := by
    have heq : extension f = (fun x ↦
        OAI.Analysis.Fourier.Restriction.sphericalExtension (sphereAmbientLift f) (c • x)) := by
      funext x
      rw [← he x, CriticalReplay.sphericalExtensionTwoPi_eq]
    rw [heq]
    simpa only [Measure.restrict_univ, Set.image_univ_of_surjective hsurj] using
      (CriticalReplay.dilation_local_norm hc _
        (OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension hgi)
        (ENNReal.ofReal q) Set.univ)
  have H : eLpNorm (extension f) (ENNReal.ofReal q) volume ≤
      D * eLpNorm f p (sphereMeasure n) := by
    rw [hnorm]
    calc
      _ ≤ K * (ENNReal.ofReal A * eLpNorm (sphereAmbientLift f) p
          (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :=
        mul_le_mul' le_rfl (HA (sphereAmbientLift f) hl).2
      _ = _ := by rw [hnrm]; exact (mul_assoc _ _ _).symm
  rw [ENNReal.coe_toNNReal hD]
  exact ⟨H.trans_lt (ENNReal.mul_lt_top hD.lt_top hf), H⟩

end RestrictionWork
