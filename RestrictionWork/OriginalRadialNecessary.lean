import RestrictionWork.SphereConstantNonintegrability
import RestrictionWork.MinimalClosureObligations
import RestrictionWork.SourceSphereBridge

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

/-- The strict radial threshold for the original `2π` sphere extension,
with the original canonical measure and all allowed input exponents. -/
theorem original_radial_necessary : RadialRestrictionNecessity := by
  intro n hn p q hp hq hE
  by_contra hbad
  have hle := le_of_not_gt hbad
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hqt : q ≠ ⊤ := (hle.trans_lt ENNReal.ofReal_lt_top).ne
  have hqc : q.toReal ≤ 2 * (n : ℝ) / ((n : ℝ) - 1) := by
    have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (div_nonneg (by positivity) (by linarith))] at H
  obtain ⟨_, HE⟩ := hE
  haveI : IsFiniteMeasure (sphereMeasure n) := by unfold sphereMeasure; infer_instance
  let f : UnitSphere n → ℂ := fun _ ↦ 1
  have hf : MemLp f p (sphereMeasure n) := memLp_const _
  have hExt := (HE f hf).1
  let K : Ambient n → ℂ := OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ ↦ 1)
  have hK : Continuous K := OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension (integrable_const _)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have he : extension f = fun x ↦ K (c • x) := by
    funext x
    have hEmb : MeasurableEmbedding (Subtype.val : UnitSphere n → Ambient n) :=
      MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet
    dsimp [K]
    unfold OAI.Analysis.Fourier.Restriction.sphericalExtension OAI.Analysis.Fourier.Restriction.sphereMeasure
    rw [hEmb.integral_map]
    simp only [extension, f, one_mul, mul_one, kernel, inner_smul_left_eq_smul, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 1
    dsimp [c]
    push_cast
    ring
  have hsurj : Function.Surjective (fun x : Ambient n ↦ c • x) := by
    intro y
    refine ⟨c⁻¹ • y, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  let J : ℝ≥0∞ := ENNReal.ofReal |(c ^ n)⁻¹| ^ q.toReal⁻¹
  have hJ : 0 < J := ENNReal.rpow_pos_of_nonneg
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hc.ne'))))
    (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have heNorm : eLpNorm (extension f) q volume = J * eLpNorm K q volume := by
    rw [he]
    simpa only [Measure.restrict_univ, Set.image_univ_of_surjective hsurj] using
      (CriticalReplay.dilation_local_norm hc K hK q Set.univ)
  have hMem : MemLp K q volume := by
    change eLpNorm K q volume < ⊤
    by_contra H
    have ht : eLpNorm K q volume = ⊤ := top_unique (le_of_not_gt H)
    change eLpNorm (extension f) q volume < ⊤ at hExt
    rw [heNorm, ht, ENNReal.mul_top hJ.ne'] at hExt
    exact (lt_irrefl ⊤) hExt
  exact sphere_constant_nonintegrability hn hq hqt hqc hMem

end RestrictionWork
