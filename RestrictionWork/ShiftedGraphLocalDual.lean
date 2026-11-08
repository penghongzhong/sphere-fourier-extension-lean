import RestrictionWork.PatchGraphCoordinates
import RestrictionWork.UniformShiftedSphericalBound
import OAI.Analysis.Fourier.Restriction.CriticalInput
import OAI.Analysis.Fourier.Restriction.Modulation
import OAI.Analysis.Fourier.Restriction.WeightedKernel
import OAI.Analysis.Fourier.Restriction.DualNorm

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction
  (restrictionInputExponent restrictionInputExponent_bounds continuous_angularFourier
    norm_angularFourier_le_integral_norm restrictionModulate measurable_restrictionModulate
    integrable_restrictionModulate angularFourier_restrictionModulate eLpNorm_restrictionModulate
    eLpNorm_le_of_integrable_pairing)
open OAI.Analysis.Fourier.BochnerRiesz
  (eLpNorm_le_of_integral_mul_bound enorm_integral_mul_le_eLpNorm)
namespace RestrictionWork

private def patchPhysicalReflect (d : ℕ) : Ambient d × ℝ ≃ᵐ Ambient (d + 1) :=
  (euclideanSliceEquiv (Fin.last d)).trans (MeasurableEquiv.neg (Ambient (d + 1)))

private theorem patch_physical_reflect_preserving (d : ℕ) :
    MeasurePreserving (patchPhysicalReflect d) volume volume :=
  (Measure.measurePreserving_neg (volume : Measure (Ambient (d + 1)))).comp
    (euclidean_slice_measure_preserving (Fin.last d))

private theorem norm_le_patch_physical_reflect {d : ℕ} (z : Ambient d × ℝ) :
    ‖z‖ ≤ ‖patchPhysicalReflect d z‖ := by
  change ‖z‖ ≤ ‖-(euclideanSliceEquiv (Fin.last d) (z.1, z.2))‖
  rw [norm_neg]
  have he := euclidean_slice_norm_sq (Fin.last d) z.1 z.2
  rw [Prod.norm_def, max_le_iff]
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [he]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Real.norm_eq_abs, sq_abs, he]
    exact le_add_of_nonneg_left (sq_nonneg _)

private theorem integral_patch_graph_pairing {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {f : Ambient (d + 1) → ℂ} (hf : Integrable f)
    {g : Ambient d → ℂ} (hg : Integrable g (patchMeasure d)) :
    (∫ v, g v * angularFourier f (patchGraphPoint φ v) ∂patchMeasure d) =
      ∫ z : Ambient d × ℝ, f (patchPhysicalReflect d z) * graphExtension g φ z := by
  let T := patchPhysicalReflect d
  let F := f ∘ T
  have hT := patch_physical_reflect_preserving d
  have hF : Integrable F := hT.integrable_comp_of_integrable hf
  have : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let K (z : Ambient d × ℝ) (v : Ambient d) : ℂ :=
    Complex.exp (((⟪z.1, v⟫ + z.2 * φ v : ℝ) : ℂ) * Complex.I)
  let J (z : Ambient d × ℝ) (v : Ambient d) : ℂ := F z * (g v * K z v)
  have hK : Measurable (fun q : (Ambient d × ℝ) × Ambient d => K q.1 q.2) := by
    unfold K
    fun_prop
  have hJ : Integrable (Function.uncurry J)
      ((volume : Measure (Ambient d × ℝ)).prod (patchMeasure d)) := by
    apply (hF.norm.mul_prod hg.norm).mono'
    · exact hF.aestronglyMeasurable.comp_fst.mul
        (hg.aestronglyMeasurable.comp_snd.mul hK.aestronglyMeasurable)
    · filter_upwards [] with q
      simp [J, K, Function.uncurry, Complex.norm_exp]
  have hfourier (v : Ambient d) :
      angularFourier f (patchGraphPoint φ v) = ∫ z : Ambient d × ℝ, F z * K z v := by
    unfold angularFourier
    rw [← hT.integral_comp' (fun x => Complex.exp (-Complex.I *
      ((inner ℝ x (patchGraphPoint φ v) : ℝ) : ℂ)) * f x)]
    apply integral_congr_ae
    filter_upwards [] with z
    change Complex.exp (-Complex.I * ((⟪-(euclideanSliceEquiv (Fin.last d) (z.1, z.2)),
      euclideanSliceEquiv (Fin.last d) (v, φ v)⟫ : ℝ) : ℂ)) * F z = F z * K z v
    rw [inner_neg_left, euclidean_slice_inner]
    simp only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg, K, mul_comm Complex.I,
      mul_comm (Complex.exp _)]
  calc
    _ = ∫ v, (∫ z, J z v) ∂patchMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hfourier, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp only [J]
      ring
    _ = ∫ z, (∫ v, J z v ∂patchMeasure d) := (integral_integral_swap hJ).symm
    _ = _ := by simp only [J, F, T, K, graphExtension, phaseExtension, integral_const_mul,
      Function.comp_apply]

theorem patch_graph_local_restriction_of_extension {d : ℕ} {p R : ℝ} (hp : 1 < p)
    (hR : 0 < R) {φ : Ambient d → ℝ} (hφ : Measurable φ) {C : ℝ≥0∞}
    (hE : ∀ g : Ambient d → ℂ, MemLp g (ENNReal.ofReal (p / (p - 1))) (patchMeasure d) →
      eLpNorm (graphExtension g φ) (ENNReal.ofReal (p / (p - 1)))
        (volume.restrict (ball (0 : Ambient d × ℝ) (2 * R))) ≤
      C * eLpNorm g (ENNReal.ofReal (p / (p - 1))) (patchMeasure d))
    {f : Ambient (d + 1) → ℂ} (hfm : Measurable f) (hfi : Integrable f)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) :
    eLpNorm (angularFourier f) (ENNReal.ofReal p) (patchGraphMeasure φ) ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
  let Q := ENNReal.ofReal (p / (p - 1))
  let ν := volume.restrict (ball (0 : Ambient d × ℝ) (2 * R))
  let H := angularFourier f ∘ patchGraphPoint φ
  let T := patchPhysicalReflect d
  let F := f ∘ T
  have hT := patch_physical_reflect_preserving d
  have hHm : Measurable H := (continuous_angularFourier hfi).measurable.comp
    (measurable_patch_graph_point hφ)
  have : IsFiniteMeasure (patchMeasure d) := by
    unfold patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hH : MemLp H (ENNReal.ofReal p) (patchMeasure d) :=
    MemLp.of_bound hHm.aestronglyMeasurable _ (.of_forall fun v =>
      norm_angularFourier_le_integral_norm f (patchGraphPoint φ v))
  change eLpNorm (angularFourier f) (ENNReal.ofReal p) ((patchMeasure d).map (patchGraphPoint φ)) ≤ _
  rw [eLpNorm_map_measure (continuous_angularFourier hfi).aestronglyMeasurable
    (measurable_patch_graph_point hφ).aemeasurable]
  apply eLpNorm_le_of_integral_mul_bound (patchMeasure d) hp hH
  intro g hg
  have hq : 1 ≤ p / (p - 1) := (le_div_iff₀ (by linarith : 0 < p - 1)).mpr (by linarith)
  have hgi : Integrable g (patchMeasure d) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (ENNReal.one_le_ofReal.mpr hq))
  have hFm : Measurable F := hfm.comp T.measurable
  have hFzero (z : Ambient d × ℝ) (hz : z ∉ ball 0 (2 * R)) : F z = 0 := by
    have hzn : 2 * R ≤ ‖z‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hz
    exact hfs (T z) ((show R < 2 * R by linarith).trans_le
      (hzn.trans (norm_le_patch_physical_reflect z)))
  have he : (∫ z : Ambient d × ℝ, F z * graphExtension g φ z) =
      ∫ z, F z * graphExtension g φ z ∂ν := by
    change _ = ∫ z in ball (0 : Ambient d × ℝ) (2 * R), F z * graphExtension g φ z
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ ball (0 : Ambient d × ℝ) (2 * R)
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, hFzero z hz, zero_mul]
  have hN : eLpNorm F (ENNReal.ofReal p) ν ≤ eLpNorm f (ENNReal.ofReal p) volume :=
    (eLpNorm_mono_measure F Measure.restrict_le_self).trans_eq
      (eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable hT)
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  change ‖∫ v, g v * angularFourier f (patchGraphPoint φ v) ∂patchMeasure d‖ₑ ≤ _
  rw [integral_patch_graph_pairing hφ hfi hgi]
  change ‖∫ z, F z * graphExtension g φ z‖ₑ ≤ _
  rw [he]
  calc
    _ ≤ eLpNorm F (ENNReal.ofReal p) ν * eLpNorm (graphExtension g φ) Q ν :=
      enorm_integral_mul_le_eLpNorm ν hFm.aestronglyMeasurable
        (graph_extension_continuous hgi hφ).aestronglyMeasurable hpq
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume * (C * eLpNorm g Q (patchMeasure d)) :=
      mul_le_mul' hN (hE g hg)
    _ = _ := by ring

theorem critical_graph_conjugacy {d : ℕ} (hd : 1 ≤ d) :
    ENNReal.ofReal (restrictionInputExponent (d + 1) / (restrictionInputExponent (d + 1) - 1)) =
      capCriticalExponent d := by
  unfold capCriticalExponent restrictionInputExponent
  push_cast
  congr 1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  field_simp [hd0.ne']
  ring_nf
  exact mul_inv_cancel₀ hd0.ne'

/-- Uniform critical local restriction on every translate of the real graph measure. -/
theorem shifted_graph_local_restriction_translated {d : ℕ} (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ R : ℝ, 1 ≤ R →
        ∀ f : Ambient (d + 1) → ℂ, Measurable f → Integrable f →
        (∀ x, R < ‖x‖ → f x = 0) → ∀ v : Ambient (d + 1),
          let p := ENNReal.ofReal (restrictionInputExponent (d + 1))
          eLpNorm (fun ω => angularFourier f (ω + v)) p
            (patchGraphMeasure (shiftedSphericalGraphPhase δ a r)) ≤
          C * ENNReal.ofReal (R ^ ε) * eLpNorm f p volume := by
  obtain ⟨A, HA⟩ := uniform_shifted_spherical_subcap_bound hd hε
  have hp := (restrictionInputExponent_bounds (show 2 ≤ d + 1 by omega)).1
  refine ⟨(A : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ ε),
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf R hR f hfm hfi hfs v
  have hRpos : 0 < R := by linarith
  let φ := shiftedSphericalGraphPhase δ a r
  have hφ : Measurable φ := by
    unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  let F := restrictionModulate v f
  have HM := patch_graph_local_restriction_of_extension hp hRpos hφ
    (C := (A : ℝ≥0∞) * ENNReal.ofReal ((2 * R) ^ ε))
    (by rw [critical_graph_conjugacy hd]; exact fun g hg =>
      (HA δ hδ hδhalf a ha r hr hrhalf (2 * R) (by linarith) g hg).2)
    (measurable_restrictionModulate v hfm) (integrable_restrictionModulate v hfi)
    (fun x hx => by simp [restrictionModulate, hfs x hx])
  have he : angularFourier (restrictionModulate v f) = fun ω => angularFourier f (ω + v) :=
    funext (angularFourier_restrictionModulate v f)
  rw [he, eLpNorm_restrictionModulate v hfm, Real.mul_rpow (by norm_num) hRpos.le,
    ENNReal.ofReal_mul (by positivity)] at HM
  simpa only [mul_assoc] using HM

/-- Global diagonal duality with the exact angular-Fourier normalization. -/
theorem patch_graph_extension_of_restriction {d : ℕ} {p : ℝ} (hp : 1 < p)
    {φ : Ambient d → ℝ} (hφ : Measurable φ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hR : ∀ f : Ambient (d + 1) → ℂ, Integrable f →
      eLpNorm (angularFourier f) (ENNReal.ofReal (p / (p - 1))) (patchGraphMeasure φ) ≤
        C * eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume)
    {g : Ambient d → ℂ} (hg : MemLp g (ENNReal.ofReal p) (patchMeasure d)) :
    MemLp (graphExtension g φ) (ENNReal.ofReal p) volume ∧
      eLpNorm (graphExtension g φ) (ENNReal.ofReal p) volume ≤
        C * eLpNorm g (ENNReal.ofReal p) (patchMeasure d) := by
  let Q := ENNReal.ofReal (p / (p - 1))
  let T := patchPhysicalReflect d
  let E := graphExtension g φ
  let U := E ∘ T.symm
  let : IsFiniteMeasure (patchMeasure d) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hgi : Integrable g (patchMeasure d) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (ENNReal.one_le_ofReal.mpr hp.le))
  have hEm : Measurable E := (graph_extension_continuous hgi hφ).measurable
  have hUm : Measurable U := hEm.comp T.symm.measurable
  have hEn (z : Ambient d × ℝ) : ‖E z‖ ≤ ∫ v, ‖g v‖ ∂patchMeasure d := by
    unfold E graphExtension phaseExtension
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have H : eLpNorm U (ENNReal.ofReal p) volume ≤ C * eLpNorm g (ENNReal.ofReal p) (patchMeasure d) := by
    apply eLpNorm_le_of_integrable_pairing hp hUm.aestronglyMeasurable (fun x => hEn (T.symm x))
    intro f hfi _
    have he : (∫ x, f x * U x) = ∫ z, f (T z) * E z := by
      rw [← (patch_physical_reflect_preserving d).integral_comp' (fun x => f x * U x)]
      simp only [Function.comp_apply, U, T, MeasurableEquiv.symm_apply_apply]
    have hpq : p.HolderConjugate (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
    have hfm := (continuous_angularFourier hfi).measurable.comp (measurable_patch_graph_point hφ)
    have hmap : eLpNorm (angularFourier f ∘ patchGraphPoint φ) Q (patchMeasure d) =
        eLpNorm (angularFourier f) Q (patchGraphMeasure φ) :=
      (eLpNorm_map_measure (continuous_angularFourier hfi).aestronglyMeasurable
        (measurable_patch_graph_point hφ).aemeasurable).symm
    rw [he, ← integral_patch_graph_pairing hφ hfi hgi]
    calc
      _ ≤ eLpNorm g (ENNReal.ofReal p) (patchMeasure d) *
          eLpNorm (angularFourier f ∘ patchGraphPoint φ) Q (patchMeasure d) :=
        enorm_integral_mul_le_eLpNorm _ hg.aestronglyMeasurable hfm.aestronglyMeasurable hpq
      _ ≤ eLpNorm g (ENNReal.ofReal p) (patchMeasure d) * (C * eLpNorm f Q volume) := by
        rw [hmap]
        exact mul_le_mul' le_rfl (hR f hfi)
      _ = _ := by ring
  have hT : eLpNorm E (ENNReal.ofReal p) volume = eLpNorm U (ENNReal.ofReal p) volume := by
    simpa only [U, T, Function.comp_def, MeasurableEquiv.symm_apply_apply] using
      eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p) hUm.aestronglyMeasurable
        (patch_physical_reflect_preserving d)
  have hE := hT.trans_le H
  exact ⟨hE.trans_lt (ENNReal.mul_lt_top hC.lt_top hg), hE⟩

end RestrictionWork
