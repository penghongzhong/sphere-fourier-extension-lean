import OAI.Analysis.Fourier.Restriction.LocalCritical
import OAI.Analysis.Fourier.Restriction.Pairing

open OAI.Analysis.Fourier.Wave
open OAI.Analysis.Fourier.Restriction
open MeasureTheory Set Metric Filter
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace CriticalReplay

/-- Local duality for the actual spherical extension. The input restriction
bound is required only for measurable, ball-supported physical functions. -/
theorem local_extension_of_restriction
    {n : ℕ} {p R : ℝ} (hp : 1 < p) {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hrestriction : ∀ f : Space n → ℂ, Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (p / (p - 1))) volume →
      (∀ x, R < ‖x‖ → f x = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f)
        (ENNReal.ofReal (p / (p - 1))) (sphereMeasure n) ≤
        C * eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume)
    {g : Space n → ℂ} (hg : MemLp g (ENNReal.ofReal p) (sphereMeasure n)) :
    MemLp (sphericalExtension g) (ENNReal.ofReal p)
      (volume.restrict (closedBall 0 R)) ∧
    eLpNorm (sphericalExtension g) (ENNReal.ofReal p)
      (volume.restrict (closedBall 0 R)) ≤
        C * eLpNorm g (ENNReal.ofReal p) (sphereMeasure n) := by
  classical
  let B : Set (Space n) := closedBall 0 R
  let u : Space n → ℂ := B.indicator (sphericalExtension g)
  have hq : 1 ≤ p / (p - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
    linarith
  have hgi : Integrable g (sphereMeasure n) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (ENNReal.one_le_ofReal.mpr hp.le))
  have hu : MemLp u (ENNReal.ofReal p) volume := by
    have htop : MemLp u ⊤ volume := by
      apply memLp_top_of_bound
        ((continuous_sphericalExtension hgi).aestronglyMeasurable.indicator measurableSet_closedBall)
        (∫ ω, ‖g ω‖ ∂sphereMeasure n)
      filter_upwards [] with x
      change ‖B.indicator (sphericalExtension g) x‖ ≤ _
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx]
        exact norm_sphericalExtension_le g x
      · rw [indicator_of_notMem hx, norm_zero]
        exact integral_nonneg (fun _ ↦ norm_nonneg _)
    exact htop.mono_exponent_of_measure_support_ne_top
      (s := B) (fun x hx ↦ by simp [u, hx]) measure_closedBall_lt_top.ne le_top
  have hnorm : eLpNorm u (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) (sphereMeasure n) := by
    apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_integral_mul_bound volume hp hu
    intro f hf
    let fm := hf.aestronglyMeasurable
    let v : Space n → ℂ := B.indicator (fm.mk f)
    have hvm : Measurable v := fm.stronglyMeasurable_mk.measurable.indicator measurableSet_closedBall
    have hvp : MemLp v (ENNReal.ofReal (p / (p - 1))) volume :=
      (hf.ae_eq fm.ae_eq_mk).indicator measurableSet_closedBall
    have hv1 : Integrable v := by
      apply memLp_one_iff_integrable.mp
      exact hvp.mono_exponent_of_measure_support_ne_top
        (s := B) (fun x hx ↦ by simp [v, hx]) measure_closedBall_lt_top.ne
        (ENNReal.one_le_ofReal.mpr hq)
    have hvs : ∀ x, R < ‖x‖ → v x = 0 := by
      intro x hx
      have hxb : x ∉ B := by simpa only [B, mem_closedBall, dist_zero_right, not_le] using hx
      simp only [v, indicator_of_notMem hxb]
    have hvsm : Measurable (fun x ↦ star (v x)) := continuous_star.measurable.comp hvm
    have hvsi : Integrable (fun x ↦ star (v x)) :=
      memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hv1).star
    have hr := hrestriction (fun x ↦ star (v x)) hvsm hvsi hvp.star
      (fun x hx ↦ by simp [hvs x hx])
    have hrf : MemLp (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (v x)))
        (ENNReal.ofReal (p / (p - 1))) (sphereMeasure n) := by
      exact hr.trans_lt (ENNReal.mul_lt_top hCt.lt_top hvp.star)
    have he : (fun x ↦ f x * u x) =ᵐ[volume] fun x ↦ v x * sphericalExtension g x := by
      filter_upwards [fm.ae_eq_mk] with x hx
      by_cases hxb : x ∈ B <;> simp [u, v, hxb, hx]
    rw [integral_congr_ae he, integral_sphericalExtension_pairing hv1 hgi]
    have hpq : p.HolderConjugate (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
    calc
      _ ≤ eLpNorm g (ENNReal.ofReal p) (sphereMeasure n) *
          eLpNorm (fun ω ↦ star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier
            (fun x ↦ star (v x)) ω)) (ENNReal.ofReal (p / (p - 1))) (sphereMeasure n) :=
        OAI.Analysis.Fourier.BochnerRiesz.enorm_integral_mul_le_eLpNorm
          (sphereMeasure n) hg.aestronglyMeasurable hrf.star.aestronglyMeasurable hpq
      _ = eLpNorm g (ENNReal.ofReal p) (sphereMeasure n) *
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier
            (fun x ↦ star (v x))) (ENNReal.ofReal (p / (p - 1))) (sphereMeasure n) := by
        rw [show (fun ω ↦ star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier
          (fun x ↦ star (v x)) ω)) =
          star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (v x))) from rfl,
          eLpNorm_star]
      _ ≤ eLpNorm g (ENNReal.ofReal p) (sphereMeasure n) *
          (C * eLpNorm (fun x ↦ star (v x)) (ENNReal.ofReal (p / (p - 1))) volume) := by
        exact mul_le_mul' le_rfl hr
      _ = (C * eLpNorm g (ENNReal.ofReal p) (sphereMeasure n)) *
          eLpNorm v (ENNReal.ofReal (p / (p - 1))) volume := by
        rw [show (fun x ↦ star (v x)) = star v from rfl, eLpNorm_star]
        ring
      _ ≤ (C * eLpNorm g (ENNReal.ofReal p) (sphereMeasure n)) *
          eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume := by
        apply mul_le_mul' le_rfl
        calc
          _ ≤ eLpNorm (fm.mk f) (ENNReal.ofReal (p / (p - 1))) volume :=
            eLpNorm_indicator_le _ measurableSet_closedBall
          _ = _ := (eLpNorm_congr_ae fm.ae_eq_mk).symm
  have hn : eLpNorm u (ENNReal.ofReal p) volume =
      eLpNorm (sphericalExtension g) (ENNReal.ofReal p) (volume.restrict B) :=
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall
  constructor
  · change eLpNorm (sphericalExtension g) (ENNReal.ofReal p) (volume.restrict B) < ⊤
    rw [← hn]
    exact hu
  · change eLpNorm (sphericalExtension g) (ENNReal.ofReal p) (volume.restrict B) ≤ _
    rw [← hn]
    exact hnorm

end CriticalReplay
