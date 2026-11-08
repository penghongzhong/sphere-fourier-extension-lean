import OAI.Analysis.Fourier.Restriction.BallAverage
import OAI.Analysis.Fourier.BochnerRiesz.Product
import RestrictionWork.Definitions

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
open OAI.Analysis.Fourier.Restriction (lintegral_ball_add)
open OAI.Analysis.Fourier.BochnerRiesz (lintegral_enorm_rpow_eq_eLpNorm_pow)
namespace RestrictionWork

/-- Averaging translates over a ball for any finite ambient measure. -/
theorem measure_ball_average_identity {n : ℕ} {μ : Measure (Ambient n)} [IsFiniteMeasure μ]
    {F : Ambient n → ℝ≥0∞} (hF : Measurable F) (ρ : ℝ) :
    (∫⁻ v in ball (0 : Ambient n) ρ, ∫⁻ ω, F (ω + v) ∂μ) =
      ∫⁻ ξ, F ξ * μ (ball ξ ρ) := by
  have hm : Measurable (fun z : Ambient n × Ambient n => F (z.2 + z.1)) := by fun_prop
  let G : Ambient n × Ambient n → ℝ≥0∞ := fun z => (ball z.1 ρ).indicator F z.2
  have hG : Measurable G := by
    have hset : MeasurableSet {z : Ambient n × Ambient n | z.2 ∈ ball z.1 ρ} := by
      change MeasurableSet {z : Ambient n × Ambient n | dist z.2 z.1 < ρ}
      exact (isOpen_lt (show Continuous (fun z : Ambient n × Ambient n => dist z.2 z.1) by fun_prop)
        continuous_const).measurableSet
    exact (hF.comp measurable_snd).indicator hset
  calc
    _ = ∫⁻ ω, ∫⁻ v in ball (0 : Ambient n) ρ, F (ω + v) ∂volume ∂μ :=
      lintegral_lintegral_swap (μ := (volume : Measure (Ambient n)).restrict (ball 0 ρ))
        (ν := μ) hm.aemeasurable
    _ = ∫⁻ ω, ∫⁻ ξ, G (ω, ξ) ∂volume ∂μ := by
      apply lintegral_congr
      intro ω
      rw [lintegral_ball_add, ← lintegral_indicator measurableSet_ball]
    _ = ∫⁻ ξ, ∫⁻ ω, G (ω, ξ) ∂μ :=
      lintegral_lintegral_swap (μ := μ) (ν := (volume : Measure (Ambient n))) hG.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro ξ
      have he : (fun ω => G (ω, ξ)) = (ball ξ ρ).indicator (fun _ => F ξ) := by
        funext ω
        dsimp [G]
        have hh : ξ ∈ ball ω ρ ↔ ω ∈ ball ξ ρ := by simp only [mem_ball, dist_comm]
        by_cases hw : ω ∈ ball ξ ρ
        · simp only [indicator_of_mem hw, indicator_of_mem (hh.mpr hw)]
        · simp only [indicator_of_notMem hw, indicator_of_notMem (mt hh.mp hw)]
      rw [he, lintegral_indicator measurableSet_ball, lintegral_const, Measure.restrict_apply_univ]

/-- The lower mass of a patch in every ball centered in the tube gives a
volume-normalized thickening estimate. -/
theorem tube_norm_of_translated_bound {n : ℕ} {μ : Measure (Ambient n)} [IsFiniteMeasure μ]
    {U : Set (Ambient n)} (hU : MeasurableSet U) {ρ : ℝ} {m : ℝ≥0∞}
    (hm0 : m ≠ 0) (hmt : m ≠ ⊤) (hm : ∀ x ∈ U, m ≤ μ (ball x ρ))
    {p : ℝ} (hp : 0 < p) {F : Ambient n → ℂ} (hF : Measurable F) {B : ℝ≥0∞}
    (hB : ∀ v : Ambient n,
      eLpNorm (fun ω => F (ω + v)) (ENNReal.ofReal p) μ ≤ B) :
    eLpNorm F (ENNReal.ofReal p) (volume.restrict U) ≤
      (m⁻¹ * volume (ball (0 : Ambient n) ρ)) ^ (1 / p) * B := by
  let G : Ambient n → ℝ≥0∞ := fun ξ => ‖F ξ‖ₑ ^ p
  have hG : Measurable G := hF.enorm.pow_const p
  have H : m * (∫⁻ ξ in U, G ξ) ≤ ∫⁻ v in ball (0 : Ambient n) ρ, ∫⁻ ω, G (ω + v) ∂μ := by
    rw [measure_ball_average_identity hG]
    calc
      _ = ∫⁻ ξ in U, G ξ * m := by
        rw [lintegral_mul_const'' _ hG.aemeasurable]
        exact mul_comm _ _
      _ ≤ ∫⁻ ξ in U, G ξ * μ (ball ξ ρ) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hU] with ξ hξ
        exact mul_le_mul' le_rfl (hm ξ hξ)
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have Hup : (∫⁻ v in ball (0 : Ambient n) ρ, ∫⁻ ω, G (ω + v) ∂μ) ≤
      B ^ p * volume (ball (0 : Ambient n) ρ) := by
    calc
      _ ≤ ∫⁻ _v in ball (0 : Ambient n) ρ, B ^ p := by
        apply lintegral_mono
        intro v
        change (∫⁻ ω, ‖F (ω + v)‖ₑ ^ p ∂μ) ≤ B ^ p
        have hM : AEStronglyMeasurable (fun ω => F (ω + v)) μ :=
          (hF.comp (measurable_id.add_const v)).aestronglyMeasurable
        rw [lintegral_enorm_rpow_eq_eLpNorm_pow hM hp]
        exact ENNReal.rpow_le_rpow (hB v) hp.le
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  have HI : (∫⁻ ξ in U, G ξ) ≤
      (m⁻¹ * volume (ball (0 : Ambient n) ρ)) * B ^ p := by
    calc
      _ = m⁻¹ * (m * (∫⁻ ξ in U, G ξ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmt, one_mul]
      _ ≤ m⁻¹ * (B ^ p * volume (ball (0 : Ambient n) ρ)) :=
        mul_le_mul' le_rfl (H.trans Hup)
      _ = _ := by ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  calc
    _ ≤ ((m⁻¹ * volume (ball (0 : Ambient n) ρ)) * B ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow HI (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end RestrictionWork
