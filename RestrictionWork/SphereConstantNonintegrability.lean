import RestrictionWork.OscillationWindows
import RestrictionWork.PeriodicWindowDivergence
import RestrictionWork.RadialPowerDensity
import OAI.Analysis.Fourier.Radial.Sphere.Decay
import OAI.Analysis.Fourier.Restriction.Polar

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RestrictionWork
open OAI.Analysis.Fourier.Wave (Space)
open OAI.Analysis.Fourier.Restriction
  (sphericalExtension continuous_sphericalExtension radialOscillation lintegral_polar_sphereMeasure)

/-- The actual angular-frequency extension of the constant sphere datum is
outside Lq at and below the radial threshold. The endpoint is included. -/
theorem sphere_constant_nonintegrability {n : ℕ} (hn : 3 ≤ n) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hqt : q ≠ ⊤)
    (hqc : q.toReal ≤ 2 * (n : ℝ) / ((n : ℝ) - 1)) :
    ¬ MemLp (sphericalExtension (fun _ : Space n ↦ (1 : ℂ))) q volume := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  have hqR : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  let β : ℝ := ((n : ℝ) - 1) / 2
  have hweight : β * q.toReal ≤ ((n - 1 : ℕ) : ℝ) + 1 := by
    have H := (le_div_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mp hqc
    rw [Nat.cast_sub hn1, Nat.cast_one]
    dsimp [β]
    nlinarith only [H]
  let K : Space n → ℂ := sphericalExtension (fun _ ↦ 1)
  let F : Space n → ℝ≥0∞ := fun x ↦ ‖K x‖ₑ ^ q.toReal
  have hK : Continuous K := continuous_sphericalExtension (integrable_const _)
  have hF : Measurable F := by dsimp [F]; fun_prop
  obtain ⟨A, B, C, _, hAB, hAsym⟩ := OAI.Analysis.Fourier.Radial.sphericalExtension_one_asymptotic hn1
  obtain ⟨s, w, a, hs, hw, hwP, ha, hwin⟩ := oscillation_windows (C := C) hAB
  have hdiv (ω : Space n) (hω : ‖ω‖ = 1) :
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * F (r • ω)) = ⊤ := by
    apply periodic_window_divergence (s := s) (P := 2 * Real.pi) (w := w)
      (c := a ^ q.toReal) (by linarith) hw hwP (Real.rpow_pos_of_pos ha _)
    intro k r hr
    have hr1 : 1 ≤ r := by
      have H : s + (k : ℝ) * (2 * Real.pi) < r := hr.1
      linarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        (show 0 ≤ 2 * Real.pi by positivity)]
    have hr0 : 0 < r := by linarith
    have hnorm : ‖r • ω‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hω, mul_one]
    have H := hAsym (r • ω) (by simpa only [hnorm] using hr1)
    rw [hnorm] at H
    change ‖((r ^ β : ℝ) : ℂ) * K (r • ω) - (radialOscillation A B r : ℂ)‖ ≤ C / r at H
    have J := norm_sub_norm_le (radialOscillation A B r : ℂ)
      (((r ^ β : ℝ) : ℂ) * K (r • ω))
    rw [norm_sub_rev (radialOscillation A B r : ℂ)] at J
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hr0.le β)] at J
    have hamp : a ≤ r ^ β * ‖K (r • ω)‖ := by linarith only [H, J, hwin k r hr]
    change ENNReal.ofReal (a ^ q.toReal / r) ≤
      ENNReal.ofReal (r ^ (n - 1)) * ‖K (r • ω)‖ₑ ^ q.toReal
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hqR.le,
      ← ENNReal.ofReal_mul (pow_nonneg hr0.le _)]
    exact ENNReal.ofReal_le_ofReal (radial_power_density hr1 ha hqR.le hweight hamp)
  have hae : (fun ω : Space n ↦
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * F (r • ω)) =ᵐ[
        OAI.Analysis.Fourier.Restriction.sphereMeasure n] (fun _ ↦ ⊤) := by
    filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
    exact hdiv ω hω
  have hInf : (∫⁻ x, F x) = ⊤ := by
    rw [lintegral_polar_sphereMeasure hn1 hF, lintegral_congr_ae hae, lintegral_const]
    exact ENNReal.top_mul (OAI.MeasureTheory.Kakeya.sphereMeasure_univ_pos hn1).ne'
  change ¬ MemLp K q volume
  intro hLp
  have H : (∫⁻ x, F x) < ⊤ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hqt hLp.aestronglyMeasurable).mp hLp
  exact H.ne hInf

end RestrictionWork
