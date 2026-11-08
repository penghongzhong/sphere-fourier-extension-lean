import CriticalExtensionContract
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open OAI.Analysis.Fourier.Wave OAI.Analysis.Fourier.Restriction
open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

set_option autoImplicit false
noncomputable section
namespace CriticalReplay

/-- The actual positive-sign extension integral in the `2π` convention. -/
def sphericalExtensionTwoPi {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (((2 * Real.pi) * inner ℝ x ω : ℝ) : ℂ)) *
    g ω ∂sphereMeasure n

theorem sphericalExtensionTwoPi_eq {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    sphericalExtensionTwoPi g x = sphericalExtension g ((2 * Real.pi) • x) := by
  simp [sphericalExtensionTwoPi, sphericalExtension, inner_smul_left]

/-- Exact local dilation of the output norm, including its Haar Jacobian. -/
theorem dilation_local_norm {n : ℕ} {c : ℝ} (hc : 0 < c)
    (F : Space n → ℂ) (hF : Continuous F) (p : ℝ≥0∞) (S : Set (Space n)) :
    eLpNorm (fun x ↦ F (c • x)) p (volume.restrict S) =
      ENNReal.ofReal |(c ^ n)⁻¹| ^ p.toReal⁻¹ *
        eLpNorm F p (volume.restrict ((fun x : Space n ↦ c • x) '' S)) := by
  let Ψ : Space n → Space n := fun x ↦ c • x
  have hΨ : Measurable Ψ := by dsimp [Ψ]; fun_prop
  have hi : Function.Injective Ψ := by
    intro x y h
    have H := congrArg (fun z : Space n ↦ c⁻¹ • z) h
    simpa only [Ψ, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using H
  have he := hΨ.measurableEmbedding hi
  have hm : (volume : Measure (Space n)).map Ψ =
      ENNReal.ofReal |(c ^ n)⁻¹| • volume := by
    simpa only [Ψ, Space, finrank_euclideanSpace_fin] using
      (Measure.map_addHaar_smul (volume : Measure (Space n)) hc.ne')
  have hms : ((volume : Measure (Space n)).restrict S).map Ψ =
      ENNReal.ofReal |(c ^ n)⁻¹| • (volume.restrict (Ψ '' S)) := by
    calc
      _ = ((volume : Measure (Space n)).map Ψ).restrict (Ψ '' S) := by
        rw [he.restrict_map, hi.preimage_image]
      _ = _ := by rw [hm, Measure.restrict_smul]
  have hc0 : ENNReal.ofReal |(c ^ n)⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hc.ne')))).ne'
  calc
    _ = eLpNorm F p (((volume : Measure (Space n)).restrict S).map Ψ) :=
      (eLpNorm_map_measure hF.aestronglyMeasurable hΨ.aemeasurable).symm
    _ = _ := by
      rw [hms, eLpNorm_smul_measure_of_ne_zero hc0]
      simp only [one_div, ENNReal.toReal_inv, smul_eq_mul, Ψ]

/-- Critical local extension with the literal `2π` integral and a finite
constant independent of the radius and sphere input. -/
theorem localSmoothing_twoPi_local_extension_critical
    (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ g : Space n → ℂ,
      MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (sphereMeasure n) →
      MemLp (sphericalExtensionTwoPi g)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (closedBall 0 R)) ∧
      eLpNorm (sphericalExtensionTwoPi g)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
        (volume.restrict (closedBall 0 R)) ≤
        D * ENNReal.ofReal (R ^ ε) *
          eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
            (sphereMeasure n) := by
  let p := ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hc1 : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  let K : ℝ≥0∞ := ENNReal.ofReal |(c ^ n)⁻¹| ^ p.toReal⁻¹
  have hK : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
    (inv_nonneg.mpr ENNReal.toReal_nonneg) ENNReal.ofReal_ne_top
  obtain ⟨C, hC, HC⟩ := localSmoothing_local_extension_critical hls hn hε
  let D : ℝ≥0∞ := K * C * ENNReal.ofReal (c ^ ε)
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hK hC) ENNReal.ofReal_ne_top
  refine ⟨D, hD, ?_⟩
  intro R hR g hg
  have hR0 : 0 ≤ R := by linarith
  have hCR : 1 ≤ c * R := by nlinarith
  have hgi : Integrable g (sphereMeasure n) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (ENNReal.one_le_ofReal.mpr
      (by
        dsimp [OAI.Analysis.Fourier.LocalSmoothing.criticalExponent]
        have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
        apply (le_div_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mpr
        linarith)))
  have hin : (fun x : Space n ↦ c • x) '' closedBall 0 R ⊆ closedBall 0 (c * R) := by
    rintro y ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_zero_right] using hx) hc.le
  have H : eLpNorm (sphericalExtensionTwoPi g) p (volume.restrict (closedBall 0 R)) ≤
      D * ENNReal.ofReal (R ^ ε) * eLpNorm g p (sphereMeasure n) := by
    rw [show sphericalExtensionTwoPi g =
      (fun x ↦ sphericalExtension g (c • x)) from funext (sphericalExtensionTwoPi_eq g)]
    calc
      _ = K * eLpNorm (sphericalExtension g) p
          (volume.restrict ((fun x : Space n ↦ c • x) '' closedBall 0 R)) :=
        dilation_local_norm hc _ (continuous_sphericalExtension hgi) p _
      _ ≤ K * eLpNorm (sphericalExtension g) p (volume.restrict (closedBall 0 (c * R))) :=
        mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hin le_rfl))
      _ ≤ K * (C * ENNReal.ofReal ((c * R) ^ ε) * eLpNorm g p (sphereMeasure n)) :=
        mul_le_mul' le_rfl (HC (c * R) hCR g hg).2
      _ = _ := by
        rw [Real.mul_rpow hc.le hR0, ENNReal.ofReal_mul (Real.rpow_nonneg hc.le ε)]
        dsimp [D]
        ring
  exact ⟨H.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top).lt_top hg), H⟩

end CriticalReplay
