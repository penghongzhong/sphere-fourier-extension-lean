import RestrictionWork.Definitions
import OAI.Analysis.Fourier.Restriction.PolynomialWeight

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction
  (continuous_angularFourier norm_angularFourier_le_integral_norm
    spherical_character_sub polynomial_decay_sub_le)
namespace RestrictionWork

/-- Angular-frequency extension against a measure on Euclidean space. -/
def measureExtension {n : ℕ} (μ : Measure (Ambient n)) (g : Ambient n → ℂ)
    (x : Ambient n) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (⟪x, ω⟫ : ℝ)) * g ω ∂μ

private theorem continuous_measure_extension {n : ℕ} {μ : Measure (Ambient n)}
    {g : Ambient n → ℂ} (hg : Integrable g μ) :
    Continuous (measureExtension μ g) := by
  unfold measureExtension
  apply continuous_of_dominated (bound := fun ω => ‖g ω‖)
  · intro x
    have hm : Measurable (fun ω : Ambient n => Complex.exp (Complex.I * (⟪x, ω⟫ : ℝ))) := by
      fun_prop
    exact hm.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · intro x
    filter_upwards [] with ω
    simp [Complex.norm_exp]
  · exact hg.norm
  · filter_upwards [] with ω
    fun_prop

private theorem norm_measure_extension_le {n : ℕ} {μ : Measure (Ambient n)}
    (g : Ambient n → ℂ) (x : Ambient n) :
    ‖measureExtension μ g x‖ ≤ ∫ ω, ‖g ω‖ ∂μ := by
  unfold measureExtension
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with ω
  simp [Complex.norm_exp]

/-- The Fubini identity from the sphere proof works with any finite measure. -/
theorem measure_extension_fourier_mul {n : ℕ} {μ : Measure (Ambient n)}
    [IsFiniteMeasure μ] {f g : Ambient n → ℂ} (hf : Integrable f) (hg : Integrable g μ)
    (x : Ambient n) :
    measureExtension μ (fun ω => angularFourier f ω * g ω) x =
      ∫ y, f y * measureExtension μ g (x - y) := by
  let F : Ambient n × Ambient n → ℂ := fun z => f z.1 *
    (Complex.exp (Complex.I * (⟪x - z.1, z.2⟫ : ℝ)) * g z.2)
  have hi : Integrable F (volume.prod μ) := by
    apply (hf.norm.mul_prod hg.norm).mono'
    · have hc : Continuous (fun z : Ambient n × Ambient n =>
          Complex.exp (Complex.I * (⟪x - z.1, z.2⟫ : ℝ))) := by fun_prop
      exact hf.aestronglyMeasurable.comp_fst.mul
        (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
    · filter_upwards [] with z
      simp [F, Complex.norm_exp]
  calc
    _ = ∫ ω, ∫ y, F (y, ω) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      unfold angularFourier
      rw [← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [F]
      rw [← spherical_character_sub]
      ring
    _ = ∫ y, ∫ ω, F (y, ω) ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [F, measureExtension, integral_const_mul]

theorem measure_extension_fourier_mul_decay {n : ℕ} {μ : Measure (Ambient n)}
    [IsFiniteMeasure μ] {f g : Ambient n → ℂ} {b C : ℝ}
    (hf : Integrable f) (hg : Integrable g μ) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hfw : Integrable (fun y => ‖f y‖ * (1 + ‖y‖) ^ b))
    (hdecay : ∀ x, ‖measureExtension μ g x‖ ≤ C * (1 + ‖x‖) ^ (-b))
    (x : Ambient n) :
    ‖measureExtension μ (fun ω => angularFourier f ω * g ω) x‖ ≤
      (C * ∫ y, ‖f y‖ * (1 + ‖y‖) ^ b) * (1 + ‖x‖) ^ (-b) := by
  rw [measure_extension_fourier_mul hf hg]
  have hi : Integrable (fun y => f y * measureExtension μ g (x - y)) := by
    have H := hf.bdd_mul
      (((continuous_measure_extension hg).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (.of_forall fun y => norm_measure_extension_le g (x - y))
    simpa only [Function.comp_apply, Pi.sub_apply, id_eq, mul_comm] using H
  calc
    _ ≤ ∫ y, ‖f y * measureExtension μ g (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (C * (1 + ‖x‖) ^ (-b)) * (‖f y‖ * (1 + ‖y‖) ^ b) := by
      apply integral_mono hi.norm (hfw.const_mul _)
      intro y
      dsimp only
      rw [norm_mul]
      calc
        _ ≤ ‖f y‖ * (C * (1 + ‖x - y‖) ^ (-b)) :=
          mul_le_mul_of_nonneg_left (hdecay (x - y)) (norm_nonneg _)
        _ ≤ ‖f y‖ * (C * ((1 + ‖x‖) ^ (-b) * (1 + ‖y‖) ^ b)) := by
          gcongr
          exact polynomial_decay_sub_le x y hb
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; ring

theorem measure_extension_fourier_product_decay {n : ℕ} {μ : Measure (Ambient n)}
    [IsFiniteMeasure μ] {f g : Ambient n → ℂ} {b C : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hfw : Integrable (fun y => ‖f y‖ * (1 + ‖y‖) ^ b))
    (hgw : Integrable (fun y => ‖g y‖ * (1 + ‖y‖) ^ b))
    (hdecay : ∀ x, ‖measureExtension μ (fun _ => 1) x‖ ≤ C * (1 + ‖x‖) ^ (-b))
    (x : Ambient n) :
    ‖measureExtension μ (fun ω => angularFourier f ω * angularFourier g ω) x‖ ≤
      (C * (∫ y, ‖f y‖ * (1 + ‖y‖) ^ b) * (∫ y, ‖g y‖ * (1 + ‖y‖) ^ b)) *
        (1 + ‖x‖) ^ (-b) := by
  have hG : Integrable (angularFourier g) μ :=
    (integrable_const (∫ y, ‖g y‖)).mono' (continuous_angularFourier hg).aestronglyMeasurable
      (.of_forall (norm_angularFourier_le_integral_norm g))
  have hGdecay (z : Ambient n) := measure_extension_fourier_mul_decay hg
    (integrable_const (1 : ℂ)) hb hC hgw hdecay z
  simp only [mul_one] at hGdecay
  have H := measure_extension_fourier_mul_decay hf hG hb
    (show 0 ≤ C * ∫ y, ‖g y‖ * (1 + ‖y‖) ^ b by positivity) hfw hGdecay x
  exact H.trans_eq (by ring)

end RestrictionWork
