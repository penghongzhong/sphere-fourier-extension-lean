import RestrictionWork.ShiftedSphericalMeasureDecay
import OAI.Analysis.Fourier.Restriction.Sparse.Decay
import OAI.Analysis.Fourier.Restriction.FourierBump

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction
  (translatedFrequencyBump translatedFrequencyBump_weight_bound integrable_translatedFrequencyBump
    localizedFourierKernel star_fourier_translatedFrequencyBump
    spherical_character_sub separated_decay_bound)
namespace RestrictionWork

theorem shifted_spherical_bump_product_decay {d : ℕ} (hd : 1 ≤ d)
    (u : SchwartzMap (Ambient (d + 1)) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ R : ℝ, 1 ≤ R → ∀ ξ η x : Ambient (d + 1),
        ‖measureExtension (patchGraphMeasure (shiftedSphericalGraphPhase δ a r))
          (fun ω => angularFourier (translatedFrequencyBump u R ξ) ω *
            angularFourier (translatedFrequencyBump u R η) ω) x‖ ≤
          C * (R ^ (d + 1) * R ^ (1 / 2 : ℝ)) ^ 2 * (1 + ‖x‖) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, hA, HA⟩ := shifted_spherical_measure_decay hd
  let b : ℝ := 1 / 2
  let M : ℝ := ∫ y, ‖u y‖ * (1 + ‖y‖) ^ b
  have hb : 0 ≤ b := by norm_num [b]
  have hM : 0 ≤ M := by unfold M; positivity
  refine ⟨A * M ^ 2, by positivity, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf R hR ξ η x
  have hR0 : 0 < R := by linarith
  let f := translatedFrequencyBump u R ξ
  let g := translatedFrequencyBump u R η
  let Mf := ∫ y, ‖f y‖ * (1 + ‖y‖) ^ b
  let Mg := ∫ y, ‖g y‖ * (1 + ‖y‖) ^ b
  let Rb := R ^ (d + 1) * R ^ b
  obtain ⟨hfi, hf⟩ := translatedFrequencyBump_weight_bound u hR hb ξ
  obtain ⟨hgi, hg⟩ := translatedFrequencyBump_weight_bound u hR hb η
  have H := measure_extension_fourier_product_decay
    (integrable_translatedFrequencyBump u.integrable hR0 ξ)
    (integrable_translatedFrequencyBump u.integrable hR0 η)
    hb hA hfi hgi (HA hδ hδhalf ha hr hrhalf) x
  change _ ≤ (A * Mf * Mg) * (1 + ‖x‖) ^ (-b) at H
  change _ ≤ A * M ^ 2 * Rb ^ 2 * (1 + ‖x‖) ^ (-b)
  calc
    _ ≤ _ := H
    _ ≤ (A * (Rb * M) * (Rb * M)) * (1 + ‖x‖) ^ (-b) := by
      have hMf : 0 ≤ Mf := by unfold Mf; positivity
      have hMg : 0 ≤ Mg := by unfold Mg; positivity
      gcongr
    _ = _ := by ring

/-- The off-diagonal Gram term of the actual graph kernel on separated
physical balls, with the same separation exponent as the sphere proof. -/
theorem shifted_spherical_separated_gram {d : ℕ} (hd : 1 ≤ d)
    (u : SchwartzMap (Ambient (d + 1)) ℂ)
    (hu : ∀ x, star (angularFourier u x) = angularFourier u x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ R N : ℝ, 1 ≤ R → 1 ≤ N →
        ∀ z w ξ η : Ambient (d + 1),
          R ^ (16 * ((d : ℝ) + 1)) * N ^ (16 * ((d : ℝ) + 1)) ≤ dist z w →
          ‖∫ ω, localizedFourierKernel u R z ω ξ *
              star (localizedFourierKernel u R w ω η)
            ∂patchGraphMeasure (shiftedSphericalGraphPhase δ a r)‖ ≤ C / N := by
  obtain ⟨C, hC, HC⟩ := shifted_spherical_bump_product_decay hd u
  refine ⟨C, hC, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf R N hR hN z w ξ η hsep
  let μ := patchGraphMeasure (shiftedSphericalGraphPhase δ a r)
  have hR0 : 0 < R := by linarith
  have he :
      (∫ ω, localizedFourierKernel u R z ω ξ * star (localizedFourierKernel u R w ω η) ∂μ) =
        measureExtension μ (fun ω => angularFourier (translatedFrequencyBump u R ξ) ω *
          angularFourier (translatedFrequencyBump u R η) ω) (w - z) := by
    unfold measureExtension
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [localizedFourierKernel, localizedFourierKernel, star_mul,
      star_fourier_translatedFrequencyBump u hu hR0]
    have hstar : star (Complex.exp (-Complex.I * (⟪w, ω⟫ : ℝ))) =
        Complex.exp (Complex.I * (⟪w, ω⟫ : ℝ)) := by
      simp [← Complex.exp_conj]
    rw [hstar, ← spherical_character_sub]
    ring
  have hscale : (R ^ (d + 1) * R ^ (1 / 2 : ℝ)) ^ 2 =
      R ^ (2 * (((d : ℝ) + 1) + 1 / 2)) := by
    rw [← Real.rpow_natCast R (d + 1), ← Real.rpow_add hR0, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hR0.le]
    push_cast
    congr 1
    ring
  have hsmall : (R ^ (d + 1) * R ^ (1 / 2 : ℝ)) ^ 2 *
      (1 + dist z w) ^ (-(1 / 2 : ℝ)) ≤ N⁻¹ := by
    rw [hscale]
    apply separated_decay_bound (a := 1 / 2) (D := 16 * ((d : ℝ) + 1))
      (by norm_num) _ _ hR hN hsep
    · linarith [Nat.cast_nonneg (α := ℝ) d]
    · linarith [Nat.cast_nonneg (α := ℝ) d]
  rw [he]
  calc
    _ ≤ C * (R ^ (d + 1) * R ^ (1 / 2 : ℝ)) ^ 2 *
        (1 + dist z w) ^ (-(1 / 2 : ℝ)) := by
      simpa only [dist_eq_norm, norm_sub_rev] using HC hδ hδhalf ha hr hrhalf R hR ξ η (w - z)
    _ ≤ C / N := by
      rw [div_eq_mul_inv, mul_assoc]
      exact mul_le_mul_of_nonneg_left hsmall hC

end RestrictionWork
