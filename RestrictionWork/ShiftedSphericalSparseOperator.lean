import RestrictionWork.ShiftedSphericalSparseGram
import OAI.Analysis.Fourier.Restriction.Sparse.Index
import OAI.Analysis.Fourier.Restriction.KernelLp

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal BigOperators
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction
  (localizedFourierKernel lintegral_localizedFourierKernel_le_ball localizedFourierKernel_row
    continuous_localizedFourierKernel indexedLocalizedKernel measurable_indexedLocalizedKernel
    norm_indexedLocalizedKernel_le gramKernel measurable_gramKernel
    lintegral_gramKernel_le_of_row_column finite_diagonal_sum_le integralKernel
    eLpNorm_integralKernel_le)
namespace RestrictionWork

theorem patch_graph_localized_column {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ)
    (u : SchwartzMap (Ambient (d + 1)) ℂ)
    (hu : ∀ ξ, ‖angularFourier u ξ‖ ≤ 1)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → angularFourier u ξ = 0)
    {R : ℝ} (hR : 0 < R) (z ξ : Ambient (d + 1)) :
    (∫⁻ ω, ‖localizedFourierKernel u R z ω ξ‖ₑ ∂patchGraphMeasure φ) ≤
      volume (ball (0 : Ambient d) 1) * ENNReal.ofReal R := by
  calc
    _ ≤ ENNReal.ofReal (R ^ (d + 1)) * patchGraphMeasure φ (ball ξ R⁻¹) :=
      lintegral_localizedFourierKernel_le_ball u hu hs _ hR z ξ
    _ ≤ ENNReal.ofReal (R ^ (d + 1)) *
        (ENNReal.ofReal ((R⁻¹) ^ d) * volume (ball (0 : Ambient d) 1)) :=
      mul_le_mul' le_rfl (patch_graph_measure_ball_upper hφ ξ (inv_pos.mpr hR))
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      have he : R ^ (d + 1) * (R⁻¹) ^ d = R := by
        rw [pow_succ, mul_comm (R ^ d) R, mul_assoc R, ← mul_pow,
          mul_inv_cancel₀ hR.ne', one_pow, mul_one]
      rw [he, mul_comm]

/-- The sparse reconstruction operator has the required (R^{1/p})
bound on the pushed-forward spherical graph measures. -/
theorem shifted_spherical_sparse_integral_kernel_bound {d : ℕ} (hd : 1 ≤ d)
    (u : SchwartzMap (Ambient (d + 1)) ℂ)
    (hu : ∀ ξ, ‖angularFourier u ξ‖ ≤ 1)
    (hr : ∀ ξ, star (angularFourier u ξ) = angularFourier u ξ)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → angularFourier u ξ = 0)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) {V : ℝ≥0∞} (hV : V ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ (N : ℕ) (R : ℝ), 1 ≤ R →
        ∀ z : Fin N → Ambient (d + 1),
          (∀ i j, i ≠ j → R ^ (16 * (d + 1)) * (N : ℝ) ^ (16 * (d + 1)) ≤ dist (z i) (z j)) →
          ∀ ν : Measure (Ambient (d + 1)), IsFiniteMeasure ν → ν ≤ volume → ν univ ≤ V →
          ∀ f : Fin N × Ambient (d + 1) → ℂ, Measurable f →
          Integrable f (Measure.count.prod ν) →
          eLpNorm (integralKernel (Measure.count.prod ν) (indexedLocalizedKernel u R z) f)
            (ENNReal.ofReal p) (patchGraphMeasure (shiftedSphericalGraphPhase δ a r)) ≤
            C * ENNReal.ofReal R ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) (Measure.count.prod ν) := by
  obtain ⟨B, hB, HB⟩ := shifted_spherical_separated_gram hd u hr
  let A := volume (ball (0 : Ambient d) 1)
  let D := volume (ball (0 : Ambient (d + 1)) 1)
  let E := D * A + ENNReal.ofReal B * V
  let Q := A * ENNReal.ofReal (p / (p - 1)) + E * ENNReal.ofReal (p / (2 - p))
  let C := 2 * Q ^ (1 / p)
  have hA : A ≠ ⊤ := measure_ball_lt_top.ne
  have hD : D ≠ ⊤ := measure_ball_lt_top.ne
  have hE : E ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top hD hA, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV⟩
  have hQ : Q ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top, ENNReal.mul_ne_top hE ENNReal.ofReal_ne_top⟩
  refine ⟨C, ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg (by positivity) hQ), ?_⟩
  intro δ r a hδ hδhalf ha hrpos hrhalf N R hR z hsep ν hνfinite hν hνV f hfm hf
  let := hνfinite
  let φ := shiftedSphericalGraphPhase δ a r
  let μ := patchGraphMeasure φ
  let K := indexedLocalizedKernel u R z
  have hφ : Measurable φ := by
    unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hR0 : 0 < R := by linarith
  have hRE : 1 ≤ ENNReal.ofReal R := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hR
  have hK : Measurable K := measurable_indexedLocalizedKernel u hR0 z
  have hcol (x : Fin N × Ambient (d + 1)) :
      (∫⁻ ω, ‖K (ω, x)‖ₑ ∂μ) ≤ A * ENNReal.ofReal R :=
    patch_graph_localized_column hφ u hu hs hR0 (z x.1) x.2
  have hgram (x : Fin N × Ambient (d + 1)) :
      (∫⁻ y, ‖gramKernel μ K (x, y)‖ₑ ∂(Measure.count.prod ν)) ≤ E * ENNReal.ofReal R := by
    have hG : Measurable (fun y : Fin N × Ambient (d + 1) => ‖gramKernel μ K (x, y)‖ₑ) := by
      have := measurable_gramKernel μ hK
      fun_prop
    rw [lintegral_prod _ hG.aemeasurable, lintegral_count, tsum_fintype]
    have hdiag : (∫⁻ η, ‖gramKernel μ K (x, (x.1, η))‖ₑ ∂ν) ≤
        D * (A * ENNReal.ofReal R) := by
      have hrow (ω : Ambient (d + 1)) :
          (∫⁻ η, ‖localizedFourierKernel u R (z x.1) ω η‖ₑ ∂ν) ≤ D :=
        (lintegral_mono' hν le_rfl).trans (localizedFourierKernel_row u hu hs hR0 (z x.1) ω)
      exact lintegral_gramKernel_le_of_row_column ν μ
        (K := fun p : Ambient (d + 1) × Ambient (d + 1) => localizedFourierKernel u R (z x.1) p.1 p.2)
        (continuous_localizedFourierKernel u hR0 (z x.1)).measurable hrow
          (patch_graph_localized_column hφ u hu hs hR0 (z x.1)) x.2
    have hN : 1 ≤ N := Nat.succ_le_of_lt (Nat.zero_lt_of_lt x.1.isLt)
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hoff (j : Fin N) (hj : j ≠ x.1) :
        (∫⁻ η, ‖gramKernel μ K (x, (j, η))‖ₑ ∂ν) ≤ ENNReal.ofReal (B / N) * ν univ := by
      calc
        _ ≤ ∫⁻ _η : Ambient (d + 1), ENNReal.ofReal (B / N) ∂ν := by
          apply lintegral_mono
          intro η
          dsimp only
          rw [← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          have hsep' : R ^ (16 * ((d : ℝ) + 1)) * (N : ℝ) ^ (16 * ((d : ℝ) + 1)) ≤
              dist (z x.1) (z j) := by
            have hcast : (16 * ((d : ℝ) + 1)) = ((16 * (d + 1) : ℕ) : ℝ) := by push_cast; rfl
            rw [hcast, Real.rpow_natCast, Real.rpow_natCast]
            exact hsep x.1 j hj.symm
          exact HB hδ hδhalf ha hrpos hrhalf R N hR hNR (z x.1) (z j) x.2 η hsep'
        _ = _ := lintegral_const _
    have Hsum := finite_diagonal_sum_le x.1
      (fun j => ∫⁻ η, ‖gramKernel μ K (x, (j, η))‖ₑ ∂ν) hdiag hoff
    have hscale : (N : ℝ≥0∞) * ENNReal.ofReal (B / N) = ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      field_simp
    apply Hsum.trans
    rw [← mul_assoc (N : ℝ≥0∞), hscale, show E = D * A + ENNReal.ofReal B * V by rfl,
      add_mul, mul_assoc]
    apply add_le_add le_rfl
    calc
      _ ≤ ENNReal.ofReal B * V := mul_le_mul' le_rfl hνV
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal B * V)) hRE
  have H := eLpNorm_integralKernel_le (Measure.count.prod ν) μ hK
    (pow_nonneg hR0.le (d + 1)) (norm_indexedLocalizedKernel_le u hu hR0 z) hcol hgram hfm hf hp hp2
  have he : (A * ENNReal.ofReal R) * ENNReal.ofReal (p / (p - 1)) +
      (E * ENNReal.ofReal R) * ENNReal.ofReal (p / (2 - p)) = Q * ENNReal.ofReal R := by
    dsimp only [Q]
    ring
  rw [he, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at H
  simpa only [C, mul_assoc] using H

end RestrictionWork
