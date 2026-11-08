import RestrictionWork.GraphExtensionPairingLimits
import OAI.Analysis.Fourier.BochnerRiesz.DualityNorm
import OAI.Analysis.Fourier.BochnerRiesz.FourierLimit

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace RestrictionWork

/-- The bounded-function pairing criterion on a sigma-finite measure space. -/
private theorem eLpNorm_le_of_spanning_pairing {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {q : ℝ} (hq : 1 < q) {F : X → ℂ}
    (hF : AEStronglyMeasurable F μ) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) {C : ℝ≥0∞}
    (H : ∀ g : X → ℂ, Integrable g μ → MemLp g (ENNReal.ofReal (q / (q - 1))) μ →
      ‖∫ x, g x * F x ∂μ‖ₑ ≤ C * eLpNorm g (ENNReal.ofReal (q / (q - 1))) μ) :
    eLpNorm F (ENNReal.ofReal q) μ ≤ C := by
  let s (n : ℕ) := spanningSets μ n
  let U (n : ℕ) := (s n).indicator F
  have hs (n : ℕ) : MeasurableSet (s n) := measurableSet_spanningSets μ n
  have hU (n : ℕ) : AEStronglyMeasurable (U n) μ := hF.indicator (hs n)
  have hUm (n : ℕ) : MemLp (U n) (ENNReal.ofReal q) μ := by
    have htop := memLp_top_of_bound (hU n) M (Eventually.of_forall (fun x => by
      exact (norm_indicator_le_norm_self F x).trans (hM x)))
    exact htop.mono_exponent_of_measure_support_ne_top (s := s n) (fun x hx => by simp [U, hx])
      (measure_spanningSets_lt_top μ n).ne le_top
  have hB (n : ℕ) : eLpNorm (U n) (ENNReal.ofReal q) μ ≤ C := by
    apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_integral_mul_bound μ hq (hUm n)
    intro g hg
    let v := (s n).indicator g
    have hv : MemLp v (ENNReal.ofReal (q / (q - 1))) μ := hg.indicator (hs n)
    have hq' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (q / (q - 1)) := by
      have h : 1 ≤ q / (q - 1) := (le_div_iff₀ (by linarith)).2 (by linarith)
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h
    have hv1 : Integrable v μ := memLp_one_iff_integrable.mp
      (hv.mono_exponent_of_measure_support_ne_top (s := s n) (fun x hx => by simp [v, hx])
        (measure_spanningSets_lt_top μ n).ne hq')
    have he : (fun x => g x * U n x) = fun x => v x * F x := by
      funext x
      by_cases hx : x ∈ s n <;> simp [U, v, hx]
    rw [he]
    exact (H v hv1 hv).trans (mul_le_mul' le_rfl (eLpNorm_indicator_le g (hs n)))
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise μ hU hF ?_
    (by linarith) hB
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_mem_spanningSets μ x] with n hn
  simp [U, s, hn]

private theorem exists_unit_eLpNorm_scale {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {r : ℝ≥0∞} {f : X → ℂ} (hn : eLpNorm f r μ ≠ 0)
    (ht : eLpNorm f r μ ≠ ⊤) :
    ∃ a : ℂ, a ≠ 0 ∧ ‖a‖ₑ = eLpNorm f r μ ∧ eLpNorm (a⁻¹ • f) r μ = 1 := by
  let N := eLpNorm f r μ
  have hN : 0 < N.toReal := ENNReal.toReal_pos hn ht
  let a : ℂ := N.toReal
  have ha : a ≠ 0 := by
    change (N.toReal : ℂ) ≠ 0
    exact_mod_cast hN.ne'
  have hae : ‖a‖ₑ = N := by
    rw [← ofReal_norm]
    simpa only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN] using
      ENNReal.ofReal_toReal ht
  refine ⟨a, ha, hae, ?_⟩
  rw [eLpNorm_const_smul, enorm_inv ha, hae, ENNReal.inv_mul_cancel hn ht]

set_option maxHeartbeats 850000 in
/-- A bound for normalized measurable input and dual test functions
implies the graph strong norm inequality on the same inner patch. -/
theorem graph_extension_le_of_unit_pairing {d : ℕ} {p q : ℝ} (hp : 1 ≤ p)
    (hq : 1 < q) {φ : Ambient d → ℝ} (hφ : Measurable φ) {C : ℝ≥0∞}
    (Hunit : ∀ {f : Ambient d → ℂ} {g : Ambient d × ℝ → ℂ}, Measurable f →
      Integrable f (patchMeasure d) → (∀ u ∉ Metric.ball 0 (1 / 4), f u = 0) →
      eLpNorm f (ENNReal.ofReal p) (patchMeasure d) ≤ 1 → Measurable g → Integrable g →
      eLpNorm g (ENNReal.ofReal (q / (q - 1))) volume ≤ 1 →
      ‖∫ z, g z * graphExtension f φ z‖ₑ ≤ C)
    {f : Ambient d → ℂ} (hf : Measurable f) (hfp : MemLp f (ENNReal.ofReal p) (patchMeasure d))
    (hfs : ∀ u ∉ Metric.ball 0 (1 / 4), f u = 0) :
    eLpNorm (graphExtension f φ) (ENNReal.ofReal q) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) (patchMeasure d) := by
  let μ := patchMeasure d
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (q / (q - 1))
  have hP : 1 ≤ P := by simpa only [P, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hQ : Q ≠ 0 := (ENNReal.ofReal_pos.mpr (div_pos (by linarith) (by linarith))).ne'
  let : IsFiniteMeasure μ := by
    unfold μ patchMeasure
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hfi : Integrable f μ := hfp.integrable hP
  by_cases hf0 : eLpNorm f P μ = 0
  · have hzero : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff (zero_lt_one.trans_le hP).ne').mp hf0
    have he : graphExtension f φ = 0 := funext fun z => by
      rw [graph_extension_congr_ae hzero φ z]
      simp [graphExtension, phaseExtension]
    change eLpNorm (graphExtension f φ) (ENNReal.ofReal q) volume ≤ C * eLpNorm f P μ
    rw [he, hf0, mul_zero, eLpNorm_zero]
  obtain ⟨a, ha, hae, hna⟩ := exists_unit_eLpNorm_scale hf0 hfp.eLpNorm_ne_top
  let F := a⁻¹ • f
  have hFm : Measurable F := hf.const_smul _
  have hFi : Integrable F μ := hfi.const_mul _
  have hFs : ∀ u ∉ Metric.ball 0 (1 / 4), F u = 0 := fun u hu => by
    simp [F, hfs u hu]
  have hdual : eLpNorm (graphExtension F φ) (ENNReal.ofReal q) volume ≤ C := by
    apply eLpNorm_le_of_spanning_pairing volume hq (graph_extension_continuous hFi hφ).aestronglyMeasurable
      (graph_extension_norm_le_integral_norm F φ)
    intro g hgi hgq
    by_cases hg0 : eLpNorm g Q volume = 0
    · have hzero : g =ᵐ[(volume : Measure (Ambient d × ℝ))] 0 := (eLpNorm_eq_zero_iff hQ).mp hg0
      have he : (∫ z, g z * graphExtension F φ z) = 0 := by
        rw [← integral_zero (Ambient d × ℝ) ℂ]
        apply integral_congr_ae
        filter_upwards [hzero] with z hz
        simp [hz]
      rw [he, enorm_zero]
      exact zero_le
    let g₀ := hgq.aestronglyMeasurable.mk g
    have hge : g =ᵐ[(volume : Measure (Ambient d × ℝ))] g₀ := hgq.aestronglyMeasurable.ae_eq_mk
    have hg₀m : Measurable g₀ := hgq.aestronglyMeasurable.measurable_mk
    have hg₀i : Integrable g₀ := hgi.congr hge
    have hg₀norm : eLpNorm g₀ Q volume = eLpNorm g Q volume := (eLpNorm_congr_ae hge).symm
    obtain ⟨b, hb, hbe, hnb⟩ := exists_unit_eLpNorm_scale
      (by rw [hg₀norm]; exact hg0) (by rw [hg₀norm]; exact hgq.eLpNorm_ne_top)
    let G := b⁻¹ • g₀
    have hu := Hunit (g := G) hFm hFi hFs hna.le (hg₀m.const_smul _) (hg₀i.const_mul _) hnb.le
    have he : (∫ z, g z * graphExtension F φ z) =
        b * ∫ z, G z * graphExtension F φ z := by
      calc
        _ = ∫ z, g₀ z * graphExtension F φ z := by
          apply integral_congr_ae
          filter_upwards [hge] with z hz
          rw [hz]
        _ = _ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact .of_forall fun z => by
            simp [G, smul_eq_mul, ← mul_assoc, hb]
    rw [he, enorm_mul, hbe, hg₀norm, mul_comm]
    exact mul_le_mul' hu le_rfl
  have hrestore : graphExtension f φ = a • graphExtension F φ := by
    funext z
    have he : f = fun u => a * F u := by
      funext u
      simp [F, smul_eq_mul, ha]
    change graphExtension f φ z = a * graphExtension F φ z
    rw [← graph_extension_const_mul, ← he]
  rw [hrestore, eLpNorm_const_smul, hae, mul_comm C]
  exact mul_le_mul' le_rfl hdual

end RestrictionWork
