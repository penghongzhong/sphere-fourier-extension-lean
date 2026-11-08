import RestrictionWork.DyadicAmplitudeApprox
import RestrictionWork.GraphExtensionPairingLimits
import RestrictionWork.RestrictedStrongMatrix
import OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace RestrictionWork

set_option maxHeartbeats 1100000 in
/-- A summable matrix bound for pairs of amplitude bands controls the
actual pairing on both unit balls. -/
theorem graph_knapp_unit_pairing_from_atoms {d : ℕ} {p s b : ℝ}
    (hp : 0 < p) (hs : 0 < s) (hb : 0 < b) (hb₁ : b < 1)
    {φ : Ambient d → ℝ} (hφ : Measurable φ)
    {f : Ambient d → ℂ} (hf : Measurable f) (hfi : Integrable f (patchMeasure d))
    (hfs : ∀ u ∉ Metric.ball (0 : Ambient d) (1 / 4), f u = 0)
    {g : Ambient d × ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g)
    (hfN : eLpNorm f (ENNReal.ofReal p) (patchMeasure d) ≤ 1)
    (hgN : eLpNorm g (ENNReal.ofReal s) volume ≤ 1)
    (K : ℤ → ℤ → ℝ≥0∞) {D C : ℝ≥0∞}
    (hrow : ∀ (i : ℤ) (J : Finset ℤ), ∑ j ∈ J, K i j ≤ D)
    (hcol : ∀ (j : ℤ) (I : Finset ℤ), ∑ i ∈ I, K i j ≤ D)
    (hAtom :
      ∀ i j : ℤ,
      let A := dyadicAmplitudeSet (Metric.ball (0 : Ambient d) (1 / 4)) f i
      let B := dyadicAmplitudeSet univ g j
      let α := ENNReal.ofReal ((2 : ℝ) ^ i) ^ p * volume A
      let β := ENNReal.ofReal ((2 : ℝ) ^ j) ^ s * volume B
      α ≤ 1 → β ≤ 1 →
      ‖∫ z, dyadicAmplitudePiece univ g j z *
          graphExtension (dyadicAmplitudePiece (Metric.ball 0 (1 / 4)) f i) φ z‖ₑ ≤
        C * (K i j * α ^ b * β ^ (1 - b))) :
    ‖∫ z, g z * graphExtension f φ z‖ₑ ≤ C * D := by
  let U := Metric.ball (0 : Ambient d) (1 / 4)
  let I (N : ℕ) := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let F (N : ℕ) := dyadicAmplitudeTrunc U f N
  let G (N : ℕ) := dyadicAmplitudeTrunc univ g N
  let A := dyadicAmplitudeSet U f
  let B := dyadicAmplitudeSet univ g
  let α i := ENNReal.ofReal ((2 : ℝ) ^ i) ^ p * volume (A i)
  let β j := ENNReal.ofReal ((2 : ℝ) ^ j) ^ s * volume (B j)
  have hUm : MeasurableSet U := measurableSet_ball
  have hAc (i : ℤ) : patchMeasure d (A i) = volume (A i) := by
    have hsub : A i ⊆ Metric.ball (0 : Ambient d) 1 :=
      inter_subset_left.trans (Metric.ball_subset_ball (by norm_num))
    rw [patchMeasure, Measure.restrict_apply (measurableSet_dyadic_amplitude_set hUm hf i),
      inter_eq_left.mpr hsub]
  have hα (N : ℕ) : ∑ i ∈ I N, α i ≤ 1 := by
    have H := dyadic_amplitude_mass_sum_le (patchMeasure d) hUm hf (I N) hp.le
    change (∑ i ∈ I N, ENNReal.ofReal ((2 : ℝ) ^ i) ^ p * patchMeasure d (A i)) ≤ _ at H
    simp_rw [hAc] at H
    refine H.trans ?_
    rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hf.aestronglyMeasurable]
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hfN hp.le
  have hβ (N : ℕ) : ∑ j ∈ I N, β j ≤ 1 := by
    refine (dyadic_amplitude_mass_sum_le volume MeasurableSet.univ hg (I N) hs.le).trans ?_
    rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hs hg.aestronglyMeasurable]
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hgN hs.le
  have hFi (i : ℤ) : Integrable (dyadicAmplitudePiece U f i) (patchMeasure d) :=
    hfi.indicator (measurableSet_dyadic_amplitude_set hUm hf i)
  have hGi (j : ℤ) : Integrable (dyadicAmplitudePiece univ g j) :=
    hgi.indicator (measurableSet_dyadic_amplitude_set MeasurableSet.univ hg j)
  have hpartial (N : ℕ) :
      ‖∫ z, G N z * graphExtension (F N) φ z‖ₑ ≤ C * D := by
    refine (graph_extension_pairing_finset_le (I N) (I N)
      (fun i _ => hFi i) (fun j _ => hGi j) hφ).trans ?_
    calc
      _ ≤ ∑ i ∈ I N, ∑ j ∈ I N, C * (K i j * α i ^ b * β j ^ (1 - b)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hAtom i j
          ((Finset.single_le_sum (f := α) (fun _ _ => zero_le) hi).trans (hα N))
          ((Finset.single_le_sum (f := β) (fun _ _ => zero_le) hj).trans (hβ N))
      _ = C * ∑ i ∈ I N, ∑ j ∈ I N, K i j * α i ^ b * β j ^ (1 - b) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul' le_rfl (weighted_matrix_rpow_sum_le_of_normalized
        (I N) (I N) K α β hb hb₁ (fun i _ => hrow i _) (fun j _ => hcol j _) (hα N) (hβ N))
  have hUeq : U.indicator f = f := by
    funext u
    by_cases hu : u ∈ U
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hfs u hu]
  have hlim := graph_extension_pairing_tendsto hfi
    (F := F) (fun n => (measurable_dyadic_amplitude_trunc hUm hf n).aestronglyMeasurable)
    (norm_dyadic_amplitude_trunc_le U f)
    (fun u => by simpa only [hUeq] using tendsto_dyadic_amplitude_trunc U f u)
    hgi (G := G)
    (fun n => (measurable_dyadic_amplitude_trunc MeasurableSet.univ hg n).aestronglyMeasurable)
    (norm_dyadic_amplitude_trunc_le univ g)
    (fun z => by simpa only [indicator_univ] using tendsto_dyadic_amplitude_trunc univ g z) hφ
  exact le_of_tendsto (continuous_enorm.continuousAt.tendsto.comp hlim) (.of_forall hpartial)

end RestrictionWork
