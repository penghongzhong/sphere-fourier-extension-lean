import RestrictionWork.ShiftedGraphTubeGeometry
import OAI.Analysis.Fourier.Restriction.Sparse.Identity
import OAI.Analysis.Fourier.Restriction.Sparse.KernelMass

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal BigOperators
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction
  (localizedFourierKernel localizedFourierKernel_eq_zero localizedFourierKernel_reconstruction
    indexedLocalizedKernel integralKernel sparsePiece integrable_sparsePiece sparsePiece_recover
    sum_ball_indicators_eq angularFourier_sum integralKernel_finite_sum integrable_finite_fourier)
namespace RestrictionWork

theorem ae_patch_graph_point {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ) :
    ∀ᵐ ω ∂patchGraphMeasure φ, ∃ v ∈ ball (0 : Ambient d) 1, ω = patchGraphPoint φ v := by
  have hinj : Function.Injective (patchGraphPoint φ) := by
    intro x y hxy
    exact congrArg Prod.fst ((euclideanSliceEquiv (Fin.last d)).injective hxy)
  have he := (measurable_patch_graph_point hφ).measurableEmbedding hinj
  change ∀ᵐ ω ∂(patchMeasure d).map (patchGraphPoint φ), _
  apply he.ae_map_iff.mpr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Ambient d))) measurableSet_ball] with v hv
  exact ⟨v, hv, rfl⟩

private theorem tube_reconstruction {d : ℕ} {φ : Ambient d → ℝ}
    {f : Ambient (d + 1) → ℂ} (hf : Integrable f) (u : SchwartzMap (Ambient (d + 1)) ℂ)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → angularFourier u ξ = 0)
    {R : ℝ} (hR : 0 < R) (z : Ambient (d + 1)) {v : Ambient d}
    (hv : v ∈ ball 0 1) :
    angularFourier (fun x => f (x - z) * u (R⁻¹ • (x - z))) (patchGraphPoint φ v) =
      (((2 * Real.pi) ^ (d + 1))⁻¹ : ℝ) •
        ∫ ξ in patchGraphTube φ R⁻¹,
          localizedFourierKernel u R z (patchGraphPoint φ v) ξ * angularFourier f ξ := by
  rw [localizedFourierKernel_reconstruction hf u hR z]
  congr 1
  rw [← integral_indicator (measurable_set_patch_graph_tube φ R⁻¹)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  by_cases hξ : ξ ∈ patchGraphTube φ R⁻¹
  · rw [indicator_of_mem hξ]
  · have hdist : R⁻¹ ≤ dist (patchGraphPoint φ v) ξ := by
      rw [dist_comm]
      exact le_of_not_gt (fun hd => hξ (patch_graph_tube_mem_iff.mpr ⟨v, hv, hd⟩))
    rw [indicator_of_notMem hξ,
      localizedFourierKernel_eq_zero u hs hR z (patchGraphPoint φ v) ξ hdist, zero_mul]

theorem patch_graph_sparse_fourier_identity {d N : ℕ} {φ : Ambient d → ℝ}
    (u : SchwartzMap (Ambient (d + 1)) ℂ)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hu : ∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖)
    (hF : ∀ ξ, ‖angularFourier u ξ‖ ≤ 1)
    (hFs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → angularFourier u ξ = 0)
    (z : Fin N → Ambient (d + 1))
    (hd : Pairwise (fun i j => Disjoint (ball (z i) R) (ball (z j) R)))
    [IsFiniteMeasure (volume.restrict (patchGraphTube φ R⁻¹))]
    {f : Ambient (d + 1) → ℂ} (hfm : Measurable f) (hfi : Integrable f)
    (hfs : ∀ x, (∀ i, x ∉ ball (z i) R) → f x = 0)
    {v : Ambient d} (hv : v ∈ ball 0 1) :
    angularFourier f (patchGraphPoint φ v) = (((2 * Real.pi) ^ (d + 1))⁻¹ : ℝ) •
      integralKernel (Measure.count.prod (volume.restrict (patchGraphTube φ R⁻¹)))
        (indexedLocalizedKernel u R z)
        (fun p : Fin N × Ambient (d + 1) => angularFourier (sparsePiece u R (z p.1) f) p.2)
        (patchGraphPoint φ v) := by
  let ω := patchGraphPoint φ v
  let g (i : Fin N) := sparsePiece u R (z i) f
  let ν := volume.restrict (patchGraphTube φ R⁻¹)
  have hg (i : Fin N) : Integrable (g i) := integrable_sparsePiece u hc hR hu (z i) hfm hfi
  have hrecover (i : Fin N) : (fun x => g i (x - z i) * u (R⁻¹ • (x - z i))) =
      (ball (z i) R).indicator f := funext (sparsePiece_recover u hc hR hu (z i) f)
  calc
    _ = angularFourier (fun x => ∑ i, (ball (z i) R).indicator f x) ω := by
      congr 1
      funext x
      exact (sum_ball_indicators_eq z R hd f hfs x).symm
    _ = ∑ i, angularFourier ((ball (z i) R).indicator f) ω :=
      angularFourier_sum Finset.univ _ (fun i _ => hfi.indicator measurableSet_ball) ω
    _ = ∑ i, (((2 * Real.pi) ^ (d + 1))⁻¹ : ℝ) •
        ∫ ξ, localizedFourierKernel u R (z i) ω ξ * angularFourier (g i) ξ ∂ν := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hrecover i]
      exact tube_reconstruction (hg i) u hFs hR (z i) hv
    _ = (((2 * Real.pi) ^ (d + 1))⁻¹ : ℝ) •
        ∑ i, ∫ ξ, localizedFourierKernel u R (z i) ω ξ * angularFourier (g i) ξ ∂ν := by
      rw [Finset.smul_sum]
    _ = _ := by
      congr 1
      exact (integralKernel_finite_sum u hF hR z ν (integrable_finite_fourier g hg ν) ω).symm

end RestrictionWork
