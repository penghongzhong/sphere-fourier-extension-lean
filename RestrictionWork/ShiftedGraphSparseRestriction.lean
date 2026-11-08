import RestrictionWork.ShiftedGraphSparseIdentity
import RestrictionWork.ShiftedGraphThinRestriction
import RestrictionWork.ShiftedSphericalSparseOperator

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal BigOperators
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction
  (restrictionInputExponent restrictionInputExponent_bounds sparse_cutoff_exists sparse_balls_disjoint
    sparsePiece measurable_sparsePiece integrable_sparsePiece sparsePiece_support sparsePiece_Lp_sum_le
    integralKernel indexedLocalizedKernel integrable_finite_fourier measurable_finite_fourier
    eLpNorm_finite_family_bound)
namespace RestrictionWork

/-- Sparse-ball restriction at the critical exponent for the same graph measure
as the local bound, with uniform loss R^ε and no dependence on the number of balls. -/
theorem shifted_graph_sparse_restriction_indexed {d : ℕ} (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ (N : ℕ) (R : ℝ), 1 ≤ R →
        ∀ z : Fin N → Ambient (d + 1),
        (∀ i j, i ≠ j → R ^ (16 * (d + 1)) * (N : ℝ) ^ (16 * (d + 1)) ≤ dist (z i) (z j)) →
        ∀ f : Ambient (d + 1) → ℂ, Measurable f → Integrable f →
        (∀ x, (∀ i, x ∉ ball (z i) R) → f x = 0) →
        let p := ENNReal.ofReal (restrictionInputExponent (d + 1))
        eLpNorm (angularFourier f) p (patchGraphMeasure (shiftedSphericalGraphPhase δ a r)) ≤
          C * ENNReal.ofReal (R ^ ε) * eLpNorm f p volume := by
  have hn : 2 ≤ d + 1 := by omega
  let p := restrictionInputExponent (d + 1)
  obtain ⟨hp, hp2⟩ := restrictionInputExponent_bounds hn
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain ⟨u, c, hc, hu, hr, hF, hFs⟩ := sparse_cutoff_exists (d + 1)
  let V := volume (ball (0 : Ambient (d + 1)) 21)
  have hV : V ≠ ⊤ := measure_ball_lt_top.ne
  obtain ⟨A, hA, HA⟩ := shifted_spherical_sparse_integral_kernel_bound hd u hF hr hFs hp hp2 hV
  obtain ⟨B, hB, HB⟩ := shifted_graph_thin_restriction hd hε
  let t : ℝ := ((2 * Real.pi) ^ (d + 1))⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  let C := ENNReal.ofReal t * A * B * ENNReal.ofReal c⁻¹
  refine ⟨C, ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA) hB) ENNReal.ofReal_ne_top, ?_⟩
  intro δ r a hδ hδhalf ha hr0 hrhalf N R hR z hsep f hfm hfi hfs
  let φ := shiftedSphericalGraphPhase δ a r
  let μ := patchGraphMeasure φ
  let ν := volume.restrict (patchGraphTube φ R⁻¹)
  let g (i : Fin N) := sparsePiece u R (z i) f
  let G : Fin N × Ambient (d + 1) → ℂ := fun x => angularFourier (g x.1) x.2
  let T := integralKernel (Measure.count.prod ν) (indexedLocalizedKernel u R z) G
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hν : ν univ ≤ V := by
    rw [show ν = volume.restrict (patchGraphTube φ R⁻¹) by rfl, Measure.restrict_apply_univ]
    exact measure_mono (shifted_graph_tube_subset_ball hδ hδhalf ha hr0 hrhalf hRinv)
  let : IsFiniteMeasure ν := ⟨hν.trans_lt hV.lt_top⟩
  have hφ : Measurable φ := by
    unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hgi (i : Fin N) : Integrable (g i) := integrable_sparsePiece u hc hR0 hu (z i) hfm hfi
  have hGm : Measurable G := measurable_finite_fourier g hgi
  have hGi : Integrable G (Measure.count.prod ν) := integrable_finite_fourier g hgi ν
  have hdis := sparse_balls_disjoint hn hR z hsep
  have Hop := HA hδ hδhalf ha hr0 hrhalf N R hR z hsep ν inferInstance Measure.restrict_le_self
    hν G hGm hGi
  let D := B * ENNReal.ofReal R⁻¹ ^ (1 / p) * ENNReal.ofReal (R ^ ε)
  have Hnorm := eLpNorm_finite_family_bound ν hGm hp0
    (fun i => eLpNorm (g i) (ENNReal.ofReal p) volume) D
    (fun i => HB hδ hδhalf ha hr0 hrhalf R hR (g i) (measurable_sparsePiece u R (z i) hfm)
      (hgi i) (sparsePiece_support u R (z i) f) R⁻¹ (inv_pos.mpr hR0) hRinv)
  have Hin : eLpNorm G (ENNReal.ofReal p) (Measure.count.prod ν) ≤
      D * (ENNReal.ofReal c⁻¹ * eLpNorm f (ENNReal.ofReal p) volume) :=
    Hnorm.trans (mul_le_mul' le_rfl (sparsePiece_Lp_sum_le u hc hR0 hu z hdis hfm hp0))
  have heq : angularFourier f =ᵐ[μ] fun ω => t • T ω := by
    filter_upwards [ae_patch_graph_point hφ] with ω hω
    obtain ⟨v, hv, rfl⟩ := hω
    exact patch_graph_sparse_fourier_identity u hc hR0 hu hF hFs z hdis hfm hfi hfs hv
  have hscale : ENNReal.ofReal R ^ (1 / p) * ENNReal.ofReal R⁻¹ ^ (1 / p) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.ofReal_mul hR0.le,
      mul_inv_cancel₀ hR0.ne', ENNReal.ofReal_one, ENNReal.one_rpow]
  change eLpNorm (angularFourier f) (ENNReal.ofReal p) μ ≤ _
  rw [eLpNorm_congr_ae heq]
  change eLpNorm (t • T) (ENNReal.ofReal p) μ ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ ENNReal.ofReal t * (A * ENNReal.ofReal R ^ (1 / p) *
        eLpNorm G (ENNReal.ofReal p) (Measure.count.prod ν)) := mul_le_mul' le_rfl Hop
    _ ≤ ENNReal.ofReal t * (A * ENNReal.ofReal R ^ (1 / p) *
        (D * (ENNReal.ofReal c⁻¹ * eLpNorm f (ENNReal.ofReal p) volume))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl Hin)
    _ = (C * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal p) volume) *
        (ENNReal.ofReal R ^ (1 / p) * ENNReal.ofReal R⁻¹ ^ (1 / p)) := by dsimp [C, D]; ring
    _ = _ := by rw [hscale, mul_one]

end RestrictionWork
