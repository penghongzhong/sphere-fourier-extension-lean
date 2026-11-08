import RestrictionWork.GraphRebaseNormTransfer
import RestrictionWork.UniformCriticalCapBound

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RestrictionWork

/-- A translated spherical subcap has the critical estimate with a scale loss
`r ^ (-2 * η)` prior to comparing scales. The parent scale `δ` is uniform. -/
theorem shifted_spherical_local_bound {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ≥0, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ a : Ambient d, ‖a‖ ≤ 1 / 2 →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ R : ℝ, 1 ≤ R →
      ∀ g : Ambient d → ℂ, MemLp g (capCriticalExponent d) (patchMeasure d) →
      MemLp (graphExtension g (shiftedSphericalGraphPhase δ a r)) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ∧
      eLpNorm (graphExtension g (shiftedSphericalGraphPhase δ a r)) (capCriticalExponent d)
        (volume.restrict (Metric.ball 0 R)) ≤
      (A : ℝ≥0∞) * ENNReal.ofReal (R ^ η * r ^ (-2 * η)) *
        eLpNorm g (capCriticalExponent d) (patchMeasure d) := by
  let p := capCriticalExponent d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpc : 0 < 2 * ((d : ℝ) + 1) / (d : ℝ) := by positivity
  have hp : 1 ≤ p := by
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ hd0).mpr
    linarith
  have hpinv : p.toReal⁻¹ = (d : ℝ) / (2 * ((d : ℝ) + 1)) := by
    rw [show p = capCriticalExponent d by rfl, capCriticalExponent,
      ENNReal.toReal_ofReal hpc.le, inv_div]
  obtain ⟨C, HC⟩ := uniform_critical_cap_bound hd hη
  let A : ℝ≥0∞ := (C : ℝ≥0∞) * ENNReal.ofReal ((5 : ℝ) ^ η)
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  refine ⟨A.toNNReal, ?_⟩
  intro δ hδ hδhalf a ha r hr hrhalf R hR g hg
  have hR0 : 0 < R := by linarith
  have hrone : r ≤ 1 := by linarith
  let T := Metric.ball (0 : Ambient d × ℝ) R
  let φ := sphericalGraphPhase (d := d) δ
  let l := sphericalGraphSlope δ a
  let F := graphExtension (graphRebaseInput a r g) φ
  let G := graphExtension g (shiftedSphericalGraphPhase δ a r)
  let L := 5 * R / r ^ 2
  let c := ENNReal.ofReal (r ^ d)
  let J := ENNReal.ofReal (r ^ (d + 2))
  have hφ : Measurable φ := by unfold φ sphericalGraphPhase sphericalPhase; fun_prop
  have hL : 1 ≤ L := by
    apply (le_div_iff₀ (pow_pos hr _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrone hr.le]
  have hsub := graph_physical_ball_image hr hrone (spherical_graph_slope_norm hδ hδhalf ha) hR0
  obtain ⟨hinput, hinputnorm⟩ := graph_rebase_input_norm hr ha hrhalf hg
  have houtput := (HC δ hδ hδhalf L hL (graphRebaseInput a r g) hinput).2
  change eLpNorm F p (volume.restrict (Metric.ball 0 L)) ≤ _ at houtput
  have H : c * eLpNorm G p (volume.restrict T) =
      J ^ p.toReal⁻¹ * eLpNorm F p (volume.restrict (graphPhysicalMap l r '' T)) :=
    graph_rebase_norm_transfer hφ hr ha hrhalf hp hg p T
  have hJc : J ^ p.toReal⁻¹ * c ^ p.toReal⁻¹ = c := by
    dsimp only [J, c]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.ofReal_mul (pow_pos hr _).le,
      ← pow_add, ENNReal.ofReal_rpow_of_nonneg (pow_pos hr _).le (by positivity)]
    congr 1
    rw [hpinv, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
    ring
  have hscale : L ^ η = (5 : ℝ) ^ η * (R ^ η * r ^ (-2 * η)) := by
    dsimp only [L]
    rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hR0.le]
    have he : (r ^ (2 : ℕ)) ^ η = r ^ (2 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num
    rw [he, show -2 * η = -(2 * η) by ring, Real.rpow_neg hr.le]
    ring
  rw [hinputnorm] at houtput
  have Hcancel : c * eLpNorm G p (volume.restrict T) ≤
      c * (A * ENNReal.ofReal (R ^ η * r ^ (-2 * η)) *
        eLpNorm g p (patchMeasure d)) := by
    calc
      _ = _ := H
      _ ≤ J ^ p.toReal⁻¹ * eLpNorm F p (volume.restrict (Metric.ball 0 L)) :=
        mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
      _ ≤ J ^ p.toReal⁻¹ * ((C : ℝ≥0∞) * ENNReal.ofReal (L ^ η) *
          (c ^ p.toReal⁻¹ * eLpNorm g p (patchMeasure d))) :=
        mul_le_mul' le_rfl houtput
      _ = (J ^ p.toReal⁻¹ * c ^ p.toReal⁻¹) *
          ((C : ℝ≥0∞) * ENNReal.ofReal (L ^ η) * eLpNorm g p (patchMeasure d)) := by ring
      _ = _ := by
        rw [hJc, hscale, ENNReal.ofReal_mul (by positivity)]
        unfold A
        ring
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have hc_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have Hfinal : eLpNorm G p (volume.restrict T) ≤
      A * ENNReal.ofReal (R ^ η * r ^ (-2 * η)) * eLpNorm g p (patchMeasure d) := by
    have H' := mul_le_mul' (le_refl c⁻¹) Hcancel
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc hc_top, one_mul] using H'
  rw [ENNReal.coe_toNNReal hA]
  exact ⟨Hfinal.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top).lt_top hg), Hfinal⟩

end RestrictionWork
