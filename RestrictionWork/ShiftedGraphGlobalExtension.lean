import RestrictionWork.ShiftedGraphEpsilonRemoval

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open OAI.Analysis.Fourier.Restriction (restrictionInputExponent)
namespace RestrictionWork

/-- The original graph integral has the uniform lossless global diagonal
extension bound for every finite exponent above the radial threshold. -/
theorem shifted_graph_global_extension {d : ℕ} (hd : 1 ≤ d)
    {p : ℝ} (hp : 2 * ((d : ℝ) + 1) / d < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ g : Ambient d → ℂ, MemLp g (ENNReal.ofReal p) (patchMeasure d) →
        MemLp (graphExtension g (shiftedSphericalGraphPhase δ a r)) (ENNReal.ofReal p) volume ∧
        eLpNorm (graphExtension g (shiftedSphericalGraphPhase δ a r)) (ENNReal.ofReal p) volume ≤
          C * eLpNorm g (ENNReal.ofReal p) (patchMeasure d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hp' : 2 * ((d : ℝ) + 1) < p * d := (div_lt_iff₀ hd0).mp hp
  have hp1 : 1 < p := by
    have h := (le_div_iff₀ hd0).mpr (by linarith : 1 * (d : ℝ) ≤ 2 * ((d : ℝ) + 1))
    exact h.trans_lt hp
  have hpos : 0 < p - 1 := sub_pos.mpr hp1
  have hq : 1 ≤ p / (p - 1) := (le_div_iff₀ hpos).mpr (by linarith)
  have hqpc : p / (p - 1) < restrictionInputExponent (d + 1) := by
    unfold restrictionInputExponent
    push_cast
    apply (div_lt_div_iff₀ hpos (by positivity)).mpr
    nlinarith only [hp']
  obtain ⟨C, hC, HC⟩ := shifted_graph_global_restriction hd hq hqpc
  refine ⟨C, hC, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf g hg
  have hφ : Measurable (shiftedSphericalGraphPhase δ a r) := by
    unfold shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  exact patch_graph_extension_of_restriction hp1 hφ hC (HC hδ hδhalf ha hr hrhalf) hg

/-- The lossless diagonal bilinear bound on the same graph, before using
any separation of the parameter supports. -/
theorem shifted_graph_global_diagonal_product {d : ℕ} (hd : 1 ≤ d)
    {p : ℝ} (hp : 2 * ((d : ℝ) + 1) / d < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ g h : Ambient d → ℂ,
        MemLp g (ENNReal.ofReal p) (patchMeasure d) → MemLp h (ENNReal.ofReal p) (patchMeasure d) →
        let φ := shiftedSphericalGraphPhase δ a r
        let P := ENNReal.ofReal p
        let Q := (P⁻¹ + P⁻¹)⁻¹
        MemLp (graphExtension g φ * graphExtension h φ) Q volume ∧
        eLpNorm (graphExtension g φ * graphExtension h φ) Q volume ≤
          C * eLpNorm g P (patchMeasure d) * eLpNorm h P (patchMeasure d) := by
  obtain ⟨A, hA, HA⟩ := shifted_graph_global_extension hd hp
  refine ⟨A * A, ENNReal.mul_ne_top hA hA, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf g h hg hh φ P Q
  obtain ⟨hG, HG⟩ := HA hδ hδhalf ha hr hrhalf g hg
  obtain ⟨hH, HH⟩ := HA hδ hδhalf ha hr hrhalf h hh
  have : ENNReal.HolderTriple P P Q := ENNReal.HolderTriple.of P P
  refine ⟨hG.mul hH, ?_⟩
  calc
    _ ≤ eLpNorm (graphExtension g φ) P volume * eLpNorm (graphExtension h φ) P volume :=
      eLpNorm_smul_le_mul_eLpNorm hG.aestronglyMeasurable hH.aestronglyMeasurable
    _ ≤ (A * eLpNorm g P (patchMeasure d)) * (A * eLpNorm h P (patchMeasure d)) :=
      mul_le_mul' HG HH
    _ = _ := by ring

end RestrictionWork
