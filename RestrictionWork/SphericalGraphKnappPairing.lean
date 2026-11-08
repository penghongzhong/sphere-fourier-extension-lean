import RestrictionWork.GraphKnappUnitPairing
import RestrictionWork.KnappAtomPairing
import RestrictionWork.RestrictedStrongNeighborhood
import RestrictionWork.DyadicExponentialKernel

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

private theorem ofReal_two_zpow_rpow (j : ℤ) (p : ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ j) ^ p = (2 : ℝ≥0∞) ^ (p * (j : ℝ)) := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : 0 < (2 : ℝ) ^ j),
    ← Real.rpow_intCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (j : ℝ) p,
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

set_option maxHeartbeats 1200000 in
/-- The spherical graph pairing on the input and dual unit balls at the
exact Knapp exponents. Neighboring restricted estimates control opposite
sides of the amplitude matrix. -/
theorem spherical_graph_knapp_unit_pairing {d : ℕ} (hd : 2 ≤ d) {y : ℝ}
    (hy : 0 < y) (hyD : y < (d : ℝ) / ((d : ℝ) + 1)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
      ∀ {f : Ambient d → ℂ}, Measurable f → Integrable f (patchMeasure d) →
      (∀ u ∉ Metric.ball (0 : Ambient d) (1 / 4), f u = 0) →
      eLpNorm f (ENNReal.ofReal (knappProductInput d y)⁻¹) (patchMeasure d) ≤ 1 →
      ∀ {g : Ambient d × ℝ → ℂ}, Measurable g → Integrable g →
      eLpNorm g (ENNReal.ofReal ((1 - y / 2)⁻¹)) volume ≤ 1 →
      ‖∫ z, g z * graphExtension f (sphericalGraphPhase δ) z‖ₑ ≤ C := by
  let p := (knappProductInput d y)⁻¹
  let s : ℝ := (1 - y / 2)⁻¹
  let a : ℝ := ((d : ℝ) + 2) / d
  have hy₁ : y < 1 := hyD.trans ((div_lt_one (by positivity)).mpr (by linarith))
  have hx : 0 < knappProductInput d y :=
    (by
      rw [knapp_input_sub_diagonal (by omega : 0 < d) y]
      positivity : 0 < knappProductInput d y - y / 2).trans_le (by linarith)
  have hs₀ : 0 < 1 - y / 2 := by linarith
  have hp : 0 < p := inv_pos.mpr hx
  have hs : 0 < s := inv_pos.mpr hs₀
  have ha : 0 < a := by unfold a; positivity
  obtain ⟨ε, b, hε, hl, hh, hb, hb₁, hbl, hbh, hxl, hxh⟩ :=
    exists_restricted_strong_nearby hd hy hyD
  let c := ε / 2
  have hc : 0 < c := by unfold c; positivity
  obtain ⟨C, hC, H⟩ := spherical_graph_knapp_atom_pairing_le hd (y := y) hl
    (by linarith : y - ε < y) (by linarith : y < y + ε) hh
    (inv_mul_cancel₀ hx.ne') (inv_mul_cancel₀ hs₀.ne')
    hb.le hb₁.le hxl hxh (by linarith) (by linarith)
    (show c ≤ y / 2 - (y - ε) / 2 by unfold c; linarith)
    (show c ≤ (y + ε) / 2 - y / 2 by unfold c; linarith)
  obtain ⟨L, hL, HL⟩ := dyadic_exponential_kernel_sum_le (mul_pos ha hp) hc
  obtain ⟨R, hR, HR⟩ := dyadic_exponential_kernel_sum_le hs hc
  let D := max L R
  let K (i j : ℤ) : ℝ≥0∞ :=
    ENNReal.ofReal ((2 : ℝ) ^ (-c * |a * p * (i : ℝ) + s * (j : ℝ)|))
  have hrow (i : ℤ) (J : Finset ℤ) : ∑ j ∈ J, K i j ≤ D := by
    apply le_trans _ (le_max_right L R)
    simpa only [K, add_comm] using HR (a * p * (i : ℝ)) J
  have hcol (j : ℤ) (I : Finset ℤ) : ∑ i ∈ I, K i j ≤ D :=
    (HL (s * (j : ℝ)) I).trans (le_max_left L R)
  refine ⟨C * D, ENNReal.mul_lt_top hC (max_lt hL hR), ?_⟩
  intro δ hδ hδ₁ f hf hfi hfs hfN g hg hgi hgN
  let φ := sphericalGraphPhase δ (d := d)
  have hφ : Measurable φ := by unfold φ sphericalGraphPhase sphericalPhase; fun_prop
  apply graph_knapp_unit_pairing_from_atoms hp hs hb hb₁ hφ hf hfi hfs hg hgi hfN hgN K hrow hcol
  intro i j A B α β hα hβ
  have hα' : (2 : ℝ≥0∞) ^ (p * (i : ℝ)) * volume A ≤ 1 := by
    simpa only [α, ofReal_two_zpow_rpow] using hα
  have hβ' : (2 : ℝ≥0∞) ^ (s * (j : ℝ)) * volume B ≤ 1 := by
    simpa only [β, ofReal_two_zpow_rpow] using hβ
  have H' := H hδ hδ₁ i j (measurableSet_dyadic_amplitude_set measurableSet_ball hf i)
    (inter_subset_left : A ⊆ Metric.ball 0 (1 / 4))
    (measurableSet_dyadic_amplitude_set MeasurableSet.univ hg j)
    (f := dyadicAmplitudePiece (Metric.ball 0 (1 / 4)) f i)
    (g := dyadicAmplitudePiece univ g j)
    (measurable_dyadic_amplitude_piece measurableSet_ball hf i)
    (measurable_dyadic_amplitude_piece MeasurableSet.univ hg j)
    (fun u => by simpa only [← Real.rpow_intCast (2 : ℝ) (i + 1), Int.cast_add, Int.cast_one] using
      norm_dyadic_amplitude_piece_le (Metric.ball 0 (1 / 4)) f i u)
    (fun z => by simpa only [← Real.rpow_intCast (2 : ℝ) (j + 1), Int.cast_add, Int.cast_one] using
      norm_dyadic_amplitude_piece_le univ g j z)
    hα' hβ'
  simpa only [K, a, α, β, ofReal_two_zpow_rpow, mul_assoc, mul_left_comm, mul_comm] using H'

end RestrictionWork
