import RestrictionWork.ShiftedSphericalTransverseRestricted

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RestrictionWork

private theorem support_energy_bound {d : ℕ} {A : Set (Ambient d)} (hA : MeasurableSet A)
    {f : Ambient d → ℂ} (hf : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) :
    (∫⁻ u, ‖f u‖ₑ ^ (2 : ℕ)) ≤ volume A := by
  calc
    _ ≤ ∫⁻ u, A.indicator (fun _ => (1 : ℝ≥0∞)) u := by
      apply lintegral_mono
      intro u
      by_cases hu : u ∈ A
      · rw [indicator_of_mem hu, ← one_pow (2 : ℕ)]
        apply pow_le_pow_left₀ zero_le
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by simpa only [indicator_of_mem hu] using hf u)
      · have he : f u = 0 := by
          apply norm_eq_zero.mp
          exact le_antisymm (by simpa only [indicator_of_notMem hu] using hf u) (norm_nonneg _)
        simp only [he, enorm_zero, zero_pow (by decide : 2 ≠ 0), indicator_of_notMem hu, le_refl]
    _ = _ := by rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ, one_mul]

private theorem support_memLp_two {d : ℕ} {A : Set (Ambient d)} (hA : MeasurableSet A)
    (hAv : volume A < ⊤) {f : Ambient d → ℂ} (hf : Measurable f)
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) : MemLp f 2 := by
  have hm := memLp_indicator_const (μ := (volume : Measure (Ambient d)))
    2 hA (1 : ℝ) (Or.inr hAv.ne)
  apply lt_of_le_of_lt _ hm.eLpNorm_lt_top
  refine eLpNorm_mono_ae hf.aestronglyMeasurable (.of_forall fun u => ?_)
  exact (hfb u).trans (le_abs_self _)

set_option maxHeartbeats 650000 in
/-- The separated indicator bounds give a symmetric restricted estimate
strictly above the Knapp line, uniformly over the normalized spherical family. -/
theorem shifted_graph_transverse_knapp_gain {d : ℕ} (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ 2 * (d : ℝ) / ((d : ℝ) + 2) * (1 - x) < 1 / 2 ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
          0 < r → r ≤ 1 / 2 → ∀ {A B : Set (Ambient d)}, MeasurableSet A → MeasurableSet B →
          A ⊆ Metric.ball (0 : Ambient d) 1 → B ⊆ Metric.ball (0 : Ambient d) 1 →
          (∀ u ∈ A, ∀ v ∈ B, σ ≤ ‖v - u‖) →
          ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g →
            (∀ u, ‖f u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
            (∀ v, ‖g v‖ ≤ B.indicator (fun _ => (1 : ℝ)) v) →
            let φ := shiftedSphericalGraphPhase δ a r
            eLpNorm (graphExtension f φ * graphExtension g φ) 2 volume ≤
              C * (volume A * volume B) ^ x := by
  let q : ℝ := (d : ℝ) + 1 / 2
  let k : ℝ := 2 * (1 - 1 / q)
  let x := (1 + k) * (1 / 4)
  have hd₂ : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hqd : q < (d : ℝ) + 1 := by dsimp [q]; linarith
  have hq0 : 0 < q := by linarith
  have hk : 0 ≤ k := by
    have H : 1 / q ≤ 1 := (div_le_iff₀ hq0).mpr (by linarith)
    dsimp [k]
    linarith
  have hx : x = 3 / 4 - 1 / (2 * q) := by
    dsimp only [x, k]
    field_simp
    ring
  have hgap : 1 / 2 - 2 * (d : ℝ) / ((d : ℝ) + 2) * (1 - x) =
      (q - (d : ℝ)) / (q * ((d : ℝ) + 2)) := by
    rw [hx]
    field_simp [hq0.ne', show (d : ℝ) + 2 ≠ 0 by positivity]
    ring
  have hgap' : 2 * (d : ℝ) / ((d : ℝ) + 2) * (1 - x) < 1 / 2 := by
    apply sub_pos.mp
    rw [hgap]
    exact div_pos (by dsimp [q]; linarith) (by positivity)
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x < 1 := by rw [hx]; linarith [show 0 < 1 / (2 * q) by positivity]
  obtain ⟨C, hC, H⟩ := shifted_graph_transverse_restricted_two (by omega : 1 ≤ d) hq hqd hσ
  refine ⟨x, hx0, hx1, hgap', C ^ (1 / 2 : ℝ),
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf A B hA hB hAb hBb hsep f g hf hg hfb hgb φ
  have hAvol : volume A < ⊤ := (measure_mono hAb).trans_lt measure_ball_lt_top
  have hBvol : volume B < ⊤ := (measure_mono hBb).trans_lt measure_ball_lt_top
  have hf₂ := support_memLp_two hA hAvol hf hfb
  have hg₂ := support_memLp_two hB hBvol hg hgb
  have hfs : ∀ u ∉ A, f u = 0 := fun u hu => norm_eq_zero.mp
    (le_antisymm (by simpa only [indicator_of_notMem hu] using hfb u) (norm_nonneg _))
  have hgs : ∀ u ∉ B, g u = 0 := fun u hu => norm_eq_zero.mp
    (le_antisymm (by simpa only [indicator_of_notMem hu] using hgb u) (norm_nonneg _))
  have hsep' : ∀ v ∈ B, ∀ u ∈ A, σ ≤ ‖u - v‖ := fun v hv u hu => by
    rw [norm_sub_rev]
    exact hsep u hu v hv
  let F := graphExtension f φ * graphExtension g φ
  let I := ∫⁻ p : Ambient d × ℝ, ‖F p‖ₑ ^ (2 : ℕ)
  have ha' : I ≤ C * volume A * (volume B) ^ k :=
    (H hδ hδhalf ha hr hrhalf hA hB hAb hBb hsep hf hg hf₂ hfs hgb).trans
      (mul_le_mul' (mul_le_mul' le_rfl (support_energy_bound hA hfb)) le_rfl)
  have hb' : I ≤ C * volume B * (volume A) ^ k := by
    have H' := H hδ hδhalf ha hr hrhalf hB hA hBb hAb hsep' hg hf hg₂ hgs hfb
    change (∫⁻ p : Ambient d × ℝ, ‖graphExtension g φ p * graphExtension f φ p‖ₑ ^ (2 : ℕ)) ≤ _ at H'
    have he : (fun p : Ambient d × ℝ => ‖graphExtension g φ p * graphExtension f φ p‖ₑ ^ (2 : ℕ)) =
        (fun p : Ambient d × ℝ => ‖graphExtension f φ p * graphExtension g φ p‖ₑ ^ (2 : ℕ)) := by
      funext p
      rw [mul_comm]
    rw [he] at H'
    exact H'.trans (mul_le_mul' (mul_le_mul' le_rfl (support_energy_bound hB hgb)) le_rfl)
  let : IsFiniteMeasure ((volume : Measure (Ambient d)).restrict (Metric.ball 0 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hφ : Measurable φ := by
    unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hfm : Measurable F := ((graph_extension_continuous
    ((hf₂.restrict (Metric.ball (0 : Ambient d) 1)).integrable (by norm_num)) hφ).mul
    (graph_extension_continuous
      ((hg₂.restrict (Metric.ball (0 : Ambient d) 1)).integrable (by norm_num)) hφ)).measurable
  have hmass :
      (C * volume A * (volume B) ^ k) * (C * volume B * (volume A) ^ k) =
        C ^ (2 : ℕ) * ((volume A * volume B) ^ (1 + k)) := by
    rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one hk, ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hk, pow_two]
    ac_rfl
  change eLpNorm F 2 volume ≤ _
  calc
    _ = (I * I) ^ (1 / 4 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfm.aestronglyMeasurable,
        ENNReal.toReal_ofNat]
      simp_rw [ENNReal.rpow_two]
      change I ^ (1 / 2 : ℝ) = (I * I) ^ (1 / 4 : ℝ)
      rw [← pow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ ((C * volume A * (volume B) ^ k) * (C * volume B * (volume A) ^ k)) ^
        (1 / 4 : ℝ) := ENNReal.rpow_le_rpow (mul_le_mul' ha' hb') (by norm_num)
    _ = _ := by
      rw [hmass, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ← ENNReal.rpow_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num [x]

end RestrictionWork
