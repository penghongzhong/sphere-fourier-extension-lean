import RestrictionWork.GraphGaussianProductEnergy
import RestrictionWork.ShiftedSphericalGaussianRow
import RestrictionWork.GraphExtensionContinuous

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RestrictionWork

private abbrev CollisionTriple (d : ℕ) := Ambient d × (Ambient d × Ambient d)

private def collisionSwap {d : ℕ} (p : CollisionTriple d) : CollisionTriple d :=
  (p.1 + p.2.1 - p.2.2, p.2.2, p.2.1)

private theorem measurePreserving_collisionSwap (d : ℕ) :
    let μ : Measure (Ambient d) := volume
    MeasurePreserving (@collisionSwap d) (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) := by
  intro μ
  have hswap : MeasurePreserving (@Prod.swap (Ambient d) (Ambient d)) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap
  have hadd : Measurable (fun p : (Ambient d × Ambient d) × Ambient d => p.2 + p.1.1 - p.1.2) := by
    fun_prop
  have h := hswap.skew_product (g := fun p u => u + p.1 - p.2) hadd
    (.of_forall fun p => by
      simpa only [add_sub_assoc] using (measurePreserving_add_right μ (p.1 - p.2)).map_eq)
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

private theorem enorm_mul_le_half_sum (a b : ℂ) :
    ‖a‖ₑ * ‖b‖ₑ ≤ (2 : ℝ≥0∞)⁻¹ * (‖a‖ₑ ^ (2 : ℕ) + ‖b‖ₑ ^ (2 : ℕ)) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

private theorem lintegral_gaussian_limit {F : ℝ → ℝ≥0∞} (hF : Measurable F) {C : ℝ≥0∞}
    (hC : ∀ h : ℝ, 0 < h → (∫⁻ t, ‖radonGaussianSymbol h t‖ₑ * F t) ≤ C) :
    (∫⁻ t, F t) ≤ C := by
  let h := fun n : ℕ => ((n : ℝ) + 1)⁻¹
  let E := fun n t => ‖radonGaussianSymbol (h n) t‖ₑ * F t
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hE (n : ℕ) : Measurable (E n) := ((radon_gaussian_symbol_measurable (h n)).enorm).mul hF
  have hh0 : Tendsto h atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hnat
  have hlim (t : ℝ) : Tendsto (fun n => E n t) atTop (𝓝 (F t)) := by
    have hc : Continuous (fun h : ℝ => ‖radonGaussianSymbol h t‖ₑ) := by
      unfold radonGaussianSymbol
      fun_prop
    have H := hc.continuousAt.tendsto.comp hh0
    have hzero : ‖radonGaussianSymbol 0 t‖ₑ = 1 := by simp [radonGaussianSymbol]
    rw [hzero] at H
    simpa only [E, Function.comp_apply, one_mul] using ENNReal.Tendsto.mul_const (b := F t) H (Or.inl one_ne_zero)
  calc
    _ = ∫⁻ t, liminf (fun n => E n t) atTop :=
      lintegral_congr fun t => (hlim t).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ t, E n t) atTop := lintegral_liminf_le hE
    _ ≤ C := by
      rw [liminf_eq_iSup_iInf_of_nat]
      exact iSup_le fun n => iInf_le_of_le n (iInf_le_of_le le_rfl (hC (h n) (hh n)))

set_option maxHeartbeats 1000000 in
/-- A width-free transverse L² estimate for the true shifted spherical
extension product. One input is arbitrary L² and the other is dominated
by a support indicator. -/
theorem shifted_graph_transverse_restricted_two {d : ℕ} (hd : 1 ≤ d)
    {q σ : ℝ} (hq : 2 ≤ q) (hqd : q < (d : ℝ) + 1) (hσ : 0 < σ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {δ r : ℝ} {a : Ambient d}, 0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 →
        0 < r → r ≤ 1 / 2 → ∀ {A B : Set (Ambient d)}, MeasurableSet A → MeasurableSet B →
        A ⊆ Metric.ball (0 : Ambient d) 1 → B ⊆ Metric.ball (0 : Ambient d) 1 →
        (∀ u ∈ A, ∀ v ∈ B, σ ≤ ‖v - u‖) →
        ∀ {f g : Ambient d → ℂ}, Measurable f → Measurable g → MemLp f 2 volume →
          (∀ u ∉ A, f u = 0) → (∀ v, ‖g v‖ ≤ B.indicator (fun _ => (1 : ℝ)) v) →
          let φ := shiftedSphericalGraphPhase δ a r
          (∫⁻ p : Ambient d × ℝ, ‖graphExtension f φ p * graphExtension g φ p‖ₑ ^ (2 : ℕ)) ≤
            C * (∫⁻ u, ‖f u‖ₑ ^ (2 : ℕ)) * (volume B) ^ (2 * (1 - 1 / q)) := by
  classical
  obtain ⟨C₀, hC₀, hrow⟩ := shifted_collision_gaussian_row_bound hd hq hqd hσ
  let C₁ := ENNReal.ofReal ((2 * Real.pi) ^ d)
  refine ⟨C₁ * C₀, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC₀, ?_⟩
  intro δ r a hδ hδhalf ha hr hrhalf A B hA hB hAb hBb hsep f g hf hg hf₂ hfA hgB φ
  let μ : Measure (Ambient d) := volume
  let ν := μ.prod (μ.prod μ)
  let M := (volume B) ^ (1 - 1 / q)
  have hq0 : 0 < q := by linarith
  have hq' : 0 ≤ 1 - 1 / q := sub_nonneg.mpr ((div_le_iff₀ hq0).mpr (by linarith))
  have hAvol : volume A < ⊤ := (measure_mono hAb).trans_lt measure_ball_lt_top
  have hBvol : volume B < ⊤ := (measure_mono hBb).trans_lt measure_ball_lt_top
  have hφ : Measurable φ := by
    unfold φ shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hg₀ (u : Ambient d) (hu : u ∉ B) : g u = 0 := by
    apply norm_eq_zero.mp
    have H := hgB u
    rw [indicator_of_notMem hu] at H
    exact le_antisymm H (norm_nonneg _)
  have hg₁ (u : Ambient d) : ‖g u‖ ≤ 1 := by
    by_cases hu : u ∈ B
    · simpa only [indicator_of_mem hu] using hgB u
    · rw [hg₀ u hu, norm_zero]
      exact zero_le_one
  have hfi : Integrable f := by
    let : IsFiniteMeasure (μ.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
    have hi : IntegrableOn f A := (hf₂.restrict A).integrable (by norm_num)
    refine ((integrable_indicator_iff hA).mpr hi).congr (.of_forall fun u => ?_)
    by_cases hu : u ∈ A
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hfA u hu]
  have hgi : Integrable g := by
    have hi : Integrable (B.indicator (fun _ : Ambient d => (1 : ℝ))) :=
      (integrable_indicator_iff hB).mpr (integrableOn_const (C := (1 : ℝ)) hBvol.ne)
    refine hi.mono' hg.aestronglyMeasurable (.of_forall fun u => ?_)
    exact hgB u
  have hfs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, f u = 0 :=
    fun u hu => hfA u (fun h => hu (hAb h))
  have hgs : ∀ u ∉ Metric.ball (0 : Ambient d) 1, g u = 0 :=
    fun u hu => hg₀ u (fun h => hu (hBb h))
  let F := fun p : Ambient d × ℝ => graphExtension f φ p * graphExtension g φ p
  have hFm : Measurable F := ((graph_extension_continuous hfi.restrict hφ).mul
    (graph_extension_continuous hgi.restrict hφ)).measurable
  let W := fun t : ℝ => ∫⁻ x : Ambient d, ‖F (x, t)‖ₑ ^ (2 : ℕ)
  have hW : Measurable W := (hFm.enorm.pow_const (2 : ℕ)).lintegral_prod_left'
  change (∫⁻ p : Ambient d × ℝ, ‖F p‖ₑ ^ (2 : ℕ) ∂μ.prod (volume : Measure ℝ)) ≤ _
  rw [lintegral_prod_symm _ (hFm.enorm.pow_const (2 : ℕ)).aemeasurable]
  change (∫⁻ t, W t) ≤ _
  apply lintegral_gaussian_limit hW
  intro h hh
  let z := fun p : CollisionTriple d => p.1 + p.2.1 - p.2.2
  let E : Set (CollisionTriple d) := {p | p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2 ∈ B ∧ z p ∈ A}
  let K := fun p : CollisionTriple d => ENNReal.ofReal (radonGaussianKernel h
    ((φ p.1 + φ p.2.1 - φ p.2.2 - φ (z p)) / (2 * Real.pi)))
  let T := E.indicator K
  let U := fun p : CollisionTriple d => ‖f p.1‖ₑ ^ (2 : ℕ) * T p
  let V := fun p : CollisionTriple d => ‖f (z p)‖ₑ ^ (2 : ℕ) * T p
  let Q := fun p : CollisionTriple d => ‖f p.1‖ₑ * ‖g p.2.1‖ₑ *
    (‖f (z p)‖ₑ * ‖g p.2.2‖ₑ) * K p
  have hz : Measurable z := by unfold z; fun_prop
  have hE : MeasurableSet E := (hA.preimage measurable_fst).inter
    ((hB.preimage (measurable_fst.comp measurable_snd)).inter
      ((hB.preimage (measurable_snd.comp measurable_snd)).inter (hA.preimage hz)))
  have hK : Measurable K := by unfold K radonGaussianKernel; fun_prop
  have hT : Measurable T := hK.indicator hE
  have hU : Measurable U := (hf.enorm.comp measurable_fst |>.pow_const (2 : ℕ)).mul hT
  have hV : Measurable V := (hf.enorm.comp hz |>.pow_const (2 : ℕ)).mul hT
  have hQ : Measurable Q := by unfold Q; fun_prop
  have hsym (p : CollisionTriple d) : T (collisionSwap p) = T p := by
    have hz' : z (collisionSwap p) = p.1 := by simp only [z, collisionSwap]; abel
    have hmem : collisionSwap p ∈ E ↔ p ∈ E := by
      change (z p ∈ A ∧ p.2.2 ∈ B ∧ p.2.1 ∈ B ∧ z (collisionSwap p) ∈ A) ↔
        (p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2 ∈ B ∧ z p ∈ A)
      rw [hz']
      tauto
    dsimp only [T]
    by_cases hp : p ∈ E
    · rw [indicator_of_mem (hmem.mpr hp), indicator_of_mem hp]
      have he : φ (z p) + φ p.2.2 - φ p.2.1 - φ p.1 =
          -(φ p.1 + φ p.2.1 - φ p.2.2 - φ (z p)) := by ring
      change ENNReal.ofReal (radonGaussianKernel h
        ((φ (z p) + φ p.2.2 - φ p.2.1 - φ (z (collisionSwap p))) / (2 * Real.pi))) = K p
      rw [hz', he, neg_div, radonGaussianKernel, neg_div, neg_sq]
      rfl
    · rw [indicator_of_notMem (fun hp' => hp (hmem.mp hp')), indicator_of_notMem hp]
  have hVeq : (∫⁻ p, V p ∂ν) = ∫⁻ p, U p ∂ν := by
    have he : V = U ∘ collisionSwap := by
      funext p
      change ‖f (z p)‖ₑ ^ (2 : ℕ) * T p = ‖f (z p)‖ₑ ^ (2 : ℕ) * T (collisionSwap p)
      rw [hsym]
    rw [he]
    exact (measurePreserving_collisionSwap d).lintegral_comp hU
  have hpoint (p : CollisionTriple d) : Q p ≤ (2 : ℝ≥0∞)⁻¹ * (U p + V p) := by
    by_cases hp : p ∈ E
    · have hg₂ (v : Ambient d) : ‖g v‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hg₁ v)
      have hQ' : Q p ≤ (‖f p.1‖ₑ * ‖f (z p)‖ₑ) * K p := by
        unfold Q
        simpa only [mul_one] using mul_le_mul' (mul_le_mul'
          (mul_le_mul' le_rfl (hg₂ p.2.1)) (mul_le_mul' le_rfl (hg₂ p.2.2))) (le_refl (K p))
      refine hQ'.trans ((mul_le_mul' (enorm_mul_le_half_sum (f p.1) (f (z p))) le_rfl).trans_eq ?_)
      unfold U V T
      rw [indicator_of_mem hp, mul_assoc, add_mul]
    · have hzero : Q p = 0 := by
        by_cases hu : p.1 ∈ A
        · by_cases hy : p.2.1 ∈ B
          · by_cases hw : p.2.2 ∈ B
            · have hzA : z p ∉ A := fun H => hp ⟨hu, hy, hw, H⟩
              simp only [Q, hfA _ hzA, enorm_zero, zero_mul, mul_zero]
            · simp only [Q, hg₀ _ hw, enorm_zero, mul_zero, zero_mul]
          · simp only [Q, hg₀ _ hy, enorm_zero, mul_zero, zero_mul]
        · simp only [Q, hfA _ hu, enorm_zero, zero_mul]
      rw [hzero]
      exact zero_le
  have hrowT (u : Ambient d) : (∫⁻ p : Ambient d × Ambient d, T (u, p) ∂μ.prod μ) ≤ C₀ * (M * M) := by
    by_cases hu : u ∈ A
    · have hu₁ : ‖u‖ ≤ 1 := (by
          simpa only [Metric.mem_ball, dist_zero_right] using hAb hu : ‖u‖ < 1).le
      have hBD : B ⊆ {v | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖} := fun v hv =>
        ⟨(by simpa only [Metric.mem_ball, dist_zero_right] using hBb hv : ‖v‖ < 1).le,
          hsep u hu v hv⟩
      have H := hrow (u := u) hδ hδhalf ha hr hrhalf hu₁ hh hB hB hBD hBD
      refine (le_trans ?_ (H.trans_eq (by dsimp [M]; ac_rfl)))
      have hm : Measurable (fun p : Ambient d × Ambient d => T (u, p)) :=
        hT.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_prod _ hm.aemeasurable, ← lintegral_indicator hB]
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ B
      · rw [indicator_of_mem hy]
        have hZ : MeasurableSet {w : Ambient d | ‖u + y - w‖ ≤ 1} :=
          measurableSet_le (by fun_prop) measurable_const
        rw [← lintegral_indicator (hB.inter hZ)]
        apply lintegral_mono
        intro w
        by_cases hp : (u, y, w) ∈ E
        · have hp' : w ∈ B ∩ {w | ‖u + y - w‖ ≤ 1} := ⟨hp.2.2.1, (by
              simpa only [Metric.mem_ball, dist_zero_right, z] using hAb hp.2.2.2 :
                ‖u + y - w‖ < 1).le⟩
          dsimp only [T]
          rw [indicator_of_mem hp', indicator_of_mem hp]
          exact le_rfl
        · dsimp only [T]
          rw [indicator_of_notMem hp]
          exact zero_le
      · rw [indicator_of_notMem hy]
        have he (w : Ambient d) : T (u, y, w) = 0 :=
          indicator_of_notMem (fun H : (u, y, w) ∈ E => hy H.2.1) _
        simp_rw [he, lintegral_zero]
        exact le_rfl
    · have he (p : Ambient d × Ambient d) : T (u, p) = 0 :=
        indicator_of_notMem (fun H : (u, p) ∈ E => hu H.1) _
      simp_rw [he, lintegral_zero]
      exact zero_le
  have hUbound : (∫⁻ p, U p ∂ν) ≤ C₀ * (∫⁻ u, ‖f u‖ₑ ^ (2 : ℕ)) * (M * M) := by
    rw [lintegral_prod _ hU.aemeasurable]
    calc
      _ = ∫⁻ u, ‖f u‖ₑ ^ (2 : ℕ) * ∫⁻ p, T (u, p) ∂μ.prod μ := by
        apply lintegral_congr
        intro u
        have hm : Measurable (fun p : Ambient d × Ambient d => T (u, p)) :=
          hT.comp (measurable_const.prodMk measurable_id)
        change (∫⁻ p : Ambient d × Ambient d, ‖f u‖ₑ ^ (2 : ℕ) * T (u, p) ∂μ.prod μ) = _
        exact lintegral_const_mul _ hm
      _ ≤ ∫⁻ u, ‖f u‖ₑ ^ (2 : ℕ) * (C₀ * (M * M)) :=
        lintegral_mono fun u => mul_le_mul' le_rfl (hrowT u)
      _ = _ := by rw [lintegral_mul_const _ (hf.enorm.pow_const (2 : ℕ))]; ac_rfl
  have hQbound : (∫⁻ p, Q p ∂ν) ≤ ∫⁻ p, U p ∂ν := by
    refine (lintegral_mono hpoint).trans_eq ?_
    have hm : Measurable (fun p => U p + V p) := hU.add hV
    rw [lintegral_const_mul _ hm, lintegral_add_left hU V, hVeq, ← two_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have henergy := graph_extension_gaussian_product_energy_le hφ hf hg hfi hgi hfs hgs hg₁ hh
  change (∫⁻ t, ‖radonGaussianSymbol h t‖ₑ * W t) ≤ _ at henergy
  change _ ≤ C₁ * C₀ * (∫⁻ u, ‖f u‖ₑ ^ (2 : ℕ)) * (volume B) ^ (2 * (1 - 1 / q))
  have hQi : (∫⁻ p, Q p ∂ν) = ∫⁻ u, ∫⁻ y, ∫⁻ w, Q (u, y, w) := by
    rw [lintegral_prod _ hQ.aemeasurable]
    apply lintegral_congr
    intro u
    exact lintegral_prod _ (hQ.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hM : M * M = (volume B) ^ (2 * (1 - 1 / q)) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hq' hq', two_mul]
  calc
    _ ≤ C₁ * (∫⁻ p, Q p ∂ν) := by
      rw [hQi]
      exact henergy
    _ ≤ C₁ * (C₀ * (∫⁻ u, ‖f u‖ₑ ^ (2 : ℕ)) * (M * M)) :=
      mul_le_mul' le_rfl (hQbound.trans hUbound)
    _ = _ := by rw [hM]; ac_rfl

end RestrictionWork
