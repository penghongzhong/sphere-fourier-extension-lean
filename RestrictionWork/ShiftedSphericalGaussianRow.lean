import RestrictionWork.ShiftedSphericalDoubleStrip

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace RestrictionWork

private theorem gaussian_le_strip_series {h : ℝ} (hh : 0 < h) (D : ℝ) :
    ENNReal.ofReal (radonGaussianKernel h (D / (2 * Real.pi))) ≤
      ENNReal.ofReal (64 / h) * ∑' n : ℕ,
        (4⁻¹ : ℝ≥0∞) ^ n * {x : ℝ | |x| ≤ (2 : ℝ) ^ n * h}.indicator (fun _ => 1) D := by
  have hex : ∃ n : ℕ, |D| ≤ (2 : ℝ) ^ n * h := by
    obtain ⟨n, hn⟩ := exists_nat_gt (|D| / h)
    have hp : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast n.lt_two_pow_self.le
    exact ⟨n, (div_le_iff₀ hh).mp (hn.le.trans hp)⟩
  let n := Nat.find hex
  let X := Real.pi * ((D / (2 * Real.pi)) / h) ^ 2
  have hX : 0 ≤ X := mul_nonneg Real.pi_pos.le (sq_nonneg _)
  have hb : Real.exp (-X) ≤ 64 / (4 : ℝ) ^ n := by
    cases hn : n with
    | zero =>
      rw [pow_zero, div_one]
      exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hX)).trans (by norm_num)
    | succ k =>
      have hk : k < Nat.find hex := by
        change n = k + 1 at hn
        change k < n
        omega
      have hprev : (2 : ℝ) ^ k * h < |D| := lt_of_not_ge (Nat.find_min hex hk)
      have habs : (2 : ℝ) ^ k ≤ |D / h| := by
        rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]
        exact hprev.le
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ) ^ k) (abs_nonneg _)).mpr habs
      rw [sq_abs, ← pow_mul, mul_comm k 2, pow_mul] at hsq
      norm_num at hsq
      have hXeq : (D / h) ^ 2 = (4 * Real.pi) * X := by
        unfold X
        field_simp [Real.pi_ne_zero, hh.ne']
        ring
      rw [hXeq] at hsq
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos X) (by positivity),
        one_mul, pow_succ]
      calc
        _ ≤ 64 * X := by nlinarith only [hsq,
          mul_le_mul_of_nonneg_right Real.pi_lt_four.le hX]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp X]) (by norm_num)
  have hterm :
      ENNReal.ofReal (radonGaussianKernel h (D / (2 * Real.pi))) ≤
        ENNReal.ofReal (64 / h) * (4⁻¹ : ℝ≥0∞) ^ n := by
    rw [radonGaussianKernel, neg_mul]
    change ENNReal.ofReal (h⁻¹ * Real.exp (-X)) ≤ _
    calc
      _ ≤ ENNReal.ofReal ((64 / h) / (4 : ℝ) ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [div_eq_mul_inv, mul_left_comm h⁻¹, mul_comm h⁻¹ (64 : ℝ), mul_assoc] using
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
      _ = _ := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  have hn : D ∈ {x : ℝ | |x| ≤ (2 : ℝ) ^ n * h} := Nat.find_spec hex
  refine hterm.trans (mul_le_mul' le_rfl ?_)
  simpa only [indicator_of_mem hn, mul_one] using
    (ENNReal.le_tsum (f := fun k : ℕ => (4⁻¹ : ℝ≥0∞) ^ k *
      {x : ℝ | |x| ≤ (2 : ℝ) ^ k * h}.indicator (fun _ => 1) D) n)

set_option maxHeartbeats 650000 in
/-- The positive Gaussian collision kernel has a uniform row bound,
with the two restricted Radon powers and no loss in the Gaussian width. -/
theorem shifted_collision_gaussian_row_bound {d : ℕ} (hd : 1 ≤ d)
    {q σ : ℝ} (hq : 2 ≤ q) (hqd : q < (d : ℝ) + 1) (hσ : 0 < σ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {δ r h : ℝ} {a u : Ambient d},
        0 < δ → δ ≤ 1 / 2 → ‖a‖ ≤ 1 / 2 → 0 < r → r ≤ 1 / 2 →
        ‖u‖ ≤ 1 → 0 < h →
        ∀ {A B : Set (Ambient d)}, MeasurableSet A → MeasurableSet B →
          A ⊆ {v | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖} →
          B ⊆ {v | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖} →
          (∫⁻ y in A, ∫⁻ w in B ∩ {w | ‖u + y - w‖ ≤ 1},
            ENNReal.ofReal (radonGaussianKernel h (shiftedCollisionPhase δ a r u y w /
              (2 * Real.pi)))) ≤
              C * (volume A) ^ (1 - 1 / q) * (volume B) ^ (1 - 1 / q) := by
  obtain ⟨C₀, hC₀, hstrip⟩ := shifted_collision_double_strip_bound hd hq hqd hσ
  refine ⟨128 * C₀, ENNReal.mul_lt_top (by norm_num) hC₀, ?_⟩
  intro δ r h a u hδ hδhalf ha hr hrhalf hu hh A B hA hB hAD hBD
  let D := shiftedCollisionPhase δ a r u
  let M := (volume A) ^ (1 - 1 / q) * (volume B) ^ (1 - 1 / q)
  let H := ENNReal.ofReal (64 / h)
  let Z := fun y : Ambient d => {w : Ambient d | ‖u + y - w‖ ≤ 1}
  let T := fun n : ℕ => {p : Ambient d × Ambient d |
    p.2 ∈ B ∧ (‖u + p.1 - p.2‖ ≤ 1 ∧ |D p.1 p.2| ≤ (2 : ℝ) ^ n * h)}
  let V := fun n : ℕ => (4⁻¹ : ℝ≥0∞) ^ n • (T n).indicator (fun _ => (1 : ℝ≥0∞))
  have hDm : Measurable (Function.uncurry D) := by
    unfold D Function.uncurry shiftedCollisionPhase shiftedSphericalGraphPhase
      graphRebasePhase sphericalGraphPhase sphericalPhase
    fun_prop
  have hZ (y : Ambient d) : MeasurableSet (Z y) := measurableSet_le (by fun_prop) measurable_const
  have hT (n : ℕ) : MeasurableSet (T n) := by
    have hZ' : Measurable (fun p : Ambient d × Ambient d => ‖u + p.1 - p.2‖) := by fun_prop
    have hD' : Measurable (fun p : Ambient d × Ambient d => |D p.1 p.2|) := by
      simpa only [Real.norm_eq_abs, Function.uncurry] using hDm.norm
    exact (hB.preimage measurable_snd).inter
      ((measurableSet_le hZ' measurable_const).inter (measurableSet_le hD' measurable_const))
  have hV (n : ℕ) : Measurable (V n) :=
    measurable_const.mul (measurable_const.indicator (hT n))
  have hrow (n : ℕ) : Measurable (fun y => ∫⁻ w, V n (y, w)) := (hV n).lintegral_prod_right'
  have hslice (n : ℕ) (y : Ambient d) :
      (∫⁻ w, V n (y, w)) = (4⁻¹ : ℝ≥0∞) ^ n *
        volume ((fun w => (y, w)) ⁻¹' T n) := by
    let U := (fun w => (y, w)) ⁻¹' T n
    have hm : MeasurableSet U := measurable_prodMk_left (hT n)
    have he (w : Ambient d) : (T n).indicator (fun _ => (1 : ℝ≥0∞)) (y, w) =
        U.indicator (fun _ => 1) w := by
      by_cases hw : w ∈ U
      · rw [indicator_of_mem hw, indicator_of_mem (show (y, w) ∈ T n from hw)]
      · rw [indicator_of_notMem hw, indicator_of_notMem (show (y, w) ∉ T n from hw)]
    change (∫⁻ w, (4⁻¹ : ℝ≥0∞) ^ n * (T n).indicator (fun _ => 1) (y, w)) = _
    simp_rw [he]
    rw [lintegral_const_mul _ (measurable_const.indicator hm), lintegral_indicator hm,
      lintegral_const, Measure.restrict_apply_univ, one_mul]
  have hsum (y : Ambient d) :
      (∫⁻ w in B ∩ Z y, ENNReal.ofReal (radonGaussianKernel h (D y w / (2 * Real.pi)))) ≤
        H * ∑' n : ℕ, ∫⁻ w, V n (y, w) := by
    have hm (n : ℕ) : Measurable (fun w : Ambient d => V n (y, w)) :=
      (hV n).comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_tsum (fun n => (hm n).aemeasurable),
      ← lintegral_const_mul H (Measurable.tsum hm), ← lintegral_indicator (hB.inter (hZ y))]
    apply lintegral_mono
    intro w
    by_cases hw : w ∈ B ∩ Z y
    · rw [indicator_of_mem hw]
      refine (gaussian_le_strip_series hh (D y w)).trans (mul_le_mul' le_rfl ?_)
      apply ENNReal.tsum_le_tsum
      intro n
      change _ ≤ (4⁻¹ : ℝ≥0∞) ^ n * (T n).indicator (fun _ => 1) (y, w)
      by_cases hn : |D y w| ≤ (2 : ℝ) ^ n * h
      · rw [indicator_of_mem (show D y w ∈ {x : ℝ | |x| ≤ (2 : ℝ) ^ n * h} from hn),
          indicator_of_mem (show (y, w) ∈ T n from ⟨hw.1, hw.2, hn⟩)]
      · rw [indicator_of_notMem (show D y w ∉ {x : ℝ | |x| ≤ (2 : ℝ) ^ n * h} from hn),
          mul_zero]
        exact zero_le
    · rw [indicator_of_notMem hw]
      exact zero_le
  have hgeom (n : ℕ) : H * ((4⁻¹ : ℝ≥0∞) ^ n * ENNReal.ofReal ((2 : ℝ) ^ n * h)) =
      64 * (2⁻¹ : ℝ≥0∞) ^ n := by
    have h2 : (4⁻¹ : ℝ≥0∞) * 2 = 2⁻¹ := by
      calc
        _ = ENNReal.ofReal ((4 : ℝ)⁻¹ * 2) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
            ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
        _ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by norm_num
        _ = _ := by rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    have he : H * ENNReal.ofReal h = 64 := by
      dsimp only [H]
      rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hh.ne', ENNReal.ofReal_ofNat]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    calc
      _ = (H * ENNReal.ofReal h) * ((4⁻¹ : ℝ≥0∞) * 2) ^ n := by rw [mul_pow]; ac_rfl
      _ = _ := by rw [he, h2]
  calc
    _ ≤ ∫⁻ y in A, H * ∑' n : ℕ, ∫⁻ w, V n (y, w) := lintegral_mono hsum
    _ = ∑' n : ℕ, H * (∫⁻ y in A, ∫⁻ w, V n (y, w)) := by
      rw [lintegral_const_mul H (Measurable.tsum hrow),
        lintegral_tsum (fun n => (hrow n).aemeasurable), ENNReal.tsum_mul_left]
    _ ≤ ∑' n : ℕ, (64 * (2⁻¹ : ℝ≥0∞) ^ n) * (C₀ * M) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simp_rw [hslice]
      have hm : Measurable (fun y => volume ((fun w => (y, w)) ⁻¹' T n)) :=
        measurable_measure_prodMk_left (hT n)
      rw [lintegral_const_mul _ hm, ← hgeom n]
      have hb := hstrip hδ hδhalf ha hr hrhalf hu (ε := (2 : ℝ) ^ n * h)
        (by positivity) hA hB hAD hBD
      have hb' : (∫⁻ y in A, volume ((fun w => (y, w)) ⁻¹' T n)) ≤
          ENNReal.ofReal ((2 : ℝ) ^ n * h) * (C₀ * M) :=
        hb.trans_eq (by unfold M; ac_rfl)
      exact (mul_le_mul' le_rfl (mul_le_mul' le_rfl hb')).trans_eq (by ac_rfl)
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
      unfold M
      rw [show (64 : ℝ≥0∞) * 2 = 128 by norm_num]
      ac_rfl

end RestrictionWork
