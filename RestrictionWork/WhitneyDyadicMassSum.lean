import RestrictionWork.WhitneyGeometricSum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Finset
open scoped ENNReal BigOperators

namespace RestrictionWork

private theorem sum_rpow_le_total_rpow {ι : Type*} (s : Finset ι) (m : ι → ℝ≥0∞)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, m i ^ p) ≤ (∑ i ∈ s, m i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos (zero_lt_one.trans_le hp)]
  | @insert i s hi hs =>
    simp only [sum_insert hi]
    exact (add_le_add le_rfl hs).trans (ENNReal.add_rpow_le_rpow_add _ _ hp)

private theorem sum_rpow_le_max_rpow_mul {ι : Type*} (s : Finset ι) (m : ι → ℝ≥0∞)
    {V : ℝ≥0∞} (hV : ∀ i ∈ s, m i ≤ V) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, m i ^ p) ≤ V ^ (p - 1) * ∑ i ∈ s, m i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hsub := sub_nonneg.mpr hp
  have he := ENNReal.rpow_add_of_nonneg (x := m i) (p - 1) 1 hsub zero_le_one
  rw [sub_add_cancel, ENNReal.rpow_one] at he
  rw [he]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (hV i hi) hsub) le_rfl

set_option maxHeartbeats 950000 in
/-- Summation of the Whitney mass bound at the exact scaling line. Here
y is the reciprocal output exponent, k the target mass power, and α
the improved mass power. The two branches use the total mass and the
largest piece respectively. -/
theorem whitney_dyadic_mass_sum {ι : Type*} {b D B : ℝ≥0∞}
    (hb : 0 < b) (hb₁ : b < 1) (hD : D < ⊤) (hB : B < ⊤)
    {α k y : ℝ} (hy : 0 < y) (hyk : y < k) (hkα : k < α) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {M : ℝ≥0∞}, 0 < M → M < ⊤ → ∀ (s : ℕ → Finset ι) (m : ℕ → ι → ℝ≥0∞),
        (∀ j, (∑ i ∈ s j, m j i) ≤ D * M) →
        (∀ j i, i ∈ s j → m j i ≤ B * b ^ j) →
        (∑' j : ℕ, (b ^ j) ^ (-(α - k)) * (∑ i ∈ s j, m j i ^ (α / y)) ^ y)
          ≤ C * M ^ k := by
  let e := α - k
  let c := k - y
  let K := max (D ^ α) (B ^ (α - y) * D ^ y)
  let G := (1 - b ^ e)⁻¹ + (1 - b ^ c)⁻¹
  have he : 0 < e := sub_pos.mpr hkα
  have hc : 0 < c := sub_pos.mpr hyk
  have hk : 0 < k := hy.trans hyk
  have hα : 0 < α := hk.trans hkα
  have hαy : 0 ≤ α - y := sub_nonneg.mpr ((hyk.trans hkα).le)
  have hK : K < ⊤ :=
    max_lt (ENNReal.rpow_lt_top_of_nonneg hα.le hD.ne)
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hαy hB.ne)
        (ENNReal.rpow_lt_top_of_nonneg hy.le hD.ne))
  have hGeom {u : ℝ} (hu : 0 < u) : (1 - b ^ u)⁻¹ < ⊤ :=
    (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt (ENNReal.rpow_lt_one hb₁ hu)).ne').lt_top
  have hG : G < ⊤ := ENNReal.add_lt_top.mpr ⟨hGeom he, hGeom hc⟩
  refine ⟨K * G, ENNReal.mul_lt_top hK hG, ?_⟩
  intro M hM hMt s m htotal hpiece
  let p := α / y
  have hp : 1 ≤ p := (le_div_iff₀ hy).mpr (by simpa only [one_mul] using (hyk.trans hkα).le)
  have hpy : p * y = α := div_mul_cancel₀ α hy.ne'
  have hp'y : (p - 1) * y = α - y := by rw [sub_mul, hpy, one_mul]
  have hmα : M ^ α = M ^ k * M ^ e := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hk.le he.le]
    congr 1
    unfold e
    ring
  have hmy : M ^ y = M ^ k / M ^ c := by
    rw [← ENNReal.rpow_sub _ _ hM.ne' hMt.ne]
    congr 1
    unfold c
    ring
  let w (j : ℕ) := min ((M / b ^ j) ^ e) (((b ^ j) / M) ^ c)
  have hblock (j : ℕ) :
      (b ^ j) ^ (-e) * (∑ i ∈ s j, m j i ^ p) ^ y ≤ (K * M ^ k) * w j := by
    let v := b ^ j
    let N := (∑ i ∈ s j, m j i ^ p) ^ y
    have hv₀ : v ≠ 0 := pow_ne_zero _ hb.ne'
    have hvt : v ≠ ⊤ := (ENNReal.pow_lt_top (hb₁.trans ENNReal.one_lt_top)).ne
    have hcoarse : N ≤ (D * M) ^ α := by
      calc
        _ ≤ ((D * M) ^ p) ^ y :=
          ENNReal.rpow_le_rpow
            ((sum_rpow_le_total_rpow (s j) (m j) hp).trans
              (ENNReal.rpow_le_rpow (htotal j) (zero_le_one.trans hp))) hy.le
        _ = _ := by rw [← ENNReal.rpow_mul, hpy]
    have hfine : N ≤ (B * v) ^ (α - y) * (D * M) ^ y := by
      calc
        _ ≤ ((B * v) ^ (p - 1) * (D * M)) ^ y :=
          ENNReal.rpow_le_rpow
            ((sum_rpow_le_max_rpow_mul (s j) (m j) (hpiece j) hp).trans
              (mul_le_mul' le_rfl (htotal j))) hy.le
        _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hy.le, ← ENNReal.rpow_mul, hp'y]
    have hvs : v ^ (-e) * v ^ (α - y) = v ^ c := by
      rw [← ENNReal.rpow_add _ _ hv₀ hvt]
      congr 1
      unfold e c
      ring
    have hL : v ^ (-e) * N ≤ (K * M ^ k) * (M / v) ^ e := by
      calc
        _ ≤ v ^ (-e) * (D * M) ^ α := mul_le_mul' le_rfl hcoarse
        _ = (D ^ α * M ^ k) * (M / v) ^ e := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le, hmα, ENNReal.rpow_neg,
            ENNReal.div_rpow_of_nonneg _ _ he.le, div_eq_mul_inv]
          ac_rfl
        _ ≤ _ := mul_le_mul' (mul_le_mul' (le_max_left _ _) le_rfl) le_rfl
    have hR : v ^ (-e) * N ≤ (K * M ^ k) * (v / M) ^ c := by
      calc
        _ ≤ v ^ (-e) * ((B * v) ^ (α - y) * (D * M) ^ y) := mul_le_mul' le_rfl hfine
        _ = (B ^ (α - y) * D ^ y) * (v ^ (-e) * v ^ (α - y)) * M ^ y := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hαy, ENNReal.mul_rpow_of_nonneg _ _ hy.le]
          ac_rfl
        _ = ((B ^ (α - y) * D ^ y) * M ^ k) * (v / M) ^ c := by
          rw [hvs, hmy, ENNReal.div_rpow_of_nonneg _ _ hc.le]
          simp only [div_eq_mul_inv]
          ac_rfl
        _ ≤ _ := mul_le_mul' (mul_le_mul' (le_max_right _ _) le_rfl) le_rfl
    have hm : Monotone (fun z : ℝ≥0∞ => (K * M ^ k) * z) :=
      fun _ _ hz => mul_le_mul' le_rfl hz
    change v ^ (-e) * N ≤ (K * M ^ k) * min ((M / v) ^ e) ((v / M) ^ c)
    rw [hm.map_min]
    exact le_min hL hR
  calc
    _ ≤ ∑' j : ℕ, (K * M ^ k) * w j := ENNReal.tsum_le_tsum hblock
    _ = (K * M ^ k) * ∑' j : ℕ, w j := ENNReal.tsum_mul_left
    _ ≤ (K * M ^ k) * G := mul_le_mul' le_rfl (whitney_geometric_sum hM hMt hb hb₁ he hc)
    _ = _ := by ac_rfl

end RestrictionWork
