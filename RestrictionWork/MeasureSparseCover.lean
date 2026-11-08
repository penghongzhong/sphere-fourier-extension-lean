import OAI.Analysis.Fourier.Restriction.Sparse.Assembly

-- Adapted from OpenAI's Apache-2.0 Lean restriction development.
-- Upstream revision 4eaee87548250b2682affda7d05d947c05554bae (see UPSTREAM_LICENSE).

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators
open OAI.Analysis.Fourier.Wave
open OAI.Analysis.Fourier.LocalSmoothing (angularFourier)
open OAI.Analysis.Fourier.Restriction

namespace RestrictionWork

/-- Fourier bounds local to a finite measurable cover combine without any
assumption of disjointness of the covering sets. -/
private theorem measure_fourier_bound_of_finite_cover {n : ℕ} {ι : Type*}
    (μ : Measure (Space n))
    (I : Finset ι) (U : ι → Set (Space n)) (hUm : ∀ i, MeasurableSet (U i))
    (B : ι → ℝ≥0∞) {p q : ℝ≥0∞} (hq : 1 ≤ q)
    (hlocal : ∀ i ∈ I, ∀ g : Space n → ℂ, Measurable g → Integrable g →
      (∀ x, x ∉ U i → g x = 0) →
        eLpNorm (angularFourier g) q μ ≤ B i * eLpNorm g p volume)
    {f : Space n → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (hfs : ∀ x, (∀ i ∈ I, x ∉ U i) → f x = 0) :
    eLpNorm (angularFourier f) q μ ≤
      (∑ i ∈ I, B i) * eLpNorm f p volume := by
  classical
  induction I using Finset.induction_on generalizing f with
  | empty =>
    have he : f = (fun _ ↦ 0) := funext fun x ↦ hfs x (by simp)
    have hF : angularFourier (fun _ : Space n ↦ (0 : ℂ)) = (fun _ ↦ 0) := by
      funext ξ
      simp [angularFourier]
    rw [he, hF]
    simp
  | @insert i I hi ih =>
    let g := (U i).indicator f
    let h := (U i)ᶜ.indicator f
    have hgm : Measurable g := hf.indicator (hUm i)
    have hhm : Measurable h := hf.indicator (hUm i).compl
    have hgi : Integrable g := hfi.indicator (hUm i)
    have hhi : Integrable h := hfi.indicator (hUm i).compl
    have hgsub : eLpNorm g p volume ≤ eLpNorm f p volume := by
      apply eLpNorm_mono hgm.aestronglyMeasurable
      intro x
      by_cases hx : x ∈ U i <;> simp [g, hx]
    have hhsub : eLpNorm h p volume ≤ eLpNorm f p volume := by
      apply eLpNorm_mono hhm.aestronglyMeasurable
      intro x
      by_cases hx : x ∈ U i <;> simp [h, hx]
    have hgs : ∀ x, x ∉ U i → g x = 0 := by
      intro x hx
      simp [g, hx]
    have hhs : ∀ x, (∀ j ∈ I, x ∉ U j) → h x = 0 := by
      intro x hx
      by_cases hxi : x ∈ U i
      · simp [h, hxi]
      · have hz : f x = 0 := hfs x (by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hxi
          · exact hx j hj)
        simp [h, hz]
    have Hg := hlocal i (Finset.mem_insert_self _ _) g hgm hgi hgs
    have Hh := ih (fun j hj ↦ hlocal j (Finset.mem_insert_of_mem hj)) hhm hhi hhs
    have hsum : f = (fun x ↦ g x + h x) := by
      funext x
      by_cases hx : x ∈ U i <;> simp [g, h, hx]
    have hF : angularFourier f = (fun ξ ↦ angularFourier g ξ + angularFourier h ξ) := by
      funext ξ
      rw [hsum]
      exact angularFourier_add hgi hhi ξ
    rw [hF, Finset.sum_insert hi]
    calc
      _ ≤ eLpNorm (angularFourier g) q μ + eLpNorm (angularFourier h) q μ := eLpNorm_add_le hq
      _ ≤ B i * eLpNorm g p volume + (∑ j ∈ I, B j) * eLpNorm h p volume := add_le_add Hg Hh
      _ ≤ B i * eLpNorm f p volume + (∑ j ∈ I, B j) * eLpNorm f p volume := by gcongr
      _ = _ := (add_mul _ _ _).symm

/-- The sparse-ball estimate used in epsilon removal. The separation depends
polynomially on both radius and the actual number of centers. -/
def SparseMeasureFourierBound {n : ℕ} (μ : Measure (Space n)) (p : ℝ≥0∞) (α : ℝ) (D : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∀ T : Finset (Space n),
    (∀ z ∈ T, ∀ w ∈ T, z ≠ w → R ^ D * (T.card : ℝ) ^ D ≤ dist z w) →
    ∀ f : Space n → ℂ, Measurable f → Integrable f →
      (∀ x, (∀ z ∈ T, x ∉ ball z R) → f x = 0) →
        eLpNorm (angularFourier f) p μ ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f p volume

/-- Sparse estimates and the quantitative geometric cover give an explicit
norm bound on every finite union of unit balls. -/
theorem sparse_measure_fourier_bound_unit_ball_cover {n : ℕ} (μ : Measure (Space n)) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {α : ℝ} (hα : 0 ≤ α) {D : ℕ} (hD : 0 < D) {C : ℝ≥0∞}
    (hSparse : SparseMeasureFourierBound μ p α D C)
    (E : Finset (Space n)) (M N : ℕ) (hM : 1 ≤ M) (hcard : E.card ≤ M) (hN : 0 < N)
    {f : Space n → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (hfs : ∀ x, (∀ e ∈ E, x ∉ ball e 1) → f x = 0) :
    eLpNorm (angularFourier f) p μ ≤
      ENNReal.ofReal (3 * N * (M : ℝ) ^ (1 / (N : ℝ))) *
        (C * ENNReal.ofReal ((5 * (4 * ((M : ℝ) + 1)) ^ ((3 * D + 1) ^ N)) ^ α)) *
          eLpNorm f p volume := by
  classical
  obtain ⟨K, T, c, hcount, hTE, hsep, hcover, hR⟩ :=
    unit_ball_sparse_cover E M N D hM hcard hN hD
  let S (i : Fin N × Fin (K + 1)) := (T i.1).filter (fun z ↦ c i.1 z = i.2)
  let R (j : Fin N) := 5 * sparseScale M D j
  let Rmax : ℝ := 5 * (4 * ((M : ℝ) + 1)) ^ ((3 * D + 1) ^ N)
  let U (i : Fin N × Fin (K + 1)) := ⋃ z ∈ S i, ball z (R i.1)
  have hUm : ∀ i, MeasurableSet (U i) := by
    intro i
    exact (isOpen_iUnion fun z ↦ isOpen_iUnion fun _ ↦ isOpen_ball).measurableSet
  have hRi (j : Fin N) : 1 ≤ R j := by
    have H := sparseScale_ge_four M D j
    dsimp [R]
    linarith
  have hSi (i : Fin N × Fin (K + 1)) : (S i).card ≤ M :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((Finset.card_le_card (hTE i.1)).trans hcard)
  have hSsep (i : Fin N × Fin (K + 1)) : ∀ z ∈ S i, ∀ w ∈ S i,
      z ≠ w → (R i.1) ^ D * ((S i).card : ℝ) ^ D ≤ dist z w := by
    intro z hz w hw hzw
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    have H := hsep i.1 z hz'.1 w hw'.1 hzw (hz'.2.trans hw'.2.symm)
    apply le_trans _ H
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_trans zero_le_one (hRi i.1)) D)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hSi i) D
  have H := measure_fourier_bound_of_finite_cover μ Finset.univ U hUm
    (fun i ↦ C * ENNReal.ofReal ((R i.1) ^ α)) hp (fun i _ g hgm hgi hgs ↦ by
      apply hSparse (R i.1) (hRi i.1) (S i) (hSsep i) g hgm hgi
      intro x hx
      apply hgs x
      simp only [U, mem_iUnion, not_exists]
      exact hx) hf hfi (fun x hx ↦ by
        apply hfs x
        intro e he hxe
        obtain ⟨j, y, hy, hxy⟩ := hcover x ⟨e, he, hxe⟩
        apply hx (j, c j y) (Finset.mem_univ _)
        change x ∈ ⋃ z ∈ S (j, c j y), ball z (R j)
        exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hy, rfl⟩, hxy⟩⟩)
  have hsum : (∑ i : Fin N × Fin (K + 1), C * ENNReal.ofReal ((R i.1) ^ α)) ≤
      ((N * (K + 1) : ℕ) : ℝ≥0∞) * (C * ENNReal.ofReal (Rmax ^ α)) := by
    calc
      _ ≤ ∑ _i : Fin N × Fin (K + 1), C * ENNReal.ofReal (Rmax ^ α) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul le_rfl _ zero_le zero_le
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow (le_trans zero_le_one (hRi i.1)) (hR i.1) hα
      _ = _ := by simp [Fintype.card_prod, nsmul_eq_mul]
  have hcountE : ((N * (K + 1) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (3 * N * (M : ℝ) ^ (1 / (N : ℝ))) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcount
  exact H.trans (mul_le_mul (hsum.trans (mul_le_mul hcountE le_rfl zero_le zero_le)) le_rfl zero_le zero_le)

end RestrictionWork
