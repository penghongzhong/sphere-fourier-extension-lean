import RestrictionWork.DyadicWhitneyPairs
import RestrictionWork.GraphProductPlancherel

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace RestrictionWork

/-- An enlargement by a fixed number of fine cells around the index sum. -/
def dyadicPairFrequency {d : ℕ} (j b : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Set (Ambient d) :=
  {s | ∀ i, |dyadicIndex (j + 1) (s i) - (p.1 i + p.2 i)| ≤ (b : ℤ)}

/-- Each convolution is supported in the corresponding sum of the fine
cells, contained in the band of width one in the sum indices. -/
theorem graph_whitney_convolution_support {d : ℕ} (j : ℕ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) (φ : Ambient d → ℝ) (f g : Ambient d → ℂ)
    (t : ℝ) :
    Function.support (graphProductConvolution φ
      ((dyadicParameterCell (j + 1) p.1).indicator f)
      ((dyadicParameterCell (j + 1) p.2).indicator g) t) ⊆ dyadicPairFrequency j 1 p := by
  intro s hs
  by_contra hfreq
  apply hs
  unfold graphProductConvolution
  rw [← integral_zero (Ambient d) ℂ (μ := volume)]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ dyadicParameterCell (j + 1) p.1
  · by_cases hv : s - u ∈ dyadicParameterCell (j + 1) p.2
    · exfalso
      apply hfreq
      intro i
      let a := (2 : ℝ) ^ (j + 1) * u i
      let b := (2 : ℝ) ^ (j + 1) * (s - u) i
      have ha : ⌊a⌋ = p.1 i := mem_dyadic_parameter_cell.mp hu i
      have hb : ⌊b⌋ = p.2 i := mem_dyadic_parameter_cell.mp hv i
      have hs' : a + b = (2 : ℝ) ^ (j + 1) * s i := by
        simp only [a, b, PiLp.sub_apply]
        ring
      have h₁ := Int.le_floor_add a b
      have h₂ := Int.le_floor_add_floor a b
      rw [ha, hb, hs'] at h₁ h₂
      change |⌊(2 : ℝ) ^ (j + 1) * s i⌋ - (p.1 i + p.2 i)| ≤ (1 : ℤ)
      exact abs_le.mpr ⟨by omega, by omega⟩
    · simp [indicator_of_notMem hv]
  · simp [indicator_of_notMem hu]

/-- The number of Whitney pairs whose frequency band contains a given
sum point is bounded independently of the Whitney scale. -/
theorem card_dyadic_whitney_frequency_overlap {d : ℕ} (j b : ℕ) (s : Ambient d) :
    (by
      classical
      exact ((dyadicWhitneyPairs d j).filter fun p => s ∈ dyadicPairFrequency j b p).card)
      ≤ 7 ^ d * (2 * b + 1) ^ d := by
  classical
  let W := (dyadicWhitneyPairs d j).filter fun p => s ∈ dyadicPairFrequency j b p
  let B := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-3 : ℤ) 3)
  let D := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(b : ℤ)) (b : ℤ))
  let m (i : Fin d) := dyadicIndex (j + 1) (s i)
  let encode (p : (Fin d → ℤ) × (Fin d → ℤ)) : (Fin d → ℤ) × (Fin d → ℤ) :=
    (fun i => p.1 i - p.2 i, fun i => m i - (p.1 i + p.2 i))
  have hcard : W.card ≤ (B ×ˢ D).card := by
    apply Finset.card_le_card_of_injOn encode
    · intro p hp
      obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_product.mpr
      refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), Fintype.mem_piFinset.mpr (fun i => ?_)⟩
      · exact Finset.mem_Icc.mpr (abs_le.mp (dyadic_whitney_pair_index_gap hp i))
      · exact Finset.mem_Icc.mpr (abs_le.mp (hs i))
    · intro p _ q _ h
      have h₁ (i : Fin d) : p.1 i - p.2 i = q.1 i - q.2 i :=
        congrArg (fun r : (Fin d → ℤ) × (Fin d → ℤ) => r.1 i) h
      have h₂ (i : Fin d) : m i - (p.1 i + p.2 i) = m i - (q.1 i + q.2 i) :=
        congrArg (fun r : (Fin d → ℤ) × (Fin d → ℤ) => r.2 i) h
      exact Prod.ext (funext fun i => by have := h₁ i; have := h₂ i; omega)
        (funext fun i => by have := h₁ i; have := h₂ i; omega)
  have hB : (Finset.Icc (-3 : ℤ) 3).card = 7 := by rw [Int.card_Icc]; norm_num
  have hD : (Finset.Icc (-(b : ℤ)) (b : ℤ)).card = 2 * b + 1 := by
    rw [Int.card_Icc]
    omega
  simpa only [Finset.card_product, B, D, Fintype.card_piFinset_const, hB, hD] using hcard

end RestrictionWork
