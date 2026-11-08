import RestrictionWork.JSP001040CatalogStatement

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace JSP001040Manuscript

private def surfaceMeasure (n : ℕ) : Measure (RestrictionWork.UnitSphere n) :=
  (volume : Measure (RestrictionWork.Ambient n)).toSphere

private def extension {n : ℕ} (f : RestrictionWork.UnitSphere n → ℂ)
    (X : RestrictionWork.Ambient n) : ℂ :=
  ∫ ω, f ω * Complex.exp
    (((2 * Real.pi * ⟪X, (ω : RestrictionWork.Ambient n)⟫ : ℝ) : ℂ) * Complex.I)
    ∂surfaceMeasure n

private theorem knappCoordinates
    (n : ℕ) (hn : 3 ≤ n) (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (((q⁻¹).toReal ≤ (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal)) ↔
      ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹ ≤ q) ∧
    (((q⁻¹).toReal = (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal)) ↔
      q = ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let a : ℝ := ((n : ℝ) - 1) / ((n : ℝ) + 1)
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  let B : ℝ≥0∞ := ENNReal.ofReal a * (1 - p⁻¹)
  have hp' : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp
  have hq' : q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le hq).ne'
  have hBt : B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((tsub_le_self.trans_lt ENNReal.one_lt_top).ne)
  have hBr : B.toReal = a * (1 - (p⁻¹).toReal) := by
    dsimp [B]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
      ENNReal.toReal_sub_of_le hp' ENNReal.one_ne_top, ENNReal.toReal_one]
  have hBinv : B⁻¹ =
      ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹ := by
    have hA0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
    dsimp [B]
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_inv_of_pos ha]
    simp only [a, inv_div]
  constructor
  · rw [← hBinv, ← ENNReal.inv_le_iff_inv_le, ← ENNReal.toReal_le_toReal hq' hBt, hBr]
  · rw [← hBinv, ← hBr, ENNReal.toReal_eq_toReal_iff' hq' hBt]
    simpa only [inv_inv] using (inv_inj : q⁻¹ = (B⁻¹)⁻¹ ↔ q = B⁻¹)

/-- Strong type on the finite Knapp boundary, with the manuscript's actual
surface measure and Fourier kernel. -/
theorem finiteKnappBoundary (n : ℕ) (hn : 3 ≤ n) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hrad : ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q)
    (hline : q = ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹)
    (hqfin : q < ⊤) :
    ∃ C : ℝ≥0, ∀ f : RestrictionWork.UnitSphere n → ℂ,
      MemLp f p (surfaceMeasure n) →
      MemLp (extension f) q (volume : Measure (RestrictionWork.Ambient n)) ∧
        eLpNorm (extension f) q volume ≤ (C : ℝ≥0∞) * eLpNorm f p (surfaceMeasure n) := by
  change RestrictionWork.BoundedSphereExtension n p q
  have hrec := (knappCoordinates n hn p q hp hq).2.mpr hline
  have hadm : RestrictionWork.AdmissibleExponents n p q := ⟨hp, hq, hrad, hrec.le⟩
  refine RestrictionWork.finiteKnappBoundary_of_quarter_graph ?_ n hn p q hqfin.ne hadm hrec
  intro d hd p₀ q₀ hfin ha hl
  obtain ⟨y, hy, hyD, hp₀, hq₀⟩ := RestrictionWork.admissible_finite_knapp_reparam hd hfin ha hl
  obtain ⟨C, hC, H⟩ := RestrictionWork.spherical_graph_knapp_strong hd hy hyD
  rw [hp₀, hq₀]
  exact ⟨C, hC, H (by norm_num : (0 : ℝ) < 1 / 2) le_rfl⟩

/-- Complete exponent range, deduced from the finite boundary theorem,
the strict range, the infinite-output estimate and necessity. -/
theorem fullRange (n : ℕ) (hn : 3 ≤ n) (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∃ C : ℝ≥0, ∀ f : RestrictionWork.UnitSphere n → ℂ,
      MemLp f p (surfaceMeasure n) →
      MemLp (extension f) q (volume : Measure (RestrictionWork.Ambient n)) ∧
        eLpNorm (extension f) q volume ≤ (C : ℝ≥0∞) * eLpNorm f p (surfaceMeasure n)) ↔
      ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 1)) < q ∧
        ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1)) * (1 - p⁻¹)⁻¹ ≤ q := by
  change RestrictionWork.BoundedSphereExtension n p q ↔ _
  have hcoords := knappCoordinates n hn p q hp hq
  constructor
  · intro H
    have hadm := RestrictionWork.original_sphere_necessity n hn p q hp hq H
    exact ⟨hadm.2.2.1, hcoords.1.mp hadm.2.2.2⟩
  · rintro ⟨hrad, hbound⟩
    by_cases hqt : q = ⊤
    · subst q
      exact RestrictionWork.extension_top_bound hp
    by_cases hs : (q⁻¹).toReal <
        (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (1 - (p⁻¹).toReal)
    · exact RestrictionWork.strict_admissible_sufficiency hn hp hq hrad hs
    · have hrec := le_antisymm (hcoords.1.mpr hbound) (le_of_not_gt hs)
      exact finiteKnappBoundary n hn p q hp hq hrad (hcoords.2.mp hrec)
        (lt_top_iff_ne_top.mpr hqt)

end JSP001040Manuscript

#print JSP001040Manuscript.finiteKnappBoundary
#print axioms JSP001040Manuscript.finiteKnappBoundary
#print JSP001040Manuscript.fullRange
#print axioms JSP001040Manuscript.fullRange
