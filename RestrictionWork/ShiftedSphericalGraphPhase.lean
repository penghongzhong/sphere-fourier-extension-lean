import RestrictionWork.ShiftedSphericalScalarPhase
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- A graph phase in translated parabolic coordinates. The vector `l`
specifies the linear phase removed before dividing by the square of the scale. -/
def graphRebasePhase {d : ℕ} (φ : Ambient d → ℝ) (a l : Ambient d)
    (r : ℝ) (u : Ambient d) : ℝ :=
  (φ (a + r • u) - φ a - r * ⟪l, u⟫) / r ^ 2

def sphericalGraphPhase {d : ℕ} (δ : ℝ) (v : Ambient d) : ℝ :=
  sphericalPhase δ (‖v‖ ^ 2)

def sphericalGraphSlope {d : ℕ} (δ : ℝ) (a : Ambient d) : Ambient d :=
  (2 / Real.sqrt (1 - δ ^ 2 * ‖a‖ ^ 2)) • a

def shiftedSphericalGraphPhase {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ) :
    Ambient d → ℝ :=
  graphRebasePhase (sphericalGraphPhase δ) a (sphericalGraphSlope δ a) r

theorem shifted_spherical_graph_error {d : ℕ} {δ r : ℝ} {a u : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) :
    |shiftedSphericalGraphPhase δ a r u -
      sphericalTangentHeight δ (‖a‖ ^ 2) ⟪a, u⟫ (‖u‖ ^ 2)| ≤ 70 * δ ^ 2 * r := by
  have hnorm : ‖a + r • u‖ ≤ 1 := by
    calc
      _ ≤ ‖a‖ + ‖r • u‖ := norm_add_le _ _
      _ = ‖a‖ + r * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ _ := by nlinarith only [ha, hrhalf, mul_le_mul_of_nonneg_left hu hr.le]
  have hsquare : ‖a + r • u‖ ^ 2 = ‖a‖ ^ 2 + 2 * r * ⟪a, u⟫ + r ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hinner : |⟪a, u⟫| ≤ 1 := by
    calc
      _ ≤ ‖a‖ * ‖u‖ := by simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) a u)
      _ ≤ (1 / 2) * 1 := mul_le_mul ha hu (norm_nonneg u) (by norm_num)
      _ ≤ _ := by norm_num
  have hrebase : shiftedSphericalGraphPhase δ a r u =
      shiftedSphericalHeight δ r (‖a‖ ^ 2) ⟪a, u⟫ (‖u‖ ^ 2) := by
    unfold shiftedSphericalGraphPhase graphRebasePhase sphericalGraphPhase
      shiftedSphericalHeight sphericalGraphSlope
    rw [hsquare, real_inner_smul_left]
    ring
  rw [hrebase]
  exact shifted_spherical_height_error hδ hδhalf hr (hrhalf.trans (by norm_num))
    (by nlinarith [norm_nonneg a]) (by rw [← hsquare]; nlinarith [norm_nonneg (a + r • u)])
    hinner (sq_nonneg _) (by nlinarith [norm_nonneg u])

theorem shifted_spherical_graph_scale_difference {d : ℕ} {δ r σ : ℝ} {a u : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) :
    |shiftedSphericalGraphPhase δ a r u - shiftedSphericalGraphPhase δ a σ u| ≤
      70 * δ ^ 2 * (r + σ) := by
  calc
    _ ≤ |shiftedSphericalGraphPhase δ a r u -
          sphericalTangentHeight δ (‖a‖ ^ 2) ⟪a, u⟫ (‖u‖ ^ 2)| +
        |shiftedSphericalGraphPhase δ a σ u -
          sphericalTangentHeight δ (‖a‖ ^ 2) ⟪a, u⟫ (‖u‖ ^ 2)| := by
          rw [abs_sub_comm (shiftedSphericalGraphPhase δ a σ u)
            (sphericalTangentHeight δ (‖a‖ ^ 2) ⟪a, u⟫ (‖u‖ ^ 2))]
          exact abs_sub_le _ _ _
    _ ≤ 70 * δ ^ 2 * r + 70 * δ ^ 2 * σ :=
      add_le_add (shifted_spherical_graph_error hδ hδhalf ha hr hrhalf hu)
        (shifted_spherical_graph_error hδ hδhalf ha hσ hσhalf hu)
    _ = _ := by ring

theorem spherical_graph_slope_norm {d : ℕ} {δ : ℝ} {a : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2) :
    ‖sphericalGraphSlope δ a‖ ≤ 4 := by
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hasq : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hheight : 1 / 2 ≤ Real.sqrt (1 - δ ^ 2 * ‖a‖ ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hδsq, mul_le_mul_of_nonneg_left hasq (sq_nonneg δ)]
  have hheightpos : 0 < Real.sqrt (1 - δ ^ 2 * ‖a‖ ^ 2) := by linarith
  have hquot : 2 / Real.sqrt (1 - δ ^ 2 * ‖a‖ ^ 2) ≤ 4 := by
    rw [div_le_iff₀ hheightpos]
    linarith
  unfold sphericalGraphSlope
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul hquot ha (norm_nonneg _) (by norm_num)).trans (by norm_num)

end RestrictionWork
