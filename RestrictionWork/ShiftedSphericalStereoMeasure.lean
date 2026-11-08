import RestrictionWork.ShiftedSphericalRadonOffset
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace
namespace RestrictionWork

private theorem volume_image_le_of_lipschitz_on {d : ℕ} {D : Set (Ambient d)}
    {f : Ambient d → Ambient d} {K : ℝ≥0} (hf : LipschitzOnWith K f D) :
    volume (f '' D) ≤ (K : ℝ≥0∞) ^ d * volume D := by
  let μ : Measure (Ambient d) := μH[(d : ℝ)]
  have hd : Module.finrank ℝ (Ambient d) = d := by simp [Ambient]
  let : μ.IsAddHaarMeasure := by
    simpa only [μ, hd] using (isAddHaarMeasure_hausdorffMeasure (E := Ambient d))
  let C := Measure.addHaarScalarFactor (volume : Measure (Ambient d)) μ
  have he : (volume : Measure (Ambient d)) = C • μ :=
    Measure.isAddLeftInvariant_eq_smul volume μ
  have h := hf.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d)
  rw [ENNReal.rpow_natCast] at h
  rw [he, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul, mul_left_comm ((K : ℝ≥0∞) ^ d)]
  exact mul_le_mul' le_rfl h

private theorem volume_pushforward_le_of_lower_distance {d : ℕ} {D : Set (Ambient d)}
    {f : Ambient d → Ambient d} (hf : Measurable f) {K : ℝ≥0}
    (hl : ∀ x ∈ D, ∀ y ∈ D, dist x y ≤ (K : ℝ) * dist (f x) (f y)) :
    Measure.map f (volume.restrict D) ≤ ((K : ℝ≥0∞) ^ d) • volume.restrict (f '' D) := by
  have hi : Set.InjOn f D := by
    intro x hx y hy hxy
    have H := hl x hx y hy
    simpa only [hxy, dist_self, mul_zero, dist_le_zero] using H
  let g := Function.invFunOn f D
  have hLeft : Set.LeftInvOn g f D := hi.leftInvOn_invFunOn
  have hLip : LipschitzOnWith K g (f '' D) := LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [hLeft hu, hLeft hv]
    exact hl u hu v hv
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hf hA, Measure.restrict_apply (hf hA), Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA]
  let S := A ∩ (f '' D)
  have he : g '' S = f ⁻¹' A ∩ D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hy.2
      rw [hLeft hu]
      exact ⟨hy.1, hu⟩
    · intro hx
      exact ⟨f x, ⟨hx.1, ⟨x, hx.2, rfl⟩⟩, hLeft hx.2⟩
  rw [← he]
  exact volume_image_le_of_lipschitz_on (hLip.mono inter_subset_right)

/-- Orthonormal coordinates on the tangent space at a nonzero pole,
extended to the ambient space by orthogonal projection. -/
def sphereTangentCoordinates {d : ℕ} (p : Ambient (d + 1)) (hp : p ≠ 0) :
    Ambient (d + 1) →L[ℝ] Ambient d :=
  let : Fact (Module.finrank ℝ (Ambient (d + 1)) = d + 1) := ⟨by simp [Ambient]⟩
  let B := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) d hp
  B.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ℝ ∙ p)ᗮ.orthogonalProjectionOnto)

theorem sphere_tangent_coordinates_inner {d : ℕ} {p x y : Ambient (d + 1)}
    (hp : p ≠ 0) (hx : ⟪p, x⟫ = 0) (hy : ⟪p, y⟫ = 0) :
    ⟪sphereTangentCoordinates p hp x, sphereTangentCoordinates p hp y⟫ = ⟪x, y⟫ := by
  let : Fact (Module.finrank ℝ (Ambient (d + 1)) = d + 1) := ⟨by simp [Ambient]⟩
  let B := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) d hp
  let V := (ℝ ∙ p)ᗮ
  let X : V := ⟨x, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx⟩
  let Y : V := ⟨y, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hy⟩
  change ⟪B.repr (V.orthogonalProjectionOnto X), B.repr (V.orthogonalProjectionOnto Y)⟫ = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, B.repr.inner_map_map]
  rfl

def shiftedStereoChart {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ) (u : Ambient d)
    (hu : shiftedCapPoint δ a r u ≠ 0) (v : Ambient d) : Ambient d :=
  sphereTangentCoordinates (shiftedCapPoint δ a r u) hu
    (sphereStereo (δ * r) (shiftedCapPoint δ a r u) (shiftedCapPoint δ a r v))

theorem shifted_stereo_chart_measurable {d : ℕ} (δ : ℝ) (a : Ambient d) (r : ℝ)
    (u : Ambient d) (hu : shiftedCapPoint δ a r u ≠ 0) :
    Measurable (shiftedStereoChart δ a r u hu) := by
  have hP : Measurable (shiftedCapPoint δ a r) := by
    rw [funext (shifted_cap_point_slice δ a r)]
    refine (euclideanSliceEquiv (Fin.last d)).measurable.comp ?_
    unfold shiftedCapHeight capHeight
    fun_prop
  unfold shiftedStereoChart sphereStereo
  fun_prop

/-- The actual chart transports the restricted parameter measure to a
measure dominated by a fixed multiple of Lebesgue measure. The forward
image bound also controls the measure of each restricted-data support. -/
theorem shifted_stereo_chart_measure_bounds {d : ℕ} {δ r σ : ℝ} {a u : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) (hσ : 0 < σ)
    (hPu : shiftedCapPoint δ a r u ≠ 0) :
    let D := {v : Ambient d | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖}
    let Ψ := shiftedStereoChart δ a r u hPu
    ∀ A ⊆ D,
      Measure.map Ψ (volume.restrict A) ≤ (16 : ℝ≥0∞) ^ d • volume.restrict (Ψ '' A) ∧
        volume (Ψ '' A) ≤ (ENNReal.ofReal (2 / σ ^ 2)) ^ d * volume A := by
  intro D Ψ
  let P := shiftedCapPoint δ a r
  let S := fun v => sphereStereo (δ * r) (P u) (P v)
  let L := sphereTangentCoordinates (P u) hPu
  have htan (v : Ambient d) (hv : v ∈ D) : ⟪P u, S v⟫ = 0 :=
    (shifted_spherical_stereo_tangent_annulus hδ hδhalf ha hr hrhalf hu hv.1 hσ hv.2).1
  have hdist (x : Ambient d) (hx : x ∈ D) (y : Ambient d) (hy : y ∈ D) :
      dist (Ψ x) (Ψ y) = ‖S x - S y‖ := by
    rw [dist_eq_norm]
    change ‖L (S x) - L (S y)‖ = ‖S x - S y‖
    rw [← map_sub]
    have H := sphere_tangent_coordinates_inner hPu
      (show ⟪P u, S x - S y⟫ = 0 by rw [inner_sub_right, htan x hx, htan y hy, sub_self])
      (show ⟪P u, S x - S y⟫ = 0 by rw [inner_sub_right, htan x hx, htan y hy, sub_self])
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at H
    exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp H.le)
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp H.symm.le)
  intro A hA
  refine ⟨?_, ?_⟩
  · have H := volume_pushforward_le_of_lower_distance
      (shifted_stereo_chart_measurable δ a r u hPu) (D := A) (K := (16 : ℝ≥0)) ?_
    · simpa only [ENNReal.coe_ofNat] using H
    · intro x hx y hy
      rw [hdist x (hA hx) y (hA hy), dist_eq_norm]
      have h := (shifted_spherical_stereo_distance_bounds hδ hδhalf ha hr hrhalf hu
        (hA hx).1 (hA hy).1 hσ (hA hx).2 (hA hy).2).1
      change ‖x - y‖ / 16 ≤ ‖S x - S y‖ at h
      norm_num
      linarith
  · let K := Real.toNNReal (2 / σ ^ 2)
    have hLip : LipschitzOnWith K Ψ A := LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [hdist x (hA hx) y (hA hy), dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      have h := (shifted_spherical_stereo_distance_bounds hδ hδhalf ha hr hrhalf hu
        (hA hx).1 (hA hy).1 hσ (hA hx).2 (hA hy).2).2
      exact h.trans_eq (by ring)
    simpa only [K, ENNReal.ofNNReal_toNNReal] using volume_image_le_of_lipschitz_on hLip

theorem shifted_stereo_chart_lintegral_le {d : ℕ} {δ r σ : ℝ} {a u : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hu : ‖u‖ ≤ 1) (hσ : 0 < σ)
    (hPu : shiftedCapPoint δ a r u ≠ 0)
    {A : Set (Ambient d)} (hA : A ⊆ {v | ‖v‖ ≤ 1 ∧ σ ≤ ‖v - u‖})
    {G : Ambient d → ℝ≥0∞} (hG : Measurable G) :
    let Ψ := shiftedStereoChart δ a r u hPu
    (∫⁻ v in A, G (Ψ v)) ≤ (16 : ℝ≥0∞) ^ d * ∫⁻ W in Ψ '' A, G W := by
  intro Ψ
  rw [← lintegral_map hG (shifted_stereo_chart_measurable δ a r u hPu)]
  have H := ((shifted_stereo_chart_measure_bounds hδ hδhalf ha hr hrhalf hu hσ hPu) A hA).1
  simpa only [lintegral_smul_measure, smul_eq_mul] using
    (lintegral_mono' H (le_refl G))

/-- The transformed collision strip is expressed in the d-dimensional
Lebesgue coordinates used by the Radon estimate. -/
theorem shifted_collision_chart_strip {d : ℕ} {δ r σ ε : ℝ} {a u y w : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖u + y - w‖ ≤ 1)
    (hσ : 0 < σ) (hsepY : σ ≤ ‖y - u‖) (hsepW : σ ≤ ‖w - u‖)
    (hε : |shiftedCollisionPhase δ a r u y w| ≤ ε)
    (hPu : shiftedCapPoint δ a r u ≠ 0) :
    let Ψ := shiftedStereoChart δ a r u hPu
    let t := ‖Ψ y‖
    let θ := t⁻¹ • Ψ y
    ‖θ‖ = 1 ∧ (1 / 8 : ℝ) ≤ t ∧ t ≤ 1 / σ ∧
      |t - ⟪Ψ w, θ⟫| ≤ 6 * ε / σ ^ 4 := by
  intro Ψ t θ
  let P := shiftedCapPoint δ a r
  let Y := sphereStereo (δ * r) (P u) (P y)
  let W := sphereStereo (δ * r) (P u) (P w)
  let Θ := ‖Y‖⁻¹ • Y
  let L := sphereTangentCoordinates (P u) hPu
  obtain ⟨hΘ, hΘt, hWt, hYlo, hYhi, hstrip⟩ :=
    shifted_collision_radon_offset_strip hδ hδhalf ha hr hrhalf hu hy hw hz hσ hsepY hsepW hε
  have hYt : ⟪P u, Y⟫ = 0 :=
    (shifted_spherical_stereo_tangent_annulus hδ hδhalf ha hr hrhalf hu hy hσ hsepY).1
  have hnorm (x : Ambient (d + 1)) (hx : ⟪P u, x⟫ = 0) : ‖L x‖ = ‖x‖ := by
    have H := sphere_tangent_coordinates_inner hPu hx hx
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at H
    exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp H.le)
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp H.symm.le)
  have ht : t = ‖Y‖ := hnorm Y hYt
  have hθ : θ = L Θ := by
    change t⁻¹ • L Y = L (‖Y‖⁻¹ • Y)
    rw [ht, map_smul]
  have hpair : ⟪Ψ w, θ⟫ = ⟪W, Θ⟫ := by
    rw [hθ]
    exact sphere_tangent_coordinates_inner hPu hWt hΘt
  rw [hθ, hnorm Θ hΘt]
  exact ⟨hΘ, by rwa [ht], by rwa [ht],
    by rw [ht]; simpa only [hθ] using (show |‖Y‖ - ⟪Ψ w, θ⟫| ≤ _ by rw [hpair]; exact hstrip)⟩

/-- The Lebesgue measure of an actual spherical collision fiber is
controlled by the corresponding Euclidean Radon strip in the image patch. -/
theorem shifted_collision_fiber_measure_le {d : ℕ} {δ r σ ε : ℝ} {a u y : Ambient d}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (ha : ‖a‖ ≤ 1 / 2)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hu : ‖u‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hσ : 0 < σ) (hsepY : σ ≤ ‖y - u‖)
    (hPu : shiftedCapPoint δ a r u ≠ 0)
    {B : Set (Ambient d)} (hB : B ⊆ {w | ‖w‖ ≤ 1 ∧ σ ≤ ‖w - u‖}) :
    let Ψ := shiftedStereoChart δ a r u hPu
    let t := ‖Ψ y‖
    let θ := t⁻¹ • Ψ y
    volume (B ∩ {w | ‖u + y - w‖ ≤ 1 ∧ |shiftedCollisionPhase δ a r u y w| ≤ ε}) ≤
      (16 : ℝ≥0∞) ^ d * volume ((Ψ '' B) ∩ {W | |t - ⟪W, θ⟫| ≤ 6 * ε / σ ^ 4}) := by
  intro Ψ t θ
  let R : Set (Ambient d) := {W | |t - ⟪W, θ⟫| ≤ 6 * ε / σ ^ 4}
  have hR : MeasurableSet R := measurableSet_le (by fun_prop) measurable_const
  have hΨ := shifted_stereo_chart_measurable δ a r u hPu
  have hsub : B ∩ {w | ‖u + y - w‖ ≤ 1 ∧ |shiftedCollisionPhase δ a r u y w| ≤ ε} ⊆
      Ψ ⁻¹' R ∩ B := by
    intro w hw
    obtain ⟨hw₁, hw₂⟩ := hB hw.1
    exact ⟨(shifted_collision_chart_strip hδ hδhalf ha hr hrhalf hu hy hw₁ hw.2.1
      hσ hsepY hw₂ hw.2.2 hPu).2.2.2, hw.1⟩
  have hmap := ((shifted_stereo_chart_measure_bounds hδ hδhalf ha hr hrhalf hu hσ hPu) B hB).1
  calc
    _ ≤ volume (Ψ ⁻¹' R ∩ B) := measure_mono hsub
    _ = Measure.map Ψ (volume.restrict B) R := by
      rw [Measure.map_apply hΨ hR, Measure.restrict_apply (hR.preimage hΨ)]
    _ ≤ ((16 : ℝ≥0∞) ^ d • volume.restrict (Ψ '' B)) R := Measure.le_iff.mp hmap R hR
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hR, inter_comm]

end RestrictionWork
