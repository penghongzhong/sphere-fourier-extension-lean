import RestrictionWork.SphereRotations
import RestrictionWork.Target

set_option autoImplicit false

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace RestrictionWork

/-- A strong estimate on one nonempty spherical ball yields a strong
estimate on the full sphere through isometries and a compact finite cover. -/
theorem boundedSphereExtension_of_ball_bound {n : ℕ} {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (pole : UnitSphere n) {ε : ℝ} (hε : 0 < ε)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hlocal : ∀ f : UnitSphere n → ℂ, Measurable f → MemLp f p (sphereMeasure n) →
      (∀ w, w ∉ Metric.ball pole ε → f w = 0) →
      eLpNorm (extension f) q volume ≤ C * eLpNorm f p (sphereMeasure n)) :
    BoundedSphereExtension n p q := by
  classical
  let : IsFiniteMeasure (sphereMeasure n) := by
    unfold sphereMeasure
    infer_instance
  have hball (z : UnitSphere n) (f : UnitSphere n → ℂ) (hm : Measurable f)
      (hf : MemLp f p (sphereMeasure n)) (hs : ∀ w, w ∉ Metric.ball z ε → f w = 0) :
      eLpNorm (extension f) q volume ≤ C * eLpNorm f p (sphereMeasure n) := by
    obtain ⟨e, he⟩ := exists_sphere_isometry_apply pole z
    let g := f ∘ sphereIsometry e
    have hpres := sphere_isometry_measurePreserving e
    have hg : MemLp g p (sphereMeasure n) := hf.comp_measurePreserving hpres
    have hgs (w : UnitSphere n) (hw : w ∉ Metric.ball pole ε) : g w = 0 := by
      apply hs
      rwa [← he, Metric.mem_ball, (sphere_isometry_isometry e).dist_eq, ← Metric.mem_ball]
    have H := hlocal g (hm.comp hpres.measurable) hg hgs
    rw [eLpNorm_extension_comp_sphereIsometry e (hf.integrable hp),
      eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hpres] at H
    exact H
  have hfinite (s : Finset (UnitSphere n)) : ∀ (f : UnitSphere n → ℂ), Measurable f →
      MemLp f p (sphereMeasure n) →
      (∀ w, (∀ i ∈ s, w ∉ Metric.ball i ε) → f w = 0) →
      eLpNorm (extension f) q volume ≤ ((s.card : ℝ≥0∞) * C) *
        eLpNorm f p (sphereMeasure n) := by
    induction s using Finset.induction_on with
    | empty =>
        intro f _ _ h
        have hf0 : f = 0 := funext fun w => h w (by simp)
        subst f
        have hext0 : extension (0 : UnitSphere n → ℂ) = (0 : Ambient n → ℂ) := by
          funext x
          simp [extension]
        simp [hext0]
    | @insert i s hi ih =>
        intro f hm hf hs
        let B := Metric.ball i ε
        let g := B.indicator f
        let h := Bᶜ.indicator f
        have hB : MeasurableSet B := measurableSet_ball
        have hgm : Measurable g := hm.indicator hB
        have hhm : Measurable h := hm.indicator hB.compl
        have hg : MemLp g p (sphereMeasure n) := hf.indicator hB
        have hh : MemLp h p (sphereMeasure n) := hf.indicator hB.compl
        have hgs (w : UnitSphere n) (hw : w ∉ B) : g w = 0 :=
          indicator_of_notMem hw _
        have hhs (w : UnitSphere n) (hw : ∀ z ∈ s, w ∉ Metric.ball z ε) : h w = 0 := by
          by_cases hb : w ∈ B
          · exact indicator_of_notMem (by simpa only [mem_compl_iff, not_not] using hb) _
          · have hz : f w = 0 := hs w (by
              intro j hj
              rcases Finset.mem_insert.mp hj with rfl | hj
              · exact hb
              · exact hw j hj)
            simp [h, hz]
        have hG := hball i g hgm hg hgs
        have hH := ih h hhm hh hhs
        have hgn : eLpNorm g p (sphereMeasure n) ≤ eLpNorm f p (sphereMeasure n) :=
          eLpNorm_mono hgm.aestronglyMeasurable (fun w => norm_indicator_le_norm_self _ w)
        have hhn : eLpNorm h p (sphereMeasure n) ≤ eLpNorm f p (sphereMeasure n) :=
          eLpNorm_mono hhm.aestronglyMeasurable (fun w => norm_indicator_le_norm_self _ w)
        have hsum : extension f = extension g + extension h := by
          funext x
          change (∫ w, f w * kernel x w ∂sphereMeasure n) =
            (∫ w, g w * kernel x w ∂sphereMeasure n) +
              ∫ w, h w * kernel x w ∂sphereMeasure n
          rw [← integral_add (integrable_kernel_product (hg.integrable hp) x)
            (integrable_kernel_product (hh.integrable hp) x)]
          apply integral_congr_ae
          exact .of_forall fun w => by_cases
            (fun hb : w ∈ B => by simp [g, h, hb])
            (fun hb : w ∉ B => by simp [g, h, hb])
        rw [hsum]
        calc
          _ ≤ eLpNorm (extension g) q volume + eLpNorm (extension h) q volume :=
            eLpNorm_add_le hq
          _ ≤ C * eLpNorm f p (sphereMeasure n) +
              ((s.card : ℝ≥0∞) * C) * eLpNorm f p (sphereMeasure n) :=
            add_le_add (hG.trans (mul_le_mul' le_rfl hgn))
              (hH.trans (mul_le_mul' le_rfl hhn))
          _ = _ := by
            rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
              add_mul, add_comm]
  let : CompactSpace (UnitSphere n) :=
    inferInstanceAs (CompactSpace (Metric.sphere (0 : Ambient n) 1))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i : UnitSphere n => Metric.ball i ε) (fun _ => Metric.isOpen_ball) (by
      intro w _
      exact Set.mem_iUnion.mpr ⟨w, Metric.mem_ball_self hε⟩)
  have hD : (s.card : ℝ≥0∞) * C < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hC
  refine ⟨((s.card : ℝ≥0∞) * C).toNNReal, ?_⟩
  intro f hf
  let g := hf.aestronglyMeasurable.mk f
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[sphereMeasure n] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g p (sphereMeasure n) := (memLp_congr_ae hfg).mp hf
  have hS : ∀ w : UnitSphere n, (∀ i ∈ s, w ∉ Metric.ball i ε) → g w = 0 := by
    intro w hw
    obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ w))
    exact (hw i hi hwi).elim
  have hnorm := hfinite s g hgm hg hS
  have he : extension f = extension g := by
    funext x
    apply integral_congr_ae
    filter_upwards [hfg] with w hw
    rw [hw]
  rw [← eLpNorm_congr_ae hfg, ← he] at hnorm
  refine ⟨hnorm.trans_lt (ENNReal.mul_lt_top hD hf.eLpNorm_lt_top), ?_⟩
  rw [ENNReal.coe_toNNReal hD.ne]
  exact hnorm

end RestrictionWork
