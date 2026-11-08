import RestrictionWork.GraphRestrictedKnapp
import OAI.Analysis.Fourier.Restriction.BoundedInput
import OAI.Analysis.Fourier.BochnerRiesz.DualityNorm

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RestrictionWork

private theorem ofReal_two_rpow (t : ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ t) = (2 : ℝ≥0∞) ^ t := by
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

private theorem dyadic_mass_factorization (p j x : ℝ) (hx : 0 ≤ x) (A : ℝ≥0∞) :
    (2 : ℝ≥0∞) ^ j * A ^ x =
      ((2 : ℝ≥0∞) ^ (p * j) * A) ^ x * (2 : ℝ≥0∞) ^ (j - p * j * x) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hx, ← ENNReal.rpow_mul]
  calc
    _ = ((2 : ℝ≥0∞) ^ (p * j * x) * (2 : ℝ≥0∞) ^ (j - p * j * x)) * A ^ x := by
      rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      congr 2
      ring
    _ = _ := by ac_rfl

/-- Two neighboring restricted estimates on the Knapp line give exponential
decay in the signed combination of the two dyadic amplitude indices. -/
theorem knapp_dyadic_pair_decay {a z zl zh p q' b c : ℝ} (hx : p * (1 - a * z) = 1)
    (hz : q' * (1 - z) = 1) (hb : 0 ≤ b) (hb₁ : b ≤ 1)
    (hbl : b ≤ 1 - a * zl) (hbh : b ≤ 1 - a * zh)
    (hcl : 1 - b ≤ 1 - zl) (hch : 1 - b ≤ 1 - zh)
    (hclow : c ≤ z - zl) (hchigh : c ≤ zh - z)
    (j k : ℤ) {A B C P : ℝ≥0∞}
    (hA : (2 : ℝ≥0∞) ^ (p * (j : ℝ)) * A ≤ 1)
    (hB : (2 : ℝ≥0∞) ^ (q' * (k : ℝ)) * B ≤ 1)
    (hl : P ≤ C * ((2 : ℝ≥0∞) ^ (j : ℝ) * A ^ (1 - a * zl)) *
      ((2 : ℝ≥0∞) ^ (k : ℝ) * B ^ (1 - zl)))
    (hh : P ≤ C * ((2 : ℝ≥0∞) ^ (j : ℝ) * A ^ (1 - a * zh)) *
      ((2 : ℝ≥0∞) ^ (k : ℝ) * B ^ (1 - zh))) :
    P ≤ C * (((2 : ℝ≥0∞) ^ (p * (j : ℝ)) * A) ^ b *
      ((2 : ℝ≥0∞) ^ (q' * (k : ℝ)) * B) ^ (1 - b)) *
      ENNReal.ofReal ((2 : ℝ) ^ (-c * |a * p * (j : ℝ) + q' * (k : ℝ)|)) := by
  let α := (2 : ℝ≥0∞) ^ (p * (j : ℝ)) * A
  let β := (2 : ℝ≥0∞) ^ (q' * (k : ℝ)) * B
  let u : ℝ := a * p * j + q' * k
  change P ≤ C * (α ^ b * β ^ (1 - b)) * ENNReal.ofReal ((2 : ℝ) ^ (-c * |u|))
  rw [ofReal_two_rpow]
  have hbound (zi : ℝ) (hbz : b ≤ 1 - a * zi) (hcz : 1 - b ≤ 1 - zi)
      (hi : P ≤ C * ((2 : ℝ≥0∞) ^ (j : ℝ) * A ^ (1 - a * zi)) *
        ((2 : ℝ≥0∞) ^ (k : ℝ) * B ^ (1 - zi))) :
      P ≤ C * (α ^ b * β ^ (1 - b)) * (2 : ℝ≥0∞) ^ ((zi - z) * u) := by
    let v := (j : ℝ) - p * (j : ℝ) * (1 - a * zi)
    let w := (k : ℝ) - q' * (k : ℝ) * (1 - zi)
    have hv : v = (zi - z) * (a * p * (j : ℝ)) := by
      dsimp [v]
      linear_combination -(j : ℝ) * hx
    have hw : w = (zi - z) * (q' * (k : ℝ)) := by
      dsimp [w]
      linear_combination -(k : ℝ) * hz
    have hsum : v + w = (zi - z) * u := by rw [hv, hw, ← mul_add]
    calc
      _ ≤ C * ((2 : ℝ≥0∞) ^ (j : ℝ) * A ^ (1 - a * zi)) *
          ((2 : ℝ≥0∞) ^ (k : ℝ) * B ^ (1 - zi)) := hi
      _ = C * (α ^ (1 - a * zi) * β ^ (1 - zi)) * (2 : ℝ≥0∞) ^ ((zi - z) * u) := by
        rw [dyadic_mass_factorization p (j : ℝ) _ (hb.trans hbz),
          dyadic_mass_factorization q' (k : ℝ) _ ((sub_nonneg.mpr hb₁).trans hcz),
          ← hsum, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
        change C * (α ^ (1 - a * zi) * (2 : ℝ≥0∞) ^ v) *
          (β ^ (1 - zi) * (2 : ℝ≥0∞) ^ w) = _
        ac_rfl
      _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl
        (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hA hbz)
          (ENNReal.rpow_le_rpow_of_exponent_ge hB hcz))) le_rfl
  by_cases hu : 0 ≤ u
  · refine (hbound zl hbl hcl hl).trans (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_))
    rw [abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_right (by linarith) hu
  · have hun : u < 0 := lt_of_not_ge hu
    refine (hbound zh hbh hch hh).trans (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_))
    rw [abs_of_neg hun, mul_neg, ← neg_mul, neg_neg]
    exact mul_le_mul_of_nonpos_right hchigh hun.le

private theorem graph_extension_atom_smul {d : ℕ} (c : ℝ)
    (f : Ambient d → ℂ) (φ : Ambient d → ℝ) :
    graphExtension (c • f) φ = c • graphExtension f φ := by
  funext z
  simp only [graphExtension, phaseExtension, Pi.smul_apply, smul_mul_assoc, integral_smul]

private theorem graph_extension_atom_bound {d : ℕ} {δ : ℝ} {A : Set (Ambient d)}
    {f : Ambient d → ℂ} (hf : Measurable f) {m : ℝ} (hm : 0 < m)
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => m) u) {P C : ℝ≥0∞} {x : ℝ}
    (H : ∀ {F : Ambient d → ℂ}, Measurable F →
      (∀ u, ‖F u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
      eLpNorm (graphExtension F (sphericalGraphPhase δ)) P volume ≤ C * volume A ^ x) :
    eLpNorm (graphExtension f (sphericalGraphPhase δ)) P volume ≤
      ENNReal.ofReal m * (C * volume A ^ x) := by
  let F := m⁻¹ • f
  have hF : Measurable F := hf.const_smul _
  have hFb (u : Ambient d) : ‖F u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u := by
    have h := mul_le_mul_of_nonneg_left (hfb u) (inv_nonneg.mpr hm.le)
    rw [show F u = m⁻¹ • f u from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hm)]
    by_cases hu : u ∈ A
    · simpa only [indicator_of_mem hu, inv_mul_cancel₀ hm.ne'] using h
    · simpa only [indicator_of_notMem hu, mul_zero] using h
  have he : m • F = f := by
    simp only [F, smul_smul, mul_inv_cancel₀ hm.ne', one_smul]
  rw [← he, graph_extension_atom_smul, eLpNorm_const_smul,
    ← ofReal_norm m, Real.norm_of_nonneg hm.le]
  exact mul_le_mul' le_rfl (H hF hFb)

private theorem graph_extension_atom_integrable {d : ℕ} {A : Set (Ambient d)}
    (hA : MeasurableSet A) (hAb : A ⊆ Metric.ball 0 (1 / 4))
    {f : Ambient d → ℂ} (hf : Measurable f) {m : ℝ}
    (hfb : ∀ u, ‖f u‖ ≤ A.indicator (fun _ => m) u) :
    Integrable f (patchMeasure d) := by
  have hAt : volume A < ⊤ := (measure_mono hAb).trans_lt measure_ball_lt_top
  have hi : Integrable (A.indicator (fun _ => m)) :=
    (integrableOn_const hAt.ne).integrable_indicator hA
  exact (hi.mono' hf.aestronglyMeasurable (.of_forall hfb)).restrict

/-- Pairing between actual dyadic atoms of the graph data and the dual test
function, with the decay obtained from the neighboring restricted bounds. -/
theorem spherical_graph_knapp_atom_pairing_le {d : ℕ} (hd : 2 ≤ d)
    {y yl yh p q' b c : ℝ} (hyl : 0 < yl) (hly : yl < y) (hyh : y < yh)
    (hyD : yh < (d : ℝ) / ((d : ℝ) + 1))
    (hx : p * knappProductInput d y = 1) (hz : q' * (1 - y / 2) = 1)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1)
    (hbl : b ≤ knappProductInput d yl) (hbh : b ≤ knappProductInput d yh)
    (hcl : 1 - b ≤ 1 - yl / 2) (hch : 1 - b ≤ 1 - yh / 2)
    (hclow : c ≤ y / 2 - yl / 2) (hchigh : c ≤ yh / 2 - y / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
      ∀ (j k : ℤ) {A : Set (Ambient d)} {B : Set (Ambient d × ℝ)},
        MeasurableSet A → A ⊆ Metric.ball 0 (1 / 4) → MeasurableSet B →
      ∀ {f : Ambient d → ℂ} {g : Ambient d × ℝ → ℂ}, Measurable f → Measurable g →
        (∀ u, ‖f u‖ ≤ A.indicator (fun _ => (2 : ℝ) ^ ((j : ℝ) + 1)) u) →
        (∀ z, ‖g z‖ ≤ B.indicator (fun _ => (2 : ℝ) ^ ((k : ℝ) + 1)) z) →
        (2 : ℝ≥0∞) ^ (p * (j : ℝ)) * volume A ≤ 1 →
        (2 : ℝ≥0∞) ^ (q' * (k : ℝ)) * volume B ≤ 1 →
        ‖∫ z, g z * graphExtension f (sphericalGraphPhase δ) z‖ₑ ≤
          C * (((2 : ℝ≥0∞) ^ (p * (j : ℝ)) * volume A) ^ b *
            ((2 : ℝ≥0∞) ^ (q' * (k : ℝ)) * volume B) ^ (1 - b)) *
          ENNReal.ofReal ((2 : ℝ) ^
            (-c * |((d : ℝ) + 2) / d * p * (j : ℝ) + q' * (k : ℝ)|)) := by
  let a : ℝ := ((d : ℝ) + 2) / d
  have he (t : ℝ) : knappProductInput d t = 1 - a * (t / 2) := by
    unfold knappProductInput a
    ring
  have hhl : yl < (d : ℝ) / ((d : ℝ) + 1) := hly.trans (hyh.trans hyD)
  have hhh : 0 < yh := hyl.trans (hly.trans hyh)
  obtain ⟨Cl, hCl, Hl⟩ := spherical_graph_restricted_knapp_linear hd hyl hhl
  obtain ⟨Ch, hCh, Hh⟩ := spherical_graph_restricted_knapp_linear hd hhh hyD
  let C := 4 * max Cl Ch
  have hC : C < ⊤ := ENNReal.mul_lt_top (by norm_num) (max_lt hCl hCh)
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ₁ j k A B hA hAb hB f g hf hg hfb hgb hα hβ
  have hφ : Measurable (sphericalGraphPhase δ (d := d)) := by
    unfold sphericalGraphPhase sphericalPhase
    fun_prop
  have hfi := graph_extension_atom_integrable hA hAb hf hfb
  have hE : AEStronglyMeasurable (graphExtension f (sphericalGraphPhase δ)) volume :=
    (graph_extension_continuous hfi hφ).aestronglyMeasurable
  have htop : yh < 2 := by
    have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    exact hyD.trans ((div_lt_iff₀ (by positivity)).mpr (by linarith))
  have hside {yi : ℝ} (hyi : 0 < yi) (hyi' : yi < 2) {Ci : ℝ≥0∞}
      (hCi : Ci ≤ max Cl Ch)
      (Hi : ∀ {F : Ambient d → ℂ}, Measurable F →
        (∀ u, ‖F u‖ ≤ A.indicator (fun _ => (1 : ℝ)) u) →
        eLpNorm (graphExtension F (sphericalGraphPhase δ)) (ENNReal.ofReal (2 / yi)) volume ≤
          Ci * volume A ^ knappProductInput d yi) :
      ‖∫ z, g z * graphExtension f (sphericalGraphPhase δ) z‖ₑ ≤
        C * ((2 : ℝ≥0∞) ^ (j : ℝ) * volume A ^ (1 - a * (yi / 2))) *
          ((2 : ℝ≥0∞) ^ (k : ℝ) * volume B ^ (1 - yi / 2)) := by
    let s : ℝ := (1 - yi / 2)⁻¹
    have hs₀ : 0 < 1 - yi / 2 := by linarith
    have hs : 1 < s := one_lt_inv₀ hs₀ |>.mpr (by linarith)
    have hc : s.HolderConjugate (2 / yi) := by
      refine (Real.holderConjugate_iff.mpr ⟨hs, ?_⟩)
      unfold s
      rw [inv_inv, inv_div]
      ring
    have hg1 (z : Ambient d × ℝ) : ‖g z‖ ≤ (2 : ℝ) ^ ((k : ℝ) + 1) :=
      (hgb z).trans (by by_cases hz : z ∈ B <;> simp [hz, Real.rpow_nonneg])
    have hg0 (z : Ambient d × ℝ) (hz : z ∉ B) : g z = 0 := by
      have H := hgb z
      rw [indicator_of_notMem hz] at H
      exact norm_eq_zero.mp (le_antisymm H (norm_nonneg _))
    have hgN := OAI.Analysis.Fourier.Restriction.eLpNorm_le_bound_mul_measure
      volume hg.aestronglyMeasurable hB (by positivity) hg1 hg0 (zero_lt_one.trans hs)
    rw [show 1 / s = 1 - yi / 2 by simp only [s, one_div, inv_inv], ofReal_two_rpow] at hgN
    have hfN := graph_extension_atom_bound hf (by positivity) hfb Hi
    rw [he, ofReal_two_rpow] at hfN
    calc
      _ ≤ _ := OAI.Analysis.Fourier.BochnerRiesz.enorm_integral_mul_le_eLpNorm
        volume hg.aestronglyMeasurable hE hc
      _ ≤ ((2 : ℝ≥0∞) ^ ((k : ℝ) + 1) * volume B ^ (1 - yi / 2)) *
          ((2 : ℝ≥0∞) ^ ((j : ℝ) + 1) * (Ci * volume A ^ (1 - a * (yi / 2)))) :=
        mul_le_mul' hgN hfN
      _ ≤ _ := by
        rw [ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
          ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, ENNReal.rpow_one]
        change _ ≤ (4 * max Cl Ch) * ((2 : ℝ≥0∞) ^ (j : ℝ) * volume A ^ (1 - a * (yi / 2))) *
          ((2 : ℝ≥0∞) ^ (k : ℝ) * volume B ^ (1 - yi / 2))
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
        calc
          _ = (2 * 2 * Ci) * ((2 : ℝ≥0∞) ^ (j : ℝ) * volume A ^ (1 - a * (yi / 2))) *
              ((2 : ℝ≥0∞) ^ (k : ℝ) * volume B ^ (1 - yi / 2)) := by ac_rfl
          _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hCi) le_rfl) le_rfl
  rw [he] at hx hbl hbh
  exact knapp_dyadic_pair_decay hx hz hb hb₁ hbl hbh hcl hch hclow hchigh j k hα hβ
    (hside hyl ((hly.trans hyh).trans htop) (le_max_left _ _) (Hl hδ hδ₁ hA hAb))
    (hside hhh htop (le_max_right _ _) (Hh hδ hδ₁ hA hAb))

end RestrictionWork
