import RestrictionWork.CapLiftDefinitions

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
namespace RestrictionWork

/-- The actual Euclidean inner product has precisely the graph phase. -/
theorem physical_cap_inner {d : ℕ} (δ : ℝ) (z : Ambient d × ℝ) (v : Ambient d) :
    ⟪physicalEmbed z, capPoint δ v⟫ =
      ⟪z.1, δ • v⟫ + z.2 * capHeight δ v := by
  simp only [PiLp.inner_apply, physicalEmbed, capPoint, WithLp.equiv_symm_apply, PiLp.toLp_apply,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    PiLp.smul_apply, smul_eq_mul]
  simp [RCLike.inner_apply, mul_comm]

end RestrictionWork
