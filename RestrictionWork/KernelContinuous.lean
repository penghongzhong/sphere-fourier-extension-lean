import RestrictionWork.Definitions
import Mathlib.Tactic.FunProp

set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace RestrictionWork

theorem kernel_continuous {n : ℕ} (x : Ambient n) :
    Continuous (kernel x) := by
  unfold kernel
  fun_prop


end RestrictionWork
