
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Field.Basic

section

open Filter Set
open scoped Topology NNReal

section Real

-- theorem uniqueDiffOn_uIcc {a b : ℝ} (hab : a ≠ b) : UniqueDiffOn ℝ (uIcc a b) :=
--   uniqueDiffOn_Icc <| min_lt_max.mpr hab

-- -- maybe not needed
-- theorem uniqueDiffOn_uIoo (a b : ℝ) : UniqueDiffOn ℝ (uIoo a b) := uniqueDiffOn_Ioo _ _

-- -- maybe not needed
-- theorem uniqueDiffOn_uIoc (a b : ℝ) : UniqueDiffOn ℝ (uIoc a b) := uniqueDiffOn_Ioc _ _

end Real

end
