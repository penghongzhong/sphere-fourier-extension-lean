import RestrictionWork.PatchGraphMeasure

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
namespace RestrictionWork

def patchGraphPoint {d : ℕ} (φ : Ambient d → ℝ) (v : Ambient d) : Ambient (d + 1) :=
  euclideanSliceEquiv (Fin.last d) (v, φ v)

theorem measurable_patch_graph_point {d : ℕ} {φ : Ambient d → ℝ} (hφ : Measurable φ) :
    Measurable (patchGraphPoint φ) :=
  (euclideanSliceEquiv (Fin.last d)).measurable.comp (measurable_id.prodMk hφ)

/-- The open union of radius-`h` balls about the actual parameter patch. -/
def patchGraphTube {d : ℕ} (φ : Ambient d → ℝ) (h : ℝ) : Set (Ambient (d + 1)) :=
  ⋃ v ∈ ball (0 : Ambient d) 1, ball (patchGraphPoint φ v) h

theorem measurable_set_patch_graph_tube {d : ℕ} (φ : Ambient d → ℝ) (h : ℝ) :
    MeasurableSet (patchGraphTube φ h) :=
  (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball).measurableSet

theorem patch_graph_tube_mem_iff {d : ℕ} {φ : Ambient d → ℝ} {h : ℝ}
    {x : Ambient (d + 1)} :
    x ∈ patchGraphTube φ h ↔
      ∃ v ∈ ball (0 : Ambient d) 1, x ∈ ball (patchGraphPoint φ v) h := by
  simp [patchGraphTube]

end RestrictionWork
