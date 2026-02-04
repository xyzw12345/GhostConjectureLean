import Mathlib.Analysis.Convex.Topology

namespace GhostConjecture

/-- A subset `C ⊆ ℝ × ℝ` is *upward closed in the vertical direction* if whenever `(x, y) ∈ C`
and `y ≤ y'`, then `(x, y') ∈ C`. -/
def VerticalUpwardClosed (C : Set (ℝ × ℝ)) : Prop :=
  ∀ x y y' : ℝ, (x, y) ∈ C → y ≤ y' → (x, y') ∈ C

/-- **Lower convex hull** of a set `S ⊆ ℝ²` (modeled as `ℝ × ℝ`): the intersection of all closed
convex sets `C` with `S ⊆ C` that are upward closed in the vertical direction. -/
def LowerConvexHull (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  Set.sInter
    { C : Set (ℝ × ℝ) |
        IsClosed C ∧ Convex ℝ C ∧ S ⊆ C ∧ VerticalUpwardClosed C }

end GhostConjecture
