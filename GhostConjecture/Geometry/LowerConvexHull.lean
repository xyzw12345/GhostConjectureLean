import Mathlib.Analysis.Convex.Topology

namespace GhostConjecture

/-- A set `C ⊆ ℝ × ℝ` is *vertically upward closed* if whenever `(x, y) ∈ C` and `y ≤ y'`,
then `(x, y') ∈ C`. This matches "downward closed in the vertical direction" in the blueprint. -/
def VerticalUpwardClosed (C : Set (ℝ × ℝ)) : Prop :=
  ∀ ⦃x y y' : ℝ⦄, (x, y) ∈ C → y ≤ y' → (x, y') ∈ C

/-- The **lower convex hull** of a set `S ⊆ ℝ²` is the intersection of all closed convex sets
containing `S` that are vertically upward closed. -/
def lowerConvexHull (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  Set.sInter {C : Set (ℝ × ℝ) |
    IsClosed C ∧ Convex ℝ C ∧ S ⊆ C ∧ VerticalUpwardClosed C}

end GhostConjecture
