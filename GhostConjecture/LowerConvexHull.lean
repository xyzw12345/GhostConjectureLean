import Mathlib/Analysis/Convex/Topology

open Set

namespace GhostConjecture

/-- A set in `R^2` is vertically upward closed if it contains all points above any of its points. -/
def VerticallyUpwardClosed (C : Set (ℝ × ℝ)) : Prop :=
  ∀ ⦃x y y' : ℝ⦄, (x, y) ∈ C → y' ≥ y → (x, y') ∈ C

/-- The lower convex hull of a set in `R^2` is the intersection of all closed convex
sets containing it that are vertically upward closed. -/
def LowerConvexHull (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  ⋂₀ { C : Set (ℝ × ℝ) |
    S ⊆ C ∧ IsClosed C ∧ Convex ℝ C ∧ VerticallyUpwardClosed C }

end GhostConjecture
