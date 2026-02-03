import GhostConjecture.Geometry.LowerConvexHull
import GhostConjecture.MinkowskiSum
import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace GhostConjecture

open scoped Pointwise

/-- Basic properties of Minkowski sums and vertical lower hull closures (blueprint lemma
`lem:lch_minkowski_basic`). -/
lemma lch_minkowski_basic
    {A A' B B' C D : Set (ℝ × ℝ)} :
    (A ⊆ A' → B ⊆ B' → minkowskiSum A B ⊆ minkowskiSum A' B') ∧
      (IsClosed C → Convex ℝ C → IsClosed D → Convex ℝ D →
        IsClosed (minkowskiSum C D) ∧ Convex ℝ (minkowskiSum C D)) ∧
      (VerticalUpwardClosed C →
        VerticalUpwardClosed D →
          VerticalUpwardClosed (minkowskiSum C D)) := by
  sorry

end GhostConjecture
