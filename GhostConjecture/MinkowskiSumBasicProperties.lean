import GhostConjecture.LowerConvexHull
import GhostConjecture.MinkowskiSum

namespace GhostConjecture

/-- Basic properties of Minkowski sums (monotonicity, preservation of closedness/convexity,
and preservation of vertical upward closedness). -/
lemma minkowskiSum_basic_properties :
    (∀ {A B A' B' : Set (ℝ × ℝ)},
        A ⊆ A' → B ⊆ B' → minkowskiSum A B ⊆ minkowskiSum A' B') ∧
      (∀ {C D : Set (ℝ × ℝ)},
        IsClosed C → Convex ℝ C → IsClosed D → Convex ℝ D →
          IsClosed (minkowskiSum C D) ∧ Convex ℝ (minkowskiSum C D)) ∧
        (∀ {C D : Set (ℝ × ℝ)},
          VerticalUpwardClosed C → VerticalUpwardClosed D →
            VerticalUpwardClosed (minkowskiSum C D)) := by
  sorry

end GhostConjecture

