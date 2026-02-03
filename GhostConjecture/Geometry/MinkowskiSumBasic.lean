import Mathlib/Analysis/Convex/Topology
import GhostConjecture/Geometry/MinkowskiSum
import GhostConjecture/LowerConvexHull

namespace GhostConjecture

open Set

lemma minkowskiSum_basic_properties
    {A A' B B' C D : Set (ℝ × ℝ)} :
    (A ⊆ A' → B ⊆ B' → minkowskiSum A B ⊆ minkowskiSum A' B') ∧
    (IsClosed C → Convex ℝ C → IsClosed D → Convex ℝ D →
      IsClosed (minkowskiSum C D) ∧ Convex ℝ (minkowskiSum C D)) ∧
    (VerticallyUpwardClosed C → VerticallyUpwardClosed D →
      VerticallyUpwardClosed (minkowskiSum C D)) := by
  sorry

end GhostConjecture
