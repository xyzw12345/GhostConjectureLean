import GhostConjecture.NewtonPoints
import GhostConjecture.Geometry.LowerConvexHull

namespace GhostConjecture

namespace NewtonPolygon

/-- The Newton polygon of a power series `F` (with respect to a valuation `v`) is the lower convex
hull of its Newton points, viewed in `ℝ × ℝ` by discarding points with value `⊤`. -/
def newtonPolygon {K : Type*} [Field K] (v : K → WithTop ℝ) (F : PowerSeries K) : Set (ℝ × ℝ) :=
  lowerConvexHull {p : ℝ × ℝ |
    ∃ n : ℕ, ∃ r : ℝ, (n, (some r : WithTop ℝ)) ∈ newtonPoints v F ∧ p = ((n : ℝ), r)}

end NewtonPolygon

end GhostConjecture
