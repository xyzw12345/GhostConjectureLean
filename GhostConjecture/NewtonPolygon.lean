import GhostConjecture.LowerConvexHull
import GhostConjecture.NewtonPoints

namespace GhostConjecture

/--
The **Newton polygon** of a formal power series `F` with respect to a non-archimedean valuation `v`
is the lower convex hull of its Newton points.

We model the Newton points in `ℝ × ℝ` by keeping only those points `(n, v (fₙ))` whose valuation is
finite (i.e. lies in the image of `ℝ` inside `WithTop ℝ`).
-/
def NewtonPolygon {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) : Set (ℝ × ℝ) :=
  LowerConvexHull
    { p : ℝ × ℝ |
        ∃ n : ℕ, ∃ r : ℝ, (n, (r : WithTop ℝ)) ∈ NewtonPoints v F ∧ p = ((n : ℝ), r) }

end GhostConjecture
