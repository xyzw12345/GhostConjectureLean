import GhostConjecture.NewtonPolygon
import GhostConjecture.MinkowskiSum

namespace GhostConjecture

/-!
## Newton polygon of a product
-/

/--
Newton polygon of a product: for `F, G : K⟦t⟧`,
`NP(F * G) = NP(F) + NP(G)` as subsets of `ℝ × ℝ`.
-/
theorem NewtonPolygon_mul {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F G : FormalPowerSeriesRing K) :
    NewtonPolygon v (F * G) = minkowskiSum (NewtonPolygon v F) (NewtonPolygon v G) := by
  sorry

end GhostConjecture
