import GhostConjecture.NewtonPolygon
import GhostConjecture.Geometry.MinkowskiSum
import GhostConjecture.SupportNewtonPolygon
import GhostConjecture.TropicalWeightMul
import GhostConjecture.SupportFunctionMinkowski

namespace GhostConjecture

/-- Newton polygon of a product is the Minkowski sum of Newton polygons. -/
theorem NewtonPolygon_mul {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F G : K⟦t⟧) :
    NewtonPolygon v (F * G) =
      minkowskiSum (NewtonPolygon v F) (NewtonPolygon v G) := by
  sorry

end GhostConjecture
