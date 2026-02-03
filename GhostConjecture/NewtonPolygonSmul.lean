import GhostConjecture.NewtonPolygon
import GhostConjecture.Geometry.MinkowskiSum

namespace GhostConjecture

lemma newtonPolygon_smul
    {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (c : K) (F : K⟦t⟧) (hc : c ≠ 0) :
    NewtonPolygon v (c • F) =
      minkowskiSum (NewtonPolygon v F)
        {((0 : ℝ), WithTop.recTopCoe 0 (fun r => r) (v.v c))} := by
  sorry

end GhostConjecture
