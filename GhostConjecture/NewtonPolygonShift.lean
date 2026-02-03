import GhostConjecture.NewtonPolygon
import GhostConjecture.Geometry.MinkowskiSum
import Mathlib.RingTheory.PowerSeries.Basic

open Set

namespace GhostConjecture

lemma newtonPolygon_tpow
    {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : K⟦t⟧) (k : ℕ) :
    NewtonPolygon v (PowerSeries.X ^ k * F) =
      minkowskiSum (NewtonPolygon v F) {((k : ℝ), (0 : ℝ))} := by
  sorry

end GhostConjecture

