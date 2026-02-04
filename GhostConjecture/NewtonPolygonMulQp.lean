import GhostConjecture.NewtonPolygonMul
import GhostConjecture.vpQp

namespace GhostConjecture

/-!
## Product formula over `ℚ_[p]`
-/

/--
Product formula over `ℚ_[p]`: for `F, G : ℚ_[p]⟦t⟧`, the Newton polygon of `F * G` is the
Minkowski sum of the Newton polygons of `F` and `G`, with respect to the `p`-adic valuation.
-/
theorem NewtonPolygon_mul_Qp (p : ℕ) [Fact p.Prime] (F G : FormalPowerSeriesRing ℚ_[p]) :
    NewtonPolygon (vpQp p) (F * G) =
      minkowskiSum (NewtonPolygon (vpQp p) F) (NewtonPolygon (vpQp p) G) := by
  simpa using (NewtonPolygon_mul (v := vpQp p) F G)

end GhostConjecture

