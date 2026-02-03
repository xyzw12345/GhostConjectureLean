import GhostConjecture.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace GhostConjecture

namespace NewtonPolygon

/-- Tropical weight of a power series `F(t) = ∑_{n≥0} fₙ tⁿ`
with respect to a valuation-like map `v`. -/
noncomputable def tropicalWeight {K : Type*} [Field K]
    (v : K → EReal) (F : PowerSeries K) (l : ℝ) : EReal :=
  sInf <|
    Set.range fun n : ℕ =>
      v ((PowerSeries.coeff (R := K) n) F) + ((l * (n : ℝ) : ℝ) : EReal)

end NewtonPolygon

end GhostConjecture
