import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace GhostConjecture

/-- Newton points of a power series with respect to a valuation `v`. -/
def newtonPoints {K : Type*} [Field K] (v : K → WithTop ℝ) (F : PowerSeries K) :
    Set (ℕ × WithTop ℝ) :=
  {p |
    ∃ n : ℕ,
      PowerSeries.coeff (R := K) n F ≠ 0 ∧ p = (n, v (PowerSeries.coeff (R := K) n F))}

end GhostConjecture
