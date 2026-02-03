import GhostConjecture.Valuation
import GhostConjecture.FormalPowerSeries

namespace GhostConjecture

/--
Newton points of a formal power series over a non-archimedean valued field.
-/
def NewtonPoints {K : Type*} [Field K] (v : NonarchimedeanValuation K) (F : K⟦t⟧) :
    Set (ℕ × WithTop ℝ) :=
  {p | ∃ n : ℕ, p = (n, v.v (PowerSeries.coeff F n)) ∧ PowerSeries.coeff F n ≠ 0}

end GhostConjecture
