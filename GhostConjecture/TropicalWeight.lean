import GhostConjecture.Valuation
import GhostConjecture.FormalPowerSeries

namespace GhostConjecture

/-- Tropical weight of a formal power series at a real parameter `λ`. -/
def tropicalWeight {K : Type*} [Field K]
    (v : NonarchimedeanValuation K) (F : FormalPowerSeriesRing K) (λ : ℝ) : WithTop ℝ :=
  ⨅ n : ℕ, v.v (PowerSeries.coeff (R := K) n F) + ((λ * (n : ℝ)) : WithTop ℝ)

end GhostConjecture
