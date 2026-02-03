import GhostConjecture.Valuation
import GhostConjecture.FormalPowerSeriesCoeff

namespace GhostConjecture

variable {K : Type*} [Field K]

/-- Valuation lower bound on convolution coefficients. -/
lemma vp_coeff_mul_lower_bound (v : NonarchimedeanValuation K) (F G : K⟦t⟧) (n : ℕ) :
    v.v (PowerSeries.coeff n (F * G)) ≥
      (Finset.range (n + 1)).inf'
        (Finset.nonempty_range_add_one)
        (fun i => v.v (PowerSeries.coeff i F) + v.v (PowerSeries.coeff (n - i) G)) := by
  sorry

end GhostConjecture
