import GhostConjecture.FormalPowerSeries
import Mathlib.Data.Real.Basic

namespace GhostConjecture

open scoped BigOperators

/-- Valuation lower bound on convolution coefficients. -/
lemma vp_coeff_mul_lower_bound {K : Type*} [Semiring K]
    (v : K → WithTop ℝ) (F G : K⟦t⟧) (n : ℕ) :
    v ((PowerSeries.coeff (R := K) n) (F * G)) ≥
      Finset.inf' (Finset.range (n + 1))
        (by
          refine ⟨0, ?_⟩
          simp)
        (fun i =>
          v ((PowerSeries.coeff (R := K) i) F) +
            v ((PowerSeries.coeff (R := K) (n - i)) G)) := by
  sorry

end GhostConjecture
