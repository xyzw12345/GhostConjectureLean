import GhostConjecture.TropicalWeight
import GhostConjecture.VpCoeffMulLowerBound

namespace GhostConjecture

open scoped BigOperators

/-!
## Multiplicativity of tropical weight
-/

variable {K : Type*} [Field K]

/--
For a non-archimedean valuation `v` on `K` and formal power series `F, G : K⟦t⟧`,
the tropical weight is multiplicative:

`w_{F*G}(λ) = w_F(λ) + w_G(λ)`.
-/
lemma tropicalWeight_mul (v : NonarchimedeanValuation K)
    (F G : FormalPowerSeriesRing K) (lam : ℝ) :
    tropicalWeight v (F * G) lam = tropicalWeight v F lam + tropicalWeight v G lam := by
  sorry

end GhostConjecture
