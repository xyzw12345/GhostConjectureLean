import GhostConjecture.TropicalWeight
import GhostConjecture.ValuationCoeffMul

namespace GhostConjecture

variable {K : Type*} [Field K]

/-- Tropical weight is multiplicative. -/
lemma tropicalWeight_mul (v : NonarchimedeanValuation K) (F G : K⟦t⟧) (λ : ℝ) :
    tropicalWeight v (F * G) λ = tropicalWeight v F λ + tropicalWeight v G λ := by
  sorry

end GhostConjecture
