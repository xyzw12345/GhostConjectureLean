import Mathlib.RingTheory.PowerSeries.Basic
import GhostConjecture.FormalPowerSeries

namespace GhostConjecture

variable {R : Type*} [CommRing R]

/-- Coefficient formula for products of formal power series. -/
lemma coeff_mul (n : ℕ) (F G : R⟦t⟧) :
    PowerSeries.coeff n (F * G) =
      ∑ i in Finset.range (n + 1),
        PowerSeries.coeff i F * PowerSeries.coeff (n - i) G := by
  sorry

end GhostConjecture
