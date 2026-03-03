import GhostConjecture.FormalPowerSeriesRing
import Mathlib.Algebra.BigOperators.NatAntidiagonal

namespace GhostConjecture

open scoped BigOperators

universe u

/-- Coefficient formula for products in `R⟦X⟧` (Cauchy product). -/
lemma coeff_mul {R : Type u} [CommRing R] (F G : FormalPowerSeriesRing R) (n : ℕ) :
    PowerSeries.coeff n (F * G)
      = ∑ i ∈ Finset.range n.succ,
          PowerSeries.coeff i F * PowerSeries.coeff (n - i) G := by
  simpa [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using
    (PowerSeries.coeff_mul (n := n) F G)

end GhostConjecture

