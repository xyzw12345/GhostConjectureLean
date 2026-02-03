import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic

namespace GhostConjecture

open scoped BigOperators

universe u

/-- The (one-variable) ring of formal power series over `R`, written `R⟦t⟧`. -/
abbrev FormalPowerSeriesRing (R : Type u) [Semiring R] : Type u :=
  PowerSeries R

notation:100 R "⟦t⟧" => FormalPowerSeriesRing R

lemma coeff_mul {K : Type*} [Semiring K] (F G : K⟦t⟧) (n : ℕ) :
    (PowerSeries.coeff (R := K) n) (F * G) =
      ∑ i ∈ Finset.range (n + 1),
        (PowerSeries.coeff (R := K) i) F * (PowerSeries.coeff (R := K) (n - i)) G := by
  refine (PowerSeries.coeff_mul (R := K) n F G).trans ?_
  simpa [Nat.succ_eq_add_one] using
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j =>
        (PowerSeries.coeff (R := K) i) F * (PowerSeries.coeff (R := K) j) G) n)

end GhostConjecture
