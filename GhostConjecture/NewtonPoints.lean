import GhostConjecture.NonarchimedeanValuation
import GhostConjecture.FormalPowerSeriesRing

namespace GhostConjecture

/--
The set of Newton points of a formal power series `F = ∑ fₙ tⁿ` with respect to a
non-archimedean valuation `v` is the set of pairs `(n, v (fₙ))` for all indices `n`
whose coefficient `fₙ` is nonzero.
-/
def NewtonPoints {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) : Set (ℕ × WithTop ℝ) :=
  {p | ∃ n : ℕ, PowerSeries.coeff n F ≠ (0 : K) ∧ p = (n, v (PowerSeries.coeff n F))}

end GhostConjecture
