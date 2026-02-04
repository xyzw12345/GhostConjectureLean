import GhostConjecture.NonarchimedeanValuation
import GhostConjecture.FormalPowerSeriesRing
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace GhostConjecture

open scoped BigOperators

/--
For a non-archimedean valued field `(K, v)` and a formal power series
`F(t) = ∑ fₙ tⁿ`, the *tropical weight* at `λ : ℝ` is

`w_F(λ) := infₙ (v(fₙ) + λ * n)`,

viewed in `ℝ ∪ { -∞, ∞ }` (implemented as `WithTop (WithBot ℝ)`).
-/
noncomputable def tropicalWeight {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) (lam : ℝ) : WithTop (WithBot ℝ) :=
  ⨅ n : ℕ,
    WithTop.map (fun r : ℝ => (r : WithBot ℝ))
        (v ((PowerSeries.coeff (R := K) n) F)) +
      (lam * (n : ℝ))

end GhostConjecture
