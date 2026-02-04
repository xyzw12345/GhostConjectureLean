import GhostConjecture.NonarchimedeanValuation
import GhostConjecture.CoeffMul
import Mathlib.Data.Finset.Lattice.Fold

namespace GhostConjecture

variable {K : Type*} [Field K]

/--
Valuation lower bound on convolution coefficients: for a non-archimedean valuation `v` and
formal power series `F, G`, the valuation of the `n`-th coefficient of `F * G` is bounded below
by the minimum of the valuations of the products of coefficients contributing to that coefficient.
-/
lemma vp_coeff_mul_lower_bound (v : NonarchimedeanValuation K)
    (F G : FormalPowerSeriesRing K) (n : ℕ) :
    v (PowerSeries.coeff n (F * G))
      ≥ Finset.inf' (Finset.range n.succ)
          (by
            refine ⟨0, ?_⟩
            simp)
          (fun i => v (PowerSeries.coeff i F) + v (PowerSeries.coeff (n - i) G)) := by
  sorry

end GhostConjecture
