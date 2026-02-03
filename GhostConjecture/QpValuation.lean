import Mathlib
import GhostConjecture.Valuation

namespace GhostConjecture

/-- The standard `p`-adic valuation on `Qp`, normalized by `v_p(p) = 1` and `v_p(0) = ∞`. -/
noncomputable def vpQp (p : ℕ) [Fact p.Prime] : NonarchimedeanValuation (Qp p) := by
  classical
  refine
    { v := fun _ => ⊤
      map_zero' := by
        -- Placeholder for the normalization `v_p(0) = ∞`.
        sorry
      map_one' := by
        sorry
      map_mul' := by
        intro x y
        sorry
      map_add' := by
        intro x y
        sorry }

end GhostConjecture
