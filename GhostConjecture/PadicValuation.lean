import Mathlib.NumberTheory.Padics.PadicNumbers

namespace GhostConjecture

/-- The standard `p`-adic valuation on `ℚ_[p]`, normalized by `v_p p = 1` and `v_p 0 = ∞`.

This is `Padic.addValuation` from Mathlib, viewed as a function `ℚ_[p] → WithTop ℤ`. -/
noncomputable abbrev vpQp (p : ℕ) [Fact p.Prime] : ℚ_[p] → WithTop ℤ :=
  Padic.addValuation (p := p)

end GhostConjecture

