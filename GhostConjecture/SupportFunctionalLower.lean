import Mathlib.Data.EReal.Basic

namespace GhostConjecture

noncomputable section

/-- Support functional for subsets of `ℝ × ℝ`.

For `C ⊆ ℝ²` and `l : ℝ`, `supportFunctionalLower C l` is the extended-real infimum of
`y + l * x` over `(x, y) ∈ C`. -/
def supportFunctionalLower (C : Set (ℝ × ℝ)) (l : ℝ) : EReal :=
  sInf ((fun p : ℝ × ℝ => ((p.2 + l * p.1 : ℝ) : EReal)) '' C)

end

end GhostConjecture
