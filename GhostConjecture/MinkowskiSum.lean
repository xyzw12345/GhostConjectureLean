import Mathlib.Data.Real.Basic

namespace GhostConjecture

/-- Minkowski sum of subsets of `ℝ × ℝ`. -/
def minkowskiSum (A B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | ∃ a ∈ A, ∃ b ∈ B, a + b = x}

end GhostConjecture

