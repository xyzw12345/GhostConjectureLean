import Mathlib

namespace GhostConjecture

open Set

/-- Minkowski sum of subsets of `ℝ × ℝ`. -/
def minkowskiSum (A B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}

end GhostConjecture
