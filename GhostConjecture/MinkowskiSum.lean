import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Operations

namespace GhostConjecture

/-- For subsets `A, B ⊆ ℝ²`, their *Minkowski sum* is `{a + b | a ∈ A, b ∈ B}`. -/
def minkowskiSum (A B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  Set.image2 (· + ·) A B

end GhostConjecture
