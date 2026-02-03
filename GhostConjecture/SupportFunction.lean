import Mathlib/Data/EReal/Basic

namespace GhostConjecture

/-- Support functional for lower convex sets. -/
noncomputable def supportFunctionLower (C : Set (ℝ × ℝ)) (λ : ℝ) : EReal :=
  sInf (Real.toEReal '' ((fun p : ℝ × ℝ => p.2 + λ * p.1) '' C))

end GhostConjecture
