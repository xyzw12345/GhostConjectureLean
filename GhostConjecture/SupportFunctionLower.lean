import Mathlib.Data.EReal.Basic

namespace GhostConjecture

/--
`supportFunctionLower C λ` is the support functional of a set `C ⊆ ℝ²` in the direction given by `λ`,
defined as the infimum of the affine function `(x,y) ↦ y + λ * x` over `C`.

It takes values in `EReal = ℝ ∪ {−∞, +∞}`.
-/
noncomputable def supportFunctionLower (C : Set (ℝ × ℝ)) (l : ℝ) : EReal :=
  sInf ((fun p : ℝ × ℝ => ((p.2 + l * p.1 : ℝ) : EReal)) '' C)

end GhostConjecture
