import GhostConjecture.NewtonPolygon
import GhostConjecture.SupportFunction
import GhostConjecture.TropicalWeight

namespace GhostConjecture

/-- Coerce `WithTop ℝ` into `EReal`, sending `⊤` to `⊤`. -/
def withTopToEReal (x : WithTop ℝ) : EReal :=
  WithTop.recTopCoe (C := fun _ => EReal) (top := (⊤ : EReal)) (coe := fun r => (r : EReal)) x

/-- Support function of the Newton polygon. -/
lemma supportFunctionLower_newtonPolygon {K : Type*} [Field K]
    (v : NonarchimedeanValuation K) (F : K⟦t⟧) (λ : ℝ) :
    supportFunctionLower (NewtonPolygon v F) λ =
      withTopToEReal (tropicalWeight v F λ) := by
  sorry

end GhostConjecture
