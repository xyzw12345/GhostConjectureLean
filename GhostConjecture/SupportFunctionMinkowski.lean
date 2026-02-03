import GhostConjecture/SupportFunction
import GhostConjecture/Geometry/MinkowskiSum

namespace GhostConjecture

/-- Support function of a Minkowski sum. -/
lemma supportFunctionLower_minkowskiSum (A B : Set (ℝ × ℝ)) (λ : ℝ) :
    supportFunctionLower (minkowskiSum A B) λ =
      supportFunctionLower A λ + supportFunctionLower B λ := by
  sorry

end GhostConjecture
