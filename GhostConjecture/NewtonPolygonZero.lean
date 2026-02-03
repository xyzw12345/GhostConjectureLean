import GhostConjecture.NewtonPolygon

namespace GhostConjecture

/-- Newton polygon of the zero series. -/
lemma newton_polygon_zero {K : Type*} [Field K] (v : NonarchimedeanValuation K) (F : K⟦t⟧)
    (hF : F = 0) :
    NewtonPoints v F = (∅ : Set (ℕ × WithTop ℝ)) ∧
      NewtonPolygon v F = LowerConvexHull (S := (∅ : Set (ℝ × ℝ))) := by
  sorry

end GhostConjecture
