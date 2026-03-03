import GhostConjecture.NewtonPolygon

namespace GhostConjecture

/-- Newton points and Newton polygon of the zero power series. -/
lemma newton_polygon_zero {K : Type*} [Field K] (v : NonarchimedeanValuation K) :
    NewtonPoints v (0 : FormalPowerSeriesRing K) = ∅ ∧
      NewtonPolygon v (0 : FormalPowerSeriesRing K) = LowerConvexHull (∅ : Set (ℝ × ℝ)) := by
  have hPoints : NewtonPoints v (0 : FormalPowerSeriesRing K) = ∅ := by
    ext p
    simp [NewtonPoints]
  constructor
  · exact hPoints
  · simp [NewtonPolygon, hPoints]

end GhostConjecture
