import GhostConjecture.NewtonPolygon

namespace GhostConjecture

/--
Monotonicity of Newton polygons under coefficientwise valuation bounds.
-/
lemma newtonPolygon_monotone {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F G : K⟦t⟧)
    (h :
      ∀ n : ℕ,
        PowerSeries.coeff F n ≠ 0 →
          PowerSeries.coeff G n ≠ 0 →
            v.v (PowerSeries.coeff G n) ≥ v.v (PowerSeries.coeff F n)) :
    NewtonPolygon v G ⊆ NewtonPolygon v F := by
  sorry

end GhostConjecture
