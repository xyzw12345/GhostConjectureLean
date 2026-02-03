import Mathlib

namespace GhostConjecture

/-- A non-archimedean valuation on a field. -/
structure NonarchimedeanValuation (K : Type*) [Field K] where
  /-- The valuation map. -/
  v : K → WithTop ℝ
  /-- `v 0 = ∞`. -/
  map_zero' : v 0 = ⊤
  /-- `v 1 = 0`. -/
  map_one' : v 1 = 0
  /-- `v (x * y) = v x + v y`. -/
  map_mul' : ∀ x y : K, v (x * y) = v x + v y
  /-- Ultrametric inequality: `v (x + y) ≥ min (v x) (v y)`. -/
  map_add' : ∀ x y : K, v (x + y) ≥ min (v x) (v y)

/-- A non-archimedean valued field. -/
structure NonarchimedeanValuedField where
  /-- The underlying field. -/
  K : Type*
  /-- Field structure on `K`. -/
  instField : Field K
  /-- A non-archimedean valuation on `K`. -/
  v : NonarchimedeanValuation K

attribute [instance] NonarchimedeanValuedField.instField

end GhostConjecture
