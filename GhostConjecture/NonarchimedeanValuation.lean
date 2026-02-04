import Mathlib.Data.Real.Basic

namespace GhostConjecture

/--
A non-archimedean valuation on a field `K` is a map `K → ℝ ∪ {∞}` satisfying
the usual axioms.
-/
structure NonarchimedeanValuation (K : Type*) [Field K] where
  /-- The underlying function `K → ℝ ∪ {∞}`. -/
  toFun : K → WithTop ℝ
  map_zero' : toFun 0 = ⊤
  map_one' : toFun 1 = 0
  map_mul' : ∀ x y : K, toFun (x * y) = toFun x + toFun y
  /-- Ultrametric inequality. -/
  map_add' : ∀ x y : K, toFun (x + y) ≥ min (toFun x) (toFun y)

namespace NonarchimedeanValuation

variable {K : Type*} [Field K]

instance :
    CoeFun (NonarchimedeanValuation K) (fun _ => K → WithTop ℝ) :=
  ⟨NonarchimedeanValuation.toFun⟩

@[simp] lemma map_zero (v : NonarchimedeanValuation K) : v 0 = (⊤ : WithTop ℝ) :=
  v.map_zero'

@[simp] lemma map_one (v : NonarchimedeanValuation K) : v 1 = (0 : WithTop ℝ) :=
  v.map_one'

lemma map_mul (v : NonarchimedeanValuation K) (x y : K) :
    v (x * y) = v x + v y :=
  v.map_mul' x y

lemma map_add (v : NonarchimedeanValuation K) (x y : K) :
    v (x + y) ≥ min (v x) (v y) := v.map_add' x y

end NonarchimedeanValuation

end GhostConjecture
