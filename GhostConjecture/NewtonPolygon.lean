import GhostConjecture.NewtonPoints
import GhostConjecture.LowerConvexHull

open Set

namespace GhostConjecture

/--
Newton polygon of a formal power series over a non-archimedean valued field.
-/
def NewtonPolygon {K : Type*} [Field K] (v : NonarchimedeanValuation K) (F : K⟦t⟧) :
    Set (ℝ × ℝ) :=
  LowerConvexHull
    (S :=
      (fun p : ℕ × WithTop ℝ =>
          ((p.1 : ℝ), WithTop.recTopCoe 0 (fun r => r) p.2)) '' (NewtonPoints v F))

end GhostConjecture

