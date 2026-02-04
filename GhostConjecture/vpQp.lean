import GhostConjecture.NonarchimedeanValuation
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace GhostConjecture

open scoped BigOperators

/--
The standard `p`-adic valuation on `ℚ_[p]`, viewed as a `NonarchimedeanValuation` and normalized by
`v_p(0) = ∞` and `v_p(p) = 1` (as an element of `WithTop ℝ`).

This is obtained from `Padic.addValuation : AddValuation ℚ_[p] (WithTop ℤ)` by casting `ℤ → ℝ`.
-/
noncomputable def vpQp (p : ℕ) [Fact p.Prime] : NonarchimedeanValuation ℚ_[p] where
  toFun x := WithTop.map (fun z : ℤ => (z : ℝ)) (Padic.addValuation x)
  map_zero' := by
    simp
  map_one' := by
    simp
  map_mul' := by
    intro x y
    calc
      WithTop.map (fun z : ℤ => (z : ℝ)) (Padic.addValuation (x * y)) =
          WithTop.map (fun z : ℤ => (z : ℝ)) (Padic.addValuation x + Padic.addValuation y) := by
        exact
          congrArg (WithTop.map (fun z : ℤ => (z : ℝ))) (Padic.addValuation.map_mul x y)
      _ =
          WithTop.map (fun z : ℤ => (z : ℝ)) (Padic.addValuation x) +
            WithTop.map (fun z : ℤ => (z : ℝ)) (Padic.addValuation y) := by
        simpa using
          (WithTop.map_add (f := (Int.castRingHom ℝ).toAddMonoidHom)
            (a := Padic.addValuation x) (b := Padic.addValuation y))
  map_add' := by
    intro x y
    -- Use monotonicity of `WithTop.map` to transport the ultrametric inequality from `WithTop ℤ` to
    -- `WithTop ℝ`.
    have hmono : Monotone (fun z : ℤ => (z : ℝ)) := by
      intro a b hab
      exact (Int.cast_le).2 hab
    have hm : Monotone (WithTop.map (fun z : ℤ => (z : ℝ))) :=
      (WithTop.monotone_map_iff).2 hmono
    have h' := hm (Padic.addValuation.map_add x y)
    -- Rewrite `WithTop.map` applied to a `min`.
    simpa [ge_iff_le, Monotone.map_min hm] using h'

end GhostConjecture
