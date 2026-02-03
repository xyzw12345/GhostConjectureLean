import Mathlib.RingTheory.PowerSeries.Basic

namespace GhostConjecture

/--
Formal power series ring over a commutative ring `R`.

This is the ring `R⟦X⟧` of formal power series in one variable, with the
usual Cauchy product.
-/
abbrev FormalPowerSeriesRing (R : Type*) [CommRing R] :=
  PowerSeries R

scoped notation:9000 R "⟦t⟧" => FormalPowerSeriesRing R

end GhostConjecture
