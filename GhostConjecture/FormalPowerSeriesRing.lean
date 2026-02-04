import Mathlib.RingTheory.PowerSeries.Basic

namespace GhostConjecture

universe u

/-- For a commutative ring `R`, `FormalPowerSeriesRing R` is the ring `R⟦X⟧` of formal power series
with coefficients in `R`, equipped with the usual Cauchy product. -/
abbrev FormalPowerSeriesRing (R : Type u) [CommRing R] : Type u :=
  PowerSeries R

end GhostConjecture
