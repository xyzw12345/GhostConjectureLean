import GhostConjecture.NewtonPolygon
import GhostConjecture.MinkowskiSum
import Mathlib.Topology.Algebra.Group.Basic

namespace GhostConjecture

namespace NewtonPolygonTpow

/-- The `ℝ × ℝ`-valued Newton points used to define `NewtonPolygon`. -/
def newtonPointsReal {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ |
      ∃ n : ℕ,
        ∃ r : ℝ, (n, (r : WithTop ℝ)) ∈ NewtonPoints v F ∧ p = ((n : ℝ), r) }

def translate (a : ℝ × ℝ) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  (fun x => x + a) '' S

lemma minkowskiSum_singleton_right (A : Set (ℝ × ℝ)) (a : ℝ × ℝ) :
    minkowskiSum A {a} = translate a A := by
  ext p
  constructor
  · intro hp
    rcases (Set.mem_image2.mp hp) with ⟨x, hx, y, hy, rfl⟩
    have hy' : y = a := by simpa using hy
    subst hy'
    exact ⟨x, hx, rfl⟩
  · intro hp
    rcases hp with ⟨x, hx, rfl⟩
    exact Set.mem_image2.mpr ⟨x, hx, a, by simp, rfl⟩

lemma translate_mono {A B : Set (ℝ × ℝ)} (a : ℝ × ℝ) (h : A ⊆ B) :
    translate a A ⊆ translate a B := by
  intro p hp
  rcases hp with ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

lemma isClosed_translate {C : Set (ℝ × ℝ)} (a : ℝ × ℝ) (hC : IsClosed C) :
    IsClosed (translate a C) :=
  (isClosedMap_add_right a) _ hC

lemma convex_translate {C : Set (ℝ × ℝ)} (a : ℝ × ℝ) (hC : Convex ℝ C) :
    Convex ℝ (translate a C) := by
  have himage :
      (fun x : ℝ × ℝ => x + a) '' C = (fun x : ℝ × ℝ => a + x) '' C := by
    ext p
    constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, by simp [add_comm]⟩
  simpa [translate, himage] using hC.translate a

lemma verticalUpwardClosed_translate {C : Set (ℝ × ℝ)} (a : ℝ × ℝ)
    (hC : VerticalUpwardClosed C) : VerticalUpwardClosed (translate a C) := by
  intro x y y' hxy hyy'
  rcases hxy with ⟨p, hpC, hpEq⟩
  have hx : p.1 + a.1 = x := by simpa using congrArg Prod.fst hpEq
  have hy : p.2 + a.2 = y := by simpa using congrArg Prod.snd hpEq
  have hnonneg : 0 ≤ y' - y := sub_nonneg.mpr hyy'
  have hle : p.2 ≤ p.2 + (y' - y) := le_add_of_nonneg_right hnonneg
  have hp' : (p.1, p.2 + (y' - y)) ∈ C :=
    hC p.1 p.2 (p.2 + (y' - y)) hpC hle
  refine ⟨(p.1, p.2 + (y' - y)), hp', ?_⟩
  apply Prod.ext
  · simp [hx]
  · -- simplify to a scalar identity in `ℝ`
    simp only [Prod.snd_add]
    calc
      (p.2 + (y' - y)) + a.2 = (p.2 + a.2) + (y' - y) := by
        simp [add_assoc, add_comm]
      _ = y + (y' - y) := by simp [hy]
      _ = y' := by
        calc
          y + (y' - y) = y + y' - y := by
            simp [sub_eq_add_neg, add_assoc]
          _ = y' := add_sub_cancel_left y y'

def Good (S C : Set (ℝ × ℝ)) : Prop :=
  IsClosed C ∧ Convex ℝ C ∧ S ⊆ C ∧ VerticalUpwardClosed C

lemma good_translate {S C : Set (ℝ × ℝ)} (a : ℝ × ℝ) (h : Good S C) :
    Good (translate a S) (translate a C) := by
  rcases h with ⟨hclosed, hconvex, hsub, hvup⟩
  refine ⟨isClosed_translate a hclosed, convex_translate a hconvex, ?_,
    verticalUpwardClosed_translate a hvup⟩
  exact translate_mono a hsub

lemma good_translate_neg {S D : Set (ℝ × ℝ)} (a : ℝ × ℝ) (h : Good (translate a S) D) :
    Good S (translate (-a) D) := by
  rcases h with ⟨hclosed, hconvex, hsub, hvup⟩
  refine ⟨isClosed_translate (-a) hclosed, convex_translate (-a) hconvex, ?_,
    verticalUpwardClosed_translate (-a) hvup⟩
  intro x hx
  have hx' : x + a ∈ D := hsub ⟨x, hx, rfl⟩
  refine ⟨x + a, hx', ?_⟩
  simp [add_assoc]

lemma lowerConvexHull_translate (S : Set (ℝ × ℝ)) (a : ℝ × ℝ) :
    LowerConvexHull (translate a S) = translate a (LowerConvexHull S) := by
  ext p
  constructor
  · intro hp
    refine ⟨p + (-a), ?_, by simp [add_assoc]⟩
    -- show `p + (-a)` is in every admissible superset of `S`
    refine Set.mem_sInter.mpr ?_
    intro C hC
    have hC' : Good (translate a S) (translate a C) :=
      good_translate a ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2⟩
    have hpC : p ∈ translate a C := by
      have : p ∈ Set.sInter {C : Set (ℝ × ℝ) | Good (translate a S) C} := hp
      exact (Set.mem_sInter.mp this) _ hC'
    rcases hpC with ⟨q, hqC, hqEq⟩
    -- `q + a = p`, hence `p + (-a) = q`
    have : p + (-a) = q := by
      calc
        p + (-a) = (q + a) + (-a) := by simp [hqEq]
        _ = q := by simp [add_assoc]
    simpa [this] using hqC
  · intro hp
    rcases hp with ⟨q, hq, rfl⟩
    refine Set.mem_sInter.mpr ?_
    intro D hD
    have hC : Good S (translate (-a) D) :=
      good_translate_neg a ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2⟩
    have hqC : q ∈ translate (-a) D := by
      have : q ∈ Set.sInter {C : Set (ℝ × ℝ) | Good S C} := hq
      exact (Set.mem_sInter.mp this) _ hC
    rcases hqC with ⟨r, hrD, hrEq⟩
    -- `r + (-a) = q`, hence `q + a = r`
    have : q + a = r := by
      calc
        q + a = (r + (-a)) + a := by simp [hrEq]
        _ = r := by simp [add_assoc]
    simpa [this] using hrD

lemma lowerConvexHull_minkowskiSum_singleton (S : Set (ℝ × ℝ)) (a : ℝ × ℝ) :
    LowerConvexHull (minkowskiSum S {a}) = minkowskiSum (LowerConvexHull S) {a} := by
  calc
    LowerConvexHull (minkowskiSum S {a}) = LowerConvexHull (translate a S) := by
      simp [minkowskiSum_singleton_right, translate]
    _ = translate a (LowerConvexHull S) := lowerConvexHull_translate S a
    _ = minkowskiSum (LowerConvexHull S) {a} := by
      simp [minkowskiSum_singleton_right, translate]

lemma newtonPointsReal_tpow {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) (k : ℕ) :
    newtonPointsReal v (((PowerSeries.X : FormalPowerSeriesRing K) ^ k) * F) =
      minkowskiSum (newtonPointsReal v F) {((k : ℝ), (0 : ℝ))} := by
  classical
  let a : ℝ × ℝ := ((k : ℝ), (0 : ℝ))
  ext p
  constructor
  · intro hp
    rcases hp with ⟨n, r, hn, rfl⟩
    rcases hn with ⟨n', hn'ne, hn'Eq⟩
    have hn_nat : n = n' := by simpa using congrArg Prod.fst hn'Eq
    subst hn_nat
    have hr : (r : WithTop ℝ) = v (PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F)) := by
      simpa using congrArg Prod.snd hn'Eq
    have hcoeff :
        PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F) =
          ite (k ≤ n) (PowerSeries.coeff (n - k) F) 0 := by
      simpa using (PowerSeries.coeff_X_pow_mul' (p := F) (n := k) (d := n))
    have hk : k ≤ n := by
      by_contra hkn
      have hzero : PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F) = (0 : K) := by
        rw [hcoeff]
        simp [hkn]
      exact hn'ne hzero
    set m : ℕ := n - k
    have hcoeff_eq :
        PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F) = PowerSeries.coeff m F := by
      rw [hcoeff]
      simp [hk, m]
    have hmne : PowerSeries.coeff m F ≠ (0 : K) := by
      intro hm0
      apply hn'ne
      simp [hcoeff_eq, hm0]
    have hr' : (r : WithTop ℝ) = v (PowerSeries.coeff m F) := by
      simpa [hcoeff_eq] using hr
    have hmn : m + k = n := by
      simpa [m] using Nat.sub_add_cancel hk
    have hmn' : (m : ℝ) + (k : ℝ) = (n : ℝ) := by exact_mod_cast hmn
    have hq : ((m : ℝ), r) ∈ newtonPointsReal v F := by
      refine ⟨m, r, ?_, rfl⟩
      refine ⟨m, hmne, ?_⟩
      ext <;> simp [hr']
    have hsum : ((m : ℝ), r) + a = ((n : ℝ), r) := by
      apply Prod.ext
      · simp [a, hmn']
      · simp [a]
    -- finish by membership in Minkowski sum
    refine (Set.mem_image2.mpr ?_)
    exact ⟨((m : ℝ), r), hq, a, by simp [a], hsum⟩
  · intro hp
    -- unwrap Minkowski sum
    have hp' : p ∈ translate a (newtonPointsReal v F) := by
      simpa [minkowskiSum_singleton_right, a] using hp
    rcases hp' with ⟨q, hq, rfl⟩
    rcases hq with ⟨m, r, hm, hqEq⟩
    subst hqEq
    rcases hm with ⟨m', hmne, hmEq⟩
    have hm_nat : m = m' := by simpa using congrArg Prod.fst hmEq
    subst hm_nat
    have hr : (r : WithTop ℝ) = v (PowerSeries.coeff m F) := by
      simpa using congrArg Prod.snd hmEq
    set n : ℕ := m + k
    have hk : k ≤ n := Nat.le_add_left k m
    have hcoeff :
        PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F) =
          ite (k ≤ n) (PowerSeries.coeff (n - k) F) 0 := by
      simpa using (PowerSeries.coeff_X_pow_mul' (p := F) (n := k) (d := n))
    have hsub : n - k = m := by
      simp [n]
    have hcoeff_eq :
        PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F) = PowerSeries.coeff m F := by
      rw [hcoeff]
      simp [hk, hsub]
    have hnne : PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F) ≠ (0 : K) := by
      intro h0
      apply hmne
      simpa [hcoeff_eq] using h0
    have hr' : (r : WithTop ℝ) = v (PowerSeries.coeff n (((PowerSeries.X : _) ^ k) * F)) := by
      simpa [hcoeff_eq] using hr
    have hn_real : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
      simp [n, Nat.cast_add]
    -- build the required witnesses
    refine ⟨n, r, ?_, ?_⟩
    · refine ⟨n, hnne, ?_⟩
      ext <;> simp [hr']
    · apply Prod.ext
      · simp [hn_real, a]
      · simp [a]

end NewtonPolygonTpow

/-- Horizontal shift of the Newton polygon under multiplication by `t^k`. -/
lemma newtonPolygon_tpow {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) (k : ℕ) :
    NewtonPolygon v (((PowerSeries.X : FormalPowerSeriesRing K) ^ k) * F) =
      minkowskiSum (NewtonPolygon v F) {((k : ℝ), (0 : ℝ))} := by
  classical
  unfold NewtonPolygon
  change
    LowerConvexHull (NewtonPolygonTpow.newtonPointsReal v (((PowerSeries.X : _) ^ k) * F)) =
      minkowskiSum (LowerConvexHull (NewtonPolygonTpow.newtonPointsReal v F)) {((k : ℝ), (0 : ℝ))}
  rw [NewtonPolygonTpow.newtonPointsReal_tpow (v := v) (F := F) (k := k)]
  exact
    NewtonPolygonTpow.lowerConvexHull_minkowskiSum_singleton
      (S := NewtonPolygonTpow.newtonPointsReal v F) (a := ((k : ℝ), (0 : ℝ)))

end GhostConjecture
