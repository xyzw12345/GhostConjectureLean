import GhostConjecture.MinkowskiSum
import GhostConjecture.SupportFunctionalLower
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

namespace GhostConjecture

noncomputable section

open scoped Pointwise

/-- Support functional of a Minkowski sum. -/
lemma supportFunctionalLower_minkowskiSum (A B : Set (ℝ × ℝ)) (l : ℝ) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    supportFunctionalLower (minkowskiSum A B) l =
      supportFunctionalLower A l + supportFunctionalLower B l := by
  classical
  -- Work with the real-valued functional first.
  set val : (ℝ × ℝ) → ℝ := fun p => p.2 + l * p.1 with hval
  set SA : Set ℝ := val '' A with hSA
  set SB : Set ℝ := val '' B with hSB
  have hSA_ne : SA.Nonempty := by
    rcases hA with ⟨a, ha⟩
    refine ⟨val a, ?_⟩
    exact ⟨a, ha, rfl⟩
  have hSB_ne : SB.Nonempty := by
    rcases hB with ⟨b, hb⟩
    refine ⟨val b, ?_⟩
    exact ⟨b, hb, rfl⟩
  -- Values over the Minkowski sum are the pointwise sum of the value-sets.
  have hval_mink : val '' minkowskiSum A B = SA + SB := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨a, ha, b, hb, rfl⟩
      refine ⟨val a, ?_, val b, ?_, ?_⟩
      · exact ⟨a, ha, rfl⟩
      · exact ⟨b, hb, rfl⟩
      · -- Expand `val (a + b)`.
        simp [hval, mul_add, add_assoc, add_left_comm]
    · rintro ⟨ra, hra, rb, hrb, rfl⟩
      rcases hra with ⟨a, ha, rfl⟩
      rcases hrb with ⟨b, hb, rfl⟩
      refine ⟨a + b, ?_, ?_⟩
      · exact ⟨a, ha, b, hb, rfl⟩
      · simp [hval, mul_add, add_assoc, add_left_comm]
  -- Re-express `supportFunctionalLower` via the real-valued `val`.
  have hSuppA :
      supportFunctionalLower A l = sInf ((fun r : ℝ => (r : EReal)) '' SA) := by
    unfold supportFunctionalLower
    rw [hSA]
    have hfun :
        (fun p : ℝ × ℝ => ((p.2 + l * p.1 : ℝ) : EReal)) = (fun r : ℝ => (r : EReal)) ∘ val := by
      funext p
      have : val p = p.2 + l * p.1 := congrArg (fun f => f p) hval
      simp [Function.comp, this]
    -- Turn `(f ∘ val) '' A` into `f '' (val '' A)`.
    rw [hfun]
    have himage :
        ((fun r : ℝ => (r : EReal)) ∘ val) '' A = (fun r : ℝ => (r : EReal)) '' (val '' A) := by
      ext z
      constructor
      · rintro ⟨p, hpA, rfl⟩
        refine ⟨val p, ?_, rfl⟩
        exact ⟨p, hpA, rfl⟩
      · rintro ⟨r, ⟨p, hpA, rfl⟩, rfl⟩
        exact ⟨p, hpA, rfl⟩
    rw [himage]
  have hSuppB :
      supportFunctionalLower B l = sInf ((fun r : ℝ => (r : EReal)) '' SB) := by
    unfold supportFunctionalLower
    rw [hSB]
    have hfun :
        (fun p : ℝ × ℝ => ((p.2 + l * p.1 : ℝ) : EReal)) = (fun r : ℝ => (r : EReal)) ∘ val := by
      funext p
      have : val p = p.2 + l * p.1 := congrArg (fun f => f p) hval
      simp [Function.comp, this]
    rw [hfun]
    have himage :
        ((fun r : ℝ => (r : EReal)) ∘ val) '' B = (fun r : ℝ => (r : EReal)) '' (val '' B) := by
      ext z
      constructor
      · rintro ⟨p, hpB, rfl⟩
        refine ⟨val p, ?_, rfl⟩
        exact ⟨p, hpB, rfl⟩
      · rintro ⟨r, ⟨p, hpB, rfl⟩, rfl⟩
        exact ⟨p, hpB, rfl⟩
    rw [himage]
  have hSuppAB :
      supportFunctionalLower (minkowskiSum A B) l =
        sInf ((fun r : ℝ => (r : EReal)) '' (SA + SB)) := by
    unfold supportFunctionalLower
    have hfun :
        (fun p : ℝ × ℝ => ((p.2 + l * p.1 : ℝ) : EReal)) = (fun r : ℝ => (r : EReal)) ∘ val := by
      funext p
      have : val p = p.2 + l * p.1 := congrArg (fun f => f p) hval
      simp [Function.comp, this]
    rw [hfun]
    have himage :
        ((fun r : ℝ => (r : EReal)) ∘ val) '' minkowskiSum A B =
          (fun r : ℝ => (r : EReal)) '' (val '' minkowskiSum A B) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨val p, ?_, rfl⟩
        exact ⟨p, hp, rfl⟩
      · rintro ⟨r, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, hp, rfl⟩
    rw [himage]
    -- Rewrite `val '' (minkowskiSum A B)` using `hval_mink`.
    rw [hval_mink]
  -- Helper: if a real set is not bounded below, its `EReal`-infimum is `⊥`.
  have sInf_coe_eq_bot_of_not_bddBelow :
      ∀ {S : Set ℝ}, ¬BddBelow S → sInf ((fun r : ℝ => (r : EReal)) '' S) = (⊥ : EReal) := by
    intro S hS
    have hS' : ∀ x : ℝ, ∃ y ∈ S, y < x := (not_bddBelow_iff).1 hS
    have hS_ne : S.Nonempty := by
      by_contra hne
      have : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
      exact hS (by simp [this])
    refine (sInf_eq_bot).2 ?_
    intro b hb
    induction b using EReal.rec with
    | bot =>
        cases (lt_irrefl (⊥ : EReal) hb)
    | top =>
        rcases hS_ne with ⟨y, hyS⟩
        refine ⟨(y : EReal), ?_, ?_⟩
        · exact ⟨y, hyS, rfl⟩
        · simp
    | coe x =>
        rcases hS' x with ⟨y, hyS, hyx⟩
        refine ⟨(y : EReal), ?_, ?_⟩
        · exact ⟨y, hyS, rfl⟩
        · -- `hb` gives `⊥ < (x : EReal)`, hence we may compare real coercions.
          simpa using (EReal.coe_lt_coe_iff.2 hyx)
  -- Helper: for a nonempty bounded-below real set, its `EReal`-infimum is the coercion of `sInf`.
  have sInf_coe_eq_coe_sInf_of_bddBelow :
      ∀ {S : Set ℝ}, S.Nonempty → BddBelow S →
        sInf ((fun r : ℝ => (r : EReal)) '' S) = ((sInf S : ℝ) : EReal) := by
    intro S hS_ne hS_bdd
    -- First go to `WithTop ℝ`, then to `WithBot (WithTop ℝ) = EReal`.
    have hS_top_bdd : BddBelow ((fun r : ℝ => (r : WithTop ℝ)) '' S) := by
      rcases hS_bdd with ⟨m, hm⟩
      refine ⟨(m : WithTop ℝ), ?_⟩
      rintro _ ⟨r, hrS, rfl⟩
      simpa using (hm hrS)
    have h1 :
        ((sInf S : ℝ) : WithTop ℝ) = sInf ((fun r : ℝ => (r : WithTop ℝ)) '' S) := by
      simpa using (WithTop.coe_sInf' (α := ℝ) (s := S) hS_ne hS_bdd)
    have h2 :
        sInf
            ((fun t : WithTop ℝ => (t : WithBot (WithTop ℝ))) ''
              ((fun r : ℝ => (r : WithTop ℝ)) '' S)) =
          ((sInf ((fun r : ℝ => (r : WithTop ℝ)) '' S) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      simpa using
        (WithBot.coe_sInf' (α := WithTop ℝ)
          (s := (fun r : ℝ => (r : WithTop ℝ)) '' S) hS_top_bdd).symm
    calc
      sInf ((fun r : ℝ => (r : EReal)) '' S)
          =
          sInf
            ((fun t : WithTop ℝ => (t : WithBot (WithTop ℝ))) ''
              ((fun r : ℝ => (r : WithTop ℝ)) '' S)) := by
            simp [Set.image_image, Function.comp, Real.toEReal, EReal]
      _ = ((sInf ((fun r : ℝ => (r : WithTop ℝ)) '' S) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
              simpa using h2
      _ = (((sInf S : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
              simp [h1]
      _ = ((sInf S : ℝ) : EReal) := rfl
  -- Main case split: bounded below vs unbounded below.
  by_cases hA_bdd : BddBelow SA
  · by_cases hB_bdd : BddBelow SB
    · -- Bounded-below case: reduce to the real statement `csInf_add`.
      have hSum_bdd : BddBelow (SA + SB) := by
        rcases hA_bdd with ⟨mA, hmA⟩
        rcases hB_bdd with ⟨mB, hmB⟩
        refine ⟨mA + mB, ?_⟩
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact add_le_add (hmA ha) (hmB hb)
      have hreal : sInf (SA + SB) = sInf SA + sInf SB :=
        csInf_add (M := ℝ) (s := SA) (t := SB) hSA_ne hA_bdd hSB_ne hB_bdd
      -- Translate real infima to `EReal` infima.
      have hSA_ereal :
          sInf ((fun r : ℝ => (r : EReal)) '' SA) = ((sInf SA : ℝ) : EReal) :=
        sInf_coe_eq_coe_sInf_of_bddBelow hSA_ne hA_bdd
      have hSB_ereal :
          sInf ((fun r : ℝ => (r : EReal)) '' SB) = ((sInf SB : ℝ) : EReal) :=
        sInf_coe_eq_coe_sInf_of_bddBelow hSB_ne hB_bdd
      have hSum_ereal :
          sInf ((fun r : ℝ => (r : EReal)) '' (SA + SB)) = ((sInf (SA + SB) : ℝ) : EReal) :=
        sInf_coe_eq_coe_sInf_of_bddBelow (by
          rcases hSA_ne with ⟨a, ha⟩
          rcases hSB_ne with ⟨b, hb⟩
          exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩⟩) hSum_bdd
      -- Finish.
      simp [hSuppAB, hSuppA, hSuppB, hSum_ereal, hSA_ereal, hSB_ereal, hreal, EReal.coe_add]
    · -- `SB` is not bounded below, so everything is `⊥` (using `SB.Nonempty`).
      have hSB_bot : sInf ((fun r : ℝ => (r : EReal)) '' SB) = (⊥ : EReal) :=
        sInf_coe_eq_bot_of_not_bddBelow hB_bdd
      -- Then `SA + SB` is not bounded below, so its infimum is `⊥`.
      have hSum_not_bdd : ¬BddBelow (SA + SB) := by
        -- Use `SB` unbounded below and pick any `a ∈ SA`.
        rcases hSA_ne with ⟨a0, ha0⟩
        have hSB' : ∀ x : ℝ, ∃ y ∈ SB, y < x := (not_bddBelow_iff).1 hB_bdd
        -- Show unboundedness of the sum-set.
        refine (not_bddBelow_iff).2 (fun x => ?_)
        rcases hSB' (x - a0) with ⟨b, hbSB, hb_lt⟩
        refine ⟨a0 + b, ⟨a0, ha0, b, hbSB, rfl⟩, ?_⟩
        linarith
      have hSum_bot : sInf ((fun r : ℝ => (r : EReal)) '' (SA + SB)) = (⊥ : EReal) :=
        sInf_coe_eq_bot_of_not_bddBelow hSum_not_bdd
      -- Conclude.
      have hadd : sInf ((fun r : ℝ => (r : EReal)) '' SA) + (⊥ : EReal) = (⊥ : EReal) := by
        cases sInf ((fun r : ℝ => (r : EReal)) '' SA) <;> rfl
      simp [hSuppAB, hSuppA, hSuppB, hSB_bot, hSum_bot, hadd]
  · -- `SA` is not bounded below, so everything is `⊥` (using `SA.Nonempty`).
    have hSA_bot : sInf ((fun r : ℝ => (r : EReal)) '' SA) = (⊥ : EReal) :=
      sInf_coe_eq_bot_of_not_bddBelow hA_bdd
    have hSum_not_bdd : ¬BddBelow (SA + SB) := by
      rcases hSB_ne with ⟨b0, hb0⟩
      have hSA' : ∀ x : ℝ, ∃ y ∈ SA, y < x := (not_bddBelow_iff).1 hA_bdd
      refine (not_bddBelow_iff).2 (fun x => ?_)
      rcases hSA' (x - b0) with ⟨a, haSA, ha_lt⟩
      refine ⟨a + b0, ⟨a, haSA, b0, hb0, rfl⟩, ?_⟩
      linarith
    have hSum_bot : sInf ((fun r : ℝ => (r : EReal)) '' (SA + SB)) = (⊥ : EReal) :=
      sInf_coe_eq_bot_of_not_bddBelow hSum_not_bdd
    have hbotadd : (⊥ : EReal) + sInf ((fun r : ℝ => (r : EReal)) '' SB) = (⊥ : EReal) := by
      cases sInf ((fun r : ℝ => (r : EReal)) '' SB) <;> rfl
    simp [hSuppAB, hSuppA, hSuppB, hSA_bot, hSum_bot, hbotadd]

end

end GhostConjecture
