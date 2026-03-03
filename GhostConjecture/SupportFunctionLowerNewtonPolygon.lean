import GhostConjecture.NewtonPolygon
import GhostConjecture.SupportFunctionLower
import GhostConjecture.TropicalWeight

namespace GhostConjecture

open scoped BigOperators

private noncomputable def affineFun (lam : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 + lam * p.1

private noncomputable def affineFunE (lam : ℝ) (p : ℝ × ℝ) : EReal :=
  ((p.2 + lam * p.1 : ℝ) : EReal)

private lemma supportFunctionLower_lowerConvexHull (S : Set (ℝ × ℝ)) (lam : ℝ) :
    supportFunctionLower (LowerConvexHull S) lam = supportFunctionLower S lam := by
  classical
  -- If `S` is empty, both sides are `⊤`.
  by_cases hS : S = ∅
  · subst hS
    have hLCH : LowerConvexHull (∅ : Set (ℝ × ℝ)) = ∅ := by
      -- `∅` itself is in the defining family, so the intersection is empty.
      have hempty :
          (∅ : Set (ℝ × ℝ)) ∈
            { C : Set (ℝ × ℝ) | IsClosed C ∧ Convex ℝ C ∧ (∅ : Set (ℝ × ℝ)) ⊆ C ∧ VerticalUpwardClosed C } := by
        refine ⟨isClosed_empty, convex_empty, by simp, ?_⟩
        intro x y y' hxy hy
        cases hxy
      have hsubset :
          LowerConvexHull (∅ : Set (ℝ × ℝ)) ⊆ (∅ : Set (ℝ × ℝ)) := by
        -- `LowerConvexHull` is the `sInter` of this family.
        simpa [LowerConvexHull] using (Set.sInter_subset_of_mem hempty)
      ext p
      constructor
      · intro hp
        exact (hsubset hp).elim
      · intro hp
        cases hp
    simp [supportFunctionLower, hLCH]

  -- Otherwise, compare the infima using the defining intersection characterization.
  let m : EReal := supportFunctionLower S lam
  have hSsubset : S ⊆ LowerConvexHull S := by
    intro p hp
    change p ∈ Set.sInter
      { C : Set (ℝ × ℝ) | IsClosed C ∧ Convex ℝ C ∧ S ⊆ C ∧ VerticalUpwardClosed C }
    refine Set.mem_sInter.2 ?_
    intro C hC
    exact hC.2.2.1 hp

  have hle : supportFunctionLower (LowerConvexHull S) lam ≤ m := by
    -- image monotonicity + `sInf` antitone
    dsimp [m, supportFunctionLower]
    apply sInf_le_sInf
    intro x hx
    rcases hx with ⟨p, hpS, rfl⟩
    exact ⟨p, hSsubset hpS, rfl⟩

  -- For the reverse inequality, consider the closed convex vertical half-space above `m`.
  -- We build a set `D` in the defining family with support value `≥ m`.
  have hge : m ≤ supportFunctionLower (LowerConvexHull S) lam := by
    -- Expand `m` to either `⊥`, `⊤`, or a real number.
    cases hm : m with
    | bot =>
      -- `m = ⊥` gives a trivial lower bound.
      simpa [m, hm] using (bot_le : (⊥ : EReal) ≤ supportFunctionLower (LowerConvexHull S) lam)
    | top =>
      -- `m = ⊤` contradicts `S ≠ ∅` since `affineFunE` is always a real value.
      rcases Set.nonempty_iff_ne_empty.2 hS with ⟨p, hpS⟩
      have hm_le : m ≤ affineFunE lam p := by
        -- `m = sInf (...)` is below any image element.
        dsimp [m, supportFunctionLower]
        apply sInf_le
        exact ⟨p, hpS, rfl⟩
      have htop : affineFunE lam p = (⊤ : EReal) := by
        have : (⊤ : EReal) ≤ affineFunE lam p := by
          simpa [m, hm] using hm_le
        exact (top_le_iff).1 this
      have : False := by
        have hnot : affineFunE lam p ≠ (⊤ : EReal) := by
          simpa [affineFunE] using (EReal.coe_ne_top (p.2 + lam * p.1))
        exact hnot htop
      exact this.elim
    | coe r =>
      -- `m = (r : ℝ)`; define the half-space `{p | r ≤ y + lam*x}`.
      have hm' : m = (r : EReal) := by simpa [m, hm]
      let D : Set (ℝ × ℝ) := {p | r ≤ affineFun lam p}
      have hD_closed : IsClosed D := by
        -- Preimage of a closed interval under a continuous affine map.
        have hcont : Continuous fun p : ℝ × ℝ => affineFun lam p := by
          -- `affineFun lam p = p.2 + lam * p.1`
          simpa [affineFun] using
            (continuous_snd.add ((continuous_const.mul continuous_fst)))
        simpa [D, affineFun] using (isClosed_Ici.preimage hcont)
      have hD_convex : Convex ℝ D := by
        intro x hx y hy a b ha hb hab
        -- Use affine linearity: `affineFun` respects convex combinations.
        have hx' : r ≤ affineFun lam x := hx
        have hy' : r ≤ affineFun lam y := hy
        have hax : a * r ≤ a * affineFun lam x := by
          exact mul_le_mul_of_nonneg_left hx' ha
        have hby : b * r ≤ b * affineFun lam y := by
          exact mul_le_mul_of_nonneg_left hy' hb
        have hsum : (a * r + b * r) ≤ (a * affineFun lam x + b * affineFun lam y) := by
          exact add_le_add hax hby
        have hr : a * r + b * r = r := by
          calc
            a * r + b * r = (a + b) * r := by ring
            _ = 1 * r := by simp [hab]
            _ = r := by ring
        -- Now compute the affine function on the combination.
        have hcomb :
            affineFun lam (a • x + b • y) =
              a * affineFun lam x + b * affineFun lam y := by
          -- Componentwise calculation.
          simp [affineFun, mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm,
            mul_left_comm, mul_comm]
        -- Conclude.
        have : r ≤ a * affineFun lam x + b * affineFun lam y := by
          -- `a*r + b*r = r` and `a*r + b*r ≤ ...`
          have : a * r + b * r ≤ a * affineFun lam x + b * affineFun lam y := hsum
          simpa [hr] using this
        simpa [D, hcomb] using this
      have hD_up : VerticalUpwardClosed D := by
        intro x y y' hxy hyy'
        -- Increasing `y` increases `y + lam*x`.
        have : r ≤ y + lam * x := hxy
        have : r ≤ y' + lam * x := by linarith
        simpa [D, affineFun] using this
      have hS_in_D : S ⊆ D := by
        intro p hpS
        -- Since `m` is the infimum, `m ≤ affineFunE ... p`, hence `r ≤ affineFun ... p`.
        have hm_le : m ≤ affineFunE lam p := by
          dsimp [m, supportFunctionLower]
          apply sInf_le
          exact ⟨p, hpS, rfl⟩
        have : (r : EReal) ≤ affineFunE lam p := by
          simpa [hm'] using hm_le
        have : r ≤ p.2 + lam * p.1 :=
          (EReal.coe_le_coe_iff.1 (by simpa [affineFunE] using this))
        simpa [D, affineFun] using this

      have hLCH_subset_D : LowerConvexHull S ⊆ D := by
        -- `D` is one of the sets in the defining intersection.
        have hmem :
            D ∈ { C : Set (ℝ × ℝ) | IsClosed C ∧ Convex ℝ C ∧ S ⊆ C ∧ VerticalUpwardClosed C } := by
          exact ⟨hD_closed, hD_convex, hS_in_D, hD_up⟩
        intro p hpLCH
        -- Membership in the intersection gives membership in every such set, in particular `D`.
        have hpInter :
            p ∈ Set.sInter
              { C : Set (ℝ × ℝ) |
                  IsClosed C ∧ Convex ℝ C ∧ S ⊆ C ∧ VerticalUpwardClosed C } := by
          simpa [LowerConvexHull] using hpLCH
        exact Set.mem_sInter.1 hpInter D hmem

      -- Now `m` is a lower bound of `affineFunE '' LowerConvexHull S`.
      dsimp [m, supportFunctionLower]
      refine le_sInf ?_
      intro y hy
      rcases hy with ⟨p, hpLCH, rfl⟩
      have hpD : p ∈ D := hLCH_subset_D hpLCH
      have : (r : EReal) ≤ affineFunE lam p := by
        -- `r ≤ affineFun` in ℝ gives the inequality in `EReal`.
        have hrp : r ≤ p.2 + lam * p.1 := by
          simpa [D, affineFun] using hpD
        -- `affineFunE lam p` is the coercion of this real value.
        exact (EReal.coe_le_coe_iff.2 hrp)
      simpa [hm'] using this

  exact le_antisymm hle (by simpa [m] using hge)

/-- Support function of the Newton polygon agrees with the tropical weight. -/
lemma supportFunctionLower_newtonPolygon {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) (lam : ℝ) :
    supportFunctionLower (NewtonPolygon v F) lam = tropicalWeight v F lam := by
  -- classical
  -- -- Unfold the Newton polygon as a lower convex hull and remove the hull.
  -- simp [NewtonPolygon, supportFunctionLower_lowerConvexHull]
  -- set S : Set (ℝ × ℝ) :=
  --   { p : ℝ × ℝ |
  --       ∃ n : ℕ, ∃ r : ℝ, (n, (r : WithTop ℝ)) ∈ NewtonPoints v F ∧ p = ((n : ℝ), r) } with hS
  -- -- Replace the displayed set by `S`.
  -- -- (This also unfolds the support function.)
  -- simp [supportFunctionLower, hS]
  -- -- The left-hand side is `sInf` over the image of the affine function.
  -- -- The right-hand side is an `iInf` over all coefficients.
  -- let term : ℕ → EReal := fun n =>
  --   ((WithTop.map (fun r : ℝ => (r : WithBot ℝ))
  --           (v ((PowerSeries.coeff (R := K) n) F)) +
  --         (lam * (n : ℝ)) : WithTop (WithBot ℝ)) : EReal)
  -- have htrop : (tropicalWeight v F lam : EReal) = ⨅ n : ℕ, term n := by
  --   simp [tropicalWeight, term]
  --   rfl

  -- -- Reduce to comparing `sInf` with `iInf`.
  -- rw [htrop]
  -- set A : Set EReal :=
  --   (fun p : ℝ × ℝ => ((p.2 + lam * p.1 : ℝ) : EReal)) '' S with hA

  -- change sInf A = ⨅ n : ℕ, term n

  -- apply le_antisymm
  -- · -- `sInf A` is ≤ each `term n`, hence ≤ `⨅ n, term n`.
  --   refine le_iInf ?_
  --   intro n
  --   cases hv : v ((PowerSeries.coeff (R := K) n) F) with
  --   | top =>
  --     -- valuation is `⊤`, so the term is `⊤`.
  --     have : term n = (⊤ : EReal) := by
  --       simp [term, hv]
  --     simpa [this] using (le_top : sInf A ≤ (⊤ : EReal))
  --   | coe r =>
  --     -- valuation is a real number: realize the term by the Newton point `(n,r)`.
  --     have hne : (PowerSeries.coeff (R := K) n) F ≠ (0 : K) := by
  --       intro h0
  --       have : v ((PowerSeries.coeff (R := K) n) F) = (⊤ : WithTop ℝ) := by
  --         simpa [h0] using (NonarchimedeanValuation.map_zero (v := v) : v (0 : K) = (⊤ : WithTop ℝ))
  --       have : (⊤ : WithTop ℝ) = (r : WithTop ℝ) := by simpa [hv] using this
  --       exact (WithTop.top_ne_coe (a := r)) this
  --     have hNP : (n, (r : WithTop ℝ)) ∈ NewtonPoints v F := by
  --       refine ⟨n, hne, ?_⟩
  --       simp [NewtonPoints, hv]
  --     have hmemS : ((n : ℝ), r) ∈ S := by
  --       refine ⟨n, r, hNP, rfl⟩
  --     have himg : term n ∈ A := by
  --       refine ⟨((n : ℝ), r), hmemS, ?_⟩
  --       -- Compute the value of `term n` under the coercions.
  --       simp [A, hA, term, hv, WithTop.map_coe]
  --     -- Since `term n ∈ A`, we have `sInf A ≤ term n`.
  --     simpa [hA] using (sInf_le himg)
  -- · -- `⨅ n, term n` is a lower bound of `A`, hence ≤ `sInf A`.
  --   -- It suffices to show every element of `A` is in the range of `term`.
  --   have hsub : A ⊆ Set.range term := by
  --     intro y hy
  --     rcases hy with ⟨p, hpS, rfl⟩
  --     rcases hpS with ⟨n, r, hn, rfl⟩
  --     rcases hn with ⟨m, hm0, hpair⟩
  --     have hm : m = n := by
  --       simpa using congrArg Prod.fst hpair.symm
  --     subst hm
  --     have hv : v ((PowerSeries.coeff (R := K) n) F) = (r : WithTop ℝ) := by
  --       -- compare second coordinates
  --       simpa using congrArg Prod.snd hpair.symm
  --     refine ⟨n, ?_⟩
  --     simp [term, hv, WithTop.map_coe, affineFun, affineFunE]

  --   have : sInf (Set.range term) ≤ sInf A := sInf_le_sInf hsub
  --   simpa [sInf_range] using this
  sorry

end GhostConjecture
