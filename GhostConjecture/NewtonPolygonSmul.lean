import GhostConjecture.NewtonPolygon
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Convex.Basic

namespace GhostConjecture

open scoped Pointwise

private lemma isClosed_add_singleton (C : Set (ℝ × ℝ)) (u : ℝ × ℝ) :
    IsClosed C → IsClosed (C + {u}) := by
  intro hC
  -- `C + {u}` is the image of `C` under the homeomorphism `x ↦ x + u`.
  simpa [Set.add_singleton, Homeomorph.coe_addRight] using
    (Homeomorph.addRight u).isClosed_image (s := C) |>.2 hC

private lemma convex_add_singleton (C : Set (ℝ × ℝ)) (u : ℝ × ℝ) :
    Convex ℝ C → Convex ℝ (C + {u}) := by
  intro hC
  exact hC.add (convex_singleton u)

private lemma verticalUpwardClosed_add_singleton (C : Set (ℝ × ℝ)) (u : ℝ × ℝ) :
    VerticalUpwardClosed C → VerticalUpwardClosed (C + {u}) := by
  intro hC x y y' hxy hy'
  -- Membership in `C + {u}` simplifies to membership in `C` after translating by `-u`.
  have hxyC : (x, y) - u ∈ C := by
    simpa [Set.add_singleton] using hxy
  have hxyC' : (x - u.1, y - u.2) ∈ C := by
    simpa using hxyC
  have hy_sub : y - u.2 ≤ y' - u.2 := sub_le_sub_right hy' u.2
  have : (x - u.1, y' - u.2) ∈ C :=
    hC (x - u.1) (y - u.2) (y' - u.2) hxyC' hy_sub
  -- Translate back to `C + {u}`.
  have : (x, y') - u ∈ C := by
    simpa using this
  simpa [Set.add_singleton] using this

private lemma lowerConvexHull_add_singleton (S : Set (ℝ × ℝ)) (u : ℝ × ℝ) :
    LowerConvexHull (S + {u}) = LowerConvexHull S + {u} := by
  classical
  ext p
  constructor
  · intro hp
    -- Translate the point back and use the defining intersection property.
    have hq : p - u ∈ LowerConvexHull S := by
      refine Set.mem_sInter.2 ?_
      intro C hC
      rcases hC with ⟨hClosed, hConvex, hSub, hUp⟩
      -- `C + {u}` is an admissible set for `S + {u}`.
      have hC' :
          C + {u} ∈
            { D : Set (ℝ × ℝ) |
                IsClosed D ∧ Convex ℝ D ∧ (S + {u}) ⊆ D ∧ VerticalUpwardClosed D } := by
        refine ⟨isClosed_add_singleton C u hClosed, convex_add_singleton C u hConvex, ?_, ?_⟩
        · intro x hx
          -- `x ∈ S + {u}` implies `x - u ∈ S`, hence `x - u ∈ C`, hence `x ∈ C + {u}`.
          have hxS : x - u ∈ S := by simpa [Set.add_singleton] using hx
          have hxC : x - u ∈ C := hSub hxS
          simpa [Set.add_singleton] using hxC
        · exact verticalUpwardClosed_add_singleton C u hUp
      have hpAll :
          ∀ D,
            D ∈
              { D : Set (ℝ × ℝ) |
                  IsClosed D ∧ Convex ℝ D ∧ (S + {u}) ⊆ D ∧ VerticalUpwardClosed D } →
              p ∈ D :=
        Set.mem_sInter.1 hp
      have hpC' : p ∈ C + {u} := hpAll (C + {u}) hC'
      -- Membership in `C + {u}` simplifies to `(p - u) ∈ C`.
      simpa [Set.add_singleton] using hpC'
    -- Translate forward again: membership in `LowerConvexHull S + {u}` reduces to
    -- membership of `p - u`.
    simpa [Set.add_singleton] using hq
  · intro hp
    -- Translate the membership back: `p ∈ LowerConvexHull S + {u}` iff `p - u ∈ LowerConvexHull S`.
    have hq : p - u ∈ LowerConvexHull S := by
      simpa [Set.add_singleton] using hp
    refine Set.mem_sInter.2 ?_
    intro C hC
    rcases hC with ⟨hClosed, hConvex, hSub, hUp⟩
    -- Translate `C` back by `-u` to get an admissible set for `S`.
    have hCback :
        C + {-u} ∈
          { D : Set (ℝ × ℝ) | IsClosed D ∧ Convex ℝ D ∧ S ⊆ D ∧ VerticalUpwardClosed D } := by
      refine ⟨isClosed_add_singleton C (-u) hClosed, convex_add_singleton C (-u) hConvex, ?_, ?_⟩
      · intro s hsS
        have hsSu : s + u ∈ S + {u} := by
          have : (s + u) - u ∈ S := by simpa using hsS
          simpa [Set.add_singleton] using this
        have hsu : s + u ∈ C := hSub hsSu
        -- `s ∈ C + {-u}` iff `s + u ∈ C`.
        simpa [Set.add_singleton, sub_eq_add_neg, add_assoc] using hsu
      · exact verticalUpwardClosed_add_singleton C (-u) hUp
    have hqC : p - u ∈ C + {-u} := (Set.mem_sInter.1 hq) (C + {-u}) hCback
    -- `p - u ∈ C + {-u}` iff `(p - u) - (-u) = p ∈ C`.
    simpa [Set.add_singleton, sub_eq_add_neg, add_assoc] using hqC

private lemma mem_newtonPoints_iff {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F : FormalPowerSeriesRing K) (n : ℕ) (r : ℝ) :
    (n, (r : WithTop ℝ)) ∈ NewtonPoints v F ↔
      PowerSeries.coeff n F ≠ (0 : K) ∧ v (PowerSeries.coeff n F) = (r : WithTop ℝ) := by
  constructor
  · rintro ⟨n', hn', hp⟩
    have hn : n = n' := congrArg Prod.fst hp
    have hv : (r : WithTop ℝ) = v (PowerSeries.coeff n' F) := congrArg Prod.snd hp
    subst hn
    exact ⟨hn', by simpa using hv.symm⟩
  · rintro ⟨hn, hv⟩
    refine ⟨n, hn, ?_⟩
    exact Prod.ext rfl hv.symm

/-- Vertical shift of the Newton polygon under multiplication by a nonzero scalar. -/
lemma newtonPolygon_smul {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (c : K) (F : FormalPowerSeriesRing K) (hc : c ≠ 0) :
    NewtonPolygon v (c • F) =
      NewtonPolygon v F +
        {((0 : ℝ),
          WithTop.untop (v c) (by
            intro htop
            have hmul : v (c * c⁻¹) = v c + v c⁻¹ := v.map_mul c c⁻¹
            have hone : v (c * c⁻¹) = (0 : WithTop ℝ) := by
              simp [mul_inv_cancel₀ hc]
            rw [hone] at hmul
            simp [htop] at hmul
          ))} := by
  classical
  -- Put the vertical shift into a name so we can use it throughout the proof.
  have hvc : v c ≠ (⊤ : WithTop ℝ) := by
    intro htop
    have hmul : v (c * c⁻¹) = v c + v c⁻¹ := v.map_mul c c⁻¹
    have hone : v (c * c⁻¹) = (0 : WithTop ℝ) := by
      simp [mul_inv_cancel₀ hc]
    rw [hone] at hmul
    simp [htop] at hmul
  set rc : ℝ := WithTop.untop (v c) hvc
  have hrc : (rc : WithTop ℝ) = v c := by
    dsimp [rc]
    exact WithTop.coe_untop (v c) hvc
  -- The set of finite Newton points used in the definition of `NewtonPolygon`.
  let P (G : FormalPowerSeriesRing K) : Set (ℝ × ℝ) :=
    { p : ℝ × ℝ |
        ∃ n : ℕ, ∃ r : ℝ, (n, (r : WithTop ℝ)) ∈ NewtonPoints v G ∧ p = ((n : ℝ), r) }
  have hP : P (c • F) = P F + {((0 : ℝ), rc)} := by
    ext p
    constructor
    · rintro ⟨n, r, hn, rfl⟩
      have hcoeff_ne : PowerSeries.coeff n (c • F) ≠ (0 : K) :=
        (mem_newtonPoints_iff v (c • F) n r).1 hn |>.1
      have hval_eq : v (PowerSeries.coeff n (c • F)) = (r : WithTop ℝ) :=
        (mem_newtonPoints_iff v (c • F) n r).1 hn |>.2
      have hcoeff_smul' :
          PowerSeries.coeff n (c • F) = c • PowerSeries.coeff n F :=
        PowerSeries.coeff_smul n F c
      have hcoeff_smul :
          PowerSeries.coeff n (c • F) = c * PowerSeries.coeff n F := by
        calc
          PowerSeries.coeff n (c • F) = c • PowerSeries.coeff n F := hcoeff_smul'
          _ = c * PowerSeries.coeff n F := by simp [smul_eq_mul]
      have hf_ne : PowerSeries.coeff n F ≠ (0 : K) := by
        intro hf0
        apply hcoeff_ne
        simp [hcoeff_smul, hf0]
      -- Extract a real `rf` with `v (coeff n F) = rf` (i.e. it is not `⊤`).
      have hvf_ne_top : v (PowerSeries.coeff n F) ≠ (⊤ : WithTop ℝ) := by
        intro hvf_top
        have htop' : v (PowerSeries.coeff n (c • F)) = (⊤ : WithTop ℝ) := by
          calc
            v (PowerSeries.coeff n (c • F))
                = v (c * PowerSeries.coeff n F) := by simp [hcoeff_smul]
            _ = v c + v (PowerSeries.coeff n F) := v.map_mul c (PowerSeries.coeff n F)
            _ = v c + (⊤ : WithTop ℝ) := by simp [hvf_top]
            _ = (⊤ : WithTop ℝ) := by simp
        have : (⊤ : WithTop ℝ) = (r : WithTop ℝ) := by
          calc
            (⊤ : WithTop ℝ) = v (PowerSeries.coeff n (c • F)) := by simpa using htop'.symm
            _ = (r : WithTop ℝ) := hval_eq
        exact (WithTop.coe_ne_top (a := r)) this.symm
      rcases (WithTop.ne_top_iff_exists).1 hvf_ne_top with ⟨rf, hrf⟩
      have hnF : (n, (rf : WithTop ℝ)) ∈ NewtonPoints v F := by
        refine (mem_newtonPoints_iff v F n rf).2 ?_
        exact ⟨hf_ne, hrf.symm⟩
      have hr : r = rf + rc := by
        have hcoe :
            (r : WithTop ℝ) = ((rc + rf : ℝ) : WithTop ℝ) := by
          calc
            (r : WithTop ℝ)
                = v (PowerSeries.coeff n (c • F)) := hval_eq.symm
            _ = v (c * PowerSeries.coeff n F) := by simp [hcoeff_smul]
            _ = v c + v (PowerSeries.coeff n F) := v.map_mul c (PowerSeries.coeff n F)
            _ = (rc : WithTop ℝ) + (rf : WithTop ℝ) := by simp [hrc, hrf]
            _ = ((rc + rf : ℝ) : WithTop ℝ) := by simp
        have : r = rc + rf := WithTop.coe_inj.1 (by simpa using hcoe)
        exact this.trans (add_comm _ _)
      -- Conclude membership in `P F + {shift}`.
      have hqP : ((n : ℝ), rf) ∈ P F := ⟨n, rf, hnF, rfl⟩
      have hsum : ((n : ℝ), rf) + ((0 : ℝ), rc) = ((n : ℝ), r) := by
        ext <;> simp [hr]
      -- Unfold the singleton-add as an image and provide the witness point.
      rw [Set.add_singleton]
      exact ⟨((n : ℝ), rf), hqP, hsum⟩
    · intro hp
      -- Unpack membership in the translated set.
      -- Work with the image description `P F + {shift} = (fun x => x + shift) '' P F`.
      rw [Set.add_singleton] at hp
      rcases hp with ⟨q, hqP, hqp⟩
      rcases hqP with ⟨n, rf, hnF, rfl⟩
      -- So `p = (n, rf) + (0, rc) = (n, rf + rc)`.
      have hp' : p = ((n : ℝ), rf + rc) := by
        simpa using hqp.symm
      -- Build the corresponding Newton point for `c • F`.
      have hf_ne : PowerSeries.coeff n F ≠ (0 : K) :=
        (mem_newtonPoints_iff v F n rf).1 hnF |>.1
      have hval_f : v (PowerSeries.coeff n F) = (rf : WithTop ℝ) :=
        (mem_newtonPoints_iff v F n rf).1 hnF |>.2
      have hcoeff_smul :
          PowerSeries.coeff n (c • F) = c * PowerSeries.coeff n F := by
        have hcoeff_smul' :
            PowerSeries.coeff n (c • F) = c • PowerSeries.coeff n F :=
          PowerSeries.coeff_smul n F c
        calc
          PowerSeries.coeff n (c • F) = c • PowerSeries.coeff n F := hcoeff_smul'
          _ = c * PowerSeries.coeff n F := by simp [smul_eq_mul]
      have hcoeff_ne : PowerSeries.coeff n (c • F) ≠ (0 : K) := by
        have : c * PowerSeries.coeff n F ≠ (0 : K) := mul_ne_zero hc hf_ne
        simpa [hcoeff_smul] using this
      have hval_cf : v (PowerSeries.coeff n (c • F)) = ((rf + rc : ℝ) : WithTop ℝ) := by
        calc
          v (PowerSeries.coeff n (c • F))
              = v (c * PowerSeries.coeff n F) := by simp [hcoeff_smul]
          _ = v c + v (PowerSeries.coeff n F) := v.map_mul c (PowerSeries.coeff n F)
          _ = (rc : WithTop ℝ) + (rf : WithTop ℝ) := by simp [hrc, hval_f]
          _ = ((rf + rc : ℝ) : WithTop ℝ) := by simp [add_comm]
      have hnCF : (n, ((rf + rc : ℝ) : WithTop ℝ)) ∈ NewtonPoints v (c • F) := by
        refine (mem_newtonPoints_iff v (c • F) n (rf + rc)).2 ?_
        exact ⟨hcoeff_ne, hval_cf⟩
      refine ⟨n, rf + rc, hnCF, ?_⟩
      exact hp'
  -- Finish by translating through `LowerConvexHull`.
  have hNP (G : FormalPowerSeriesRing K) : NewtonPolygon v G = LowerConvexHull (P G) := by
    simp [NewtonPolygon, P]
  calc
    NewtonPolygon v (c • F) = LowerConvexHull (P (c • F)) := hNP (G := c • F)
    _ = LowerConvexHull (P F + {((0 : ℝ), rc)}) := by simp [hP]
    _ = LowerConvexHull (P F) + {((0 : ℝ), rc)} := by
      simpa using (lowerConvexHull_add_singleton (S := P F) (u := ((0 : ℝ), rc)))
    _ = NewtonPolygon v F + {((0 : ℝ), rc)} := by simp [hNP (G := F)]

end GhostConjecture
