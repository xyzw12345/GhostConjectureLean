import GhostConjecture.NewtonPolygon

namespace GhostConjecture

/--
Monotonicity of Newton polygons under coefficientwise valuation bounds.
-/
lemma newtonPolygon_monotone {K : Type*} [Field K] (v : NonarchimedeanValuation K)
    (F G : FormalPowerSeriesRing K)
    (hsupp : ∀ n : ℕ, PowerSeries.coeff n G ≠ (0 : K) → PowerSeries.coeff n F ≠ (0 : K))
    (h : ∀ n : ℕ,
      PowerSeries.coeff n F ≠ (0 : K) →
      PowerSeries.coeff n G ≠ (0 : K) →
      v (PowerSeries.coeff n G) ≥ v (PowerSeries.coeff n F)) :
    NewtonPolygon v G ⊆ NewtonPolygon v F := by
  classical
  let SF : Set (ℝ × ℝ) :=
    { p : ℝ × ℝ |
        ∃ n : ℕ, ∃ r : ℝ, (n, (r : WithTop ℝ)) ∈ NewtonPoints v F ∧ p = ((n : ℝ), r) }
  let SG : Set (ℝ × ℝ) :=
    { p : ℝ × ℝ |
        ∃ n : ℕ, ∃ r : ℝ, (n, (r : WithTop ℝ)) ∈ NewtonPoints v G ∧ p = ((n : ℝ), r) }
  intro p hp
  -- Unfold the definition of `LowerConvexHull` membership for `p ∈ NewtonPolygon v G`.
  have hp_all :
      ∀ C : Set (ℝ × ℝ),
        (IsClosed C ∧ Convex ℝ C ∧ SG ⊆ C ∧ VerticalUpwardClosed C) → p ∈ C := by
    intro C hC
    have hp' :
        p ∈
          Set.sInter
            { C : Set (ℝ × ℝ) | IsClosed C ∧ Convex ℝ C ∧ SG ⊆ C ∧ VerticalUpwardClosed C } := by
      simpa [NewtonPolygon, LowerConvexHull, SG] using hp
    exact (Set.mem_sInter.mp hp') C hC
  -- Now show `p` belongs to the intersection defining `NewtonPolygon v F`.
  have hp' :
      p ∈
        Set.sInter
          { C : Set (ℝ × ℝ) | IsClosed C ∧ Convex ℝ C ∧ SF ⊆ C ∧ VerticalUpwardClosed C } := by
    refine Set.mem_sInter.mpr ?_
    intro C hC
    rcases hC with ⟨hC_closed, hC_convex, hC_SF, hC_vup⟩
    have hC_SG : SG ⊆ C := by
      intro q hq
      rcases hq with ⟨n, r, hnG, rfl⟩
      -- Unpack the Newton point information for `G`.
      rcases hnG with ⟨n', hGnz', hEq⟩
      have hnEq : n = n' := congrArg Prod.fst hEq
      have hGnz : PowerSeries.coeff n G ≠ (0 : K) := by
        simpa [hnEq] using hGnz'
      have hvG : v (PowerSeries.coeff n G) = (r : WithTop ℝ) := by
        have hr : (r : WithTop ℝ) = v (PowerSeries.coeff n' G) := congrArg Prod.snd hEq
        have hr' : (r : WithTop ℝ) = v (PowerSeries.coeff n G) := by simpa [hnEq] using hr
        exact hr'.symm
      -- Use the support inclusion to apply the valuation comparison hypothesis.
      have hFnz : PowerSeries.coeff n F ≠ (0 : K) := hsupp n hGnz
      have hle : v (PowerSeries.coeff n F) ≤ v (PowerSeries.coeff n G) := by
        simpa using (h n hFnz hGnz)
      -- Since `v(gₙ)` is finite (it equals `r`), so is `v(fₙ)`.
      have hvG_ne_top : v (PowerSeries.coeff n G) ≠ (⊤ : WithTop ℝ) := by
        simp [hvG]
      have hvF_ne_top : v (PowerSeries.coeff n F) ≠ (⊤ : WithTop ℝ) := by
        intro hvF_top
        have : (⊤ : WithTop ℝ) ≤ v (PowerSeries.coeff n G) := by simpa [hvF_top] using hle
        have hvG_top : v (PowerSeries.coeff n G) = (⊤ : WithTop ℝ) := (top_le_iff.mp this)
        exact hvG_ne_top hvG_top
      -- Extract the real valuation `rF` of `fₙ`, giving a point in `SF ⊆ C`.
      rcases
          (by
            cases hVF : v (PowerSeries.coeff n F) with
            | top =>
                exfalso
                exact hvF_ne_top (by simp [hVF])
            | coe rF =>
                exact ⟨rF, rfl⟩ :
            ∃ rF : ℝ, v (PowerSeries.coeff n F) = (rF : WithTop ℝ)) with
        ⟨rF, hvF⟩
      have hNewtonF : (n, (rF : WithTop ℝ)) ∈ NewtonPoints v F := by
        refine ⟨n, hFnz, ?_⟩
        simp [hvF]
      have hqF : ((n : ℝ), rF) ∈ SF := by
        refine ⟨n, rF, hNewtonF, rfl⟩
      have hqF_mem : ((n : ℝ), rF) ∈ C := hC_SF hqF
      -- Compare the real coordinates `rF ≤ r` using the hypothesis in `WithTop ℝ`.
      have hleWT : (rF : WithTop ℝ) ≤ (r : WithTop ℝ) := by
        simpa [hvF, hvG] using hle
      have hleReal : rF ≤ r := (WithTop.coe_le_coe.mp hleWT)
      exact hC_vup (n : ℝ) rF r hqF_mem hleReal
    exact hp_all C ⟨hC_closed, hC_convex, hC_SG, hC_vup⟩
  simpa [NewtonPolygon, LowerConvexHull, SF] using hp'
end GhostConjecture
