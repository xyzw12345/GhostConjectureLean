import GhostConjecture.MinkowskiSum
import GhostConjecture.SupportFunctionLower

namespace GhostConjecture

/-- Support function of a Minkowski sum: `h_{A+B}(λ) = h_A(λ) + h_B(λ)` (in `EReal`). -/
lemma supportFunctionLower_minkowskiSum (A B : Set (ℝ × ℝ)) (l : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    supportFunctionLower (minkowskiSum A B) l =
      supportFunctionLower A l + supportFunctionLower B l := by
  classical
  let φ : (ℝ × ℝ) → EReal := fun p => ((p.2 + l * p.1 : ℝ) : EReal)
  have hφ_add : ∀ a b : ℝ × ℝ, φ (a + b) = φ a + φ b := by
    intro a b
    -- rewrite the right-hand side to a single coercion, then reduce to a real identity
    change (( (a + b).2 + l * (a + b).1 : ℝ) : EReal) =
        ((a.2 + l * a.1 : ℝ) : EReal) + ((b.2 + l * b.1 : ℝ) : EReal)
    rw [← EReal.coe_add (a.2 + l * a.1) (b.2 + l * b.1)]
    refine (EReal.coe_eq_coe_iff).2 ?_
    simp [mul_add]
    ring
  -- Rewrite the left-hand side as an `sInf` over an `image2`.
  have h_image :
      φ '' minkowskiSum A B =
        Set.image2 (fun a b => φ a + φ b) A B := by
    -- `minkowskiSum A B` is `Set.image2 (· + ·) A B`
    -- and `φ (a + b) = φ a + φ b`.
    unfold minkowskiSum
    have :
        φ '' Set.image2 (· + ·) A B =
          Set.image2 (fun a b => φ (a + b)) A B := by
      simpa using (Set.image_image2 (f := (· + ·)) (g := φ) (s := A) (t := B))
    simpa [hφ_add] using this
  -- Unfold `supportFunctionLower` into an `sInf` and rewrite everything in terms of `φ`.
  unfold supportFunctionLower
  change sInf (φ '' minkowskiSum A B) = sInf (φ '' A) + sInf (φ '' B)
  rw [h_image, sInf_image2, sInf_image, sInf_image]
  -- abbreviate the two 1-variable infima
  set IA : EReal := ⨅ a ∈ A, φ a
  set IB : EReal := ⨅ b ∈ B, φ b
  change (⨅ a ∈ A, ⨅ b ∈ B, φ a + φ b) = IA + IB
  have hIA_ne_top : IA ≠ (⊤ : EReal) := by
    rcases hA with ⟨a, ha⟩
    have hle : IA ≤ φ a := by
      -- `IA` is an infimum, hence `≤` any term in the family.
      simpa [IA] using (iInf₂_le a ha)
    have hlt : φ a < (⊤ : EReal) := by
      -- `φ a` is a coerced real.
      simpa [φ] using (EReal.coe_lt_top (a.2 + l * a.1))
    exact (lt_of_le_of_lt hle hlt).ne
  have hIB_ne_top : IB ≠ (⊤ : EReal) := by
    rcases hB with ⟨b, hb⟩
    have hle : IB ≤ φ b := by
      simpa [IB] using (iInf₂_le b hb)
    have hlt : φ b < (⊤ : EReal) := by
      simpa [φ] using (EReal.coe_lt_top (b.2 + l * b.1))
    exact (lt_of_le_of_lt hle hlt).ne
  -- First inequality: `IA + IB` is a lower bound of all `φ a + φ b`.
  have h_le : IA + IB ≤ ⨅ a ∈ A, ⨅ b ∈ B, φ a + φ b := by
    refine le_iInf fun a => le_iInf fun ha => le_iInf fun b => le_iInf fun hb => ?_
    exact add_le_add (by simpa [IA] using (iInf₂_le a ha)) (by simpa [IB] using (iInf₂_le b hb))
  -- Second inequality: approximate the infima from above.
  have h_ge : (⨅ a ∈ A, ⨅ b ∈ B, φ a + φ b) ≤ IA + IB := by
    -- Use `le_of_forall_gt`: it suffices to show `⨅ ... < c` for every `c > IA + IB`.
    refine le_of_forall_gt ?_
    intro c hc
    -- Choose a real `r` with `IA + IB < r < c`.
    obtain ⟨r, hr₁, hr₂⟩ := EReal.exists_between_coe_real hc
    have hr₂' : ((r : ℝ) : EReal) < c := hr₂
    have hr₁' : IA + IB < ((r : ℝ) : EReal) := hr₁
    -- Show there exist `a ∈ A` and `b ∈ B` with `φ a + φ b < r`.
    have hexists :
        ∃ a ∈ A, ∃ b ∈ B, φ a + φ b < ((r : ℝ) : EReal) := by
      by_cases hIA_bot : IA = (⊥ : EReal)
      · -- If `IA = ⊥`, pick `b₀ ∈ B` and choose `a` far enough below.
        rcases hB with ⟨b0, hb0⟩
        let rb0 : ℝ := b0.2 + l * b0.1
        have hφb0 : φ b0 = (rb0 : EReal) := by simp [φ, rb0]
        have hsInfA : sInf (φ '' A) = (⊥ : EReal) := by
          -- `sInf (φ '' A) = IA` by `sInf_image`.
          simpa [IA, hIA_bot] using (sInf_image (f := φ) (s := A))
        have hbelow :
            ∀ t : ℝ, ∃ a ∈ A, φ a < ((t : ℝ) : EReal) := by
          intro t
          rcases (sInf_eq_bot.1 hsInfA) ((t : ℝ) : EReal) (by simp) with
            ⟨x, hx, hxlt⟩
          rcases hx with ⟨a, ha, rfl⟩
          exact ⟨a, ha, hxlt⟩
        -- Take `t = r - rb0 - 1`.
        rcases hbelow (r - rb0 - 1) with ⟨a, ha, ha_lt⟩
        refine ⟨a, ha, b0, hb0, ?_⟩
        -- Convert to a real inequality to finish.
        have ha_real :
            (a.2 + l * a.1) < (r - rb0 - 1) := by
          simpa [φ] using (EReal.coe_lt_coe_iff.1 ha_lt)
        have hsum_real : (a.2 + l * a.1) + rb0 < r := by
          linarith
        -- Now lift back to `EReal`.
        have hsumE : (((a.2 + l * a.1) + rb0 : ℝ) : EReal) < (r : EReal) :=
          (EReal.coe_lt_coe_iff).2 hsum_real
        have hsumE' :
            ((a.2 + l * a.1 : ℝ) : EReal) + (rb0 : EReal) < (r : EReal) := by
          simpa [EReal.coe_add] using hsumE
        simpa [φ, hφb0, rb0] using hsumE'
      · -- Otherwise, `IA` is finite. Symmetrically handle `IB = ⊥`, else both are finite.
        by_cases hIB_bot : IB = (⊥ : EReal)
        · rcases hA with ⟨a0, ha0⟩
          let ra0 : ℝ := a0.2 + l * a0.1
          have hφa0 : φ a0 = (ra0 : EReal) := by simp [φ, ra0]
          have hsInfB : sInf (φ '' B) = (⊥ : EReal) := by
            simpa [IB, hIB_bot] using (sInf_image (f := φ) (s := B))
          have hbelow :
              ∀ t : ℝ, ∃ b ∈ B, φ b < ((t : ℝ) : EReal) := by
            intro t
            rcases (sInf_eq_bot.1 hsInfB) ((t : ℝ) : EReal) (by simp) with
              ⟨x, hx, hxlt⟩
            rcases hx with ⟨b, hb, rfl⟩
            exact ⟨b, hb, hxlt⟩
          rcases hbelow (r - ra0 - 1) with ⟨b, hb, hb_lt⟩
          refine ⟨a0, ha0, b, hb, ?_⟩
          have hb_real :
              (b.2 + l * b.1) < (r - ra0 - 1) := by
            simpa [φ] using (EReal.coe_lt_coe_iff.1 hb_lt)
          have hsum_real : ra0 + (b.2 + l * b.1) < r := by
            linarith
          have hsumE : ((ra0 + (b.2 + l * b.1) : ℝ) : EReal) < (r : EReal) :=
            (EReal.coe_lt_coe_iff).2 hsum_real
          have hsumE' : (ra0 : EReal) + ((b.2 + l * b.1 : ℝ) : EReal) < (r : EReal) := by
            simpa [EReal.coe_add] using hsumE
          simpa [φ, hφa0, ra0] using hsumE'
        · -- Both `IA` and `IB` are finite; lift them to reals and use an epsilon argument.
          have hIA_ne_bot : IA ≠ (⊥ : EReal) := hIA_bot
          have hIB_ne_bot : IB ≠ (⊥ : EReal) := hIB_bot
          set aInf : ℝ := IA.toReal
          set bInf : ℝ := IB.toReal
          have hIA_coe : (aInf : EReal) = IA := by
            simpa [aInf] using (EReal.coe_toReal hIA_ne_top hIA_ne_bot)
          have hIB_coe : (bInf : EReal) = IB := by
            simpa [bInf] using (EReal.coe_toReal hIB_ne_top hIB_ne_bot)
          have hr_real : aInf + bInf < r := by
            have hr' : (aInf : EReal) + (bInf : EReal) < (r : EReal) := by
              simpa [hIA_coe, hIB_coe] using hr₁'
            have hrE : ((aInf + bInf : ℝ) : EReal) < (r : EReal) := by
              calc
                ((aInf + bInf : ℝ) : EReal) = (aInf : EReal) + (bInf : EReal) := by
                  simp [EReal.coe_add]
                _ < (r : EReal) := hr'
            exact (EReal.coe_lt_coe_iff).1 hrE
          let ε : ℝ := (r - (aInf + bInf)) / 2
          have hε : 0 < ε := by
            dsimp [ε]
            linarith
          let rA : ℝ := aInf + ε
          let rB : ℝ := bInf + ε
          have hIA_lt : IA < (rA : EReal) := by
            have : aInf < rA := by
              dsimp [rA]
              linarith
            have : (aInf : EReal) < (rA : EReal) := by
              simpa [EReal.coe_lt_coe_iff] using this
            simpa [hIA_coe] using this
          have hIB_lt : IB < (rB : EReal) := by
            have : bInf < rB := by
              dsimp [rB]
              linarith
            have : (bInf : EReal) < (rB : EReal) := by
              simpa [EReal.coe_lt_coe_iff] using this
            simpa [hIB_coe] using this
          -- Choose `a ∈ A` and `b ∈ B` close enough to the respective infima.
          have hA_exists : ∃ a ∈ A, φ a < (rA : EReal) :=
            (biInf_lt_iff.1 (by simpa [IA] using hIA_lt))
          have hB_exists : ∃ b ∈ B, φ b < (rB : EReal) :=
            (biInf_lt_iff.1 (by simpa [IB] using hIB_lt))
          rcases hA_exists with ⟨a, ha, ha_lt⟩
          rcases hB_exists with ⟨b, hb, hb_lt⟩
          refine ⟨a, ha, b, hb, ?_⟩
          -- Convert to a real inequality.
          have ha_real : (a.2 + l * a.1) < rA := by
            simpa [φ] using (EReal.coe_lt_coe_iff.1 ha_lt)
          have hb_real : (b.2 + l * b.1) < rB := by
            simpa [φ] using (EReal.coe_lt_coe_iff.1 hb_lt)
          have hsum_real : (a.2 + l * a.1) + (b.2 + l * b.1) < r := by
            have : rA + rB = r := by
              dsimp [rA, rB, ε]
              ring
            -- strict sum bound
            calc
              (a.2 + l * a.1) + (b.2 + l * b.1) < rA + rB := by
                exact add_lt_add ha_real hb_real
              _ = r := this
          have hsumE :
              (((a.2 + l * a.1) + (b.2 + l * b.1) : ℝ) : EReal) < (r : EReal) :=
            (EReal.coe_lt_coe_iff).2 hsum_real
          have hsumE' :
              ((a.2 + l * a.1 : ℝ) : EReal) + ((b.2 + l * b.1 : ℝ) : EReal) < (r : EReal) := by
            simpa [EReal.coe_add] using hsumE
          simpa [φ] using hsumE'
    -- Turn the witness into `⨅ a ∈ A, ⨅ b ∈ B, φ a + φ b < c`.
    rcases hexists with ⟨a, ha, b, hb, hab⟩
    -- `hab : φ a + φ b < r`, and `r < c`.
    have hab' : φ a + φ b < c := lt_trans hab hr₂'
    -- Use `biInf_lt_iff` twice.
    refine (biInf_lt_iff).2 ?_
    refine ⟨a, ha, ?_⟩
    refine (biInf_lt_iff).2 ?_
    exact ⟨b, hb, hab'⟩
  -- combine the inequalities
  exact le_antisymm (by simpa [IA, IB] using h_ge) (by simpa [IA, IB] using h_le)
end GhostConjecture
