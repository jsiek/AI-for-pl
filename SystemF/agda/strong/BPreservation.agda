module strong.BPreservation where

-- Type preservation for the tight dual boundary (B₀) design (PLAN.md §3–§4).
--
-- Stated at RUNTIME term contexts (Γₜ = []) over the KNOWLEDGE-INDEXED
-- reduction relation: one step preserves the type, at the SAME type context
-- on both judgements.  Case order follows BReduction's rhythm — the four
-- computation rules first, then the five ξ congruences.
--
--   TyBeta  is where a boundary is BORN.  Its (env) premises are discharged by
--        the reveal's well-formedness (bwf↑), the two face equations (int-eq
--        for γᵇ, ext-eq for ρᵇ), and — for the Scoped premise, which no
--        reduction rule carries — the typing ⇒ wf ⇒ Scoped bridge scB-bridge.
--        The Λ-binder's abstract slot becomes the new reveal's KNOWLEDGE slot,
--        so the body is retagged along `abst ≼≈ anything` (⊢retag≈).
--   Beta  is the term-substitution lemma (strong.TermSubst).
--   TyPeel is TyWrap's case with the body weakened by ⊢⇑ᵀ and type-applied
--        at the new reveal's variable (peel-tyarg); everything outside the
--        wrapped term is TyWrap's, verbatim.
--   TyWrap transports the Λ body by the shift family (intOf-shift,
--        γᵇ-shift-ty, ρᵇ-shift-ty, baseS-shift, bwf-shift); the type argument
--        is recorded UNCHANGED as the new reveal's rep — the PARALLEL reveal
--        block reads it in the plain exterior, where the redex's own Δ ⊢ A
--        already places it, so no lift and no wf-lift.
--   Peel  builds the AMBIENT DUAL (as the old Wrap did, minus the
--        β-substitution).  Its face laws are theorems
--        (ρᵇ-dual-ty / γᵇ-dual-ty); its well-formedness and its rebuild law
--        are the strong.DualDef parameters — see there for exactly which part
--        is proven and which is the (R2) residue.
--   ξ-*  are each one induction hypothesis under the corresponding typing
--        rule.  Two of them change the index: ξ-Λ recurses at (abst ∷ Δ) —
--        and ⤊ [] = [] definitionally — and ξ-⟪⟫ at the boundary INTERIOR
--        intOf Δ Θ, which is exactly what the reduction rule extends by.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst; subst₂)
open import strong.Types
open import strong.TypeSubst using (subst-cong; subst-id)
open import strong.Context using (TCtx; TyEntry; _⊢_; wf-var)
open import strong.Boundary
open import strong.BReduction
open import strong.ScopeBridge using (scB-bridge)
open import strong.TermSubst using (preserve-Beta)
open import strong.DualDef
  using (DualRep≈; DualCnc≈; DualInt≈; bwf-dual)

private
  variable
    Δ : TCtx
    A B B₁ B₂ : Ty
    M M′ : Term

-- Parameterised over the three open facts about the ambient dual
-- (strong.DualDef).  Everything else is proven.  Instantiate `Impl` once the
-- (R2) residue is ruled on.
module Impl (dual-rep : DualRep≈) (dual-cnc : DualCnc≈)
            (dual-int : DualInt≈)
  where

  preservation : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A

  ----------------------------------------------------------------------
  -- Computation rules
  ----------------------------------------------------------------------

  -- TyBeta:  (ΛX.V) [B , A]  →  V ⟪ ↑X:=A , B ⟫
  preservation {Δ} (⊢·[] {B = B} {A = A} (⊢Λ {N = V} ⊢V) ⊢A) (TyBeta v) =
    subst (λ T → Δ ∣ [] ⊢ V ⟪ rvl A ∷ [] , B ⟫ ⦂ T) ext-eq
      (env {B₀ = B} (bwf↑ ⊢A bwf[])
           scB
           (subst (λ T → intOf Δ (rvl A ∷ []) ∣ [] ⊢ V ⦂ T) (sym int-eq)
                  (⊢retag≈ (≼≈abst (≼≈-refl Δ)) ⊢V)))
    where
      -- internal face:  γᵇ [rvl A] = prepId 1 (γcnc 1 0 [rvl A]),
      -- pointwise `_
      gvar : (x : ℕ) → γᵇ (rvl A ∷ []) x ≡ ` x
      gvar zero    = refl
      gvar (suc _) = refl
      int-eq : substᵗ (γᵇ (rvl A ∷ [])) B ≡ B
      int-eq = trans (subst-cong gvar B) (subst-id B)
      -- external face:  ρᵇ [rvl A] is A •ᵗ `_, i.e. singleTyEnv A on the nose
      ext-eq : substᵗ (ρᵇ (rvl A ∷ [])) B ≡ B [ A ]ᵗ
      ext-eq = subst-cong (λ { zero → refl ; (suc _) → refl }) B
      -- Scoped obligation: baseS [rvl A] Δ is ALL ok (cmax = 0), and B is the
      -- ∀-body of Λ V — well-scoped over abst ∷ Δ.  ⊢V is typed at ⤊ [] = [],
      -- exactly scB-bridge's shape.
      scB : Scoped (baseS (rvl A ∷ []) Δ) B
      scB = scB-bridge ⊢V

  -- Beta:  (λx:A.N) · W  →  N[x:=W]  — the term-substitution lemma
  preservation (⊢· (⊢ƛ wfA ⊢N) ⊢W) (Beta w) =
    preserve-Beta (⊢· (⊢ƛ wfA ⊢N) ⊢W)

  -- R1:  ((Λ V) ⟪ Θ , ∀B₀ ⟫) ·[ B , A ]  →  V ⟪ ↑?:=A ∷ Θ⁺ , B₀ ⟫
  --
  -- The redex's B is FORCED, so the pattern supplies it: (env) types the
  -- wrapper at substᵗ (ρᵇ Θ) (`∀ B₀), which is `∀ (substᵗ (extsᵗ (ρᵇ Θ)) B₀),
  -- so B is that ∀-body.  Likewise the body Λ V is typed at
  -- substᵗ (γᵇ Θ) (`∀ B₀) = `∀ (substᵗ (extsᵗ (γᵇ Θ)) B₀), so inverting ⊢Λ
  -- gives ⊢V at (abst ∷ intOf Δ Θ) ∣ ⤊ [].  The new boundary's interior is
  -- that context with the new reveal's KNOWLEDGE entry in place of the
  -- abstract one (intOf-shift), so ⊢retag≈ along `abst ≼≈ anything` moves V
  -- there; its interior face is γᵇ-shift-ty.  NOTHING renames the term: the
  -- Λ-binder's slot became the reveal slot.  The type argument A is not
  -- pushed inward and NOT LIFTED either — under the parallel reveal block it
  -- is the new reveal's rep verbatim, licensed by the redex's own Δ ⊢ A and
  -- read back by ρᵇ-shift-ty into the redex's B [ A ]ᵗ.
  preservation {Δ} (⊢·[] (env {Θ = Θ} {B₀ = `∀ B₀} bwf (sc-∀ sc)
                              (⊢Λ {N = V} ⊢V))
                         wfA)
                   (TyWrap {A = A} v) =
    subst (λ T → Δ ∣ [] ⊢ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫ ⦂ T)
          (ρᵇ-shift-ty A Θ B₀)
      (env (bwf-shift Θ bwf wfA) sc′ ⊢body)
    where
      -- scope: the new stack is the old one with the reveal's slot on top
      -- (baseS-shift), which is exactly what sc-∀ inverted out of the redex's
      sc′ : Scoped (baseS (rvl A ∷ shiftReps Θ) Δ) B₀
      sc′ = subst (λ Ψ → Scoped Ψ B₀) (sym (baseS-shift A Θ Δ)) sc
      -- the Λ-body, retagged into the new interior and retyped at the new
      -- interior face
      ⊢body : intOf Δ (rvl A ∷ shiftReps Θ) ∣ []
                ⊢ V ⦂ substᵗ (γᵇ (rvl A ∷ shiftReps Θ)) B₀
      ⊢body = subst₂ (λ Ψ T → Ψ ∣ [] ⊢ V ⦂ T)
                     (sym (intOf-shift Δ A Θ))
                     (sym (γᵇ-shift-ty A Θ B₀))
                     (⊢retag≈ (≼≈abst (≼≈-refl (intOf Δ Θ))) ⊢V)

  -- TyPeel:  ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ , ∀B₀ ⟫) ·[ B , A ]
  --            →  (⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ peelB Θ B₀ , ` 0 ])
  --                 ⟪ ↑?:=A ∷ Θ⁺ , B₀ ⟫
  --
  -- Everything OUTSIDE the wrapped term is TyWrap's case verbatim: the same
  -- boundary is minted (bwf-shift), the same scope premise survives
  -- (baseS-shift), and the same external face law (ρᵇ-shift-ty) carries the
  -- contractum to the redex's B [ A ]ᵗ.  What changes is the BODY.  TyWrap
  -- consumed a Λ whose binder's slot BECAME the new reveal slot, so its body
  -- was already typed one context deeper; TyPeel's body is an arbitrary
  -- wrapper typed at the OLD interior, so it is WEAKENED by the one slot the
  -- new reveal adds (⊢⇑ᵀ) and then type-applied to that very slot's
  -- variable ` 0.  Instantiating a weakened ∀ at the fresh variable is the
  -- identity on types (peel-tyarg), so the body lands at the interior face
  -- substᵗ (extsᵗ (γᵇ Θ)) B₀ — which γᵇ-shift-ty turns into the new
  -- boundary's internal face, exactly as in TyWrap.
  preservation {Δ} (⊢·[] (env {Θ = Θ} {B₀ = `∀ B₀} bwf (sc-∀ sc) ⊢Vw)
                         wfA)
                   (TyPeel {V = V} {Θ₁ = Θ₁} {B₁ = B₁} {A = A} v) =
    subst (λ T → Δ ∣ [] ⊢ Ctr ⦂ T) (ρᵇ-shift-ty A Θ B₀)
      (env (bwf-shift Θ bwf wfA) sc′ ⊢body)
    where
      Ent : TyEntry
      Ent = ⟦ rvl A ∷ shiftReps Θ ⟧ᴴ 0 A
      Inn : Term                                   -- the peeled application
      Inn = ⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ peelB Θ B₀ , ` 0 ]
      Ctr : Term                                   -- the contractum
      Ctr = Inn ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫
      sc′ : Scoped (baseS (rvl A ∷ shiftReps Θ) Δ) B₀
      sc′ = subst (λ Ψ → Scoped Ψ B₀) (sym (baseS-shift A Θ Δ)) sc
      -- the wrapped value, weakened by the new reveal's slot
      ⊢w : (Ent ∷ intOf Δ Θ) ∣ []
             ⊢ ⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ⦂ ⇑ᵗ (substᵗ (γᵇ Θ) (`∀ B₀))
      ⊢w = ⊢⇑ᵀ ⊢Vw
      -- … type-applied at the new reveal's own variable
      ⊢app : (Ent ∷ intOf Δ Θ) ∣ []
               ⊢ Inn ⦂ substᵗ (extsᵗ (γᵇ Θ)) B₀
      ⊢app = subst (λ T → (Ent ∷ intOf Δ Θ) ∣ [] ⊢ Inn ⦂ T)
                   (peel-tyarg (substᵗ (extsᵗ (γᵇ Θ)) B₀))
                   (⊢·[] ⊢w (wf-var (ent-here-tv Ent)))
      ⊢body : intOf Δ (rvl A ∷ shiftReps Θ) ∣ []
                ⊢ Inn ⦂ substᵗ (γᵇ (rvl A ∷ shiftReps Θ)) B₀
      ⊢body = subst₂ (λ Ψ T → Ψ ∣ [] ⊢ Inn ⦂ T)
                     (sym (intOf-shift Δ A Θ))
                     (sym (γᵇ-shift-ty A Θ B₀))
                     ⊢app

  -- Peel:  ((V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W)
  --         →  (V · (W ⟪ Θᵈ , B₁ᵈ ⟫)) ⟪ Θ , B₂ ⟫
  --
  -- Both indices of the redex are FORCED: (env) types the wrapper at
  -- substᵗ (ρᵇ Θ) (B₁ ⇒ B₂), which is substᵗ (ρᵇ Θ) B₁ ⇒ substᵗ (ρᵇ Θ) B₂,
  -- so ⊢W is at substᵗ (ρᵇ Θ) B₁ and the whole redex at substᵗ (ρᵇ Θ) B₂ —
  -- which is exactly what the rebuilt (env) returns, so the outer type needs
  -- no transport.  The body is typed at the INTERIOR face
  -- substᵗ (γᵇ Θ) B₁ ⇒ substᵗ (γᵇ Θ) B₂, so it applies to the crossed
  -- argument on the nose — THIS IS THE OLD Wrap CASE MINUS THE
  -- β-SUBSTITUTION: the ⊢ƛ inversion and strong.TermSubst's ⊢[]ᵐ are gone,
  -- and (⊢·) takes their place.  The dual-crossing machinery is untouched.
  --
  -- The INNER wrapper sits at exterior intOf Δ Θ with the AMBIENT dual: its
  -- exterior face is the argument type the interior demands (ρᵇ-dual-ty,
  -- scope-restricted — the blocked slots differ, and (env)'s premise for B₁
  -- is what rules them out) and its interior face is W's own type
  -- (γᵇ-dual-ty).  Both are theorems.  What is assumed is only that the dual
  -- is a WELL-FORMED boundary (dual-rep / dual-cnc, assembled by bwf-dualᴳ)
  -- and that its interior rebuilds Δ up to ≼ (dual-int) — strong.DualDef.
  preservation {Δ} (⊢· {M = W} (env {Θ = Θ} {B₀ = B₁ ⇒ B₂} bwf
                                    (sc-⇒ sc₁ sc₂) ⊢V)
                       ⊢W)
                   (Peel v w) =
    env bwf sc₂ (⊢· ⊢V ⊢arg)
    where
      -- W retypes in the dual's interior, at the dual's interior face
      ⊢W′ : intOf (intOf Δ Θ) (dualᴳ Δ Θ) ∣ []
              ⊢ W ⦂ substᵗ (γᵇ (dualᴳ Δ Θ)) (renameᵗ (swapᵇ Θ) B₁)
      ⊢W′ = subst (λ T → intOf (intOf Δ Θ) (dualᴳ Δ Θ) ∣ [] ⊢ W ⦂ T)
                  (sym (γᵇ-dual-ty Δ B₁ Θ sc₁))
                  (⊢retag≈ (dual-int bwf) ⊢W)
      -- the wrapped argument, at the type the ƛ's annotation demands
      ⊢arg : intOf Δ Θ ∣ []
               ⊢ W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ⦂ substᵗ (γᵇ Θ) B₁
      ⊢arg = subst (λ T → intOf Δ Θ ∣ []
                            ⊢ W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ⦂ T)
                   (ρᵇ-dual-ty Δ B₁ Θ sc₁)
                   (env (bwf-dual dual-rep dual-cnc dual-int bwf)
                        (sc-dual Δ Θ sc₁) ⊢W′)

  -- Merge:  (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫  →  V ⟪ Θ₁ ⊕ Θ₂ , B₂′ ⟫
  --
  -- The redex's type is FORCED to be the outer wrapper's external face
  -- substᵗ (ρᵇ Θ₂) B₂, and the merged wrapper's is substᵗ (ρᵇ (Θ₁ ⊕ Θ₂))
  -- B₂′ — MergeOK's last component is exactly the equation between them
  -- (see strong.BReduction's part 4 for why it is a premise and not a
  -- lemma).  Everything else:
  --
  --   * the MIDDLE-TYPE equation comes from inverting the nested (env)
  --     (env-ty / mid-eq): the inner wrapper's external face IS the outer
  --     one's internal face, which is what makes the body's own typing
  --     usable at all;
  --   * the body moves from the nested interior intOf (intOf Δ Θ₂) Θ₁ to
  --     the composite's intOf Δ (Θ₁ ⊕ Θ₂) by ⊢retag≈ along MergeOK's
  --     ordering — the interiors compose only UP TO ≼≈ (Example 3's tower:
  --     nested, the innermost entry is the reveal VARIABLE below it;
  --     merged, it is that reveal's own rep, one unfolding further);
  --   * its TYPE is unchanged, because the INTERNAL face composes on the
  --     nose — ⊕-γ, a theorem, given MergeOK's scope side condition and
  --     the inner (env)'s own Scoped premise (env-sc).
  preservation {Δ} (env {Θ = Θ₂} {B₀ = B₂} bwf₂ sc₂ ⊢in)
                   (Merge {Θ₁ = Θ₁} {B₁ = B₁} v
                          (le , b⊕ , sc⊕ , int , ext)) =
    subst (λ T → Δ ∣ [] ⊢ _ ⦂ T) ext (env b⊕ sc⊕ ⊢body)
    where
      ⊢body : intOf Δ (Θ₁ ⊕ Θ₂) ∣ []
                ⊢ _ ⦂ substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁)
      ⊢body = subst (λ T → intOf Δ (Θ₁ ⊕ Θ₂) ∣ [] ⊢ _ ⦂ T)
                    (sym (⊕-γ Θ₁ Θ₂ le (env-sc ⊢in)))
                    (⊢retag≈ int (env-body ⊢in))

  -- Drop∅:  V ⟪ ∅ , B₀ ⟫  →  V.  At Θ = [] the interior IS the exterior
  -- (revEnts [] = [] and dropN 0 Δ = Δ, both definitionally) and BOTH
  -- faces are the identity substitution — ρᵇ [] is `_ on the nose and
  -- γᵇ [] is pointwise `_ — so the case is refl up to that one
  -- subst-cong.
  preservation {Δ} (env {B₀ = B₀} bwf sc ⊢V) (Drop∅ v) =
    subst (λ T → Δ ∣ [] ⊢ _ ⦂ T) faces ⊢V
    where
      gvar : ∀ j → γᵇ [] j ≡ ρᵇ [] j
      gvar j = refl
      faces : substᵗ (γᵇ []) B₀ ≡ substᵗ (ρᵇ []) B₀
      faces = subst-cong gvar B₀

  ----------------------------------------------------------------------
  -- ξ (congruence) rules: the induction hypothesis under the typing rule
  ----------------------------------------------------------------------

  preservation (⊢· ⊢L ⊢M) (ξ-·-l L→L′) =
    ⊢· (preservation ⊢L L→L′) ⊢M

  preservation (⊢· ⊢V ⊢M) (ξ-·-r v M→M′) =
    ⊢· ⊢V (preservation ⊢M M→M′)

  preservation (⊢·[] ⊢L ⊢A) (ξ-·[] L→L′) =
    ⊢·[] (preservation ⊢L L→L′) ⊢A

  -- the body of a Λ is typed at (abst ∷ Δ) ∣ ⤊ [], and ⤊ [] = [] — which is
  -- exactly the index ξ-Λ extends by
  preservation (⊢Λ ⊢N) (ξ-Λ N→N′) =
    ⊢Λ (preservation ⊢N N→N′)

  -- the interior of a boundary is typed at intOf Δ Θ ∣ [] — exactly the index
  -- ξ-⟪⟫ extends by; the boundary's premises (bwf, sc) mention only Θ and B₀,
  -- so they are carried across intact
  preservation (env bwf sc ⊢M) (ξ-⟪⟫ M→M′) =
    env bwf sc (preservation ⊢M M→M′)
