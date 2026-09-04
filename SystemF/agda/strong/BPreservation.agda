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
--        so the body is retagged along `abst ≼ anything` (⊢retag).
--   Beta  is the term-substitution lemma (strong.TermSubst).
--   TyWrap transports the Λ body by the shift family (intOf-shift,
--        γᵇ-shift-ty, ρᵇ-shift-ty, baseS-shift, bwf-shift); the type argument
--        is LIFTED past the boundary's existing reveals (the telescopic reveal
--        block), and wf-lift is that lift's well-formedness.
--   Wrap  builds the AMBIENT DUAL.  Its face laws are theorems
--        (ρᵇ-dual-ty / γᵇ-dual-ty); its well-formedness and its rebuild law
--        are the strong.DualDef parameters — see there for exactly which part
--        is proven and which is the (R2) residue.
--   ξ-*  are each one induction hypothesis under the corresponding typing
--        rule.  Two of them change the index: ξ-Λ recurses at (abst ∷ Δ) —
--        and ⤊ [] = [] definitionally — and ξ-⟪⟫ at the boundary INTERIOR
--        intOf Δ Θ, which is exactly what the reduction rule extends by.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst; subst₂)
open import strong.Types
open import strong.TypeSubst using (subst-cong; subst-id)
open import strong.Context using (TCtx; _⊢_)
open import strong.Boundary
open import strong.BReduction
open import strong.ScopeBridge using (scB-bridge)
open import strong.TermSubst using (preserve-Beta; ⊢[]ᵐ)
open import strong.DualDef
  using (DualRep; DualCnc; DualInt; bwf-dualᴳ)

private
  variable
    Δ : TCtx
    A B B₁ B₂ : Ty
    M M′ : Term

-- Parameterised over the three open facts about the ambient dual
-- (strong.DualDef).  Everything else is proven.  Instantiate `Impl` once the
-- (R2) residue is ruled on.
module Impl (dual-rep : DualRep) (dual-cnc : DualCnc) (dual-int : DualInt)
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
                  (⊢retag (≼abst (≼-refl Δ)) ⊢V)))
    where
      -- internal face:  γᵇ [rvl A] = prepId 1 (γcnc 1 0 [rvl A]),
      -- pointwise `_
      gvar : (x : ℕ) → γᵇ (rvl A ∷ []) x ≡ ` x
      gvar zero    = refl
      gvar (suc _) = refl
      int-eq : substᵗ (γᵇ (rvl A ∷ [])) B ≡ B
      int-eq = trans (subst-cong gvar B) (subst-id B)
      -- external face:  ρᵇ [rvl A] is (substᵗ `_ A) •ᵗ `_, i.e. singleTyEnv A
      ext-eq : substᵗ (ρᵇ (rvl A ∷ [])) B ≡ B [ A ]ᵗ
      ext-eq = subst-cong (λ { zero → subst-id A ; (suc _) → refl }) B
      -- Scoped obligation: baseS [rvl A] Δ is ALL ok (cmax = 0), and B is the
      -- ∀-body of Λ V — well-scoped over abst ∷ Δ.  ⊢V is typed at ⤊ [] = [],
      -- exactly scB-bridge's shape.
      scB : Scoped (baseS (rvl A ∷ []) Δ) B
      scB = scB-bridge ⊢V

  -- Beta:  (λx:A.N) · W  →  N[x:=W]  — the term-substitution lemma
  preservation (⊢· (⊢ƛ wfA ⊢N) ⊢W) (Beta w) =
    preserve-Beta (⊢· (⊢ƛ wfA ⊢N) ⊢W)

  -- R1:  ((Λ V) ⟪ Θ , ∀B₀ ⟫) ·[ B , A ]  →  V ⟪ ↑(A lifted) ∷ Θ⁺ , B₀ ⟫
  --
  -- The redex's B is FORCED, so the pattern supplies it: (env) types the
  -- wrapper at substᵗ (ρᵇ Θ) (`∀ B₀), which is `∀ (substᵗ (extsᵗ (ρᵇ Θ)) B₀),
  -- so B is that ∀-body.  Likewise the body Λ V is typed at
  -- substᵗ (γᵇ Θ) (`∀ B₀) = `∀ (substᵗ (extsᵗ (γᵇ Θ)) B₀), so inverting ⊢Λ
  -- gives ⊢V at (abst ∷ intOf Δ Θ) ∣ ⤊ [].  The new boundary's interior is
  -- that context with the new reveal's KNOWLEDGE entry in place of the
  -- abstract one (intOf-shift), so ⊢retag along `abst ≼ anything` moves V
  -- there; its interior face is γᵇ-shift-ty.  NOTHING renames the term: the
  -- Λ-binder's slot became the reveal slot.  The type argument A is not
  -- pushed inward — it is the new reveal's rep, lifted past the boundary's
  -- existing reveals (the telescope) and read back by ρᵇ-shift-ty into the
  -- redex's B [ A ]ᵗ.
  preservation {Δ} (⊢·[] (env {Θ = Θ} {B₀ = `∀ B₀} bwf (sc-∀ sc)
                              (⊢Λ {N = V} ⊢V))
                         wfA)
                   (TyWrap {A = A} v) =
    subst (λ T → Δ ∣ [] ⊢ V ⟪ rvl A′ ∷ shiftReps Θ , B₀ ⟫ ⦂ T)
          (ρᵇ-shift-ty A Θ B₀)
      (env (bwf-shift Θ bwf (wf-lift Θ wfA)) sc′ ⊢body)
    where
      A′ : Ty
      A′ = renameᵗ (revs Θ +_) A
      -- scope: the new stack is the old one with the reveal's slot on top
      -- (baseS-shift), which is exactly what sc-∀ inverted out of the redex's
      sc′ : Scoped (baseS (rvl A′ ∷ shiftReps Θ) Δ) B₀
      sc′ = subst (λ Ψ → Scoped Ψ B₀) (sym (baseS-shift A′ Θ Δ)) sc
      -- the Λ-body, retagged into the new interior and retyped at the new
      -- interior face
      ⊢body : intOf Δ (rvl A′ ∷ shiftReps Θ) ∣ []
                ⊢ V ⦂ substᵗ (γᵇ (rvl A′ ∷ shiftReps Θ)) B₀
      ⊢body = subst₂ (λ Ψ T → Ψ ∣ [] ⊢ V ⦂ T)
                     (sym (intOf-shift Δ A′ Θ))
                     (sym (γᵇ-shift-ty A′ Θ B₀))
                     (⊢retag (≼abst (≼-refl (intOf Δ Θ))) ⊢V)

  -- R2:  ((ƛ A′ ∙ N) ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
  --         →  (N [ W ⟪ Θᵈ , B₁ᵈ ⟫ ]ᵐ) ⟪ Θ , B₂ ⟫
  --
  -- Both indices of the redex are FORCED: (env) types the wrapper at
  -- substᵗ (ρᵇ Θ) (B₁ ⇒ B₂), which is substᵗ (ρᵇ Θ) B₁ ⇒ substᵗ (ρᵇ Θ) B₂,
  -- so ⊢W is at substᵗ (ρᵇ Θ) B₁ and the whole redex at substᵗ (ρᵇ Θ) B₂ —
  -- which is exactly what the rebuilt (env) returns, so the outer type needs
  -- no transport.  Likewise the body is typed at the INTERIOR face
  -- substᵗ (γᵇ Θ) B₁ ⇒ substᵗ (γᵇ Θ) B₂, so inverting ⊢ƛ forces the ƛ's
  -- annotation to be substᵗ (γᵇ Θ) B₁ and gives ⊢N at the term context
  -- (substᵗ (γᵇ Θ) B₁ ∷ []) — exactly ⊢[]ᵐ's shape.
  --
  -- The INNER wrapper sits at exterior intOf Δ Θ with the AMBIENT dual: its
  -- exterior face is the argument type the ƛ demands (ρᵇ-dual-ty, scope-
  -- restricted — the blocked slots differ, and (env)'s premise for B₁ is what
  -- rules them out) and its interior face is W's own type (γᵇ-dual-ty).
  -- Both are theorems.  What is assumed is only that the dual is a WELL-FORMED
  -- boundary (dual-rep / dual-cnc, assembled by bwf-dualᴳ) and that its
  -- interior rebuilds Δ up to ≼ (dual-int) — strong.DualDef.
  preservation {Δ} (⊢· {M = W} (env {Θ = Θ} {B₀ = B₁ ⇒ B₂} bwf
                                    (sc-⇒ sc₁ sc₂) (⊢ƛ wfA′ ⊢N))
                       ⊢W)
                   (Wrap w) =
    env bwf sc₂ (⊢[]ᵐ ⊢N ⊢arg)
    where
      -- W retypes in the dual's interior, at the dual's interior face
      ⊢W′ : intOf (intOf Δ Θ) (dualᴳ Δ Θ) ∣ []
              ⊢ W ⦂ substᵗ (γᵇ (dualᴳ Δ Θ)) (renameᵗ (swapᵇ Θ) B₁)
      ⊢W′ = subst (λ T → intOf (intOf Δ Θ) (dualᴳ Δ Θ) ∣ [] ⊢ W ⦂ T)
                  (sym (γᵇ-dual-ty Δ B₁ Θ)) (⊢retag (dual-int bwf) ⊢W)
      -- the wrapped argument, at the type the ƛ's annotation demands
      ⊢arg : intOf Δ Θ ∣ []
               ⊢ W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ⦂ substᵗ (γᵇ Θ) B₁
      ⊢arg = subst (λ T → intOf Δ Θ ∣ []
                            ⊢ W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ⦂ T)
                   (ρᵇ-dual-ty Δ B₁ Θ sc₁)
                   (env (bwf-dualᴳ Θ bwf (dual-rep bwf) (dual-cnc bwf))
                        (sc-dual Δ Θ sc₁) ⊢W′)

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
