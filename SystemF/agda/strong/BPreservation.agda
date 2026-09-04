module strong.BPreservation where

-- Type preservation for the tight dual boundary (B₀) design (PLAN.md §3–§4).
--
-- Stated at RUNTIME term contexts (Γₜ = []): one reduction step preserves the
-- type.  Case order follows BReduction's rhythm — the two computation rules
-- first, then the five ξ congruences.
--
--   TyBeta  is where a boundary is BORN.  Its (env) premises are discharged by
--        the reveal's well-formedness (bwf↑), the two face equations (int-eq
--        for γᵇ, ext-eq for ρᵇ), and — for the Scoped premise, which no
--        reduction rule carries — the typing ⇒ wf ⇒ Scoped bridge scB-bridge.
--   Beta  is the term-substitution lemma, still in flight.
--   ξ-*  are each one induction hypothesis under the corresponding typing
--        rule.  Two of them change context: ξ-Λ recurses at the Λ body's
--        context (abst ∷ Δ) ∣ ⤊ [], and ⤊ [] = [] definitionally
--        (⤊ = map ⇑ᵗ), so the statement applies unchanged; ξ-⟪⟫ recurses at
--        the boundary INTERIOR intOf Δ Θ ∣ [], i.e. at a DIFFERENT Δ — which
--        is why preservation is generalised over Δ rather than fixed at [].

open import Data.Nat using (ℕ; zero; suc)
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

private
  variable
    Δ : TCtx
    A B B₁ B₂ : Ty
    M M′ : Term

preservation : Δ ∣ [] ⊢ M ⦂ A → M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A

------------------------------------------------------------------------
-- Computation rules
------------------------------------------------------------------------

-- TyBeta:  (ΛX.V) [B , A]  →  V ⟪ ↑X:=A , B ⟫
preservation (⊢·[] {B = B} {A = A} (⊢Λ {N = V} ⊢V) ⊢A) (TyBeta v) =
  subst (λ T → _ ∣ [] ⊢ V ⟪ rvl A ∷ [] , B ⟫ ⦂ T) ext-eq
    (env {B₀ = B} (bwf↑ ⊢A bwf[])
         scB
         (subst (λ T → _ ∣ [] ⊢ V ⦂ T) (sym int-eq) ⊢V))
  where
    -- internal face:  γᵇ [rvl A] = prepId 1 (γcnc 1 0 [rvl A]) is pointwise `_
    gvar : (x : ℕ) → γᵇ (rvl A ∷ []) x ≡ ` x
    gvar zero    = refl
    gvar (suc _) = refl
    int-eq : substᵗ (γᵇ (rvl A ∷ [])) B ≡ B
    int-eq = trans (subst-cong gvar B) (subst-id B)
    -- external face:  substᵗ (ρᵇ [rvl A]) B = substᵗ (A •ᵗ `_) B ≡ B [ A ]ᵗ
    ext-eq : substᵗ (ρᵇ (rvl A ∷ [])) B ≡ B [ A ]ᵗ
    ext-eq = subst-cong (λ { zero → refl ; (suc _) → refl }) B
    -- Scoped obligation: baseS [rvl A] Δ is ALL ok (cmax = 0), and B is the
    -- ∀-body of Λ V — well-scoped over abst ∷ Δ.  ⊢V is typed at ⤊ [] = [],
    -- exactly scB-bridge's shape.
    scB : Scoped (baseS (rvl A ∷ []) _) B
    scB = scB-bridge ⊢V

-- Beta:  (λx:A.N) · W  →  N[x:=W]  — the term-substitution lemma (TermSubst)
preservation (⊢· (⊢ƛ wfA ⊢N) ⊢W) (Beta w) = preserve-Beta (⊢· (⊢ƛ wfA ⊢N) ⊢W)

-- R1:  ((Λ V) ⟪ Θ , ∀B₀ ⟫) ·[ B , A ]  →  V ⟪ ↑A ∷ Θ⁺ , B₀ ⟫
--
-- The redex's B is FORCED, so the pattern supplies it: (env) types the
-- wrapper at substᵗ (ρᵇ Θ) (`∀ B₀), which is `∀ (substᵗ (extsᵗ (ρᵇ Θ)) B₀),
-- so B is that ∀-body.  Likewise the body Λ V is typed at
-- substᵗ (γᵇ Θ) (`∀ B₀) = `∀ (substᵗ (extsᵗ (γᵇ Θ)) B₀), so inverting ⊢Λ
-- gives ⊢V at (abst ∷ intOf Δ Θ) ∣ ⤊ [] with the extsᵗ face — which is
-- EXACTLY the new boundary's interior (intOf-shift, ⤊ [] = [] definitionally)
-- and interior face (γᵇ-shift-ty).  So V transports by two substs and NOTHING
-- renames the term: the Λ-binder's slot became the reveal slot.  The type
-- argument A is not pushed inward — it is the new reveal's rep, read in the
-- exterior, which is what ρᵇ-shift-ty turns back into the redex's B [ A ]ᵗ.
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
    -- the Λ-body, retyped at the new interior and the new interior face
    ⊢body : intOf Δ (rvl A ∷ shiftReps Θ) ∣ []
              ⊢ V ⦂ substᵗ (γᵇ (rvl A ∷ shiftReps Θ)) B₀
    ⊢body = subst₂ (λ Ψ T → Ψ ∣ [] ⊢ V ⦂ T)
                   (sym (intOf-shift Δ A Θ))
                   (sym (γᵇ-shift-ty A Θ B₀))
                   ⊢V

-- R2:  ((ƛ A′ ∙ N) ⟪ Θ , B₁ ⇒ B₂ ⟫) · W  →  (N [ W ⟪ Θᵈ , B₁ᵈ ⟫ ]ᵐ) ⟪ Θ , B₂ ⟫
--
-- Both indices of the redex are FORCED: (env) types the wrapper at
-- substᵗ (ρᵇ Θ) (B₁ ⇒ B₂), which is substᵗ (ρᵇ Θ) B₁ ⇒ substᵗ (ρᵇ Θ) B₂,
-- so ⊢W is at substᵗ (ρᵇ Θ) B₁ and the whole redex at substᵗ (ρᵇ Θ) B₂ —
-- which is exactly what the rebuilt (env) returns, so the outer type needs
-- no transport.  Likewise the body is typed at the INTERIOR face
-- substᵗ (γᵇ Θ) B₁ ⇒ substᵗ (γᵇ Θ) B₂, so inverting ⊢ƛ forces the ƛ's
-- annotation A′ to be substᵗ (γᵇ Θ) B₁ and gives ⊢N at the term context
-- (substᵗ (γᵇ Θ) B₁ ∷ []) — exactly ⊢[]ᵐ's shape.
--
-- The INNER wrapper sits at exterior intOf Δ Θ with the dual boundary: its
-- exterior face is the argument type the ƛ demands (ρᵇ-dual-ty, scope-
-- restricted — the blocked slots differ, and (env)'s premise for B₁ is what
-- rules them out) and its interior face is W's own type (γᵇ-dual-ty).
--
-- The dual's interior is  prepAbst (cmax Θ) (dropN (cmax Θ) Δ)  — Δ with
-- its dropped prefix rebuilt as `abst.  That is Δ on the nose only over an
-- all-`abst` exterior; in general it is merely a context of the SAME
-- LENGTH, which is all typing can tell apart (⊢retag), so preservation
-- keeps its statement — no AllAbst premise.
preservation {Δ} (⊢· {M = W} (env {Θ = Θ} {B₀ = B₁ ⇒ B₂} bwf
                                  (sc-⇒ sc₁ sc₂) (⊢ƛ wfA′ ⊢N))
                     ⊢W)
                 (Wrap w) =
  env bwf sc₂ (⊢[]ᵐ ⊢N ⊢arg)
  where
    -- the dual's interior rebuilds Δ up to the abst/rvld marker …
    lenq : length Δ ≡ length (intOf (intOf Δ Θ) (dualᵇ Θ))
    lenq = len-dual Δ Θ (bwf-cmax Θ bwf)
    -- … so W retypes there, at its own type = the dual's interior face
    ⊢W′ : intOf (intOf Δ Θ) (dualᵇ Θ) ∣ []
            ⊢ W ⦂ substᵗ (γᵇ (dualᵇ Θ)) (renameᵗ (swapᵇ Θ) B₁)
    ⊢W′ = subst (λ T → intOf (intOf Δ Θ) (dualᵇ Θ) ∣ [] ⊢ W ⦂ T)
                (sym (γᵇ-dual-ty B₁ Θ)) (⊢retag lenq ⊢W)
    -- the wrapped argument, at the type the ƛ's annotation demands
    ⊢arg : intOf Δ Θ ∣ []
             ⊢ W ⟪ dualᵇ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ⦂ substᵗ (γᵇ Θ) B₁
    ⊢arg = subst (λ T → intOf Δ Θ ∣ []
                          ⊢ W ⟪ dualᵇ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ⦂ T)
                 (ρᵇ-dual-ty B₁ Θ sc₁)
                 (env (bwf-dual Θ bwf lenq) (sc-dual Θ sc₁) ⊢W′)

------------------------------------------------------------------------
-- ξ (congruence) rules: the induction hypothesis under the typing rule
------------------------------------------------------------------------

preservation (⊢· ⊢L ⊢M) (ξ-·-l L→L′) =
  ⊢· (preservation ⊢L L→L′) ⊢M

preservation (⊢· ⊢V ⊢M) (ξ-·-r v M→M′) =
  ⊢· ⊢V (preservation ⊢M M→M′)

preservation (⊢·[] ⊢L ⊢A) (ξ-·[] L→L′) =
  ⊢·[] (preservation ⊢L L→L′) ⊢A

-- the body of a Λ is typed at (abst ∷ Δ) ∣ ⤊ [], and ⤊ [] = []
preservation (⊢Λ ⊢N) (ξ-Λ N→N′) =
  ⊢Λ (preservation ⊢N N→N′)

-- the interior of a boundary is typed at intOf Δ Θ ∣ []; the boundary's
-- premises (bwf, sc) mention only Θ and B₀, so they are carried across intact
preservation (env bwf sc ⊢M) (ξ-⟪⟫ M→M′) =
  env bwf sc (preservation ⊢M M→M′)
