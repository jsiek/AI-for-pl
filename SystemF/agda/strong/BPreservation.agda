module strong.BPreservation where

-- Type preservation for the tight dual boundary (B₀) design (PLAN.md §3–§4).
--
-- Stated at RUNTIME term contexts (Γₜ = []): one reduction step preserves the
-- type.  Case order follows BReduction's rhythm — the two computation rules
-- first, then the five ξ congruences.
--
--   β-Λ  is where a boundary is BORN.  Its (env) premises are discharged by
--        the reveal's well-formedness (bwf↑), the two face equations (int-eq
--        for γᵇ, ext-eq for ρᵇ), and — for the Scoped premise, which no
--        reduction rule carries — the typing ⇒ wf ⇒ Scoped bridge scB-bridge.
--   β-ƛ  is the term-substitution lemma, still in flight.
--   ξ-*  are each one induction hypothesis under the corresponding typing
--        rule.  Two of them change context: ξ-Λ recurses at the Λ body's
--        context (abst ∷ Δ) ∣ ⤊ [], and ⤊ [] = [] definitionally
--        (⤊ = map ⇑ᵗ), so the statement applies unchanged; ξ-⟪⟫ recurses at
--        the boundary INTERIOR intOf Δ Θ ∣ [], i.e. at a DIFFERENT Δ — which
--        is why preservation is generalised over Δ rather than fixed at [].

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst)
open import strong.Types
open import strong.TypeSubst using (subst-cong; subst-id)
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction
open import strong.ScopeBridge using (scB-bridge)
open import strong.TermSubst using (preserve-β-ƛ)

private
  variable
    Δ : TCtx
    A B : Ty
    M M′ : Term

preservation : Δ ∣ [] ⊢ M ⦂ A → M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A

------------------------------------------------------------------------
-- Computation rules
------------------------------------------------------------------------

-- TyBeta:  (ΛX.V) [B , A]  →  V ⟪ ↑X:=A , B ⟫
preservation (⊢·[] {B = B} {A = A} (⊢Λ {N = V} ⊢V) ⊢A) (β-Λ v) =
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
preservation (⊢· (⊢ƛ wfA ⊢N) ⊢W) (β-ƛ w) = preserve-β-ƛ (⊢· (⊢ƛ wfA ⊢N) ⊢W)

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
