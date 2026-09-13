module strong.proof.PreservationFramework where

-- Strong System F v7 — preservation induction, parameterized by the five
-- computational cases that need substitution or boundary algebra.

open import Data.Nat using (zero)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.RepresentationTypes using (shiftByᴿ)
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.CtxProperties using
  (ok-Λ; ok-boundary; store-unique; scope-unique)

module Impl
  (preserve-Beta : ∀ {Δ A N W B}
    → Δ ok
    → Value W
    → Δ ⊢ᵗ A
    → Δ ∣ A ∷ [] ⊢ N ⦂ B
    → Δ ∣ [] ⊢ W ⦂ A
    → Δ ∣ [] ⊢ N [ W ∶ A ]ᵐ ⦂ B)
  (preserve-TyBeta : ∀ {Δ V B A R C}
    → Δ ok
    → Value V
    → Δ ⊢⌊ A ⌋ R
    → Δ ∣ [] ⊢ (Λ V) • B [ A ] ⦂ C
    → Δ ∣ [] ⊢ ν repBind R ∷ [] , reveal zero ∷ []
         [ V ∣ revTy zero zero A B ] ⦂ C)
  (preserve-Wrap : ∀ {Δ Θ χ V c W c₁ c₂ B}
    → Δ ok
    → Value (ν Θ , χ [ V ∣ c ])
    → Value W
    → arr c ≡ just (c₁ , c₂)
    → Δ ∣ [] ⊢ (ν Θ , χ [ V ∣ c ]) · W ⦂ B
    → Δ ∣ [] ⊢ ν Θ , χ
         [ V · (ν [] , dual χ
           [ renAnchᴹ (shiftAnchor (length Θ)) W ∣ c₁ ])
         ∣ c₂ ] ⦂ B)
  (preserve-TyWrap : ∀ {Δ Θ χ V c B A d R C}
    → Δ ok
    → Value V
    → allView c ≡ just d
    → Δ ⊢⌊ A ⌋ R
    → Δ ∣ [] ⊢ (ν Θ , χ [ Λ V ∣ c ]) • B [ A ] ⦂ C
    → Δ ∣ [] ⊢ ν (Θ ++ (repBind (shiftByᴿ (length Θ) R) ∷ []))
         , (shiftScope 1 χ ++ (reveal zero ∷ []))
         [ V ∣ instReveal zero zero (` zero) d ] ⦂ C)
  (preserve-Merge : ∀ {Δ Θ₁ Θ₂ χ₁ χ₂ V c d B}
    → Δ ok
    → Value (ν Θ₂ , χ₂ [ V ∣ c ])
    → Δ ∣ [] ⊢ ν Θ₁ , χ₁ [ ν Θ₂ , χ₂ [ V ∣ c ] ∣ d ] ⦂ B
    → Δ ∣ [] ⊢ ν (Θ₁ ++ Θ₂)
         , (shiftScope (length Θ₂) χ₁ ++ χ₂)
         [ V ∣ c ⨟ renConv (λ X → X) (shiftAnchor (length Θ₂)) d ] ⦂ B)
  where

  preserve : ∀ {Δ M M′ A}
    → Δ ok
    → Δ ∣ [] ⊢ M ⦂ A
    → Δ ⊢ M -→ M′
    → Δ ∣ [] ⊢ M′ ⦂ A
  preserve ctx-ok (⊢· (⊢ƛ wf body) arg) (Beta value) =
    preserve-Beta ctx-ok value wf body arg
  preserve ctx-ok (⊢⊕ ⊢$ ⊢$) PrimBeta = ⊢$
  preserve ctx-ok typing (TyBeta value q) =
    preserve-TyBeta ctx-ok value q typing
  preserve ctx-ok typing (Wrap boundary arg arr-eq) =
    preserve-Wrap ctx-ok boundary arg arr-eq typing
  preserve ctx-ok typing (TyWrap value all-eq q) =
    preserve-TyWrap ctx-ok value all-eq q typing
  preserve ctx-ok typing (Merge inner) = preserve-Merge ctx-ok inner typing
  preserve ctx-ok (⊢ν store scope nf ⊢$ (conv-id same-ℕ))
    (Const literal-$ base-ℕ) = ⊢$
  preserve ctx-ok (⊢ν store scope nf ⊢# (conv-id same-𝔹))
    (Const literal-# base-𝔹) = ⊢#
  preserve ctx-ok (⊢⊕ left right) (ξ-⊕-l step) =
    ⊢⊕ (preserve ctx-ok left step) right
  preserve ctx-ok (⊢⊕ left right) (ξ-⊕-r value step) =
    ⊢⊕ left (preserve ctx-ok right step)
  preserve ctx-ok (⊢· left right) (ξ-·-l step) =
    ⊢· (preserve ctx-ok left step) right
  preserve ctx-ok (⊢· left right) (ξ-·-r value step) =
    ⊢· left (preserve ctx-ok right step)
  preserve ctx-ok (⊢•[] left wf) (ξ-•[] step) =
    ⊢•[] (preserve ctx-ok left step) wf
  preserve ctx-ok (⊢Λ body) (ξ-Λ step) =
    ⊢Λ (preserve (ok-Λ ctx-ok) body step)
  preserve ctx-ok (⊢ν store scope nf body conv) (ξ-ν s ch step)
    with store-unique store s
  preserve ctx-ok (⊢ν store scope nf body conv) (ξ-ν s ch step)
    | refl with scope-unique scope ch
  preserve ctx-ok (⊢ν store scope nf body conv) (ξ-ν s ch step)
    | refl | refl =
    ⊢ν store scope nf
      (preserve (ok-boundary ctx-ok store scope) body step) conv
