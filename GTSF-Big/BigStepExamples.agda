module BigStepExamples where

-- File Charter:
--   * Small checked derivations exercising the structural big-step rules.
--   * Covers term beta, primitives, successful and failing tag checks, and
--     allocation followed by runtime type application.
--   * Depends only on the semantics and the existing Nu root reductions.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; _+_)

open import BigStep
open import Coercions
open import NuReduction using
  ( bind
  ; keep
  ; β
  ; β-Λ•
  ; δ-⊕
  ; tag-untag-bad
  ; tag-untag-ok
  )
open import NuTerms
open import Primitives using (addℕ; κℕ)
open import Types

Nat : Ty
Nat = ‵ `ℕ

Bool : Ty
Bool = ‵ `𝔹

beta-identity :
  (ƛ (` zero)) · $ (κℕ 7)
    ⇓[ keep ∷ [] ] $ (κℕ 7)
beta-identity =
  ⇓-app
    (⇓-value (ƛ (` zero)))
    (ƛ (` zero))
    shiftable-[]
    (⇓-value ($ (κℕ 7)))
    ($ (κℕ 7))
    shiftable-[]
    (β ($ (κℕ 7)))
    (⇓-value ($ (κℕ 7)))

primitive-addition :
  $ (κℕ 2) ⊕[ addℕ ] $ (κℕ 3)
    ⇓[ keep ∷ [] ] $ (κℕ (2 + 3))
primitive-addition =
  ⇓-prim
    (⇓-value ($ (κℕ 2)))
    ($ (κℕ 2))
    shiftable-[]
    (⇓-value ($ (κℕ 3)))
    ($ (κℕ 3))
    shiftable-[]
    δ-⊕
    (⇓-value ($ (κℕ (2 + 3))))

tag-check-success :
  $ (κℕ 7) ⟨ Nat ! ⟩ ⟨ Nat ？ ⟩
    ⇓[ keep ∷ [] ] $ (κℕ 7)
tag-check-success =
  ⇓-cast-active
    (⇓-cast-inert
      (⇓-value ($ (κℕ 7)))
      ($ (κℕ 7))
      (Nat !))
    (($ (κℕ 7)) ⟨ Nat ! ⟩)
    (tag-untag-ok ($ (κℕ 7)))
    (⇓-value ($ (κℕ 7)))

tag-check-failure :
  $ (κℕ 7) ⟨ Nat ! ⟩ ⟨ Bool ？ ⟩
    ⇓[ keep ∷ [] ] blame
tag-check-failure =
  ⇓-cast-active
    (⇓-cast-inert
      (⇓-value ($ (κℕ 7)))
      ($ (κℕ 7))
      (Nat !))
    (($ (κℕ 7)) ⟨ Nat ! ⟩)
    (tag-untag-bad ($ (κℕ 7)) (λ ()))
    ⇓-blame

nu-polymorphic-identity :
  ν Nat (Λ (ƛ (` zero))) (seal Nat zero ↦ unseal zero Nat)
    ⇓[ bind Nat ∷ keep ∷ [] ]
      (ƛ (` zero)) ⟨ seal Nat zero ↦ unseal zero Nat ⟩
nu-polymorphic-identity =
  ⇓-nu
    (⇓-value (Λ (ƛ (` zero))))
    (Λ (ƛ (` zero)))
    (no•-Λ (no•-ƛ no•-`))
    (⇓-cast-inert
      (⇓-type-app
        (β-Λ• (ƛ (` zero)))
        (⇓-value (ƛ (` zero))))
      (ƛ (` zero))
      (seal Nat zero ↦ unseal zero Nat))
