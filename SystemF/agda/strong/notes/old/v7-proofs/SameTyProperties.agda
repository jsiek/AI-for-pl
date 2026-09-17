module strong.proof.SameTyProperties where

-- Strong System F v7 — the algebra of `SameAnchor` / `SameTy`.
--
-- `conv-id` compares its two endpoint types across TWO contexts, matching
-- free source variables by the ANCHOR LEVEL they name.  Everything the
-- conversion-builder lemmas need about that comparison lives here:
-- reflexivity (at a well-formed type), symmetry, and the two weakenings
-- that push a `name`/`abst` pair onto both sides.

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.List using (_∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.proof.CtxProperties using (name-of-tv; named-anchor)

private
  variable
    Δ Δ₁ Δ₂ Δ₃ : Ctxᵗ
    A B C : Ty
    R S : RepTy
    X Y : ℕ
    α β γ : Anchor
    k : ℕ

------------------------------------------------------------------------
-- Anchors
------------------------------------------------------------------------

sameAnchor-refl : Δ ∋a α → SameAnchor Δ α Δ α
sameAnchor-refl a = same-anchor a a refl

sameAnchor-sym : SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₂ β Δ₁ α
sameAnchor-sym (same-anchor a₁ a₂ eq) = same-anchor a₂ a₁ (sym eq)

sameAnchor-trans : SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₂ β Δ₃ γ
                 → SameAnchor Δ₁ α Δ₃ γ
sameAnchor-trans (same-anchor a₁ a₂ eq₁) (same-anchor a₂′ a₃ eq₂) =
  same-anchor a₁ a₃ (trans eq₁ eq₂)

-- Going under a structural `∀` pushes ONE entry onto each side, so an
-- anchor match survives by `cong suc` — no level bookkeeping.
sameAnchor-Λ : SameAnchor Δ₁ α Δ₂ β
             → SameAnchor (anch revealed abstA ∷ Δ₁) (suc α)
                          (anch revealed abstA ∷ Δ₂) (suc β)
sameAnchor-Λ (same-anchor a₁ a₂ eq) =
  same-anchor (a-there a₁) (a-there a₂) (cong suc eq)

-- And the freshly pushed anchor matches itself unconditionally: it is
-- index zero on both sides.
sameAnchor-Λ-zero : SameAnchor (anch revealed abstA ∷ Δ₁) zero
                               (anch revealed abstA ∷ Δ₂) zero
sameAnchor-Λ-zero = same-anchor a-here a-here refl

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

sameTy-sym : SameTy k Δ₁ A Δ₂ B → SameTy k Δ₂ B Δ₁ A
sameTy-sym (same-bound p) = same-bound p
sameTy-sym (same-free n₁ n₂ sa) = same-free n₂ n₁ (sameAnchor-sym sa)
sameTy-sym same-ℕ = same-ℕ
sameTy-sym same-𝔹 = same-𝔹
sameTy-sym (same-⇒ a b) = same-⇒ (sameTy-sym a) (sameTy-sym b)
sameTy-sym (same-∀ a) = same-∀ (sameTy-sym a)

-- A well-formed type matches itself.  No well-formedness premise: an
-- anchor is in scope as soon as a source variable names it, because the
-- name is a bit on the anchor's own entry.
sameTy-refl : Δ ⊢ᵗ A → SameTy k Δ A Δ A
sameTy-refl (wf-var x) with name-of-tv x
sameTy-refl (wf-var x) | α , n = same-free n n (sameAnchor-refl (named-anchor n))
sameTy-refl wf-ℕ = same-ℕ
sameTy-refl wf-𝔹 = same-𝔹
sameTy-refl (wf-⇒ a b) = same-⇒ (sameTy-refl a) (sameTy-refl b)
sameTy-refl (wf-∀ a) = same-∀ (sameTy-refl a)
