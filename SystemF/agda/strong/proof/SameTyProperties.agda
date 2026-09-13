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
open import strong.proof.CtxProperties using
  (name-of-tv; named-anchor; anchor-binding-unique)

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

anchor-binding : Δ ∋a α → Σ[ b ∈ AnchorBinding ] (Δ ∋ab α := b)
anchor-binding a-here-abst = abstA , ab-here-abst
anchor-binding (a-here-bind {R = R}) = bindA R , ab-here-bind
anchor-binding (a-over-abst a) with anchor-binding a
anchor-binding (a-over-abst a) | b , ab = b , ab-over-abst ab
anchor-binding (a-over-bind a) with anchor-binding a
anchor-binding (a-over-bind a) | b , ab = b , ab-over-bind ab
anchor-binding (a-over-name a) with anchor-binding a
anchor-binding (a-over-name a) | b , ab = b , ab-over-name ab

sameAnchor-refl : Δ ∋a α → SameAnchor Δ α Δ α
sameAnchor-refl a with anchor-binding a
sameAnchor-refl a | b , ab = same-anchor ab ab refl

sameAnchor-sym : SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₂ β Δ₁ α
sameAnchor-sym (same-anchor ab₁ ab₂ eq) = same-anchor ab₂ ab₁ (sym eq)

sameAnchor-trans : SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₂ β Δ₃ γ
                 → SameAnchor Δ₁ α Δ₃ γ
sameAnchor-trans (same-anchor ab₁ ab₂ eq₁) (same-anchor ab₂′ ab₃ eq₂)
  with anchor-binding-unique ab₂ ab₂′
sameAnchor-trans (same-anchor ab₁ ab₂ eq₁) (same-anchor ab₂′ ab₃ eq₂)
  | refl = same-anchor ab₁ ab₃ (trans eq₁ eq₂)

-- Pushing one `name`/`abst` pair onto both sides preserves an anchor match,
-- because the pair adds exactly one anchor to each context.
sameAnchor-Λ : SameAnchor Δ₁ α Δ₂ β
             → SameAnchor (name zero ∷ abst ∷ Δ₁) (suc α)
                          (name zero ∷ abst ∷ Δ₂) (suc β)
sameAnchor-Λ (same-anchor ab₁ ab₂ eq) =
  same-anchor (ab-over-name (ab-over-abst ab₁))
              (ab-over-name (ab-over-abst ab₂))
              eq

-- The freshly pushed anchor matches itself, PROVIDED the two contexts carry
-- the same number of anchors — the level of index 0 is `anchorCount ∸ 1`.
sameAnchor-Λ-zero : anchorCount Δ₁ ≡ anchorCount Δ₂
                  → SameAnchor (name zero ∷ abst ∷ Δ₁) zero
                               (name zero ∷ abst ∷ Δ₂) zero
sameAnchor-Λ-zero eq =
  same-anchor (ab-over-name ab-here-abst) (ab-over-name ab-here-abst)
              (cong (λ n → suc n ∸ 1) eq)

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

-- A well-formed type matches itself: every free variable names an anchor,
-- and an anchor matches itself at the same context.
sameTy-refl : Δ ok → Δ ⊢ᵗ A → SameTy k Δ A Δ A
sameTy-refl ctx-ok (wf-var x) with name-of-tv x
sameTy-refl ctx-ok (wf-var x) | α , n =
  same-free n n (sameAnchor-refl (named-anchor ctx-ok n))
sameTy-refl ctx-ok wf-ℕ = same-ℕ
sameTy-refl ctx-ok wf-𝔹 = same-𝔹
sameTy-refl ctx-ok (wf-⇒ a b) =
  same-⇒ (sameTy-refl ctx-ok a) (sameTy-refl ctx-ok b)
sameTy-refl ctx-ok (wf-∀ a) =
  same-∀ (sameTy-refl (ok-name (ok-abst ctx-ok) a-here-abst fresh) a)
  where
  fresh : Unoccupied (abst ∷ _) zero
  fresh X (suc α , n-over-abst n , ())
