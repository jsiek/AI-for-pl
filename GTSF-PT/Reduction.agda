-- File Charter:
--   * One-step small-step reduction for typed coercion terms.
--   * Primary export is the `_—→_` reduction relation.
--   * Depends on labels, types, coercion typing, coercion terms, and expression
--     contexts.

module Reduction where

open import Data.List using (length; _∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Label
open import Types
open import Coercions
open import CoercionTerms
open import Terms using (ExCtx; ∅; _▷_; renameᵉ; ExVar)

--------------------------------------------------------------------------------
-- One-step reduction
--------------------------------------------------------------------------------


infix 2 _—→_
data _—→_ {Δ}{Ψ : Subset Δ} {Γ : ExCtx Δ} : ∀  {B : Ty Δ} →
  Ex {Ψ = Ψ} Γ B → Ex {Ψ = Ψ} Γ B → Set where

  β : ∀ {A B : Ty Δ}{V : Ex {Ψ = Ψ} Γ A}{N : Ex (Γ ▷ A) B}
    → Value V
    ---------------------
    → app (λx: A ⇒ N) V —→ N [ V ]


  β-↦ : ∀{p q}{A A′ B B′} {V : Ex Γ (A ⇒ B)}{W : Ex Γ A′}
    → Value V → Value W
    → (p⊢ : Δ ∣ Ψ ⊢ p ∶ A′ =⇒ A)
    → (q⊢ : Δ ∣ Ψ ⊢ q ∶ B =⇒ B′)
    -- p ↦ q
    --------------------------------------------
    → (V ⟨ cast-fun p⊢ q⊢ ⟩) · W  —→ (V · (W ⟨ p⊢ ⟩)) ⟨ q⊢ ⟩


  β-id : ∀{A} {V : Ex Γ A}
    → Value V
    -- id A
    -------------------
    → V ⟨ cast-id ⟩ —→  V


  β-seq : ∀ {A B C} {V : Ex Γ A} {p q}
    → Value V
    → (p⊢ : Δ ∣ Ψ ⊢ p ∶ A =⇒ B)
    → (q⊢ : Δ ∣ Ψ ⊢ q ∶ B =⇒ C)
    -- p ︔ q
    ------------------------------
    → V ⟨ cast-seq p⊢ q⊢ ⟩ —→ V ⟨ p⊢ ⟩ ⟨ q⊢ ⟩

  seal-unseal : ∀ {α A} {V : Ex Γ A}
    → Value V
    → (α∈Ψ : tyVarToFin α ∈ Ψ)
    -- seal A α / unseal α B
    ------------------------------------
    → V ⟨ cast-seal α∈Ψ ⟩ ⟨ cast-unseal α∈Ψ ⟩ —→ V

  tag-untag-ok : ∀ {G}{V : Ex Γ G}{ℓ}
    → (gG : Ground G)
    → Value V
    -- G ! / G ？ ℓ
    ------------------------------
    → V ⟨ cast-tag gG ⟩ ⟨ cast-untag {ℓ = ℓ} gG ⟩  —→  V

  tag-untag-bad : ∀ {G H} {V : Ex Γ G} {ℓ : Label}
    → (gG : Ground G)
    → (gH : Ground H)
    → Value V → G ≢ H
    -- G ! / H ？ ℓ
    ----------------------------------------
    → V ⟨ cast-tag gG ⟩ ⟨ cast-untag {ℓ = ℓ} gH ⟩ —→  blame ℓ

--   δ-⊕ : ∀ {m n : ℕ} →
--     -----------------------------------------------
--     $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)  —→  $ (κℕ (m + n))

--   blame-·₁ : ∀ {ℓ : Label} {M : Term} →
--     (blame ℓ · M) —→ blame ℓ

--   blame-·₂ : ∀ {ℓ : Label} {V : Term} →
--     Value V →
--     (V · blame ℓ) —→ blame ℓ

--   blame-·α : ∀ {ℓ : Label} {B T : Ty} →
--     (blame ℓ ⦂∀ B • T) —→ blame ℓ

--   blame-⟨⟩ : ∀ {c : Coercion} {ℓ : Label} →
--     ((blame ℓ) ⟨ c ⟩) —→ blame ℓ

--   blame-⊕₁ : ∀ {ℓ : Label} {M : Term} {op : Prim} →
--     (blame ℓ ⊕[ op ] M) —→ blame ℓ

--   blame-⊕₂ : ∀ {ℓ : Label} {L : Term} {op : Prim} →
--     Value L →
--     (L ⊕[ op ] blame ℓ) —→ blame ℓ


-- --------------------------------------------------------------------------------
-- -- Store-threaded one-step reduction
-- --------------------------------------------------------------------------------

-- infix 2 _∣_—→_∣_
-- data _∣_—→_∣_ : Store → Term → Store → Term → Set where

--   pure-step : ∀ {Σ : Store} {M M′ : Term} →
--     M —→ M′ →
--     ---------------
--     Σ ∣ M —→ Σ ∣ M′

--   β-∀ : ∀ {Σ : Store}{V : Term} {A B : Ty}{c : Coercion} →
--    Value V →
--    ----------------------------------------------------------------------------
--    let α = length Σ in
--    Σ ∣ V ⟨ `∀ c ⟩ ⦂∀ B • A
--      —→ (α , A) ∷ Σ ∣ (V ⦂∀ src c • ＇ α) ⟨ c [ α ]ᶜ ⟩ ⟨ reveal (B [ α ]ᴿ) α A ⟩

--   β-Λ : ∀ {Σ : Store} {A B : Ty} {V : Term} →
--     ------------------------------------------------------------------------
--     let α = length Σ in
--     Σ ∣ (Λ V) ⦂∀ B • A  —→  (α , A) ∷ Σ ∣ V [ α ]ᵀ ⟨ reveal (B [ α ]ᴿ) α A ⟩

--   β-down-ν : ∀ {Σ : Store} {A B C V c} →
--     Value V →
--     ------------------------------------------------------------
--     let α = length Σ in
--     Σ ∣ V ⟨ gen C c ⟩ ⦂∀ B • A
--       —→ (α , A) ∷ Σ ∣ V ⟨ c [ α ]ᶜ ⟩ ⟨ reveal (B [ α ]ᴿ) α A ⟩

--   β-up-ν : ∀ {Σ : Store} {V B c} →
--     Value V →
--     ---------------------------------------------------------------------
--     let α = length Σ in
--     Σ ∣ V ⟨ inst B c ⟩ —→ (α , ★) ∷ Σ ∣ (V ⦂∀ (src c) • ＇ α ) ⟨ c [ α ]ᶜ ⟩

--   ξ-·₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} →
--     Σ ∣ L —→ Σ′ ∣ L′ →
--     Σ ∣ (L · M) —→ Σ′ ∣ (L′ · M)

--   ξ-·₂ : ∀ {Σ Σ′ : Store} {V M M′ : Term} →
--     Value V →
--     Σ ∣ M —→ Σ′ ∣ M′ →
--     Σ ∣ (V · M) —→ Σ′ ∣ (V · M′)

--   ξ-·α : ∀ {Σ Σ′ : Store} {M M′ : Term} {B A : Ty} →
--     Σ ∣ M —→ Σ′ ∣ M′ →
--     Σ ∣ (M ⦂∀ B • A) —→ Σ′ ∣ (M′ ⦂∀ B • A)

--   ξ-⟨⟩ : ∀ {Σ Σ′ : Store} {c : Coercion} {M M′ : Term} →
--     Σ ∣ M —→ Σ′ ∣ M′ →
--     Σ ∣ (M ⟨ c ⟩) —→ Σ′ ∣ (M′ ⟨ c ⟩)

--   ξ-⊕₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} {op : Prim} →
--     Σ ∣ L —→ Σ′ ∣ L′ →
--     Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L′ ⊕[ op ] M)

--   ξ-⊕₂ : ∀ {Σ Σ′ : Store} {L M M′ : Term} {op : Prim} →
--     Value L →
--     Σ ∣ M —→ Σ′ ∣ M′ →
--     Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L ⊕[ op ] M′)
