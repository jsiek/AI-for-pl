module Reduction where

open import Data.List using (length; _∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Coercions
open import Terms
open import Primitives

--------------------------------------------------------------------------------
-- One-step reduction
--------------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : Term → Term → Set where

  β : ∀ {N V : Term}
    → Value V
    ---------------------
    → (ƛ N) · V —→ N [ V ]


  β-↦ : ∀ {V W p q}
    → Value V → Value W
    --------------------------------------------
    → V ⟨ p ↦ q ⟩ · W  —→  (V · (W ⟨ p ⟩)) ⟨ q ⟩

  β-id : ∀ {V}{A}
    → Value V
    -------------------
    → V ⟨ id A ⟩ —→  V

  β-seq : ∀ {V p q}
    → Value V
    ------------------------------
    → V ⟨ p ︔ q ⟩ —→ V ⟨ p ⟩ ⟨ q ⟩

  seal-unseal : ∀ {α V A B}
    → Value V
    ------------------------------------
    → V ⟨ seal A α ⟩ ⟨ unseal α B ⟩ —→ V

  tag-untag-ok : ∀ {V G}
    → Value V
    ------------------------------
    → V ⟨ G ! ⟩ ⟨ G ？ ⟩  —→  V

  tag-untag-bad : ∀ {V G H}
    → Value V → G ≢ H
    ----------------------------------------
    → V ⟨ G ! ⟩ ⟨ H ？ ⟩ —→  blame

  δ-⊕ : ∀ {m n : ℕ} →
    -----------------------------------------------
    $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)  —→  $ (κℕ (m + n))

  blame-·₁ : ∀ {M : Term} →
    (blame · M) —→ blame

  blame-·₂ : ∀ {V : Term} →
    Value V →
    (V · blame) —→ blame

  blame-·α : ∀ {B T : Ty} →
    (blame ⦂∀ B • T) —→ blame

  blame-⟨⟩ : ∀ {c : Coercion} →
    (blame ⟨ c ⟩) —→ blame

  blame-⊕₁ : ∀ {M : Term} {op : Prim} →
    (blame ⊕[ op ] M) —→ blame

  blame-⊕₂ : ∀ {L : Term} {op : Prim} →
    Value L →
    (L ⊕[ op ] blame) —→ blame


--------------------------------------------------------------------------------
-- Store-threaded one-step reduction
--------------------------------------------------------------------------------

infix 2 _∣_—→_∣_
data _∣_—→_∣_ : Store → Term → Store → Term → Set where

  pure-step : ∀ {Σ : Store} {M M′ : Term} →
    M —→ M′ →
    ---------------
    Σ ∣ M —→ Σ ∣ M′

  β-∀ : ∀ {Σ : Store}{V : Term} {A B : Ty}{c : Coercion} →
   Value V →
   ----------------------------------------------------------------------------
   let α = length Σ in
   Σ ∣ V ⟨ `∀ c ⟩ ⦂∀ B • A
     —→ (α , A) ∷ Σ ∣ (V ⦂∀ src c • ＇ α) ⟨ c [ α ]ᶜ ⟩ ⟨ reveal (B [ α ]ᴿ) α A ⟩

  β-Λ : ∀ {Σ : Store} {A B : Ty} {V : Term} →
    ------------------------------------------------------------------------
    let α = length Σ in
    Σ ∣ (Λ V) ⦂∀ B • A  —→  (α , A) ∷ Σ ∣ V [ α ]ᵀ ⟨ reveal (B [ α ]ᴿ) α A ⟩

  β-down-ν : ∀ {Σ : Store} {A B C V c} →
    Value V →
    ------------------------------------------------------------
    let α = length Σ in
    Σ ∣ V ⟨ gen C c ⟩ ⦂∀ B • A
      —→ (α , A) ∷ Σ ∣ V ⟨ c [ α ]ᶜ ⟩ ⟨ reveal (B [ α ]ᴿ) α A ⟩

  β-up-ν : ∀ {Σ : Store} {V B c} →
    Value V →
    ---------------------------------------------------------------------
    let α = length Σ in
    Σ ∣ V ⟨ inst B c ⟩ —→ (α , ★) ∷ Σ ∣ (V ⦂∀ (src c) • ＇ α ) ⟨ c [ α ]ᶜ ⟩

  ξ-·₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} →
    Σ ∣ L —→ Σ′ ∣ L′ →
    Σ ∣ (L · M) —→ Σ′ ∣ (L′ · M)

  ξ-·₂ : ∀ {Σ Σ′ : Store} {V M M′ : Term} →
    Value V →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (V · M) —→ Σ′ ∣ (V · M′)

  ξ-·α : ∀ {Σ Σ′ : Store} {M M′ : Term} {B A : Ty} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ⦂∀ B • A) —→ Σ′ ∣ (M′ ⦂∀ B • A)

  ξ-⟨⟩ : ∀ {Σ Σ′ : Store} {c : Coercion} {M M′ : Term} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ⟨ c ⟩) —→ Σ′ ∣ (M′ ⟨ c ⟩)

  ξ-⊕₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} {op : Prim} →
    Σ ∣ L —→ Σ′ ∣ L′ →
    Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L′ ⊕[ op ] M)

  ξ-⊕₂ : ∀ {Σ Σ′ : Store} {L M M′ : Term} {op : Prim} →
    Value L →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L ⊕[ op ] M′)
