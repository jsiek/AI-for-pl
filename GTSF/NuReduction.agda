module NuReduction where

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)



open import Types
open import Coercions
open import NuTerms
open import Primitives

--------------------------------------------------------------------------------
-- One-step reduction
--------------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : Term → Term → Set where

  δ-⊕ : ∀ {m n : ℕ} →
    -----------------------------------------------
    $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)  —→  $ (κℕ (m + n))

  β : ∀ {N V : Term}
    → Value V
    ---------------------
    → (ƛ N) · V —→ N [ V ]

  β-Λ : ∀ {α : TyVar} {V : Term} 
    ------------------------
    → (Λ V) • α  —→ V [ α ]ᵀ

  β-id : ∀ {V}{A}
    → Value V
    -------------------
    → V ⟨ id A ⟩ —→  V

  β-seq : ∀ {V p q}
    → Value V
    ------------------------------
    → V ⟨ p ︔ q ⟩ —→ V ⟨ p ⟩ ⟨ q ⟩

  β-↦ : ∀ {V W p q}
    → Value V → Value W
    --------------------------------------------
    → V ⟨ p ↦ q ⟩ · W  —→  (V · (W ⟨ p ⟩)) ⟨ q ⟩

  β-∀ : ∀ {V : Term}{c : Coercion}{α : TyVar}
    → Value V
    ----------------------------------------
    → V ⟨ `∀ c ⟩ • α —→ (V • α) ⟨ c [ α ]ᶜ ⟩

  β-gen : ∀ {Σ : Store} {C V c α}
    → Value V
    --------------------------------------
    → V ⟨ gen C c ⟩ • α —→ V ⟨ c [ α ]ᶜ ⟩

  β-inst : ∀ {Σ : Store} {V B c}
    → Value V
    ----------------------------------------------
    → V ⟨ inst B c ⟩ —→ ν ★ (((⇑ᵗᵐ V) • 0 ) ⟨ c ⟩)

  tag-untag-ok : ∀ {V G}{ℓ}
    → Value V
    ------------------------------
    → V ⟨ G ! ⟩ ⟨ G ？ ℓ ⟩  —→  V

  tag-untag-bad : ∀ {V G H} {ℓ : Label}
    → Value V → G ≢ H
    ----------------------------------------
    → V ⟨ G ! ⟩ ⟨ H ？ ℓ ⟩ —→  blame ℓ

  seal-unseal : ∀ {α V A B}
    → Value V
    ------------------------------------
    → V ⟨ seal A α ⟩ ⟨ unseal α B ⟩ —→ V

  blame-·₁ : ∀ {ℓ : Label} {M : Term} →
    (blame ℓ · M) —→ blame ℓ

  blame-·₂ : ∀ {ℓ : Label} {V : Term} →
    Value V →
    (V · blame ℓ) —→ blame ℓ

  blame-·α : ∀ {ℓ : Label} {α : TyVar} →
    (blame ℓ • α) —→ blame ℓ

  blame-⟨⟩ : ∀ {c : Coercion} {ℓ : Label} →
    ((blame ℓ) ⟨ c ⟩) —→ blame ℓ

  blame-⊕₁ : ∀ {ℓ : Label} {M : Term} {op : Prim} →
    (blame ℓ ⊕[ op ] M) —→ blame ℓ

  blame-⊕₂ : ∀ {ℓ : Label} {L : Term} {op : Prim} →
    Value L →
    (L ⊕[ op ] blame ℓ) —→ blame ℓ


--------------------------------------------------------------------------------
-- Store-threaded one-step reduction
--------------------------------------------------------------------------------

infix 2 _∣_—→_∣_
data _∣_—→_∣_ : Store → Term → Store → Term → Set where

  pure-step : ∀ {Σ : Store} {M M′ : Term}
    → M —→ M′
    -----------------
    → Σ ∣ M —→ Σ ∣ M′

  -- Allow non-deterministic choice of α here so that in the proof of the
  -- Gradual Guarantee, we can choose a matching α in the simulating program.
  ν-step : ∀ {Σ : Store} {N : Term} {A : Ty} {α : TyVar}
   → α ∉ domˢ Σ
    -------------------------------------
   → Σ ∣ ν A N —→ (α , A) ∷ Σ ∣ N [ α ]ᵀ

  ξ-·₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} →
    Σ ∣ L —→ Σ′ ∣ L′ →
    Σ ∣ (L · M) —→ Σ′ ∣ (L′ · M)

  ξ-·₂ : ∀ {Σ Σ′ : Store} {V M M′ : Term} →
    Value V →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (V · M) —→ Σ′ ∣ (V · M′)

  ξ-·α : ∀ {Σ Σ′ : Store} {M M′ : Term} {α : TyVar} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M • α) —→ Σ′ ∣ (M′ • α)

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
