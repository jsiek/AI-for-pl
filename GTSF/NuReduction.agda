module NuReduction where

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; _+_; _≤_)
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

  tag-untag-ok : ∀ {V G}
    → Value V
    ------------------------------
    → V ⟨ G ! ⟩ ⟨ G ？ ⟩  —→  V

  tag-untag-bad : ∀ {V G H}
    → Value V → G ≢ H
    ----------------------------------------
    → V ⟨ G ! ⟩ ⟨ H ？ ⟩ —→  blame

  seal-unseal : ∀ {α V A B}
    → Value V
    ------------------------------------
    → V ⟨ seal A α ⟩ ⟨ unseal α B ⟩ —→ V

  blame-·₁ : ∀ {M : Term} →
    (blame · M) —→ blame

  blame-·₂ : ∀ {V : Term} →
    Value V →
    (V · blame) —→ blame

  blame-·α : ∀ {α : TyVar} →
    (blame • α) —→ blame

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

infix 2 _∣_∣_—→_∣_
data _∣_∣_—→_∣_ : TyCtx → Store → Term → Store → Term → Set where

  pure-step : ∀ {Δ : TyCtx} {Σ : Store} {M M′ : Term}
    → M —→ M′
    -----------------
    → Δ ∣ Σ ∣ M —→ Σ ∣ M′

  -- Allow non-deterministic choice of α here so that in the proof of the
  -- Gradual Guarantee, we can choose a matching α in the simulating program.
  ν-step : ∀ {Δ : TyCtx} {Σ : Store} {N : Term} {A : Ty} {α : TyVar}
   → Δ ≤ α
    -------------------------------------
   → Δ ∣ Σ ∣ ν A N —→ (α , A) ∷ Σ ∣ N [ α ]ᵀ

  ξ-·₁ : ∀ {Δ : TyCtx} {Σ Σ′ : Store} {L M L′ : Term} →
    Δ ∣ Σ ∣ L —→ Σ′ ∣ L′ →
    Δ ∣ Σ ∣ (L · M) —→ Σ′ ∣ (L′ · M)

  ξ-·₂ : ∀ {Δ : TyCtx} {Σ Σ′ : Store} {V M M′ : Term} →
    Value V →
    Δ ∣ Σ ∣ M —→ Σ′ ∣ M′ →
    Δ ∣ Σ ∣ (V · M) —→ Σ′ ∣ (V · M′)

  ξ-·α : ∀ {Δ : TyCtx} {Σ Σ′ : Store} {M M′ : Term} {α : TyVar} →
    Δ ∣ Σ ∣ M —→ Σ′ ∣ M′ →
    Δ ∣ Σ ∣ (M • α) —→ Σ′ ∣ (M′ • α)

  ξ-⟨⟩ : ∀ {Δ : TyCtx} {Σ Σ′ : Store} {c : Coercion} {M M′ : Term} →
    Δ ∣ Σ ∣ M —→ Σ′ ∣ M′ →
    Δ ∣ Σ ∣ (M ⟨ c ⟩) —→ Σ′ ∣ (M′ ⟨ c ⟩)

  ξ-⊕₁ : ∀ {Δ : TyCtx} {Σ Σ′ : Store} {L M L′ : Term} {op : Prim} →
    Δ ∣ Σ ∣ L —→ Σ′ ∣ L′ →
    Δ ∣ Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L′ ⊕[ op ] M)

  ξ-⊕₂ : ∀ {Δ : TyCtx} {Σ Σ′ : Store} {L M M′ : Term} {op : Prim} →
    Value L →
    Δ ∣ Σ ∣ M —→ Σ′ ∣ M′ →
    Δ ∣ Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L ⊕[ op ] M′)
