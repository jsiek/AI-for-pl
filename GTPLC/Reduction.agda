module Reduction where

-- File Charter:
--   * Small-step reduction for terms.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import TyStore
open import Coercions
open import Terms
open import Primitives

--------------------------------------------------------------------------------
-- Store changes emitted by a step
--------------------------------------------------------------------------------

data StoreChange : Set where
  keep : StoreChange
  bind : Ty → StoreChange

changeTyCtx : StoreChange → TyCtx → TyCtx
changeTyCtx keep Δ = Δ
changeTyCtx (bind A) Δ = suc Δ

changeStore : StoreChange → TyStore → TyStore
changeStore keep Σ = Σ
changeStore (bind A) Σ = (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ

changeᵗ : StoreChange → Ty → Ty
changeᵗ keep A = A
changeᵗ (bind B) A = ⇑ᵗ A

change : StoreChange → Term → Term
change keep M = M
change (bind A) M = ⇑ᵗᵐ M

changeᶜ : StoreChange → Coercion → Coercion
changeᶜ keep c = c
changeᶜ (bind A) c = ⇑ᶜ c

changeᶜExt : StoreChange → Coercion → Coercion
changeᶜExt keep c = c
changeᶜExt (bind A) c = renameᶜ (extᵗ suc) c

StoreChanges : Set
StoreChanges = List StoreChange

changeTyCtxs : StoreChanges → TyCtx → TyCtx
changeTyCtxs [] Δ = Δ
changeTyCtxs (χ ∷ χs) Δ = changeTyCtxs χs (changeTyCtx χ Δ)

changeStores : StoreChanges → TyStore → TyStore
changeStores [] Σ = Σ
changeStores (χ ∷ χs) Σ = changeStores χs (changeStore χ Σ)

changeTys : StoreChanges → Ty → Ty
changeTys [] A = A
changeTys (χ ∷ χs) A = changeTys χs (changeᵗ χ A)

changes : StoreChanges → Term → Term
changes [] M = M
changes (χ ∷ χs) M = changes χs (change χ M)

--------------------------------------------------------------------------------
-- Type application
--------------------------------------------------------------------------------

infixl 7 _•

_• : Term → Term
(Λ V) • = V [ zero ]ᵀ
(V ⟨ `∀ c ⟩) • = (V •) ⟨ c [ zero ]ᶜ ⟩
(V ⟨ gen c ⟩) • = V ⟨ c [ zero ]ᶜ ⟩
V • = V

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

  β-id : ∀ {V}
    → Value V
    -------------------
    → V ⟨ id ⟩ —→  V

  β-seq : ∀ {V p q}
    → Value V
    ------------------------------
    → V ⟨ p ︔ q ⟩ —→ V ⟨ p ⟩ ⟨ q ⟩

  β-↦ : ∀ {V W p q}
    → Value V → Value W
    --------------------------------------------
    → V ⟨ p ↦ q ⟩ · W  —→  (V · (W ⟨ p ⟩)) ⟨ q ⟩

  β-inst : ∀ {V c}
    → Value V
    ---------------------------------
    → V ⟨ inst c ⟩ —→ ν ★ · V •⟨ c ⟩ 

  tag-untag-ok : ∀ {V G}
    → Value V
    ---------------------------
    → V ⟨ G ! ⟩ ⟨ G ？ ⟩  —→  V

  tag-untag-bad : ∀ {V G H}
    → Value V → G ≢ H
    ------------------------------
    → V ⟨ G ! ⟩ ⟨ H ？ ⟩ —→  blame

  seal-unseal : ∀ {α V}
    → Value V
    --------------------------------
    → V ⟨ seal α ⟩ ⟨ unseal α ⟩ —→ V

  blame-·₁ : ∀ {M : Term} 
    ----------------------
    → (blame · M) —→ blame

  blame-·₂ : ∀ {V : Term}
    → Value V
    ----------------------
    → (V · blame) —→ blame

  blame-⟨⟩ : ∀ {c : Coercion}
    -------------------------
    → (blame ⟨ c ⟩) —→ blame

  blame-⊕₁ : ∀ {M : Term} {op : Prim} 
    -----------------------------
    → (blame ⊕[ op ] M) —→ blame

  blame-⊕₂ : ∀ {L : Term} {op : Prim} 
    → Value L 
    -----------------------------
    → (L ⊕[ op ] blame) —→ blame


--------------------------------------------------------------------------------
-- Store-change one-step reduction
--------------------------------------------------------------------------------

infix 2 _—→[_]_
data _—→[_]_ : Term → StoreChange → Term → Set where

  pure-step : ∀ {M M′ : Term}
    → M —→ M′
    -----------------
    → M —→[ keep ] M′

  ν-step : ∀ {A : Ty} {V : Term} {c : Coercion}
   → Value V
    ----------------------------------------------
   → ν A · V •⟨ c ⟩ —→[ bind A ] ((⇑ᵗᵐ V) •) ⟨ c ⟩

  ξ-·₁ : ∀ {χ : StoreChange} {L M L′ : Term}
   → L —→[ χ ] L′
    --------------------------------------
   → (L · M) —→[ χ ] (L′ · change χ M)

  ξ-·₂ : ∀ {χ : StoreChange} {V M M′ : Term} →
    Value V →
    M —→[ χ ] M′ →
    (V · M) —→[ χ ] (change χ V · M′)

  ξ-⟨⟩ : ∀ {χ : StoreChange} {c : Coercion} {M M′ : Term} →
    M —→[ χ ] M′ →
    (M ⟨ c ⟩) —→[ χ ] (M′ ⟨ changeᶜ χ c ⟩)

  ξ-ν : ∀ {χ : StoreChange} {A : Ty} {L L′ : Term} {c : Coercion} →
    L —→[ χ ] L′ →
    ν A · L •⟨ c ⟩ —→[ χ ] ν (changeᵗ χ A) · L′ •⟨ changeᶜExt χ c ⟩

  blame-ν : ∀ {A : Ty} {c : Coercion} →
    ν A · blame •⟨ c ⟩  —→[ keep ] blame

  ξ-⊕₁ : ∀ {χ : StoreChange} {L M L′ : Term} {op : Prim} →
    L —→[ χ ] L′ →
    (L ⊕[ op ] M) —→[ χ ] (L′ ⊕[ op ] change χ M)

  ξ-⊕₂ : ∀ {χ : StoreChange} {L M M′ : Term} {op : Prim} →
    Value L →
    M —→[ χ ] M′ →
    (L ⊕[ op ] M) —→[ χ ] (change χ L ⊕[ op ] M′)

infix 2 _—↠[_]_
data _—↠[_]_ : Term → StoreChanges → Term → Set where
  ↠-refl : ∀ {M : Term} →
    M —↠[ [] ] M

  ↠-step : ∀ {M N P : Term}{χ : StoreChange}{χs : StoreChanges} →
    M —→[ χ ] N →
    N —↠[ χs ] P →
    M —↠[ χ ∷ χs ] P
