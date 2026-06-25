module NuReduction where

-- File Charter:
--   * Small-step reduction for Nu GTSF terms.
--   * Defines store-change steps, runtime bullet type-application redexes,
--     context-shifting side conditions, and the multi-step closure.
--   * Store changes are interpreted by `applyTyCtx`, `applyStore`, and related
--     syntax actions used by preservation.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)



open import Types
open import Coercions
open import NuTerms
open import Primitives

--------------------------------------------------------------------------------
-- Store changes emitted by a step
--------------------------------------------------------------------------------

data StoreChange : Set where
  keep : StoreChange
  bind : Ty → StoreChange

data Shiftable : StoreChange → Term → Set where
  shift-keep : ∀ {M} → Shiftable keep M
  shift-bind : ∀ {A M} → No• M → Shiftable (bind A) M

applyTyCtx : StoreChange → TyCtx → TyCtx
applyTyCtx keep Δ = Δ
applyTyCtx (bind A) Δ = suc Δ

applyStore : StoreChange → Store → Store
applyStore keep Σ = Σ
applyStore (bind A) Σ = (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ

applyTy : StoreChange → Ty → Ty
applyTy keep A = A
applyTy (bind B) A = ⇑ᵗ A

applyTerm : StoreChange → Term → Term
applyTerm keep M = M
applyTerm (bind A) M = ⇑ᵗᵐ M

applyCoercion : StoreChange → Coercion → Coercion
applyCoercion keep c = c
applyCoercion (bind A) c = ⇑ᶜ c

applyCoercionUnderTyBinder : StoreChange → Coercion → Coercion
applyCoercionUnderTyBinder keep c = c
applyCoercionUnderTyBinder (bind A) c = renameᶜ (extᵗ suc) c

StoreChanges : Set
StoreChanges = List StoreChange

applyTyCtxs : StoreChanges → TyCtx → TyCtx
applyTyCtxs [] Δ = Δ
applyTyCtxs (χ ∷ χs) Δ = applyTyCtxs χs (applyTyCtx χ Δ)

applyStores : StoreChanges → Store → Store
applyStores [] Σ = Σ
applyStores (χ ∷ χs) Σ = applyStores χs (applyStore χ Σ)

applyTys : StoreChanges → Ty → Ty
applyTys [] A = A
applyTys (χ ∷ χs) A = applyTys χs (applyTy χ A)

applyTerms : StoreChanges → Term → Term
applyTerms [] M = M
applyTerms (χ ∷ χs) M = applyTerms χs (applyTerm χ M)

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

  β-Λ• : ∀ {V : Term}
    → Value V
    ---------------------
    → (Λ V) • —→ V [ zero ]ᵀ

  β-∀• : ∀ {V : Term}{c : Coercion}
    → Value V
    ---------------------------------------
    → (V ⟨ `∀ c ⟩) • —→ (V •) ⟨ c [ zero ]ᶜ ⟩

  β-gen• : ∀ {A : Ty}{V : Term}{c : Coercion}
    → Value V
    -------------------------------------
    → (V ⟨ gen A c ⟩) • —→ V ⟨ c [ zero ]ᶜ ⟩

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

  β-inst : ∀ {V B c}
    → Value V
    ----------------------------------------------
    → V ⟨ inst B c ⟩ —→ ν ★ V c

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

  blame-• : blame • —→ blame

  blame-⟨⟩ : ∀ {c : Coercion} →
    (blame ⟨ c ⟩) —→ blame

  blame-⊕₁ : ∀ {M : Term} {op : Prim} →
    (blame ⊕[ op ] M) —→ blame

  blame-⊕₂ : ∀ {L : Term} {op : Prim} →
    Value L →
    (L ⊕[ op ] blame) —→ blame


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
   → No• V
    -------------------------------------
   → ν A V c —→[ bind A ] ((⇑ᵗᵐ V) •) ⟨ c ⟩

  ξ-·₁ : ∀ {χ : StoreChange} {L M L′ : Term} →
    L —→[ χ ] L′ →
    Shiftable χ M →
    (L · M) —→[ χ ] (L′ · applyTerm χ M)

  ξ-·₂ : ∀ {χ : StoreChange} {V M M′ : Term} →
    Value V →
    Shiftable χ V →
    M —→[ χ ] M′ →
    (V · M) —→[ χ ] (applyTerm χ V · M′)

  ξ-⟨⟩ : ∀ {χ : StoreChange} {c : Coercion} {M M′ : Term} →
    M —→[ χ ] M′ →
    (M ⟨ c ⟩) —→[ χ ] (M′ ⟨ applyCoercion χ c ⟩)

  ξ-ν : ∀ {χ : StoreChange} {A : Ty} {L L′ : Term}
      {c : Coercion} →
    L —→[ χ ] L′ →
    ν A L c —→[ χ ] ν (applyTy χ A) L′
      (applyCoercionUnderTyBinder χ c)

  blame-ν : ∀ {A : Ty} {c : Coercion} →
    ν A blame c —→[ keep ] blame

  ξ-⊕₁ : ∀ {χ : StoreChange} {L M L′ : Term} {op : Prim} →
    L —→[ χ ] L′ →
    Shiftable χ M →
    (L ⊕[ op ] M) —→[ χ ] (L′ ⊕[ op ] applyTerm χ M)

  ξ-⊕₂ : ∀ {χ : StoreChange} {L M M′ : Term} {op : Prim} →
    Value L →
    Shiftable χ L →
    M —→[ χ ] M′ →
    (L ⊕[ op ] M) —→[ χ ] (applyTerm χ L ⊕[ op ] M′)

infix 2 _—↠[_]_
data _—↠[_]_ : Term → StoreChanges → Term → Set where
  ↠-refl : ∀ {M : Term} →
    M —↠[ [] ] M

  ↠-step : ∀ {M N P : Term}{χ : StoreChange}{χs : StoreChanges} →
    M —→[ χ ] N →
    N —↠[ χs ] P →
    M —↠[ χ ∷ χs ] P
