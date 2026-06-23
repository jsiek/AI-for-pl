module NuReduction where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_; _≤_; suc)
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
-- Type-application reduction
--------------------------------------------------------------------------------

applyCoercions : Term → List Coercion → Term
applyCoercions M [] = M
applyCoercions M (c ∷ cs) = applyCoercions (M ⟨ c ⟩) cs

data TypeApp : Set where
  app : Term → TyVar → List Coercion → TypeApp
  val : Term → List Coercion → TypeApp

infix 2 _—→ᵀ_
data _—→ᵀ_ : TypeApp → TypeApp → Set where

  β-Λᵀ : ∀ {V : Term}{α : TyVar}{cs : List Coercion}
    → Value V
    ---------------------------------------------
    → app (Λ V) α cs —→ᵀ val (V [ α ]ᵀ) cs

  β-∀ᵀ : ∀ {V : Term}{c : Coercion}{α : TyVar}{cs : List Coercion}
    → Value V
    ----------------------------------------------------------------
    → app (V ⟨ `∀ c ⟩) α cs —→ᵀ app V α ((c [ α ]ᶜ) ∷ cs)

  β-genᵀ : ∀ {A : Ty}{V : Term}{c : Coercion}{α : TyVar}
      {cs : List Coercion}
    → Value V
    ---------------------------------------------------------------
    → app (V ⟨ gen A c ⟩) α cs —→ᵀ val V ((c [ α ]ᶜ) ∷ cs)

infix 2 _—↠ᵀ_
data _—↠ᵀ_ : TypeApp → TypeApp → Set where

  doneᵀ : ∀ {S : TypeApp}
      ------------
    → S —↠ᵀ S

  stepᵀ : ∀ {S T U : TypeApp}
    → S —→ᵀ T
    → T —↠ᵀ U
      ------------
    → S —↠ᵀ U

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

infix 2 _∣_∣_—→_∣_∣_
data _∣_∣_—→_∣_∣_ :
    TyCtx → Store → Term → TyCtx → Store → Term → Set where

  pure-step : ∀ {Δ : TyCtx} {Σ : Store} {M M′ : Term}
    → M —→ M′
    -----------------
    → Δ ∣ Σ ∣ M —→ Δ ∣ Σ ∣ M′

  -- Allow non-deterministic choice of α here so that in the proof of the
  -- Gradual Guarantee, we can choose a matching α in the simulating program.
  ν-step : ∀ {Δ : TyCtx} {Σ : Store} {A : Ty} {L V : Term}
      {c : Coercion} {α : TyVar} {cs : List Coercion}
   → Δ ≤ α
   → α ∉ domˢ Σ
   → app L α ((c [ α ]ᶜ) ∷ []) —↠ᵀ val V cs
    -------------------------------------
   → Δ ∣ Σ ∣ ν A L c —→ suc α ∣ (α , A) ∷ Σ
       ∣ applyCoercions V cs

  ξ-·₁ : ∀ {Δ Δ′ : TyCtx} {Σ Σ′ : Store} {L M L′ : Term} →
    Δ ∣ Σ ∣ L —→ Δ′ ∣ Σ′ ∣ L′ →
    Δ ∣ Σ ∣ (L · M) —→ Δ′ ∣ Σ′ ∣ (L′ · M)

  ξ-·₂ : ∀ {Δ Δ′ : TyCtx} {Σ Σ′ : Store} {V M M′ : Term} →
    Value V →
    Δ ∣ Σ ∣ M —→ Δ′ ∣ Σ′ ∣ M′ →
    Δ ∣ Σ ∣ (V · M) —→ Δ′ ∣ Σ′ ∣ (V · M′)

  ξ-⟨⟩ : ∀ {Δ Δ′ : TyCtx} {Σ Σ′ : Store}
      {c : Coercion} {M M′ : Term} →
    Δ ∣ Σ ∣ M —→ Δ′ ∣ Σ′ ∣ M′ →
    Δ ∣ Σ ∣ (M ⟨ c ⟩) —→ Δ′ ∣ Σ′ ∣ (M′ ⟨ c ⟩)

  ξ-ν : ∀ {Δ Δ′ : TyCtx} {Σ Σ′ : Store}
      {A : Ty} {L L′ : Term} {c : Coercion} →
    Δ ∣ Σ ∣ L —→ Δ′ ∣ Σ′ ∣ L′ →
    Δ ∣ Σ ∣ ν A L c —→ Δ′ ∣ Σ′ ∣ ν A L′ c

  blame-ν : ∀ {Δ : TyCtx} {Σ : Store} {A : Ty} {c : Coercion} →
    Δ ∣ Σ ∣ ν A blame c —→ Δ ∣ Σ ∣ blame

  ξ-⊕₁ : ∀ {Δ Δ′ : TyCtx} {Σ Σ′ : Store}
      {L M L′ : Term} {op : Prim} →
    Δ ∣ Σ ∣ L —→ Δ′ ∣ Σ′ ∣ L′ →
    Δ ∣ Σ ∣ (L ⊕[ op ] M) —→ Δ′ ∣ Σ′ ∣ (L′ ⊕[ op ] M)

  ξ-⊕₂ : ∀ {Δ Δ′ : TyCtx} {Σ Σ′ : Store}
      {L M M′ : Term} {op : Prim} →
    Value L →
    Δ ∣ Σ ∣ M —→ Δ′ ∣ Σ′ ∣ M′ →
    Δ ∣ Σ ∣ (L ⊕[ op ] M) —→ Δ′ ∣ Σ′ ∣ (L ⊕[ op ] M′)
