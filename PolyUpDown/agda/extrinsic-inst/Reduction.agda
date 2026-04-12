module Reduction where

-- File Charter:
--   * Dynamic semantics for extrinsic-inst PolyUpDown terms.
--   * Raw values, one-step reduction with seal-renaming/store effects,
--   * and multi-step closure.
--   * Store invariants extracted from reduction (growth and uniqueness).
-- Note to self:
--   * Keep typing-preservation lemmas in a separate preservation-oriented file.
--   * Keep store-shape helper facts in `Store.agda` when not reduction-specific.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂)

open import Types
open import TypeProperties
open import Store
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermProperties using (_[_]; _[_]ᵀ)

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data UpValue : Up → Set where
  tag : ∀ {G : Ty} →
    UpValue (tag G)

  _↦_ : ∀ {p : Down} {q : Up} →
    UpValue (p ↦ q)

  ∀ᵖ : ∀ {p : Up} →
    UpValue (∀ᵖ p)

data DownValue : Down → Set where
  seal : ∀ {α : Seal} →
    DownValue (seal α)

  _↦_ : ∀ {p : Up} {q : Down} →
    DownValue (p ↦ q)

  ∀ᵖ : ∀ {p : Down} →
    DownValue (∀ᵖ p)

  ν_ : ∀ {p : Down} →
    DownValue (ν p)

data Value : Term → Set where
  ƛ_⇒_ :
    (A : Ty) (N : Term) →
    Value (ƛ A ⇒ N)

  $ :
    (κ : Const) →
    Value ($ κ)

  Λ_ :
    (N : Term) →
    Value (Λ N)

  _up_ : ∀ {V : Term} {p : Up} →
    Value V →
    UpValue p →
    Value (V up p)

  _down_ : ∀ {V : Term} {p : Down} →
    Value V →
    DownValue p →
    Value (V down p)

------------------------------------------------------------------------
-- One-step reduction helpers
------------------------------------------------------------------------

idˢ : Renameˢ
idˢ α = α

renameˢ-id : ∀ {A : Ty} →
  renameˢ idˢ A ≡ A
renameˢ-id {A = ＇ X} = refl
renameˢ-id {A = ｀ α} = refl
renameˢ-id {A = ‵ ι} = refl
renameˢ-id {A = ★} = refl
renameˢ-id {A = A ⇒ B} = cong₂ _⇒_ renameˢ-id renameˢ-id
renameˢ-id {A = `∀ A} = cong `∀ renameˢ-id

map-renameˢ-id : (Γ : Ctx) →
  map (renameˢ idˢ) Γ ≡ Γ
map-renameˢ-id [] = refl
map-renameˢ-id (A ∷ Γ) = cong₂ _∷_ renameˢ-id (map-renameˢ-id Γ)

renameStoreˢ-id : ∀ {Σ : Store} →
  renameStoreˢ idˢ Σ ≡ Σ
renameStoreˢ-id {Σ = []} = refl
renameStoreˢ-id {Σ = ((α , A) ∷ Σ)} =
  cong₂ _∷_
    (cong₂ _,_ refl renameˢ-id)
    renameStoreˢ-id

idˢ-⊆ˢ : ∀ {Σ : Store} →
  renameStoreˢ idˢ Σ ⊆ˢ Σ
idˢ-⊆ˢ {Σ = Σ} rewrite renameStoreˢ-id {Σ = Σ} = ⊆ˢ-refl

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : Term → Term → Set where

  β : ∀ {B : Ty} {N V : Term} →
    Value V →
    ((ƛ B ⇒ N) · V) —→ (N [ V ])

  β-up-∀ : ∀ {V : Term} {p : Up} {B T : Ty} →
    ((V up (∀ᵖ p)) ⦂∀ B [ T ]) —→
    ((V ⦂∀ up-src ∅ˢ p [ T ]) up (p [ T ]↑))

  β-up-↦ : ∀ {V W : Term} {p : Down} {q : Up} →
    ((V up (p ↦ q)) · W) —→ ((V · (W down p)) up q)

  β-down-↦ : ∀ {V W : Term} {p : Up} {q : Down} →
    ((V down (p ↦ q)) · W) —→ ((V · (W up p)) down q)

  id-up : ∀ {V : Term} {A : Ty} →
    (V up (id A)) —→ V

  id-down : ∀ {V : Term} {A : Ty} →
    (V down (id A)) —→ V

  seal-unseal : ∀ {V : Term} {α : Seal} →
    ((V down (seal α)) up (unseal α)) —→ V

  tag-untag-ok :
    ∀ {G : Ty} {V : Term} {ℓ′ : Label} →
    ((V up (tag G)) down (untag G ℓ′)) —→ V

  tag-untag-bad :
    ∀ {G H : Ty} {V : Term} {ℓ′ : Label} →
    G ≢ H →
    ((V up (tag G)) down (untag H ℓ′)) —→ blame ℓ′

  β-up-； : ∀ {V : Term} {p : Up} {q : Up} →
    (V up (p ； q)) —→ ((V up p) up q)

  β-down-； : ∀ {V : Term} {p : Down} {q : Down} →
    (V down (p ； q)) —→ ((V down p) down q)

  δ-⊕ : ∀ {m n : ℕ} →
    ($ (κℕ m) ⊕[ addℕ ] $ (κℕ n)) —→ $ (κℕ (m + n))

  blame-·₁ : ∀ {ℓ : Label} {M : Term} →
    (blame ℓ · M) —→ blame ℓ

  blame-·₂ : ∀ {ℓ : Label} {V : Term} →
    Value V →
    (V · blame ℓ) —→ blame ℓ

  blame-·α : ∀ {ℓ : Label} {B T : Ty} →
    (blame ℓ ⦂∀ B [ T ]) —→ blame ℓ

  blame-up : ∀ {p : Up} {ℓ : Label} →
    ((blame ℓ) up p) —→ blame ℓ

  blame-down : ∀ {p : Down} {ℓ : Label} →
    ((blame ℓ) down p) —→ blame ℓ

  blame-⊕₁ : ∀ {ℓ : Label} {M : Term} {op : Prim} →
    (blame ℓ ⊕[ op ] M) —→ blame ℓ

  blame-⊕₂ : ∀ {ℓ : Label} {L : Term} {op : Prim} →
    Value L →
    (L ⊕[ op ] blame ℓ) —→ blame ℓ


infix 2 _∣_—→[_]_∣_
data _∣_—→[_]_∣_ :
  Store → Term → Renameˢ → Store → Term → Set where

  id-step : ∀ {Σ : Store} {M M′ : Term} →
    M —→ M′ →
    Σ ∣ M —→[ idˢ ] Σ ∣ M′

  β-Λ : ∀ {Σ : Store} {A B : Ty} {V : Term} →
    Σ ∣ ((Λ V) ⦂∀ B [ A ]) —→[ suc ] ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣
      ((((⇑ˢᵐ V) [ ｀ zero ]ᵀ) up (reveal-⊑ A B)))

  β-down-∀ : ∀ {Σ : Store} {A B : Ty} {V : Term} {p : Down} →
    Σ ∣ ((V down (∀ᵖ p)) ⦂∀ B [ A ]) —→[ suc ] ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣
      (((((⇑ˢᵐ V) ⦂∀ ⇑ˢ (down-src (⟰ᵗ Σ) p) [ ｀ zero ]) down ((rename⊒ˢ suc p) [ ｀ zero ]↓))
         up (reveal-⊑ A (down-tgt (⟰ᵗ Σ) p))))

  β-down-ν : ∀ {Σ : Store} {A B : Ty} {V : Term} {p : Down} →
    -- TODO: add premise: Value V
    Σ ∣ ((V down (ν p)) ⦂∀ B [ A ]) —→[ suc ] ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣
      ((((⇑ˢᵐ V) down ((rename⊒ˢ suc p) [ zero ]↓ˢ))
         up (reveal-⊑ A B)))

  β-up-ν : ∀ {Σ : Store} {V : Term} {p : Up} →
    Σ ∣ (V up (ν p)) —→[ suc ] ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣
      ((((⇑ˢᵐ V) ⦂∀ ⇑ˢ (((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)) [ ｀ zero ]) up p))

  ξ-·₁ : ∀ {Σ Σ′ : Store} {ρ : Renameˢ} {L M L′ : Term} →
    Σ ∣ L —→[ ρ ] Σ′ ∣ L′ →
    Σ ∣ (L · M) —→[ ρ ] Σ′ ∣ (L′ · renameˢᵐ ρ M)

  ξ-·₂ : ∀ {Σ Σ′ : Store} {ρ : Renameˢ} {V M M′ : Term} →
    Value V →
    Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
    Σ ∣ (V · M) —→[ ρ ] Σ′ ∣ (renameˢᵐ ρ V · M′)

  ξ-·α : ∀ {Σ Σ′ : Store} {ρ : Renameˢ} {M M′ : Term} {B T : Ty} →
    Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
    Σ ∣ (M ⦂∀ B [ T ]) —→[ ρ ] Σ′ ∣ (M′ ⦂∀ renameˢ ρ B [ renameˢ ρ T ])

  ξ-up : ∀ {Σ Σ′ : Store} {ρ : Renameˢ} {p : Up} {M M′ : Term} →
    Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
    Σ ∣ (M up p) —→[ ρ ] Σ′ ∣ ((M′) up (rename⊑ˢ ρ p))

  ξ-down : ∀ {Σ Σ′ : Store} {ρ : Renameˢ} {p : Down} {M M′ : Term} →
    Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
    Σ ∣ (M down p) —→[ ρ ] Σ′ ∣ ((M′) down (rename⊒ˢ ρ p))

  ξ-⊕₁ : ∀ {Σ Σ′ : Store} {ρ : Renameˢ} {L M L′ : Term} {op : Prim} →
    Σ ∣ L —→[ ρ ] Σ′ ∣ L′ →
    Σ ∣ (L ⊕[ op ] M) —→[ ρ ] Σ′ ∣ (L′ ⊕[ op ] renameˢᵐ ρ M)

  ξ-⊕₂ : ∀ {Σ Σ′ : Store} {ρ : Renameˢ} {L M M′ : Term} {op : Prim} →
    Value L →
    Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
    Σ ∣ (L ⊕[ op ] M) —→[ ρ ] Σ′ ∣ (renameˢᵐ ρ L ⊕[ op ] M′)

------------------------------------------------------------------------
-- Store growth witness extracted from one step
------------------------------------------------------------------------

store-growth :
  ∀ {Σ Σ′ : Store}{ρ : Renameˢ}{M M′ : Term} →
  Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
  renameStoreˢ ρ Σ ⊆ˢ Σ′
store-growth (id-step red) = idˢ-⊆ˢ
store-growth β-Λ = drop ⊆ˢ-refl
store-growth β-down-∀ = drop ⊆ˢ-refl
store-growth β-down-ν = drop ⊆ˢ-refl
store-growth β-up-ν = drop ⊆ˢ-refl
store-growth (ξ-·₁ red) = store-growth red
store-growth (ξ-·₂ v red) = store-growth red
store-growth (ξ-·α red) = store-growth red
store-growth (ξ-up red) = store-growth red
store-growth (ξ-down red) = store-growth red
store-growth (ξ-⊕₁ red) = store-growth red
store-growth (ξ-⊕₂ v red) = store-growth red

unique-store-step :
  ∀ {Σ Σ′ : Store}{ρ : Renameˢ}{M M′ : Term} →
  Uniqueˢ Σ →
  Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
  Uniqueˢ Σ′
unique-store-step uΣ (id-step red) = uΣ
unique-store-step uΣ (β-Λ {A = A}) = unique-ν A uΣ
unique-store-step uΣ (β-down-∀ {A = A}) = unique-ν A uΣ
unique-store-step uΣ (β-down-ν {A = A}) = unique-ν A uΣ
unique-store-step uΣ (β-up-ν {V = V}) = unique-ν ★ uΣ
unique-store-step uΣ (ξ-·₁ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-·₂ v red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-·α red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-up red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-down red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-⊕₁ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-⊕₂ v red) = unique-store-step uΣ red

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

infix 2 _∣_—↠_∣_
infix 3 _∎
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_

data _∣_—↠_∣_ :
  Store → Term → Store → Term → Set where
  _∎ : ∀ {Σ : Store} (M : Term) →
    Σ ∣ M —↠ Σ ∣ M

  _—→⟨_⟩_ :
    ∀ {Σ Σ′ Σ″ : Store} {M N : Term} {ρ : Renameˢ} →
    (L : Term) →
    Σ ∣ L —→[ ρ ] Σ′ ∣ M →
    Σ′ ∣ M —↠ Σ″ ∣ N →
    Σ ∣ L —↠ Σ″ ∣ N

multi-trans :
  ∀ {Σ Σ′ Σ″ : Store}
    {L M N : Term} →
  Σ ∣ L —↠ Σ′ ∣ M →
  Σ′ ∣ M —↠ Σ″ ∣ N →
  Σ ∣ L —↠ Σ″ ∣ N
multi-trans (_ ∎) M—↠N = M—↠N
multi-trans (_ —→⟨ L—→M ⟩ M—↠N) N—↠P =
  _ —→⟨ L—→M ⟩ multi-trans M—↠N N—↠P

_—↠⟨_⟩_ :
  ∀ {Σ Σ′ Σ″ : Store}
    (L : Term)
    {M N : Term} →
  Σ ∣ L —↠ Σ′ ∣ M →
  Σ′ ∣ M —↠ Σ″ ∣ N →
  Σ ∣ L —↠ Σ″ ∣ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N
