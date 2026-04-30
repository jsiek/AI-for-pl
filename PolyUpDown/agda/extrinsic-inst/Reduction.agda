module Reduction where

-- File Charter:
--   * Dynamic semantics for extrinsic-inst PolyUpDown terms.
--   * Raw values and raw one-step reduction shared by store-threaded
--   * semantics.
-- Note to self:
--   * Keep typing-preservation lemmas in a separate preservation-oriented file.
--   * Keep store-threaded reduction rules in `ReductionFresh.agda`.

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
open import Terms public hiding (_[_]ᵀ)
open import TermProperties using (_[_]; _[_]ᵀ)

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

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : Term → Term → Set where

  β : ∀ {B : Ty} {N V : Term} →
    Value V →
    ((ƛ B ⇒ N) · V) —→ (N [ V ])

  β-up-∀ : ∀ {V : Term} {p : Up} {B T : Ty} →
    Value V →
    ((V up (∀ᵖ p)) ⦂∀ B [ T ]) —→
    ((V ⦂∀ up-src ∅ˢ p [ T ]) up (p [ T ]↑))

  β-up-↦ : ∀ {V W : Term} {p : Down} {q : Up} →
    Value V →
    Value W →
    ((V up (p ↦ q)) · W) —→ ((V · (W down p)) up q)

  β-down-↦ : ∀ {V W : Term} {p : Up} {q : Down} →
    Value V →
    Value W →
    ((V down (p ↦ q)) · W) —→ ((V · (W up p)) down q)

  id-up : ∀ {V : Term} {A : Ty} →
    Value V →
    (V up (id A)) —→ V

  id-down : ∀ {V : Term} {A : Ty} →
    Value V →
    (V down (id A)) —→ V

  seal-unseal : ∀ {V : Term} {p : Down} {q : Up} {α : Seal} →
    Value V →
    ((V down (seal p α)) up (unseal α q)) —→ ((V down p) up q)

  tag-untag-ok :
    ∀ {G : Ty} {V : Term} {p : Up} {q : Down} {ℓ′ : Label} →
    Value V →
    ((V up (tag p G)) down (untag G ℓ′ q)) —→ ((V up p) down q)

  tag-untag-bad :
    ∀ {G H : Ty} {V : Term} {p : Up} {q : Down} {ℓ′ : Label} →
    Value V →
    G ≢ H →
    ((V up (tag p G)) down (untag H ℓ′ q)) —→ blame ℓ′

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

raw-value-no-step :
  ∀ {V N : Term} →
  Value V →
  V —→ N →
  ⊥
raw-value-no-step () (β v)
raw-value-no-step () (β-up-∀ v)
raw-value-no-step () (β-up-↦ vV vW)
raw-value-no-step () (β-down-↦ vV vW)
raw-value-no-step (_up_ vV ()) (id-up v)
raw-value-no-step (_down_ vV ()) (id-down v)
raw-value-no-step (_up_ vV ()) (seal-unseal v)
raw-value-no-step (_down_ vV ()) (tag-untag-ok v)
raw-value-no-step (_down_ vV ()) (tag-untag-bad v neq)
raw-value-no-step () δ-⊕
raw-value-no-step () blame-·₁
raw-value-no-step () (blame-·₂ v)
raw-value-no-step () blame-·α
raw-value-no-step (_up_ () vp) blame-up
raw-value-no-step (_down_ () vp) blame-down
raw-value-no-step () blame-⊕₁
raw-value-no-step () (blame-⊕₂ v)
