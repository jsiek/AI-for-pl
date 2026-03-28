module Reduction where

-- File Charter:
--   * Dynamic semantics (values and one-step/multi-step reduction) for PolyCast terms.
--   * Adapted from PolyBlame reduction rules, but using intrinsic PolyCast coercions.
--   * No imprecision up/down judgments; casts use `_⟨_⟩` with `Σ ⊢ A ⇨ B`.
-- Note to self:
--   * Place substitution-specific facts in `TermSubst.agda`.

open import Data.Nat using (ℕ; _+_; suc)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst; refl)
open import Types
open import Store
open import Coercions
open import PolyCast
open import TermSubst

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Set where
  V-ƛ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
    {N : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B} →
    Value (ƛ A ⇒ N)

  V-const :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{κ : Const} →
    Value ($ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} κ refl)

  V-Λ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ}
    {N : (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A} →
    Value (Λ N)

  V-⟨!⟩ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{G : Ty Δ Ψ}
    {g : Ground G}{V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G} →
    Value V →
    Value (V ⟨ id ； (g !) ⟩)

  V-⟨⁻⟩ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty 0 Ψ}{α}
    {h : Σ ∋ˢ α ⦂ A}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ wkTy0 A} →
    Value V →
    Value (V ⟨ id ； (h ⁻) ⟩)

  V-⟨↦⟩ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B C D : Ty Δ Ψ}
    {c : Σ ⊢ C ⇨ A}{d : Σ ⊢ B ⇨ D}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
    Value V →
    Value (V ⟨ id ； (c ↦ d) ⟩)

  V-⟨∀⟩ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty (suc Δ) Ψ}
    {c : Σ ⊢ A ⇨ B}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)} →
    Value V →
    Value (V ⟨ id ； (∀ᶜ c) ⟩)

  V-⟨𝒢⟩ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A [ `★ ]ᵗ)} →
    Value V →
    Value (V ⟨ id ； (𝒢 {A = A}) ⟩)

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Set where

  β :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
      {N : Δ ∣ Ψ ∣ Σ ∣ (B ∷ Γ) ⊢ A}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B} →
    Value V →
    (ƛ B ⇒ N) · V —→ N [ V ]

  β-Λ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A : Ty (suc Δ) Ψ}
      {V : (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((Λ V) ·α α [ h ]) refl —→ V [ ｀ α ]ᵀ

  β-⟨∀⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty (suc Δ) Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)}
      {c : Σ ⊢ A ⇨ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((V ⟨ id ； (∀ᶜ c) ⟩) ·α α [ h ]) refl —→ ((V ·α α [ h ]) refl) ⟨ c [ ｀ α ]ᶜᵗ ⟩

  β-⟨↦⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B C D : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ C}
      {c : Σ ⊢ C ⇨ A}
      {d : Σ ⊢ B ⇨ D} →
    (V ⟨ id ； (c ↦ d) ⟩) · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩

  ⟨id⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A} →
    (V ⟨ id ⟩) —→ V

  ⟨⁻⟩⟨⁺⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty 0 Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ wkTy0 A}
      {α}
      {h : Σ ∋ˢ α ⦂ A}
      {h′ : Σ ∋ˢ α ⦂ B}
      (uΣ : Uniqueˢ Σ) →
    (V ⟨ id ； (h ⁻) ⟩ ⟨ id ； (h′ ⁺) ⟩) —→
      subst
        (λ T → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ T)
        (cong wkTy0 (lookup-unique uΣ h h′))
        V

  ⟨!⟩⟨?⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{G : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G}
      {g g′ : Ground G}{ℓ} →
    (V ⟨ id ； (g !) ⟩ ⟨ id ； (g′ `? ℓ) ⟩) —→ V

  ⟨!⟩⟨?⟩-bad :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{G H : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G}
      {g : Ground G}{h : Ground H}{ℓ} →
    G ≢ H →
    (V ⟨ id ； (g !) ⟩ ⟨ id ； (h `? ℓ) ⟩) —→ blame ℓ

  β-⟨；⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B C : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {c : Σ ⊢ A ⇨ B}
      {d : Σ ⊢ B ⇨ᵃ C} →
    V ⟨ c ； d ⟩ —→ (V ⟨ c ⟩) ⟨ id ； d ⟩

  β-⟨cstep⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {c c′ : Σ ⊢ A ⇨ B} →
    c —→ᶜᶜ c′ →
    V ⟨ c ⟩ —→ V ⟨ c′ ⟩

  ξ-·₁ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {L L′ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A} →
    L —→ L′ →
    (L · M) —→ (L′ · M)

  ξ-·₂ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {M M′ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A} →
    Value V →
    M —→ M′ →
    (V · M) —→ (V · M′)

  ξ-·α :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A : Ty (suc Δ) Ψ}
      {M M′ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    M —→ M′ →
    ((M ·α α [ h ]) refl) —→ ((M′ ·α α [ h ]) refl)

  ξ-⟨⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {M M′ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {c : Σ ⊢ A ⇨ B} →
    M —→ M′ →
    (M ⟨ c ⟩) —→ (M′ ⟨ c ⟩)

  ξ-⊕₁ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {L L′ M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    L —→ L′ →
    (L ⊕[ op ] M) —→ (L′ ⊕[ op ] M)

  ξ-⊕₂ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {L M M′ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    M —→ M′ →
    (L ⊕[ op ] M) —→ (L ⊕[ op ] M′)

  δ-⊕ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {m n : ℕ} →
    ($ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} (κℕ m) refl
      ⊕[ addℕ ]
      $ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} (κℕ n) refl)
      —→
    $ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} (κℕ (m + n)) refl

  blame-·₁ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
      {ℓ : Label}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A} →
    (blame {A = A ⇒ B} ℓ · M) —→ blame {A = B} ℓ

  blame-·₂ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
      {ℓ : Label}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
    Value V →
    (V · blame {A = A} ℓ) —→ blame {A = B} ℓ

  blame-·α :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A : Ty (suc Δ) Ψ}
      {ℓ : Label}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (_·α_[_]
      {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
      {A = A} {C = C}
      (blame {A = `∀ A} ℓ) α h refl) —→
      blame {A = A [ ｀ α ]ᵗ} ℓ

  blame-⟨⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {ℓ : Label}
      {c : Σ ⊢ A ⇨ B} →
    (_⟨_⟩
      {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
      {A = A} {B = B}
      (blame {A = A} ℓ) c) —→
    blame {A = B} ℓ

  blame-⊕₁ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {ℓ : Label}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    (blame {A = ‵ `ℕ} ℓ ⊕[ op ] M) —→ blame {A = ‵ `ℕ} ℓ

  blame-⊕₂ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {ℓ : Label}
      {L : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (L ⊕[ op ] blame {A = ‵ `ℕ} ℓ) —→ blame {A = ‵ `ℕ} ℓ

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

infix 2 _—↠_
infix 3 _∎
infixr 2 _—→⟨_⟩_

data _—↠_ : ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Set where

  _∎ : ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ}
    (M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A) →
    M —↠ M

  _—→⟨_⟩_ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ}
      (L : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A)
      {M N : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A} →
    L —→ M →
    M —↠ N →
    L —↠ N
