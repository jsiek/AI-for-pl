module Reduction where

-- File Charter:
--   * Dynamic semantics (values and one-step/multi-step reduction) for PolyCast terms.
--   * Adapted from PolyBlame reduction rules, but using intrinsic PolyCast coercions.
--   * No imprecision up/down judgments; casts use `_⟨_⟩` with `Σ ⊢ A ⇨ B`.
-- Note to self:
--   * Place substitution-specific facts in `TermSubst.agda`.

open import Data.Nat using (ℕ; _+_; suc)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; subst; sym; refl)
open import Types
open import Store
open import Coercions
open import PolyCast
open import TypeSubst using (renameLookupˢ)
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

idˢ : ∀{Ψ} → Renameˢ Ψ Ψ
idˢ α = α

renameˢ-id :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ} →
  renameˢ idˢ A ≡ A
renameˢ-id {A = ＇ X} = refl
renameˢ-id {A = ｀ α} = refl
renameˢ-id {A = ‵ ι} = refl
renameˢ-id {A = `★} = refl
renameˢ-id {A = A ⇒ B} = cong₂ _⇒_ renameˢ-id renameˢ-id
renameˢ-id {A = `∀ A} = cong `∀ renameˢ-id

map-renameˢ-id :
  ∀{Δ}{Ψ} →
  (Γ : Ctx Δ Ψ) →
  map (renameˢ idˢ) Γ ≡ Γ
map-renameˢ-id [] = refl
map-renameˢ-id (A ∷ Γ) = cong₂ _∷_ renameˢ-id (map-renameˢ-id Γ)

renameStoreˢ-id :
  ∀{Ψ}{Σ : Store Ψ} →
  renameStoreˢ idˢ Σ ≡ Σ
renameStoreˢ-id {Σ = []} = refl
renameStoreˢ-id {Σ = ((α , A) ∷ Σ)} =
  cong₂ _∷_
    (cong₂ _,_ refl renameˢ-id)
    renameStoreˢ-id

idˢ-⊆ˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  renameStoreˢ idˢ Σ ⊆ˢ Σ
idˢ-⊆ˢ {Σ = Σ} rewrite renameStoreˢ-id {Σ = Σ} = ⊆ˢ-refl

id-step-term :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ map (renameˢ idˢ) Γ ⊢ renameˢ idˢ A
id-step-term {Γ = Γ} {A = A} M =
  cast⊢
    refl
    (sym (map-renameˢ-id Γ))
    (sym renameˢ-id)
    M

infix 2 _—→[_]_
data _—→[_]_ :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  (ρ : Renameˢ Ψ Ψ′) →
  Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A → Set where

  β :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
      {N : Δ ∣ Ψ ∣ Σ ∣ (B ∷ Γ) ⊢ A}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B} →
    Value V →
    (ƛ B ⇒ N) · V —→[ idˢ ] id-step-term (N [ V ])

  β-Λ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A : Ty (suc Δ) Ψ}
      {V : (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((Λ V) ·α α [ h ]) refl —→[ idˢ ] id-step-term (V [ ｀ α ]ᵀ)

  β-⟨∀⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty (suc Δ) Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)}
      {c : Σ ⊢ A ⇨ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((V ⟨ id ； (∀ᶜ c) ⟩) ·α α [ h ]) refl
      —→[ idˢ ]
    id-step-term (((V ·α α [ h ]) refl) ⟨ c [ ｀ α ]ᶜᵗ ⟩)

  β-⟨↦⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B C D : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {W : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ C}
      {c : Σ ⊢ C ⇨ A}
      {d : Σ ⊢ B ⇨ D} →
    (V ⟨ id ； (c ↦ d) ⟩) · W
      —→[ idˢ ]
    id-step-term ((V · (W ⟨ c ⟩)) ⟨ d ⟩)

  β-ν :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A : Ty 0 Ψ}{B : Ty Δ Ψ}
      {N : Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ B)} →
    (ν:= A ∙ N) —→[ Sˢ ] N

  ⟨id⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A} →
    (V ⟨ id ⟩) —→[ idˢ ] id-step-term V

  ⟨⁻⟩⟨⁺⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty 0 Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ wkTy0 A}
      {α}
      {h : Σ ∋ˢ α ⦂ A}
      {h′ : Σ ∋ˢ α ⦂ B}
      (uΣ : Uniqueˢ Σ) →
    (V ⟨ id ； (h ⁻) ⟩ ⟨ id ； (h′ ⁺) ⟩)
      —→[ idˢ ]
    id-step-term
      (subst
        (λ T → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ T)
        (cong wkTy0 (lookup-unique uΣ h h′))
        V)

  ⟨!⟩⟨?⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{G : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G}
      {g g′ : Ground G}{ℓ} →
    (V ⟨ id ； (g !) ⟩ ⟨ id ； (g′ `? ℓ) ⟩) —→[ idˢ ] id-step-term V

  ⟨!⟩⟨?⟩-bad :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{G H : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G}
      {g : Ground G}{h : Ground H}{ℓ} →
    G ≢ H →
    (V ⟨ id ； (g !) ⟩ ⟨ id ； (h `? ℓ) ⟩) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = Γ} {A = H} (blame {A = H} ℓ)

  β-⟨；⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B C : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {c : Σ ⊢ A ⇨ B}
      {d : Σ ⊢ B ⇨ᵃ C} →
    V ⟨ c ； d ⟩ —→[ idˢ ] id-step-term ((V ⟨ c ⟩) ⟨ id ； d ⟩)

  ξ-·₁ :
    ∀ {Δ}{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {L : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {L′ : Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ (A ⇒ B)} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L · M) —→[ ρ ] (L′ · wkΣ-term wρ (renameˢ-term ρ M))

  ξ-·₂ :
    ∀ {Δ}{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {M′ : Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A} →
    Value V →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (V · M) —→[ ρ ] (wkΣ-term wρ (renameˢ-term ρ V) · M′)

  ξ-·α :
    ∀ {Δ}{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}
      {A : Ty (suc Δ) Ψ}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)}
      {M′ : Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ (`∀ A)}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    ((M ·α α [ h ]) refl)
      —→[ ρ ]
    cast⊢
      refl
      refl
      (sym (renameˢ-[]ᵗ-seal ρ A α))
      ((M′ ·α (ρ α) [ wkLookupˢ wρ (renameLookupˢ ρ h) ]) refl)

  ξ-⟨⟩ :
    ∀ {Δ}{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
      {M′ : Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A}
      {c : Σ ⊢ A ⇨ B} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (M ⟨ c ⟩) —→[ ρ ] (M′ ⟨ wkΣᶜ wρ (renameᶜˢ ρ c) ⟩)

  ξ-⊕₁ :
    ∀ {Δ}{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}
      {L M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {L′ : Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L ⊕[ op ] M) —→[ ρ ] (L′ ⊕[ op ] wkΣ-term wρ (renameˢ-term ρ M))

  ξ-⊕₂ :
    ∀ {Δ}{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}
      {L M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {M′ : Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (L ⊕[ op ] M) —→[ ρ ] (wkΣ-term wρ (renameˢ-term ρ L) ⊕[ op ] M′)

  δ-⊕ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {m n : ℕ} →
    ($ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} (κℕ m) refl
      ⊕[ addℕ ]
      $ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} (κℕ n) refl)
      —→[ idˢ ]
    id-step-term ($ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} (κℕ (m + n)) refl)

  blame-·₁ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
      {ℓ : Label}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A} →
    (blame {A = A ⇒ B} ℓ · M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = Γ} {A = B} (blame {A = B} ℓ)

  blame-·₂ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
      {ℓ : Label}
      {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
    Value V →
    (V · blame {A = A} ℓ) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = Γ} {A = B} (blame {A = B} ℓ)

  blame-·α :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A : Ty (suc Δ) Ψ}
      {ℓ : Label}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (_·α_[_]
      {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
      {A = A} {C = C}
      (blame {A = `∀ A} ℓ) α h refl)
      —→[ idˢ ]
    id-step-term
      {Σ = Σ}
      {Γ = Γ}
      {A = A [ ｀ α ]ᵗ}
      (blame {A = A [ ｀ α ]ᵗ} ℓ)

  blame-⟨⟩ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {A B : Ty Δ Ψ}
      {ℓ : Label}
      {c : Σ ⊢ A ⇨ B} →
    (_⟨_⟩
      {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
      {A = A} {B = B}
      (blame {A = A} ℓ) c)
      —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = Γ} {A = B} (blame {A = B} ℓ)

  blame-⊕₁ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {ℓ : Label}
      {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    (blame {A = ‵ `ℕ} ℓ ⊕[ op ] M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = Γ} {A = ‵ `ℕ} (blame {A = ‵ `ℕ} ℓ)

  blame-⊕₂ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
      {ℓ : Label}
      {L : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (L ⊕[ op ] blame {A = ‵ `ℕ} ℓ) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = Γ} {A = ‵ `ℕ} (blame {A = ‵ `ℕ} ℓ)

------------------------------------------------------------------------
-- Store growth witness extracted from one step
------------------------------------------------------------------------

store-growth :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ}
    {ρ : Renameˢ Ψ Ψ′}
    {M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A}
    {M′ : Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A} →
  M —→[ ρ ] M′ →
  renameStoreˢ ρ Σ ⊆ˢ Σ′
store-growth (β v) = idˢ-⊆ˢ
store-growth (β-Λ) = idˢ-⊆ˢ
store-growth (β-⟨∀⟩) = idˢ-⊆ˢ
store-growth (β-⟨↦⟩) = idˢ-⊆ˢ
store-growth β-ν = drop ⊆ˢ-refl
store-growth ⟨id⟩ = idˢ-⊆ˢ
store-growth (⟨⁻⟩⟨⁺⟩ uΣ) = idˢ-⊆ˢ
store-growth ⟨!⟩⟨?⟩ = idˢ-⊆ˢ
store-growth (⟨!⟩⟨?⟩-bad neq) = idˢ-⊆ˢ
store-growth β-⟨；⟩ = idˢ-⊆ˢ
store-growth (ξ-·₁ wρ red) = wρ
store-growth (ξ-·₂ v wρ red) = wρ
store-growth (ξ-·α wρ red) = wρ
store-growth (ξ-⟨⟩ wρ red) = wρ
store-growth (ξ-⊕₁ wρ red) = wρ
store-growth (ξ-⊕₂ v wρ red) = wρ
store-growth δ-⊕ = idˢ-⊆ˢ
store-growth blame-·₁ = idˢ-⊆ˢ
store-growth (blame-·₂ v) = idˢ-⊆ˢ
store-growth blame-·α = idˢ-⊆ˢ
store-growth blame-⟨⟩ = idˢ-⊆ˢ
store-growth blame-⊕₁ = idˢ-⊆ˢ
store-growth (blame-⊕₂ v) = idˢ-⊆ˢ
