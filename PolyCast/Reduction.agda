module Reduction where

-- File Charter:
--   * Dynamic semantics (values and one-step/multi-step reduction) for PolyCast terms.
--   * Adapted from PolyBlame reduction rules, but using intrinsic PolyCast coercions.
--   * No imprecision up/down judgments; casts use `_⟨_⟩` with `Σ ⊢ A ⇨ B`.
-- Note to self:
--   * Place substitution-specific facts in `TermSubst.agda`.

open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; subst; sym; trans; refl)
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
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
    {g : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ (⇑ˢ B) ⇨ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B} →
    Value V →
    Value (V ⟨ id ； (𝒢 {A = A} g) ⟩)

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

-- Coercion synthesis for substituting one type environment by another.
-- `instSubst⁺` builds a coercion from `substᵗ σ A` to `substᵗ τ A`,
-- while `instSubst⁻` builds the reverse direction.
-- We thread both variable-direction hypotheses so the function case
-- can flip variance in the domain (`↦` expects a reverse coercion there).
mutual
  instSubst⁺ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ} →
    (σ τ : Substᵗ Δ Δ′ Ψ) →
    ((X : TyVar Δ) → Σ ⊢ σ X ⇨ τ X) →
    ((X : TyVar Δ) → Σ ⊢ τ X ⇨ σ X) →
    (A : Ty Δ Ψ) →
    Σ ⊢ substᵗ σ A ⇨ substᵗ τ A
  instSubst⁺ σ τ up down (＇ X) = up X
  instSubst⁺ σ τ up down (｀ α) = id
  instSubst⁺ σ τ up down (‵ ι) = id
  instSubst⁺ σ τ up down `★ = id
  instSubst⁺ σ τ up down (A ⇒ B) =
    id ； ((instSubst⁻ σ τ up down A) ↦ (instSubst⁺ σ τ up down B))
  instSubst⁺ {Σ = Σ} σ τ up down (`∀ A) =
    id ； (∀ᶜ (instSubst⁺ (extsᵗ σ) (extsᵗ τ) up′ down′ A))
    where
      up′ : (X : TyVar (suc _)) → Σ ⊢ extsᵗ σ X ⇨ extsᵗ τ X
      up′ Zᵗ = id
      up′ (Sᵗ X) = renameᶜᵗ Sᵗ (up X)

      down′ : (X : TyVar (suc _)) → Σ ⊢ extsᵗ τ X ⇨ extsᵗ σ X
      down′ Zᵗ = id
      down′ (Sᵗ X) = renameᶜᵗ Sᵗ (down X)

  instSubst⁻ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ} →
    (σ τ : Substᵗ Δ Δ′ Ψ) →
    ((X : TyVar Δ) → Σ ⊢ σ X ⇨ τ X) →
    ((X : TyVar Δ) → Σ ⊢ τ X ⇨ σ X) →
    (A : Ty Δ Ψ) →
    Σ ⊢ substᵗ τ A ⇨ substᵗ σ A
  instSubst⁻ σ τ up down (＇ X) = down X
  instSubst⁻ σ τ up down (｀ α) = id
  instSubst⁻ σ τ up down (‵ ι) = id
  instSubst⁻ σ τ up down `★ = id
  instSubst⁻ σ τ up down (A ⇒ B) =
    id ； ((instSubst⁺ σ τ up down A) ↦ (instSubst⁻ σ τ up down B))
  instSubst⁻ {Σ = Σ} σ τ up down (`∀ A) =
    id ； (∀ᶜ (instSubst⁻ (extsᵗ σ) (extsᵗ τ) up′ down′ A))
    where
      up′ : (X : TyVar (suc _)) → Σ ⊢ extsᵗ σ X ⇨ extsᵗ τ X
      up′ Zᵗ = id
      up′ (Sᵗ X) = renameᶜᵗ Sᵗ (up X)

      down′ : (X : TyVar (suc _)) → Σ ⊢ extsᵗ τ X ⇨ extsᵗ σ X
      down′ Zᵗ = id
      down′ (Sᵗ X) = renameᶜᵗ Sᵗ (down X)

-- Variable-level bridge for the single-variable substitution used by
-- instantiation: map the bound variable from `★` to `｀ α` (and back).
-- For Δ = 1, only `Zᵗ` is possible; `Sᵗ ()` is unreachable.
instVar⁺ :
  ∀ {Ψ}{Σ : Store Ψ}
    {α : Seal Ψ}{C : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ C →
  (X : TyVar (suc 0)) →
  Σ ⊢ singleTyEnv `★ X ⇨ singleTyEnv (｀ α) X
instVar⁺ {α = α} h Zᵗ = id ； ((｀ α) `? zero)
instVar⁺ h (Sᵗ ())

instVar⁻ :
  ∀ {Ψ}{Σ : Store Ψ}
    {α : Seal Ψ}{C : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ C →
  (X : TyVar (suc 0)) →
  Σ ⊢ singleTyEnv (｀ α) X ⇨ singleTyEnv `★ X
instVar⁻ {α = α} h Zᵗ = id ； ((｀ α) !)
instVar⁻ h (Sᵗ ())

instSeal :
  ∀ {Ψ}{Σ : Store Ψ}
    {A : Ty (suc 0) Ψ}
    {α : Seal Ψ}{C : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ C →
  Σ ⊢ (A [ `★ ]ᵗ) ⇨ (A [ ｀ α ]ᵗ)
instSeal {A = A} {α = α} h =
  instSubst⁺
    (singleTyEnv `★)
    (singleTyEnv (｀ α))
    (instVar⁺ h)
    (instVar⁻ h)
    A

instUnseal :
  ∀ {Ψ}{Σ : Store Ψ}
    {A : Ty (suc 0) Ψ}
    {α : Seal Ψ}{C : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ C →
  Σ ⊢ (A [ ｀ α ]ᵗ) ⇨ (A [ `★ ]ᵗ)
instUnseal {A = A} {α = α} h =
  instSubst⁻
    (singleTyEnv `★)
    (singleTyEnv (｀ α))
    (instVar⁺ h)
    (instVar⁻ h)
    A

instVar★⁺ :
  ∀ {Ψ}{Σ : Store Ψ}
    {α : Seal Ψ} →
  Σ ∋ˢ α ⦂ `★ →
  (X : TyVar (suc 0)) →
  Σ ⊢ singleTyEnv `★ X ⇨ singleTyEnv (｀ α) X
instVar★⁺ h Zᵗ = id ； (h ⁻)
instVar★⁺ h (Sᵗ ())

instVar★⁻ :
  ∀ {Ψ}{Σ : Store Ψ}
    {α : Seal Ψ} →
  Σ ∋ˢ α ⦂ `★ →
  (X : TyVar (suc 0)) →
  Σ ⊢ singleTyEnv (｀ α) X ⇨ singleTyEnv `★ X
instVar★⁻ h Zᵗ = id ； (h ⁺)
instVar★⁻ h (Sᵗ ())

instUnseal★ :
  ∀ {Ψ}{Σ : Store Ψ}
    {A : Ty (suc 0) Ψ}
    {α : Seal Ψ} →
  Σ ∋ˢ α ⦂ `★ →
  Σ ⊢ (A [ ｀ α ]ᵗ) ⇨ (A [ `★ ]ᵗ)
instUnseal★ {A = A} {α = α} h =
  instSubst⁻
    (singleTyEnv `★)
    (singleTyEnv (｀ α))
    (instVar★⁺ h)
    (instVar★⁻ h)
    A

top★-lookup :
  ∀ {Ψ}{Σ : Store Ψ} →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ∋ˢ Zˢ ⦂ `★
top★-lookup = Z∋ˢ refl refl

open𝒢 :
  ∀ {Ψ}{Σ : Store Ψ}
    {A : Ty (suc 0) Ψ}
    {B : Ty 0 Ψ} →
  (g : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ (⇑ˢ B) ⇨ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) →
  (α : Seal Ψ) →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ (⇑ˢ B) ⇨ ((⇑ˢ A) [ ｀ (Sˢ α) ]ᵗ)
open𝒢 {A = A} g α = g ⨟ swap
  where
    up :
      (X : TyVar (suc 0)) →
      ((Zˢ , ⇑ˢ `★) ∷ _) ⊢ singleTyEnv (｀ Zˢ) X ⇨ singleTyEnv (｀ (Sˢ α)) X
    up Zᵗ = (id ； ((｀ Zˢ) !)) ； ((｀ (Sˢ α)) `? zero)
    up (Sᵗ ())

    down :
      (X : TyVar (suc 0)) →
      ((Zˢ , ⇑ˢ `★) ∷ _) ⊢ singleTyEnv (｀ (Sˢ α)) X ⇨ singleTyEnv (｀ Zˢ) X
    down Zᵗ = (id ； ((｀ (Sˢ α)) !)) ； ((｀ Zˢ) `? zero)
    down (Sᵗ ())

    swap :
      ((Zˢ , ⇑ˢ `★) ∷ _) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⇨ ((⇑ˢ A) [ ｀ (Sˢ α) ]ᵗ)
    swap = instSubst⁺ (singleTyEnv (｀ Zˢ)) (singleTyEnv (｀ (Sˢ α))) up down (⇑ˢ A)

infix 2 _—→[_]_
data _—→[_]_ :
  ∀ {Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{A : Ty 0 Ψ} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
  (ρ : Renameˢ Ψ Ψ′) →
  0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A → Set where

  β :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {N : 0 ∣ Ψ ∣ Σ ∣ (B ∷ []) ⊢ A}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B} →
    Value V →
    (ƛ B ⇒ N) · V —→[ idˢ ] id-step-term (N [ V ])

  β-Λ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {V : (suc 0) ∣ Ψ ∣ Σ ∣ (⤊ᵗ []) ⊢ A}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((Λ V) ·α α [ h ]) refl —→[ idˢ ] id-step-term (V [ ｀ α ]ᵀ)

  β-⟨∀⟩ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B : Ty (suc 0) Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)}
      {c : Σ ⊢ A ⇨ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((V ⟨ id ； (∀ᶜ c) ⟩) ·α α [ h ]) refl
      —→[ idˢ ]
    id-step-term (((V ·α α [ h ]) refl) ⟨ c [ ｀ α ]ᶜᵗ ⟩)

  β-⟨𝒢⟩ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {B : Ty 0 Ψ}
      {g : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ (⇑ˢ B) ⇨ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((V ⟨ id ； (𝒢 {A = A} g) ⟩) ·α α [ h ]) refl
      —→[ Sˢ ]
    cast⊢
      refl
      refl
      (sym (renameˢ-[]ᵗ-seal Sˢ A α))
      ((wkΣ-term (drop ⊆ˢ-refl) (renameˢ-term Sˢ V)) ⟨ open𝒢 {A = A} g α ⟩)

  β-⟨↦⟩ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B C D : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {W : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ C}
      {c : Σ ⊢ C ⇨ A}
      {d : Σ ⊢ B ⇨ D} →
    (V ⟨ id ； (c ↦ d) ⟩) · W
      —→[ idˢ ]
    id-step-term ((V · (W ⟨ c ⟩)) ⟨ d ⟩)

  β-ν :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B : Ty 0 Ψ}
      {N : 0 ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ []) ⊢ (⇑ˢ B)} →
    (ν:= A ∙ N) —→[ Sˢ ] N

  ⟨id⟩ :
    ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    (V ⟨ id ⟩) —→[ idˢ ] id-step-term V

  ⟨⁻⟩⟨⁺⟩-★ :
    ∀ {Ψ}{Σ : Store Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ `★}
      {α}
      {h h′ : Σ ∋ˢ α ⦂ `★} →
    (V ⟨ id ； (h ⁻) ⟩ ⟨ id ； (h′ ⁺) ⟩)
      —→[ idˢ ]
    id-step-term V

  ⟨⁻⟩⟨⁺⟩ :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ wkTy0 A}
      {α}
      {h : Σ ∋ˢ α ⦂ A}
      {h′ : Σ ∋ˢ α ⦂ B}
      (uΣ : Uniqueˢ Σ) →
    (V ⟨ id ； (h ⁻) ⟩ ⟨ id ； (h′ ⁺) ⟩)
      —→[ idˢ ]
    id-step-term
      (subst
        (λ T → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ T)
        (cong wkTy0 (lookup-unique uΣ h h′))
        V)

  ⟨!⟩⟨?⟩ :
    ∀ {Ψ}{Σ : Store Ψ}{G : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ G}
      {g g′ : Ground G}{ℓ} →
    (V ⟨ id ； (g !) ⟩ ⟨ id ； (g′ `? ℓ) ⟩) —→[ idˢ ] id-step-term V

  ⟨!⟩⟨?⟩-bad :
    ∀ {Ψ}{Σ : Store Ψ}{G H : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ G}
      {g : Ground G}{h : Ground H}{ℓ} →
    G ≢ H →
    (V ⟨ id ； (g !) ⟩ ⟨ id ； (h `? ℓ) ⟩) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = H} (blame {A = H} ℓ)

  β-⟨；⟩ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B C D : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {c : Σ ⊢ A ⇨ B}
      {d : Σ ⊢ B ⇨ᵃ C}
      {e : Σ ⊢ C ⇨ᵃ D} →
    V ⟨ (c ； d) ； e ⟩ —→[ idˢ ] id-step-term ((V ⟨ c ； d ⟩) ⟨ id ； e ⟩)

  β-ℐ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {B : Ty 0 Ψ}
      {i : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⇨ (⇑ˢ B)}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)} →
    V ⟨ id ； (ℐ {A = A} i) ⟩ —→[ idˢ ]
    id-step-term
      (ν:= `★ ∙
        ((((wkΣ-term (drop ⊆ˢ-refl) (renameˢ-term Sˢ V))
            ·α Zˢ [ top★-lookup ]) refl)
          ⟨ i ⟩))

  β-⊥ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {ℓ : Label} →
    V ⟨ id ； (`⊥ {A = A} {B = B} ℓ) ⟩ —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  ξ-·₁ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A B : Ty 0 Ψ}
      {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (A ⇒ B)} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L · M) —→[ ρ ] (L′ · wkΣ-term wρ (renameˢ-term ρ M))

  ξ-·₂ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A B : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    Value V →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (V · M) —→[ ρ ] (wkΣ-term wρ (renameˢ-term ρ V) · M′)

  ξ-·α :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A : Ty (suc 0) Ψ}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (`∀ A)}
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
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A B : Ty 0 Ψ}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A}
      {c : Σ ⊢ A ⇨ B} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (M ⟨ c ⟩) —→[ ρ ] (M′ ⟨ wkΣᶜ wρ (renameᶜˢ ρ c) ⟩)

  ξ-⊕₁ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {L M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L ⊕[ op ] M) —→[ ρ ] (L′ ⊕[ op ] wkΣ-term wρ (renameˢ-term ρ M))

  ξ-⊕₂ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {L M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (L ⊕[ op ] M) —→[ ρ ] (wkΣ-term wρ (renameˢ-term ρ L) ⊕[ op ] M′)

  δ-⊕ :
    ∀ {Ψ}{Σ : Store Ψ}
      {m n : ℕ} →
    ($ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ m) refl
      ⊕[ addℕ ]
      $ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ n) refl)
      —→[ idˢ ]
    id-step-term ($ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ (m + n)) refl)

  blame-·₁ :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {ℓ : Label}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    (blame {A = A ⇒ B} ℓ · M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  blame-·₂ :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {ℓ : Label}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)} →
    Value V →
    (V · blame {A = A} ℓ) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  blame-·α :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {ℓ : Label}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (_·α_[_]
      {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []}
      {A = A} {C = C}
      (blame {A = `∀ A} ℓ) α h refl)
      —→[ idˢ ]
    id-step-term
      {Σ = Σ}
      {Γ = []}
      {A = A [ ｀ α ]ᵗ}
      (blame {A = A [ ｀ α ]ᵗ} ℓ)

  blame-⟨⟩ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B : Ty 0 Ψ}
      {ℓ : Label}
      {c : Σ ⊢ A ⇨ B} →
    (_⟨_⟩
      {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []}
      {A = A} {B = B}
      (blame {A = A} ℓ) c)
      —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  blame-⊕₁ :
    ∀ {Ψ}{Σ : Store Ψ}
      {ℓ : Label}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    (blame {A = ‵ `ℕ} ℓ ⊕[ op ] M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = ‵ `ℕ} (blame {A = ‵ `ℕ} ℓ)

  blame-⊕₂ :
    ∀ {Ψ}{Σ : Store Ψ}
      {ℓ : Label}
      {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (L ⊕[ op ] blame {A = ‵ `ℕ} ℓ) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = ‵ `ℕ} (blame {A = ‵ `ℕ} ℓ)

------------------------------------------------------------------------
-- Store growth witness extracted from one step
------------------------------------------------------------------------

store-growth :
  ∀ {Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{A : Ty 0 Ψ}
    {ρ : Renameˢ Ψ Ψ′}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
  M —→[ ρ ] M′ →
  renameStoreˢ ρ Σ ⊆ˢ Σ′
store-growth (β v) = idˢ-⊆ˢ
store-growth (β-Λ) = idˢ-⊆ˢ
store-growth (β-⟨∀⟩) = idˢ-⊆ˢ
store-growth (β-⟨𝒢⟩) = drop ⊆ˢ-refl
store-growth (β-⟨↦⟩) = idˢ-⊆ˢ
store-growth β-ν = drop ⊆ˢ-refl
store-growth ⟨id⟩ = idˢ-⊆ˢ
store-growth ⟨⁻⟩⟨⁺⟩-★ = idˢ-⊆ˢ
store-growth (⟨⁻⟩⟨⁺⟩ uΣ) = idˢ-⊆ˢ
store-growth ⟨!⟩⟨?⟩ = idˢ-⊆ˢ
store-growth (⟨!⟩⟨?⟩-bad neq) = idˢ-⊆ˢ
store-growth β-⟨；⟩ = idˢ-⊆ˢ
store-growth β-ℐ = idˢ-⊆ˢ
store-growth β-⊥ = idˢ-⊆ˢ
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

unique-store-step :
  ∀ {Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{A : Ty 0 Ψ}
    {ρ : Renameˢ Ψ Ψ′}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
  Uniqueˢ Σ →
  M —→[ ρ ] M′ →
  Uniqueˢ Σ′
unique-store-step uΣ (β v) = uΣ
unique-store-step uΣ β-Λ = uΣ
unique-store-step uΣ β-⟨∀⟩ = uΣ
unique-store-step uΣ β-⟨𝒢⟩ = unique-ν `★ uΣ
unique-store-step uΣ β-⟨↦⟩ = uΣ
unique-store-step uΣ (β-ν {A = A}) = unique-ν A uΣ
unique-store-step uΣ ⟨id⟩ = uΣ
unique-store-step uΣ ⟨⁻⟩⟨⁺⟩-★ = uΣ
unique-store-step uΣ (⟨⁻⟩⟨⁺⟩ uΣ′) = uΣ
unique-store-step uΣ ⟨!⟩⟨?⟩ = uΣ
unique-store-step uΣ (⟨!⟩⟨?⟩-bad neq) = uΣ
unique-store-step uΣ β-⟨；⟩ = uΣ
unique-store-step uΣ β-ℐ = uΣ
unique-store-step uΣ β-⊥ = uΣ
unique-store-step uΣ (ξ-·₁ wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-·₂ v wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-·α wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-⟨⟩ wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-⊕₁ wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-⊕₂ v wρ red) = unique-store-step uΣ red
unique-store-step uΣ δ-⊕ = uΣ
unique-store-step uΣ blame-·₁ = uΣ
unique-store-step uΣ (blame-·₂ v) = uΣ
unique-store-step uΣ blame-·α = uΣ
unique-store-step uΣ blame-⟨⟩ = uΣ
unique-store-step uΣ blame-⊕₁ = uΣ
unique-store-step uΣ (blame-⊕₂ v) = uΣ

------------------------------------------------------------------------
-- Multi-step reduction on intrinsic closed terms
------------------------------------------------------------------------

infix 2 _—↠_
infix 3 _∎
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
data _—↠_ :
  ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ} →
  (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  ∀ {Ψ′}{Σ′ : Store Ψ′}{A′ : Ty 0 Ψ′} →
  (N : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ A′) →
  Set where
  _∎ :
    ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
      (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
    M —↠ M

  _—→⟨_⟩_ :
    ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
      (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A)
      {Ψ′}{Σ′ : Store Ψ′}
      {ρ : Renameˢ Ψ Ψ′}
      {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A}
      {Ψ″}{Σ″ : Store Ψ″}
      {B : Ty 0 Ψ″}
      {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ B} →
    L —→[ ρ ] M →
    M —↠ N →
    L —↠ N

multi-trans :
  ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
    {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {Ψ′}{Σ′ : Store Ψ′}
    {B : Ty 0 Ψ′}
    {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ B}
    {Ψ″}{Σ″ : Store Ψ″}
    {C : Ty 0 Ψ″}
    {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ C} →
  L —↠ M →
  M —↠ N →
  L —↠ N
multi-trans (_ ∎) M—↠N = M—↠N
multi-trans (_ —→⟨ L—→M ⟩ M—↠N) N—↠P = _ —→⟨ L—→M ⟩ multi-trans M—↠N N—↠P

_—↠⟨_⟩_ :
  ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
    (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A)
    {Ψ′}{Σ′ : Store Ψ′}
    {B : Ty 0 Ψ′}
    {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ B}
    {Ψ″}{Σ″ : Store Ψ″}
    {C : Ty 0 Ψ″}
    {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ C}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N
