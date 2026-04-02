module Terms where

-- File Charter:
--   * Intrinsically typed term syntax for PolyUpDown.
--   * Core term constructors and structural actions on terms
--     (type-variable renaming/substitution and seal renaming).
--   * Terms cast through `_at[_]_`, carrying direction (`up`/`down`) and
--     widening/narrowing witnesses in the `every/every` fragment used by the
--     internal language.
-- Note to self:
--   * Keep reduction and metatheory in separate modules; this file should stay
--     focused on syntax and structural actions on syntax.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; here; there)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import Types
open import TypeProperties
open import Ctx
  using
    ( renameLookup
    ; substLookup
    ; map-substᵗ-⤊ᵗ
    ; map-substᵗ-⤊ˢ
    ; map-renameᵗ-⤊ᵗ
    ; map-renameᵗ-⤊ˢ
    ; map-renameˢ-⤊ᵗ
    ; map-renameˢ-⤊ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-ctx )
open import Store
  using
    ( _⊆ˢ_
    ; ⊆ˢ-refl
    ; done
    ; keep
    ; drop
    ; wkLookupˢ
    ; ν-⊆ˢ
    ; substStoreᵗ
    ; renameStoreᵗ-ext-⟰ᵗ
    ; substStoreᵗ-ext-⟰ᵗ
    ; renameStoreˢ-ext-⟰ᵗ
    ; renameStoreᵗ-cons-⟰ˢ
    ; substStoreᵗ-cons-⟰ˢ
    ; renameStoreˢ-cons-⟰ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-store
    ; substLookupᵗ to substLookupᵗ-store
    )
open import UpDown

------------------------------------------------------------------------
-- Constants, primitive operators, and permission environments
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : ∀{Δ}{Ψ} → Const → Ty Δ Ψ
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : ∀{Δ}{Ψ} → Prim → Ty Δ Ψ
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

every : (Ψ : SealCtx) → Vec Bool Ψ
every zero = []
every (suc Ψ) = true ∷ every Ψ

none : (Ψ : SealCtx) → Vec Bool Ψ
none zero = []
none (suc Ψ) = false ∷ none Ψ

every-member : ∀{Ψ} (α : Seal Ψ) → ⌊ α ⌋ ∈ every Ψ
every-member Zˢ = here
every-member (Sˢ α) = there (every-member α)

none-excluded : ∀{Ψ} (α : Seal Ψ) → ⌊ α ⌋ ∉ none Ψ
none-excluded Zˢ ()
none-excluded (Sˢ α) (there p) = none-excluded α p

RenOk-every :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenOk ρ (every Ψ) (every Ψ′)
RenOk-every ρ {α} _ = every-member (ρ α)

RenOk-none :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenOk ρ (none Ψ) (none Ψ′)
RenOk-none ρ {α} p = ⊥-elim (none-excluded α p)

RenOk-any-every :
  ∀{Ψ}{Ψ′}{P : Vec Bool Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenOk ρ P (every Ψ′)
RenOk-any-every ρ {α} _ = every-member (ρ α)

------------------------------------------------------------------------
-- Intrinsic terms
------------------------------------------------------------------------

⤊ᵗ : ∀{Δ}{Ψ} → Ctx Δ Ψ → Ctx (suc Δ) Ψ
⤊ᵗ Γ = map (renameᵗ Sᵗ) Γ

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _•_[_]
infix  5 ν:=_∙_
infixl 6 _⊕[_]_
infix  8 _at[_]_
infix  9 `_
infix  4 _∣_∣_∣_⊢_

data Direction : Set where
  up down : Direction

Cast :
  ∀{Δ}{Ψ} →
  Direction →
  Store Δ Ψ →
  Ty Δ Ψ →
  Ty Δ Ψ →
  Set
Cast {Ψ = Ψ} up Σ A B = Σ ∣ every Ψ ∣ every Ψ ⊢ A ⊑ B
Cast {Ψ = Ψ} down Σ A B = Σ ∣ every Ψ ∣ every Ψ ⊢ A ⊒ B

data _∣_∣_∣_⊢_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Δ Ψ) (Γ : Ctx Δ Ψ) : Ty Δ Ψ → Set where
  `_        : ∀{A : Ty Δ Ψ}{x : Var} →
              Γ ∋ x ⦂ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

  ƛ_⇒_      : ∀{B : Ty Δ Ψ} →
              (A : Ty Δ Ψ) →
              Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)

  _·_       : ∀{A B : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  Λ_        : ∀{A : Ty (suc Δ) Ψ} →
              (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)

  _•_[_]    : ∀{A : Ty (suc Δ) Ψ}{B}{C : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A) →
              (α : Seal Ψ) →
              Σ ∋ˢ α ⦂ C →
              B ≡ (A [ ｀ α ]ᵗ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  ν:=_∙_    : ∀{B : Ty Δ Ψ} →
              (A : Ty Δ Ψ) →
              Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  $         : ∀ {A}
              (κ : Const) →
              constTy κ ≡ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

  _⊕[_]_    :
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              (op : Prim) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)

  at        : ∀{A B : Ty Δ Ψ} →
              {C D : Ty Δ Ψ} →
              (M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ C) →
              (d : Direction) →
              (p : Cast d Σ A B) →
              C ≡ A →
              D ≡ B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ D

  blame     : ∀{A : Ty Δ Ψ} →
              Label →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

pattern _at[_]_ M d p = at M d p refl refl

------------------------------------------------------------------------
-- Instantiation shorthand
------------------------------------------------------------------------

cast⊢ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Δ Ψ}{Γ Γ′ : Ctx Δ Ψ}{A A′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Γ ≡ Γ′ →
  A ≡ A′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ′ ⊢ A′
cast⊢ refl refl refl M = M

mutual
  instSubst⊑ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Δ′ Ψ} →
    (σ τ : Substᵗ Δ Δ′ Ψ) →
    ((X : TyVar Δ) → Σ ∣ every Ψ ∣ every Ψ ⊢ σ X ⊑ τ X) →
    ((X : TyVar Δ) → Σ ∣ every Ψ ∣ every Ψ ⊢ τ X ⊒ σ X) →
    (A : Ty Δ Ψ) →
    Σ ∣ every Ψ ∣ every Ψ ⊢ substᵗ σ A ⊑ substᵗ τ A
  instSubst⊑ {Ψ = Ψ} {Σ = Σ} =
    λ σ τ var⊑ var⊒ → go σ τ var⊑ var⊒
    where
      go :
        ∀ {Δ}{Δ′}{Σ′ : Store Δ′ Ψ} →
        (σ τ : Substᵗ Δ Δ′ Ψ) →
        ((X : TyVar Δ) → Σ′ ∣ every Ψ ∣ every Ψ ⊢ σ X ⊑ τ X) →
        ((X : TyVar Δ) → Σ′ ∣ every Ψ ∣ every Ψ ⊢ τ X ⊒ σ X) →
        (A : Ty Δ Ψ) →
        Σ′ ∣ every Ψ ∣ every Ψ ⊢ substᵗ σ A ⊑ substᵗ τ A
      go σ τ var⊑ var⊒ (＇ X) = var⊑ X
      go σ τ var⊑ var⊒ (｀ α) = id
      go σ τ var⊑ var⊒ (‵ ι) = id
      go σ τ var⊑ var⊒ ★ = id
      go σ τ var⊑ var⊒ (A ⇒ B) = instSubst⊒ σ τ var⊑ var⊒ A ↦ go σ τ var⊑ var⊒ B
      go {Σ′ = Σ′} σ τ var⊑ var⊒ (`∀ A) = ∀ᵖ (go (extsᵗ σ) (extsᵗ τ) var⊑′ var⊒′ A)
        where
          var⊑′ :
            (X : TyVar (suc _)) →
            ⟰ᵗ Σ′ ∣ every Ψ ∣ every Ψ ⊢ extsᵗ σ X ⊑ extsᵗ τ X
          var⊑′ Zᵗ = id
          var⊑′ (Sᵗ X) = ⊑-renameᵗ Sᵗ (var⊑ X)

          var⊒′ :
            (X : TyVar (suc _)) →
            ⟰ᵗ Σ′ ∣ every Ψ ∣ every Ψ ⊢ extsᵗ τ X ⊒ extsᵗ σ X
          var⊒′ Zᵗ = id
          var⊒′ (Sᵗ X) = ⊒-renameᵗ Sᵗ (var⊒ X)

  instSubst⊒ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Δ′ Ψ} →
    (σ τ : Substᵗ Δ Δ′ Ψ) →
    ((X : TyVar Δ) → Σ ∣ every Ψ ∣ every Ψ ⊢ σ X ⊑ τ X) →
    ((X : TyVar Δ) → Σ ∣ every Ψ ∣ every Ψ ⊢ τ X ⊒ σ X) →
    (A : Ty Δ Ψ) →
    Σ ∣ every Ψ ∣ every Ψ ⊢ substᵗ τ A ⊒ substᵗ σ A
  instSubst⊒ {Ψ = Ψ} {Σ = Σ} =
    λ σ τ var⊑ var⊒ → go σ τ var⊑ var⊒
    where
      go :
        ∀ {Δ}{Δ′}{Σ′ : Store Δ′ Ψ} →
        (σ τ : Substᵗ Δ Δ′ Ψ) →
        ((X : TyVar Δ) → Σ′ ∣ every Ψ ∣ every Ψ ⊢ σ X ⊑ τ X) →
        ((X : TyVar Δ) → Σ′ ∣ every Ψ ∣ every Ψ ⊢ τ X ⊒ σ X) →
        (A : Ty Δ Ψ) →
        Σ′ ∣ every Ψ ∣ every Ψ ⊢ substᵗ τ A ⊒ substᵗ σ A
      go σ τ var⊑ var⊒ (＇ X) = var⊒ X
      go σ τ var⊑ var⊒ (｀ α) = id
      go σ τ var⊑ var⊒ (‵ ι) = id
      go σ τ var⊑ var⊒ ★ = id
      go σ τ var⊑ var⊒ (A ⇒ B) = instSubst⊑ σ τ var⊑ var⊒ A ↦ go σ τ var⊑ var⊒ B
      go {Σ′ = Σ′} σ τ var⊑ var⊒ (`∀ A) = ∀ᵖ (go (extsᵗ σ) (extsᵗ τ) var⊑′ var⊒′ A)
        where
          var⊑′ :
            (X : TyVar (suc _)) →
            ⟰ᵗ Σ′ ∣ every Ψ ∣ every Ψ ⊢ extsᵗ σ X ⊑ extsᵗ τ X
          var⊑′ Zᵗ = id
          var⊑′ (Sᵗ X) = ⊑-renameᵗ Sᵗ (var⊑ X)

          var⊒′ :
            (X : TyVar (suc _)) →
            ⟰ᵗ Σ′ ∣ every Ψ ∣ every Ψ ⊢ extsᵗ τ X ⊒ extsᵗ σ X
          var⊒′ Zᵗ = id
          var⊒′ (Sᵗ X) = ⊒-renameᵗ Sᵗ (var⊒ X)

instVar⊑ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{A : Ty Δ Ψ}{α : Seal Ψ} →
  (h : Σ ∋ˢ α ⦂ A) →
  (X : TyVar (suc Δ)) →
  Σ ∣ every Ψ ∣ every Ψ ⊢ singleTyEnv (｀ α) X ⊑ singleTyEnv A X
instVar⊑ {α = α} h Zᵗ = unseal h (every-member α)
instVar⊑ h (Sᵗ X) = id

instVar⊒ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{A : Ty Δ Ψ}{α : Seal Ψ} →
  (h : Σ ∋ˢ α ⦂ A) →
  (X : TyVar (suc Δ)) →
  Σ ∣ every Ψ ∣ every Ψ ⊢ singleTyEnv A X ⊒ singleTyEnv (｀ α) X
instVar⊒ {α = α} h Zᵗ = seal h (every-member α)
instVar⊒ h (Sᵗ X) = id

instCast⊑ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{A : Ty Δ Ψ}{B : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  (h : Σ ∋ˢ α ⦂ A) →
  Σ ∣ every Ψ ∣ every Ψ ⊢ B [ ｀ α ]ᵗ ⊑ B [ A ]ᵗ
instCast⊑ {A = A} {B = B} {α = α} h =
  instSubst⊑
    (singleTyEnv (｀ α))
    (singleTyEnv A)
    (instVar⊑ h)
    (instVar⊒ h)
    B

instCast⊒ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{A : Ty Δ Ψ}{B : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  (h : Σ ∋ˢ α ⦂ A) →
  Σ ∣ every Ψ ∣ every Ψ ⊢ B [ A ]ᵗ ⊒ B [ ｀ α ]ᵗ
instCast⊒ {A = A} {B = B} {α = α} h =
  instSubst⊒
    (singleTyEnv (｀ α))
    (singleTyEnv A)
    (instVar⊑ h)
    (instVar⊒ h)
    B

inst-⟰ᵗ-⊆ˢ :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Δ Ψ} →
  Σ ⊆ˢ Σ′ →
  ⟰ᵗ Σ ⊆ˢ ⟰ᵗ Σ′
inst-⟰ᵗ-⊆ˢ done = done
inst-⟰ᵗ-⊆ˢ (keep {α = α} {A = A} w) =
  keep {α = α} {A = renameᵗ Sᵗ A} (inst-⟰ᵗ-⊆ˢ w)
inst-⟰ᵗ-⊆ˢ (drop {α = α} {A = A} w) =
  drop {α = α} {A = renameᵗ Sᵗ A} (inst-⟰ᵗ-⊆ˢ w)

mutual
  wk⊑′ :
    ∀ {Δ}{Ψ}{Σ Σ′ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B →
    Σ′ ∣ Φ ∣ Ξ ⊢ A ⊑ B
  wk⊑′ w (tag g gok) = tag g gok
  wk⊑′ w (unseal h α∈Φ) = unseal (wkLookupˢ w h) α∈Φ
  wk⊑′ w (p ↦ q) = wk⊒′ w p ↦ wk⊑′ w q
  wk⊑′ w (∀ᵖ p) = ∀ᵖ (wk⊑′ (inst-⟰ᵗ-⊆ˢ w) p)
  wk⊑′ w (ν i) = ν (wk⊑′ (ν-⊆ˢ ★ w) i)
  wk⊑′ w id = id
  wk⊑′ w (p ； q) = wk⊑′ w p ； wk⊑′ w q

  wk⊒′ :
    ∀ {Δ}{Ψ}{Σ Σ′ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B →
    Σ′ ∣ Φ ∣ Ξ ⊢ A ⊒ B
  wk⊒′ w (untag g gok ℓ) = untag g gok ℓ
  wk⊒′ w (seal h α∈Φ) = seal (wkLookupˢ w h) α∈Φ
  wk⊒′ w (p ↦ q) = wk⊑′ w p ↦ wk⊒′ w q
  wk⊒′ w (∀ᵖ p) = ∀ᵖ (wk⊒′ (inst-⟰ᵗ-⊆ˢ w) p)
  wk⊒′ w (ν i) = ν (wk⊒′ (ν-⊆ˢ ★ w) i)
  wk⊒′ w id = id
  wk⊒′ w (p ； q) = wk⊒′ w p ； wk⊒′ w q

wkCast-every :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Δ Ψ}{A B : Ty Δ Ψ} →
  (d : Direction) →
  Σ ⊆ˢ Σ′ →
  Cast d Σ A B →
  Cast d Σ′ A B
wkCast-every up w p = wk⊑′ w p
wkCast-every down w p = wk⊒′ w p

wkΣ-term-every :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Σ ⊆ˢ Σ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ ⊢ A
wkΣ-term-every w (` h) = ` h
wkΣ-term-every w (ƛ A ⇒ M) = ƛ A ⇒ wkΣ-term-every w M
wkΣ-term-every w (L · M) = wkΣ-term-every w L · wkΣ-term-every w M
wkΣ-term-every w (Λ M) = Λ (wkΣ-term-every (inst-⟰ᵗ-⊆ˢ w) M)
wkΣ-term-every w ((M • α [ h ]) eq) =
  cast⊢
    refl
    refl
    (sym eq)
    ((wkΣ-term-every w M • α [ wkLookupˢ w h ]) refl)
wkΣ-term-every w (ν:= A ∙ M) = ν:= A ∙ wkΣ-term-every (ν-⊆ˢ A w) M
wkΣ-term-every w ($ κ eq) = $ κ eq
wkΣ-term-every w (L ⊕[ op ] M) = wkΣ-term-every w L ⊕[ op ] wkΣ-term-every w M
wkΣ-term-every w (M at[ d ] p) = wkΣ-term-every w M at[ d ] wkCast-every d w p
wkΣ-term-every w (blame ℓ) = blame ℓ

inst-top-lookup :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{A : Ty Δ Ψ} →
  ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∋ˢ Zˢ ⦂ ⇑ˢ A
inst-top-lookup = Z∋ˢ refl refl

inst-⇑ˢ :
  ∀ {Δ}{Ψ} →
  (A : Ty Δ Ψ) →
  (B : Ty (suc Δ) Ψ) →
  (⇑ˢ B) [ ⇑ˢ A ]ᵗ ≡ ⇑ˢ (B [ A ]ᵗ)
inst-⇑ˢ A B =
  trans
    (substᵗ-cong env (⇑ˢ B))
    (substᵗ-⇑ˢ (singleTyEnv A) B)
  where
    env :
      (X : TyVar (suc _)) →
      singleTyEnv (⇑ˢ A) X ≡ liftSubstˢ (singleTyEnv A) X
    env Zᵗ = refl
    env (Sᵗ X) = refl

------------------------------------------------------------------------
-- Structural actions on terms
------------------------------------------------------------------------

renameᵗ-constTy :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (κ : Const) →
  renameᵗ ρ (constTy {Δ}{Ψ} κ) ≡ constTy κ
renameᵗ-constTy ρ (κℕ n) = refl

substᵗ-constTy :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (κ : Const) →
  substᵗ σ (constTy {Δ}{Ψ} κ) ≡ constTy κ
substᵗ-constTy σ (κℕ n) = refl

renameˢ-constTy :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (κ : Const) →
  renameˢ ρ (constTy {Δ}{Ψ} κ) ≡ constTy κ
renameˢ-constTy ρ (κℕ n) = refl

renameCastᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{A B}
  (d : Direction) (ρ : Renameᵗ Δ Δ′) →
  Cast d Σ A B →
  Cast d (renameStoreᵗ ρ Σ) (renameᵗ ρ A) (renameᵗ ρ B)
renameCastᵗ up ρ p = ⊑-renameᵗ ρ p
renameCastᵗ down ρ p = ⊒-renameᵗ ρ p

substCastᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{A B}
  (d : Direction) (σ : Substᵗ Δ Δ′ Ψ) →
  Cast d Σ A B →
  Cast d (substStoreᵗ σ Σ) (substᵗ σ A) (substᵗ σ B)
substCastᵗ up σ p = ⊑-substᵗ σ p
substCastᵗ down σ p = ⊒-substᵗ σ p

renameCastˢ :
  ∀{Δ}{Ψ}{Ψ′}{Σ : Store Δ Ψ}{A B}
  (d : Direction) (ρ : Renameˢ Ψ Ψ′) →
  Cast d Σ A B →
  Cast d (renameStoreˢ ρ Σ) (renameˢ ρ A) (renameˢ ρ B)
renameCastˢ up ρ p = ⊑-renameˢ ρ (RenOk-every ρ) (RenOk-every ρ) p
renameCastˢ down ρ p = ⊒-renameˢ ρ (RenOk-every ρ) (RenOk-every ρ) p

renameᵗ-term :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ′ ∣ Ψ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ ⊢ renameᵗ ρ A
renameᵗ-term ρ (` h) = ` (renameLookupᵗ-ctx ρ h)
renameᵗ-term ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗ-term ρ M
renameᵗ-term ρ (L · M) = renameᵗ-term ρ L · renameᵗ-term ρ M
renameᵗ-term {Σ = Σ} {Γ = Γ} ρ (Λ_ {A = A} M) =
  Λ (cast⊢
       (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
       (map-renameᵗ-⤊ᵗ ρ Γ)
       refl
       (renameᵗ-term (extᵗ ρ) M))
renameᵗ-term ρ (_•_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameᵗ-[]ᵗ-seal ρ A α))
      (cong (renameᵗ ρ) (sym eq)))
    ((renameᵗ-term ρ M • α [ renameLookupᵗ-store ρ h ]) refl)
renameᵗ-term {Σ = Σ} {Γ = Γ} ρ (ν:=_∙_ {B = B} A M) =
  ν:= renameᵗ ρ A ∙
    cast⊢
      (renameStoreᵗ-cons-⟰ˢ ρ A Σ)
      (map-renameᵗ-⤊ˢ ρ Γ)
      (renameᵗ-⇑ˢ ρ B)
      (renameᵗ-term ρ M)
renameᵗ-term ρ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameᵗ-constTy ρ κ))
      (cong (renameᵗ ρ) eq))
    ($ κ refl)
renameᵗ-term ρ (L ⊕[ op ] M) = renameᵗ-term ρ L ⊕[ op ] renameᵗ-term ρ M
renameᵗ-term ρ (M at[ d ] p) = renameᵗ-term ρ M at[ d ] renameCastᵗ d ρ p
renameᵗ-term ρ (blame ℓ) = blame ℓ

substᵗ-term :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (σ : Substᵗ Δ Δ′ Ψ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ∣ map (substᵗ σ) Γ ⊢ substᵗ σ A
substᵗ-term σ (` h) = ` (substLookup σ h)
substᵗ-term σ (ƛ A ⇒ M) = ƛ substᵗ σ A ⇒ substᵗ-term σ M
substᵗ-term σ (L · M) = substᵗ-term σ L · substᵗ-term σ M
substᵗ-term {Σ = Σ} {Γ = Γ} σ (Λ_ {A = A} M) =
  Λ (cast⊢
       (substStoreᵗ-ext-⟰ᵗ σ Σ)
       (map-substᵗ-⤊ᵗ σ Γ)
       refl
       (substᵗ-term (extsᵗ σ) M))
substᵗ-term σ (_•_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (substᵗ-[]ᵗ-seal σ A α))
      (cong (substᵗ σ) (sym eq)))
    ((substᵗ-term σ M • α [ substLookupᵗ-store σ h ]) refl)
substᵗ-term {Σ = Σ} {Γ = Γ} σ (ν:=_∙_ {B = B} A M) =
  ν:= substᵗ σ A ∙
    cast⊢
      (substStoreᵗ-cons-⟰ˢ σ A Σ)
      (map-substᵗ-⤊ˢ σ Γ)
      (substᵗ-⇑ˢ σ B)
      (substᵗ-term (liftSubstˢ σ) M)
substᵗ-term σ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (substᵗ-constTy σ κ))
      (cong (substᵗ σ) eq))
    ($ κ refl)
substᵗ-term σ (L ⊕[ op ] M) = substᵗ-term σ L ⊕[ op ] substᵗ-term σ M
substᵗ-term σ (M at[ d ] p) = substᵗ-term σ M at[ d ] substCastᵗ d σ p
substᵗ-term σ (blame ℓ) = blame ℓ

renameˢ-term :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A
renameˢ-term ρ (` h) = ` (renameLookup ρ h)
renameˢ-term ρ (ƛ A ⇒ M) = ƛ renameˢ ρ A ⇒ renameˢ-term ρ M
renameˢ-term ρ (L · M) = renameˢ-term ρ L · renameˢ-term ρ M
renameˢ-term {Σ = Σ} {Γ = Γ} ρ (Λ_ {A = A} M) =
  Λ (cast⊢
       (renameStoreˢ-ext-⟰ᵗ ρ Σ)
       (map-renameˢ-⤊ᵗ ρ Γ)
       refl
       (renameˢ-term ρ M))
renameˢ-term ρ (_•_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameˢ-[]ᵗ-seal ρ A α))
      (cong (renameˢ ρ) (sym eq)))
    ((renameˢ-term ρ M • (ρ α) [ renameLookupˢ ρ h ]) refl)
renameˢ-term {Σ = Σ} {Γ = Γ} ρ (ν:=_∙_ {B = B} A M) =
  ν:= renameˢ ρ A ∙
    cast⊢
      (renameStoreˢ-cons-⟰ˢ ρ A Σ)
      (map-renameˢ-⤊ˢ ρ Γ)
      (renameˢ-ext-⇑ˢ ρ B)
      (renameˢ-term (extˢ ρ) M)
renameˢ-term ρ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameˢ-constTy ρ κ))
      (cong (renameˢ ρ) eq))
    ($ κ refl)
renameˢ-term ρ (L ⊕[ op ] M) = renameˢ-term ρ L ⊕[ op ] renameˢ-term ρ M
renameˢ-term ρ (M at[ d ] p) = renameˢ-term ρ M at[ d ] renameCastˢ d ρ p
renameˢ-term ρ (blame ℓ) = blame ℓ

infix 8 ⇑ˢᵐ_
⇑ˢᵐ_ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ (suc Ψ) ∣ (⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ A)
⇑ˢᵐ M = renameˢ-term Sˢ M

inst :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {A : Ty Δ Ψ}{B : Ty (suc Δ) Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ `∀ B →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B [ A ]ᵗ
inst {Σ = Σ} {Γ = Γ} {A = A} {B = B} L =
  ν:= A ∙
    cast⊢
      refl
      refl
      (inst-⇑ˢ A B)
      ((((wkΣ-term-every (drop ⊆ˢ-refl) (⇑ˢᵐ L))
          • Zˢ [ inst-top-lookup ]) refl)
        at[ up ] (instCast⊑ {A = ⇑ˢ A} {B = ⇑ˢ B} inst-top-lookup))
