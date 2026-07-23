module ConsistencyProperties where

-- File Charter:
--   * GTSF-specific metatheory for consistency and its interaction with stores.
--   * No generic `Ty` substitution algebra and no standalone precision-transport layer;
--     reuse `TypeSubst` and `TypePrecisionProperties` for those.
--   * This is the home for properties that fundamentally combine consistency with GTSF
--     sealing/store invariants.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _<_; suc; zero)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (sym; subst; trans; cong; cong₂)

open import Types
open import Consistency
open import TypePrecision
open import TypePrecisionProperties
open import TypeSubst
  using
    ( renameLookupˢ
    ; renameˢ-ground
    ; renameˢ-substᵗ
    ; renameˢ-ext-⇑ˢ
    ; renameˢ-[]ᵗ-seal
    ; substᵗ-cong
    ; substᵗ-ground
    ; substᵗ-wkTy0
    ; substᵗ-⇑ˢ
    ; renameᵗ-⇑ˢ
    ; liftSubstˢ
    ; exts-liftSubstˢ
    ; renameˢ-single-⇑ˢ-id
    )
open import PolyCast using (substᵗ-[]ᵗ-seal)
open import Store
  using
    ( Uniqueˢ
    ; unique-ν
    ; lookup-unique
    ; lookup-Sˢ-⟰ˢ-eq
    ; renameStoreˢ-single-⟰ˢ
    ; _⊆ˢ_
    ; ⊆ˢ-refl
    ; drop
    ; wkLookupˢ
    ; ν-⊆ˢ
    ; Zˢ∉dom-⟰ˢ
    )

------------------------------------------------------------------------
-- No free type variables (de Bruijn-depth aware)
------------------------------------------------------------------------

tyVar→ℕ : ∀{Δ} → TyVar Δ → ℕ
tyVar→ℕ Zᵗ = zero
tyVar→ℕ (Sᵗ X) = suc (tyVar→ℕ X)

data NoFreeXᵈ : ∀{Δ}{Ψ} → ℕ → Ty Δ Ψ → Set where
  nx-var :
    ∀{Δ}{Ψ}{d}{X : TyVar Δ} →
    tyVar→ℕ X < d →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (＇ X)

  nx-seal :
    ∀{Δ}{Ψ}{d}{α : Seal Ψ} →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (｀ α)

  nx-base :
    ∀{Δ}{Ψ}{d}{ι : Base} →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (‵ ι)

  nx-star :
    ∀{Δ}{Ψ}{d} →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d `★

  nx-arr :
    ∀{Δ}{Ψ}{d}{A B : Ty Δ Ψ} →
    NoFreeXᵈ d A →
    NoFreeXᵈ d B →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (A ⇒ B)

  nx-all :
    ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ} →
    NoFreeXᵈ {Δ = suc Δ} {Ψ = Ψ} (suc d) A →
    NoFreeXᵈ {Δ = Δ} {Ψ = Ψ} d (`∀ A)

NoFreeX : ∀{Δ}{Ψ} → Ty Δ Ψ → Set
NoFreeX = NoFreeXᵈ 0

varTy : ∀{Δ}{Ψ} → TyVar Δ → Ty Δ Ψ
varTy X = ＇ X

data SealsAt★ : ∀{Δ}{Ψ} → Store Ψ → Ty Δ Ψ → Set where
  sX :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{X : TyVar Δ} →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (＇ X)

  sα :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ} →
    Σ ∋ˢ α ⦂ `★ →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (｀ α)

  s-base :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{ι : Base} →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (‵ ι)

  s-star :
    ∀{Δ}{Ψ}{Σ : Store Ψ} →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ `★

  s-arr :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    SealsAt★ Σ A →
    SealsAt★ Σ B →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (A ⇒ B)

  s-all :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ} →
    SealsAt★ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) →
    SealsAt★ {Δ = Δ} {Ψ = Ψ} Σ (`∀ A)

≤-raise :
  ∀{m n} →
  m ≤ n →
  m ≤ suc n
≤-raise z≤n = z≤n
≤-raise (s≤s p) = s≤s (≤-raise p)

<-zero-impossible : ∀{Δ}{X : TyVar Δ} → tyVar→ℕ X < zero → ⊥
<-zero-impossible ()

<-raise :
  ∀{Δ}{d}{X : TyVar Δ} →
  tyVar→ℕ X < d →
  tyVar→ℕ X < suc d
<-raise = ≤-raise

NoFreeXᵈ-raise :
  ∀{Δ}{Ψ}{d}{A : Ty Δ Ψ} →
  NoFreeXᵈ d A →
  NoFreeXᵈ (suc d) A
NoFreeXᵈ-raise (nx-var p) = nx-var (<-raise p)
NoFreeXᵈ-raise nx-seal = nx-seal
NoFreeXᵈ-raise nx-base = nx-base
NoFreeXᵈ-raise nx-star = nx-star
NoFreeXᵈ-raise (nx-arr nxA nxB) =
  nx-arr (NoFreeXᵈ-raise nxA) (NoFreeXᵈ-raise nxB)
NoFreeXᵈ-raise (nx-all nxA) =
  nx-all (NoFreeXᵈ-raise nxA)

RenPres :
  ∀{Δ}{Δ′} →
  ℕ →
  ℕ →
  Renameᵗ Δ Δ′ →
  Set
RenPres d d′ ρ = ∀{X} → tyVar→ℕ X < d → tyVar→ℕ (ρ X) < d′

RenPresInv :
  ∀{Δ}{Δ′} →
  ℕ →
  ℕ →
  Renameᵗ Δ Δ′ →
  Set
RenPresInv d d′ ρ = ∀{X} → tyVar→ℕ (ρ X) < d′ → tyVar→ℕ X < d

RenPres-ext :
  ∀{Δ}{Δ′}{d}{d′}{ρ : Renameᵗ Δ Δ′} →
  RenPres d d′ ρ →
  RenPres (suc d) (suc d′) (extᵗ ρ)
RenPres-ext {ρ = ρ} hρ {X = Zᵗ} p = s≤s z≤n
RenPres-ext {ρ = ρ} hρ {X = Sᵗ X} (s≤s p) = s≤s (hρ p)

RenPresInv-ext :
  ∀{Δ}{Δ′}{d}{d′}{ρ : Renameᵗ Δ Δ′} →
  RenPresInv d d′ ρ →
  RenPresInv (suc d) (suc d′) (extᵗ ρ)
RenPresInv-ext {ρ = ρ} hρ {X = Zᵗ} p = s≤s z≤n
RenPresInv-ext {ρ = ρ} hρ {X = Sᵗ X} (s≤s p) = s≤s (hρ p)

NoFreeXᵈ-rename :
  ∀{Δ}{Δ′}{Ψ}{d}{d′}{ρ : Renameᵗ Δ Δ′}{A : Ty Δ Ψ} →
  RenPres d d′ ρ →
  NoFreeXᵈ d A →
  NoFreeXᵈ d′ (renameᵗ ρ A)
NoFreeXᵈ-rename hρ (nx-var p) = nx-var (hρ p)
NoFreeXᵈ-rename hρ nx-seal = nx-seal
NoFreeXᵈ-rename hρ nx-base = nx-base
NoFreeXᵈ-rename hρ nx-star = nx-star
NoFreeXᵈ-rename hρ (nx-arr nxA nxB) =
  nx-arr (NoFreeXᵈ-rename hρ nxA) (NoFreeXᵈ-rename hρ nxB)
NoFreeXᵈ-rename hρ (nx-all nxA) =
  nx-all (NoFreeXᵈ-rename (RenPres-ext hρ) nxA)

NoFreeXᵈ-rename-S :
  ∀{Δ}{Ψ}{d}{A : Ty Δ Ψ} →
  NoFreeXᵈ d A →
  NoFreeXᵈ (suc d) (renameᵗ Sᵗ A)
NoFreeXᵈ-rename-S =
  NoFreeXᵈ-rename (λ p → s≤s p)

NoFreeXᵈ-rename-inv :
  ∀{Δ}{Δ′}{Ψ}{d}{d′}{ρ : Renameᵗ Δ Δ′}{A : Ty Δ Ψ} →
  RenPresInv d d′ ρ →
  NoFreeXᵈ d′ (renameᵗ ρ A) →
  NoFreeXᵈ d A
NoFreeXᵈ-rename-inv {A = ＇ X} hρ (nx-var p) = nx-var (hρ p)
NoFreeXᵈ-rename-inv {A = ｀ α} hρ nx-seal = nx-seal
NoFreeXᵈ-rename-inv {A = ‵ ι} hρ nx-base = nx-base
NoFreeXᵈ-rename-inv {A = `★} hρ nx-star = nx-star
NoFreeXᵈ-rename-inv {A = A ⇒ B} hρ (nx-arr nxA nxB) =
  nx-arr (NoFreeXᵈ-rename-inv hρ nxA) (NoFreeXᵈ-rename-inv hρ nxB)
NoFreeXᵈ-rename-inv {A = `∀ A} hρ (nx-all nxA) =
  nx-all (NoFreeXᵈ-rename-inv (RenPresInv-ext hρ) nxA)

NoFreeXᵈ-rename-S-inv :
  ∀{Δ}{Ψ}{d}{A : Ty Δ Ψ} →
  NoFreeXᵈ (suc d) (renameᵗ Sᵗ A) →
  NoFreeXᵈ d A
NoFreeXᵈ-rename-S-inv =
  NoFreeXᵈ-rename-inv (λ { (s≤s p) → p })

NoFreeXᵈ-⇑ˢ :
  ∀{Δ}{Ψ}{d}{A : Ty Δ Ψ} →
  NoFreeXᵈ d A →
  NoFreeXᵈ d (⇑ˢ A)
NoFreeXᵈ-⇑ˢ (nx-var p) = nx-var p
NoFreeXᵈ-⇑ˢ nx-seal = nx-seal
NoFreeXᵈ-⇑ˢ nx-base = nx-base
NoFreeXᵈ-⇑ˢ nx-star = nx-star
NoFreeXᵈ-⇑ˢ (nx-arr nxA nxB) =
  nx-arr (NoFreeXᵈ-⇑ˢ nxA) (NoFreeXᵈ-⇑ˢ nxB)
NoFreeXᵈ-⇑ˢ (nx-all nxA) =
  nx-all (NoFreeXᵈ-⇑ˢ nxA)

NoFreeXᵈ-⇑ˢ-inv :
  ∀{Δ}{Ψ}{d}{A : Ty Δ Ψ} →
  NoFreeXᵈ d (⇑ˢ A) →
  NoFreeXᵈ d A
NoFreeXᵈ-⇑ˢ-inv {A = ＇ X} (nx-var p) = nx-var p
NoFreeXᵈ-⇑ˢ-inv {A = ｀ α} nx-seal = nx-seal
NoFreeXᵈ-⇑ˢ-inv {A = ‵ ι} nx-base = nx-base
NoFreeXᵈ-⇑ˢ-inv {A = `★} nx-star = nx-star
NoFreeXᵈ-⇑ˢ-inv {A = A ⇒ B} (nx-arr nxA nxB) =
  nx-arr (NoFreeXᵈ-⇑ˢ-inv nxA) (NoFreeXᵈ-⇑ˢ-inv nxB)
NoFreeXᵈ-⇑ˢ-inv {A = `∀ A} (nx-all nxA) =
  nx-all (NoFreeXᵈ-⇑ˢ-inv nxA)

SubstOKᵈ :
  ∀{Δ}{Δ′}{Ψ} →
  ℕ →
  Substᵗ Δ Δ′ Ψ →
  Set
SubstOKᵈ d σ = ∀{X} → tyVar→ℕ X < suc d → NoFreeXᵈ d (σ X)

SubstOKᵈ-exts :
  ∀{Δ}{Δ′}{Ψ}{d}{σ : Substᵗ Δ Δ′ Ψ} →
  SubstOKᵈ d σ →
  SubstOKᵈ (suc d) (extsᵗ σ)
SubstOKᵈ-exts hσ {X = Zᵗ} p = nx-var (s≤s z≤n)
SubstOKᵈ-exts hσ {X = Sᵗ X} (s≤s p) =
  NoFreeXᵈ-rename-S (hσ p)

NoFreeXᵈ-substᵗ :
  ∀{Δ}{Δ′}{Ψ}{d}{A : Ty Δ Ψ}{σ : Substᵗ Δ Δ′ Ψ} →
  NoFreeXᵈ (suc d) A →
  SubstOKᵈ d σ →
  NoFreeXᵈ d (substᵗ σ A)
NoFreeXᵈ-substᵗ (nx-var p) hσ = hσ p
NoFreeXᵈ-substᵗ nx-seal hσ = nx-seal
NoFreeXᵈ-substᵗ nx-base hσ = nx-base
NoFreeXᵈ-substᵗ nx-star hσ = nx-star
NoFreeXᵈ-substᵗ (nx-arr nxA nxB) hσ =
  nx-arr (NoFreeXᵈ-substᵗ nxA hσ) (NoFreeXᵈ-substᵗ nxB hσ)
NoFreeXᵈ-substᵗ (nx-all nxA) hσ =
  nx-all (NoFreeXᵈ-substᵗ nxA (SubstOKᵈ-exts hσ))

SubstOKᵈ-single-var :
  ∀{Δ}{Ψ}{d}{V : TyVar Δ} →
  tyVar→ℕ V < d →
  SubstOKᵈ d (singleTyEnv {Δ = Δ} {Ψ = Ψ} (varTy {Ψ = Ψ} V))
SubstOKᵈ-single-var v< {X = Zᵗ} p = nx-var v<
SubstOKᵈ-single-var v< {X = Sᵗ X} (s≤s p) = nx-var p

SubstOKᵈ-single-seal :
  ∀{Δ}{Ψ}{d}{α : Seal Ψ} →
  SubstOKᵈ d (singleTyEnv {Δ = Δ} (｀ α))
SubstOKᵈ-single-seal {X = Zᵗ} p = nx-seal
SubstOKᵈ-single-seal {X = Sᵗ X} (s≤s p) = nx-var p

NoFreeXᵈ-subst-var :
  ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ}{X : TyVar Δ} →
  NoFreeXᵈ (suc d) A →
  tyVar→ℕ X < d →
  NoFreeXᵈ d (A [ ＇ X ]ᵗ)
NoFreeXᵈ-subst-var {Δ = Δ} {Ψ = Ψ} {d = d} {X = X} nxA x< =
  NoFreeXᵈ-substᵗ {d = d} {σ = singleTyEnv {Δ = Δ} {Ψ = Ψ} (varTy {Ψ = Ψ} X)}
    nxA
    (SubstOKᵈ-single-var {Ψ = Ψ} x<)

NoFreeXᵈ-subst-seal :
  ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  NoFreeXᵈ (suc d) A →
  NoFreeXᵈ d (A [ ｀ α ]ᵗ)
NoFreeXᵈ-subst-seal {Δ = Δ} {d = d} {α = α} nxA =
  NoFreeXᵈ-substᵗ {d = d} {σ = singleTyEnv {Δ = Δ} (｀ α)}
    nxA
    SubstOKᵈ-single-seal

SubstInvᵈ :
  ∀{Δ}{Δ′}{Ψ} →
  ℕ →
  Substᵗ Δ Δ′ Ψ →
  Set
SubstInvᵈ {Ψ = Ψ} d σ =
  ∀{X} → NoFreeXᵈ d (σ X) → NoFreeXᵈ (suc d) (varTy {Ψ = Ψ} X)

SubstInvᵈ-exts :
  ∀{Δ}{Δ′}{Ψ}{d}{σ : Substᵗ Δ Δ′ Ψ} →
  SubstInvᵈ d σ →
  SubstInvᵈ (suc d) (extsᵗ σ)
SubstInvᵈ-exts hσ {X = Zᵗ} nxX =
  nx-var (s≤s z≤n)
SubstInvᵈ-exts hσ {X = Sᵗ X} nxX =
  NoFreeXᵈ-rename-S
    (hσ (NoFreeXᵈ-rename-S-inv nxX))

NoFreeXᵈ-substᵗ-inv :
  ∀{Δ}{Δ′}{Ψ}{d}{A : Ty Δ Ψ}{σ : Substᵗ Δ Δ′ Ψ} →
  NoFreeXᵈ d (substᵗ σ A) →
  SubstInvᵈ d σ →
  NoFreeXᵈ (suc d) A
NoFreeXᵈ-substᵗ-inv {A = ＇ X} nxA hσ = hσ {X = X} nxA
NoFreeXᵈ-substᵗ-inv {A = ｀ α} nxA hσ = nx-seal
NoFreeXᵈ-substᵗ-inv {A = ‵ ι} nxA hσ = nx-base
NoFreeXᵈ-substᵗ-inv {A = `★} nxA hσ = nx-star
NoFreeXᵈ-substᵗ-inv {A = A ⇒ B} (nx-arr nxA nxB) hσ =
  nx-arr
    (NoFreeXᵈ-substᵗ-inv nxA hσ)
    (NoFreeXᵈ-substᵗ-inv nxB hσ)
NoFreeXᵈ-substᵗ-inv {A = `∀ A} (nx-all nxA) hσ =
  nx-all (NoFreeXᵈ-substᵗ-inv nxA (SubstInvᵈ-exts hσ))

SubstInvᵈ-single-seal :
  ∀{Δ}{Ψ}{d}{α : Seal Ψ} →
  SubstInvᵈ d (singleTyEnv {Δ = Δ} (｀ α))
SubstInvᵈ-single-seal {X = Zᵗ} nx-seal =
  nx-var (s≤s z≤n)
SubstInvᵈ-single-seal {X = Sᵗ X} (nx-var p) =
  nx-var (s≤s p)

NoFreeXᵈ-subst-seal-inv :
  ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  NoFreeXᵈ d (A [ ｀ α ]ᵗ) →
  NoFreeXᵈ (suc d) A
NoFreeXᵈ-subst-seal-inv nxA =
  NoFreeXᵈ-substᵗ-inv nxA SubstInvᵈ-single-seal

<-ctx :
  ∀{Δ}{X : TyVar Δ} →
  tyVar→ℕ X < Δ
<-ctx {Δ = suc Δ} {X = Zᵗ} = s≤s z≤n
<-ctx {Δ = suc Δ} {X = Sᵗ X} = s≤s (<-ctx {Δ = Δ} {X = X})

NoFreeXᵈ-ctx :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ} →
  NoFreeXᵈ Δ A
NoFreeXᵈ-ctx {A = ＇ X} = nx-var <-ctx
NoFreeXᵈ-ctx {A = ｀ α} = nx-seal
NoFreeXᵈ-ctx {A = ‵ ι} = nx-base
NoFreeXᵈ-ctx {A = `★} = nx-star
NoFreeXᵈ-ctx {A = A ⇒ B} =
  nx-arr NoFreeXᵈ-ctx NoFreeXᵈ-ctx
NoFreeXᵈ-ctx {A = `∀ A} =
  nx-all NoFreeXᵈ-ctx

RenPres-0-lift0 :
  ∀{Δ}{X : TyVar 0} →
  tyVar→ℕ X < zero →
  tyVar→ℕ (lift0ᵗ {Δ = Δ} X) < zero
RenPres-0-lift0 ()

NoFreeXᵈ-wkTy0 :
  ∀{Δ}{Ψ}{A : Ty 0 Ψ} →
  NoFreeXᵈ 0 (wkTy0 {Δ = Δ} A)
NoFreeXᵈ-wkTy0 {A = A} =
  NoFreeXᵈ-rename RenPres-0-lift0 (NoFreeXᵈ-ctx {A = A})

NoFreeXᵈ-wkTy0ᵈ :
  ∀{Δ}{Ψ}{d}{A : Ty 0 Ψ} →
  NoFreeXᵈ d (wkTy0 {Δ = Δ} A)
NoFreeXᵈ-wkTy0ᵈ {d = zero} =
  NoFreeXᵈ-wkTy0
NoFreeXᵈ-wkTy0ᵈ {d = suc d} =
  NoFreeXᵈ-raise (NoFreeXᵈ-wkTy0ᵈ {d = d})

lookup-shift★ :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ A →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ∋ˢ Sˢ α ⦂ ⇑ˢ A
lookup-shift★ h =
  S∋ˢ (renameLookupˢ Sˢ h)

unique-shift★ :
  ∀{Ψ}{Σ : Store Ψ} →
  Uniqueˢ Σ →
  Uniqueˢ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ)
unique-shift★ =
  unique-ν `★

wkTy0-⇑ˢ :
  ∀{Δ}{Ψ}{A : Ty 0 Ψ} →
  ⇑ˢ (wkTy0 {Δ = Δ} A) ≡ wkTy0 {Δ = Δ} (⇑ˢ A)
wkTy0-⇑ˢ {A = A} =
  TypeSubst.renameˢ-wkTy0 Sˢ A

seal-prec :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ A →
  Σ ⊢ wkTy0 {Δ = Δ} A ⊑ ｀ α
seal-prec h = 〔 seal h 〕

seal-prec-shift :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ A →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ⇑ˢ (wkTy0 {Δ = Δ} A) ⊑ ｀ Sˢ α
seal-prec-shift {A = A} h =
  Eq.subst
    (λ T → _ ⊢ T ⊑ ｀ Sˢ _)
    (Eq.sym (wkTy0-⇑ˢ {A = A}))
    (seal-prec (lookup-shift★ h))

------------------------------------------------------------------------
-- Precision preserves no-free-type-variable facts
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  ⊑ᵃ-nofree-leftᵈ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{d}{A B : Ty Δ Ψ} →
    Σ ⊢ A ⊑ᵃ B →
    NoFreeXᵈ d B →
    NoFreeXᵈ d A
  ⊑ᵃ-nofree-leftᵈ (tag g) nxB =
    nx-star
  ⊑ᵃ-nofree-leftᵈ (seal {A = A₀} h) nxB =
    NoFreeXᵈ-wkTy0ᵈ {A = A₀}
  ⊑ᵃ-nofree-leftᵈ (_↦_ p q) (nx-arr nxA nxB) =
    nx-arr (⊑-nofree-leftᵈ p nxA) (⊑-nofree-leftᵈ q nxB)
  ⊑ᵃ-nofree-leftᵈ (∀ᵖ p) (nx-all nxB) =
    nx-all (⊑-nofree-leftᵈ p nxB)
  ⊑ᵃ-nofree-leftᵈ {d = d} (ν p) nxB =
    nx-all
      (NoFreeXᵈ-⇑ˢ-inv
        (NoFreeXᵈ-subst-seal-inv
          (⊑-nofree-leftᵈ p (NoFreeXᵈ-⇑ˢ nxB))))

  ⊑-nofree-leftᵈ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{d}{A B : Ty Δ Ψ} →
    Σ ⊢ A ⊑ B →
    NoFreeXᵈ d B →
    NoFreeXᵈ d A
  ⊑-nofree-leftᵈ id nxB = nxB
  ⊑-nofree-leftᵈ (p ； a) nxC =
    ⊑-nofree-leftᵈ p (⊑ᵃ-nofree-leftᵈ a nxC)

  ⊑ᵃ-nofree-rightᵈ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{d}{A B : Ty Δ Ψ} →
    NoFreeXᵈ d A →
    Σ ⊢ A ⊑ᵃ B →
    NoFreeXᵈ d B
  ⊑ᵃ-nofree-rightᵈ nxA (tag (｀ α)) =
    nx-seal
  ⊑ᵃ-nofree-rightᵈ nxA (tag (‵ ι)) =
    nx-base
  ⊑ᵃ-nofree-rightᵈ nxA (tag ★⇒★) =
    nx-arr nx-star nx-star
  ⊑ᵃ-nofree-rightᵈ nxA (seal h) =
    nx-seal
  ⊑ᵃ-nofree-rightᵈ (nx-arr nxA nxB) (_↦_ p q) =
    nx-arr (⊑-nofree-rightᵈ nxA p) (⊑-nofree-rightᵈ nxB q)
  ⊑ᵃ-nofree-rightᵈ (nx-all nxA) (∀ᵖ p) =
    nx-all (⊑-nofree-rightᵈ nxA p)
  ⊑ᵃ-nofree-rightᵈ (nx-all nxA) (ν p) =
    NoFreeXᵈ-⇑ˢ-inv
      (⊑-nofree-rightᵈ
        (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA))
        p)

  ⊑-nofree-rightᵈ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{d}{A B : Ty Δ Ψ} →
    NoFreeXᵈ d A →
    Σ ⊢ A ⊑ B →
    NoFreeXᵈ d B
  ⊑-nofree-rightᵈ nxA id = nxA
  ⊑-nofree-rightᵈ nxA (p ； a) =
    ⊑ᵃ-nofree-rightᵈ (⊑-nofree-rightᵈ nxA p) a

⊑ᵃ-nofree-left :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ A ⊑ᵃ B →
  NoFreeX B →
  NoFreeX A
⊑ᵃ-nofree-left = ⊑ᵃ-nofree-leftᵈ

⊑-nofree-left :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ A ⊑ B →
  NoFreeX B →
  NoFreeX A
⊑-nofree-left = ⊑-nofree-leftᵈ

⊑ᵃ-nofree-right :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  NoFreeX A →
  Σ ⊢ A ⊑ᵃ B →
  NoFreeX B
⊑ᵃ-nofree-right = ⊑ᵃ-nofree-rightᵈ

⊑-nofree-right :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  NoFreeX A →
  Σ ⊢ A ⊑ B →
  NoFreeX B
⊑-nofree-right = ⊑-nofree-rightᵈ

★⊑→nofree :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
  Σ ⊢ `★ ⊑ A →
  NoFreeX A
★⊑→nofree =
  ⊑-nofree-right nx-star

------------------------------------------------------------------------
-- Precision transport lemmas
------------------------------------------------------------------------

mutual
  ~-wkΣ :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ⊢ A ~ B →
    Σ′ ⊢ A ~ B
  ~-wkΣ w X~X = X~X
  ~-wkΣ w α~α = α~α
  ~-wkΣ w ι~ι = ι~ι
  ~-wkΣ w ★~★ = ★~★
  ~-wkΣ w (★~G g) = ★~G g
  ~-wkΣ w (G~★ g) = G~★ g
  ~-wkΣ w (★~⇒ c d) = ★~⇒ (~-wkΣ w c) (~-wkΣ w d)
  ~-wkΣ w (⇒~★ c d) = ⇒~★ (~-wkΣ w c) (~-wkΣ w d)
  ~-wkΣ w (A~α h eq) = A~α (wkLookupˢ w h) eq
  ~-wkΣ w (A~α* h c) = A~α* (wkLookupˢ w h) (~-wkΣ w c)
  ~-wkΣ w (α~A h eq) = α~A (wkLookupˢ w h) eq
  ~-wkΣ w (α~A* h c) = α~A* (wkLookupˢ w h) (~-wkΣ w c)
  ~-wkΣ w (↦~↦ c d) = ↦~↦ (~-wkΣ w c) (~-wkΣ w d)
  ~-wkΣ w (∀~∀ c) = ∀~∀ (~-wkΣ w c)
  ~-wkΣ w (∀~ c) = ∀~ (~-wkΣ (ν-⊆ˢ `★ w) c)
  ~-wkΣ w (~∀ c) = ~∀ (~-wkΣ (ν-⊆ˢ `★ w) c)

mutual
  ~-renameˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ~ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ~ renameˢ ρ B
  ~-renameˢ ρ X~X = X~X
  ~-renameˢ ρ α~α = α~α
  ~-renameˢ ρ ι~ι = ι~ι
  ~-renameˢ ρ ★~★ = ★~★
  ~-renameˢ ρ (★~G g) = ★~G (renameˢ-ground ρ g)
  ~-renameˢ ρ (G~★ g) = G~★ (renameˢ-ground ρ g)
  ~-renameˢ ρ (★~⇒ c d) = ★~⇒ (~-renameˢ ρ c) (~-renameˢ ρ d)
  ~-renameˢ ρ (⇒~★ c d) = ⇒~★ (~-renameˢ ρ c) (~-renameˢ ρ d)
  ~-renameˢ ρ (A~α {α = α} {A = A} h eq) with eq
  ... | refl =
    Eq.subst
      (λ T → _ ⊢ T ~ ｀ (ρ α))
      (Eq.sym (TypeSubst.renameˢ-wkTy0 ρ A))
      (A~α (renameLookupˢ ρ h) refl)
  ~-renameˢ ρ (A~α* {α = α} {A = A} h c) =
    A~α* (renameLookupˢ ρ h)
      (Eq.subst
        (λ T → _ ⊢ _ ~ T)
        (TypeSubst.renameˢ-wkTy0 ρ A)
        (~-renameˢ ρ c))
  ~-renameˢ ρ (α~A {α = α} {A = A} h eq) with eq
  ... | refl =
    Eq.subst
      (λ T → _ ⊢ ｀ (ρ α) ~ T)
      (Eq.sym (TypeSubst.renameˢ-wkTy0 ρ A))
      (α~A (renameLookupˢ ρ h) refl)
  ~-renameˢ ρ (α~A* {α = α} {A = A} h c) =
    α~A* (renameLookupˢ ρ h)
      (Eq.subst
        (λ T → _ ⊢ T ~ _)
        (TypeSubst.renameˢ-wkTy0 ρ A)
        (~-renameˢ ρ c))
  ~-renameˢ ρ (↦~↦ c d) = ↦~↦ (~-renameˢ ρ c) (~-renameˢ ρ d)
  ~-renameˢ ρ (∀~∀ c) = ∀~∀ (~-renameˢ ρ c)
  ~-renameˢ {Σ = Σ} ρ (∀~ {A = A} {B = B} c) =
    ∀~
      (Eq.subst
        (λ Σ′ →
          Σ′ ⊢
            ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ) ~
            (⇑ˢ (renameˢ ρ B)))
        (renameStoreˢ-ext-ν ρ Σ)
        (Eq.subst
          (λ T →
            renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ) ~
              T)
          (renameˢ-ext-⇑ˢ ρ B)
          (Eq.subst
            (λ T →
              renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
                T ~
                renameˢ (extˢ ρ) (⇑ˢ B))
          (trans
            (renameˢ-[]ᵗ-seal (extˢ ρ) (⇑ˢ A) Zˢ)
            (cong (λ T → T [ ｀ Zˢ ]ᵗ) (renameˢ-ext-⇑ˢ ρ A)))
            (~-renameˢ (extˢ ρ) c))))
  ~-renameˢ {Σ = Σ} ρ (~∀ {A = A} {B = B} c) =
    ~∀
      (Eq.subst
        (λ Σ′ →
          Σ′ ⊢
            (⇑ˢ (renameˢ ρ A)) ~
            ((⇑ˢ (renameˢ ρ B)) [ ｀ Zˢ ]ᵗ))
        (renameStoreˢ-ext-ν ρ Σ)
        (Eq.subst
          (λ T →
            renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              T ~
              ((⇑ˢ (renameˢ ρ B)) [ ｀ Zˢ ]ᵗ))
          (renameˢ-ext-⇑ˢ ρ A)
          (Eq.subst
            (λ T →
              renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
                renameˢ (extˢ ρ) (⇑ˢ A) ~
                T)
            (trans
              (renameˢ-[]ᵗ-seal (extˢ ρ) (⇑ˢ B) Zˢ)
              (cong (λ T → T [ ｀ Zˢ ]ᵗ) (renameˢ-ext-⇑ˢ ρ B)))
            (~-renameˢ (extˢ ρ) c))))

~-shift★ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ A ~ B →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ⇑ˢ A ~ ⇑ˢ B
~-shift★ c =
  ~-wkΣ (drop ⊆ˢ-refl) (~-renameˢ Sˢ c)

~-refl′ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
  Σ ⊢ A ~ A
~-refl′ {A = ＇ X} = X~X
~-refl′ {A = ｀ α} = α~α
~-refl′ {A = ‵ ι} = ι~ι
~-refl′ {A = `★} = ★~★
~-refl′ {A = A ⇒ B} = ↦~↦ ~-refl′ ~-refl′
~-refl′ {A = `∀ A} = ∀~∀ ~-refl′

mutual
  ~-substᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ~ B →
    Σ ⊢ substᵗ σ A ~ substᵗ σ B
  ~-substᵗ σ X~X = ~-refl′
  ~-substᵗ σ α~α = α~α
  ~-substᵗ σ ι~ι = ι~ι
  ~-substᵗ σ ★~★ = ★~★
  ~-substᵗ σ (★~G g) = ★~G (substᵗ-ground σ g)
  ~-substᵗ σ (G~★ g) = G~★ (substᵗ-ground σ g)
  ~-substᵗ σ (★~⇒ c d) = ★~⇒ (~-substᵗ σ c) (~-substᵗ σ d)
  ~-substᵗ σ (⇒~★ c d) = ⇒~★ (~-substᵗ σ c) (~-substᵗ σ d)
  ~-substᵗ σ (A~α {A = A₀} h eq) =
    A~α h (trans (cong (substᵗ σ) eq) (substᵗ-wkTy0 σ A₀))
  ~-substᵗ σ (A~α* {A = A₀} h c) =
    A~α* h
      (Eq.subst
        (λ T → _ ⊢ _ ~ T)
        (substᵗ-wkTy0 σ A₀)
        (~-substᵗ σ c))
  ~-substᵗ σ (α~A {A = A₀} h eq) =
    α~A h (trans (cong (substᵗ σ) eq) (substᵗ-wkTy0 σ A₀))
  ~-substᵗ σ (α~A* {A = A₀} h c) =
    α~A* h
      (Eq.subst
        (λ T → _ ⊢ T ~ _)
        (substᵗ-wkTy0 σ A₀)
        (~-substᵗ σ c))
  ~-substᵗ σ (↦~↦ c d) = ↦~↦ (~-substᵗ σ c) (~-substᵗ σ d)
  ~-substᵗ σ (∀~∀ c) = ∀~∀ (~-substᵗ (extsᵗ σ) c)
  ~-substᵗ {Σ = Σ} {A = `∀ A} {B = B} σ (∀~ c) =
    ∀~
      (Eq.subst
        (λ T →
          ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
            ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ) ~
            T)
        cod-eq
        (Eq.subst
          (λ T →
            ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              T ~
              substᵗ liftσ (⇑ˢ B))
          dom-eq
          (~-substᵗ liftσ c)))
    where
      liftσ : Substᵗ _ _ (suc _)
      liftσ = liftSubstˢ σ

      inner-eq :
        substᵗ (extsᵗ liftσ) (⇑ˢ A) ≡
        ⇑ˢ (substᵗ (extsᵗ σ) A)
      inner-eq =
        trans
          (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ A))
          (substᵗ-⇑ˢ (extsᵗ σ) A)

      dom-eq :
        substᵗ liftσ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ≡
        ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ)
      dom-eq =
        trans
          (substᵗ-[]ᵗ-seal liftσ (⇑ˢ A) Zˢ)
          (cong (λ T → T [ ｀ Zˢ ]ᵗ) inner-eq)

      cod-eq :
        substᵗ liftσ (⇑ˢ B) ≡
        (⇑ˢ (substᵗ σ B))
      cod-eq = substᵗ-⇑ˢ σ B

  ~-substᵗ {Σ = Σ} {A = A} {B = `∀ B} σ (~∀ c) =
    ~∀
      (Eq.subst
        (λ T →
          ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
            T ~
            ((⇑ˢ (substᵗ (extsᵗ σ) B)) [ ｀ Zˢ ]ᵗ))
        dom-eq
        (Eq.subst
          (λ T →
            ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              substᵗ liftσ (⇑ˢ A) ~
              T)
          cod-eq
          (~-substᵗ liftσ c)))
    where
      liftσ : Substᵗ _ _ (suc _)
      liftσ = liftSubstˢ σ

      inner-eq :
        substᵗ (extsᵗ liftσ) (⇑ˢ B) ≡
        ⇑ˢ (substᵗ (extsᵗ σ) B)
      inner-eq =
        trans
          (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ B))
          (substᵗ-⇑ˢ (extsᵗ σ) B)

      dom-eq :
        substᵗ liftσ (⇑ˢ A) ≡
        (⇑ˢ (substᵗ σ A))
      dom-eq = substᵗ-⇑ˢ σ A

      cod-eq :
        substᵗ liftσ ((⇑ˢ B) [ ｀ Zˢ ]ᵗ) ≡
        ((⇑ˢ (substᵗ (extsᵗ σ) B)) [ ｀ Zˢ ]ᵗ)
      cod-eq =
        trans
          (substᵗ-[]ᵗ-seal liftσ (⇑ˢ B) Zˢ)
          (cong (λ T → T [ ｀ Zˢ ]ᵗ) inner-eq)

~-[]ᵗ-seal :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  Σ ⊢ A ~ B →
  Σ ⊢ A [ ｀ α ]ᵗ ~ B [ ｀ α ]ᵗ
~-[]ᵗ-seal {α = α} c =
  ~-substᵗ (singleTyEnv (｀ α)) c

------------------------------------------------------------------------
-- If A has no free X and all free seals in A map to ★, then ★ ~ A.
------------------------------------------------------------------------

mutual
  ★~-closed :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
    NoFreeXᵈ 0 A →
    SealsAt★ Σ A →
    Σ ⊢ `★ ~ A
  ★~-closed {A = ＇ X} (nx-var nxX) sX = ⊥-elim (<-zero-impossible nxX)
  ★~-closed {A = ｀ α} nx-seal (sα hα) = A~α hα refl
  ★~-closed {A = ‵ ι} nx-base s-base = ★~G (‵ ι)
  ★~-closed {A = `★} nx-star s-star = ★~★
  ★~-closed (nx-arr nxA nxB) (s-arr hA hB) =
    ★~⇒ (~★-closed nxA hA) (★~-closed nxB hB)
  ★~-closed {A = `∀ A} (nx-all nxA) (s-all hA) =
    ~∀ (★~-closed (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA)) hA)

  ~★-closed :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
    NoFreeXᵈ 0 A →
    SealsAt★ Σ A →
    Σ ⊢ A ~ `★
  ~★-closed {A = ＇ X} (nx-var nxX) sX = ⊥-elim (<-zero-impossible nxX)
  ~★-closed {A = ｀ α} nx-seal (sα hα) = α~A hα refl
  ~★-closed {A = ‵ ι} nx-base s-base = G~★ (‵ ι)
  ~★-closed {A = `★} nx-star s-star = ★~★
  ~★-closed (nx-arr nxA nxB) (s-arr hA hB) =
    ⇒~★ (★~-closed nxA hA) (~★-closed nxB hB)
  ~★-closed {A = `∀ A} (nx-all nxA) (s-all hA) =
    ∀~ (~★-closed (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA)) hA)

------------------------------------------------------------------------
-- Consistency is symmetric
------------------------------------------------------------------------

~-sym :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ A ~ B →
  Σ ⊢ B ~ A
~-sym X~X = X~X
~-sym α~α = α~α
~-sym ι~ι = ι~ι
~-sym ★~★ = ★~★
~-sym (★~G g) = G~★ g
~-sym (G~★ g) = ★~G g
~-sym (★~⇒ A~★ ★~B) = ⇒~★ (~-sym A~★) (~-sym ★~B)
~-sym (⇒~★ ★~A B~★) = ★~⇒ (~-sym ★~A) (~-sym B~★)
~-sym (A~α h eq) = α~A h eq
~-sym (A~α* h c) = α~A* h (~-sym c)
~-sym (α~A h eq) = A~α h eq
~-sym (α~A* h c) = A~α* h (~-sym c)
~-sym (↦~↦ c d) = ↦~↦ (~-sym c) (~-sym d)
~-sym (∀~∀ c) = ∀~∀ (~-sym c)
~-sym (∀~ c) = ~∀ (~-sym c)
~-sym (~∀ c) = ∀~ (~-sym c)

------------------------------------------------------------------------
-- Monotonicity/Inversion helpers used by prec-leftᵃ/prec-rightᵃ
------------------------------------------------------------------------

★~⇒-dom :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ `★ ~ (A ⇒ B) →
  Σ ⊢ A ~ `★
★~⇒-dom (★~⇒ c d) = c
★~⇒-dom (★~G ★⇒★) = ★~★

★~⇒-cod :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ `★ ~ (A ⇒ B) →
  Σ ⊢ `★ ~ B
★~⇒-cod (★~⇒ c d) = d
★~⇒-cod (★~G ★⇒★) = ★~★

⇒~★-dom :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ (A ⇒ B) ~ `★ →
  Σ ⊢ `★ ~ A
⇒~★-dom (⇒~★ c d) = c
⇒~★-dom (G~★ ★⇒★) = ★~★

⇒~★-cod :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ (A ⇒ B) ~ `★ →
  Σ ⊢ B ~ `★
⇒~★-cod (⇒~★ c d) = d
⇒~★-cod (G~★ ★⇒★) = ★~★

★~∀-open :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ} →
  Σ ⊢ `★ ~ (`∀ A) →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ `★ ~ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)
★~∀-open (~∀ c) = c

∀~★-open :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ} →
  Σ ⊢ (`∀ A) ~ `★ →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ~ `★
∀~★-open (∀~ c) = c

------------------------------------------------------------------------
-- Basic derived consistency facts
------------------------------------------------------------------------

~-refl :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
  Σ ⊢ A ~ A
~-refl {A = ＇ X} = X~X
~-refl {A = ｀ α} = α~α
~-refl {A = ‵ ι} = ι~ι
~-refl {A = `★} = ★~★
~-refl {A = A ⇒ B} = ↦~↦ ~-refl ~-refl
~-refl {A = `∀ A} = ∀~∀ ~-refl

{-# TERMINATING #-}
mutual
  ★~-nofree :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
    NoFreeXᵈ 0 A →
    Σ ⊢ `★ ~ A
  ★~-nofree {A = ＇ X} (nx-var nxX) = ⊥-elim (<-zero-impossible nxX)
  ★~-nofree {A = ｀ α} nx-seal = ★~G (｀ α)
  ★~-nofree {A = ‵ ι} nx-base = ★~G (‵ ι)
  ★~-nofree {A = `★} nx-star = ★~★
  ★~-nofree (nx-arr nxA nxB) =
    ★~⇒ (~★-nofree nxA) (★~-nofree nxB)
  ★~-nofree {A = `∀ A} (nx-all nxA) =
    ~∀ (★~-nofree (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA)))

  ~★-nofree :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ} →
    NoFreeXᵈ 0 A →
    Σ ⊢ A ~ `★
  ~★-nofree {A = ＇ X} (nx-var nxX) = ⊥-elim (<-zero-impossible nxX)
  ~★-nofree {A = ｀ α} nx-seal = G~★ (｀ α)
  ~★-nofree {A = ‵ ι} nx-base = G~★ (‵ ι)
  ~★-nofree {A = `★} nx-star = ★~★
  ~★-nofree (nx-arr nxA nxB) =
    ⇒~★ (★~-nofree nxA) (~★-nofree nxB)
  ~★-nofree {A = `∀ A} (nx-all nxA) =
    ∀~ (~★-nofree (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA)))

★~-wkTy0 :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ} →
  Σ ⊢ `★ ~ wkTy0 {Δ = Δ} A
★~-wkTy0 {A = A} =
  ★~-nofree (NoFreeXᵈ-wkTy0 {A = A})

~★-wkTy0 :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ} →
  Σ ⊢ wkTy0 {Δ = Δ} A ~ `★
~★-wkTy0 {A = A} =
  ~★-nofree (NoFreeXᵈ-wkTy0 {A = A})

------------------------------------------------------------------------
-- Store erasure for star-consistency
------------------------------------------------------------------------

infix 4 _↠⋆_

data _↠⋆_ : ∀{Ψ} → Store Ψ → Store Ψ → Set where
  erase-refl :
    ∀{Ψ}{Σ : Store Ψ} →
    Σ ↠⋆ Σ

  erase-keep :
    ∀{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
    Σ ↠⋆ Σ′ →
    ((α , A) ∷ Σ) ↠⋆ ((α , A) ∷ Σ′)

  erase-shift :
    ∀{Ψ}{Σ Σ′ : Store Ψ} →
    Σ ↠⋆ Σ′ →
    ⟰ˢ Σ ↠⋆ ⟰ˢ Σ′

  erase-dup★ :
    ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ} →
    ((α , `★) ∷ (α , `★) ∷ Σ) ↠⋆ ((α , `★) ∷ Σ)

erase-ν★ :
  ∀{Ψ}{Σ Σ′ : Store Ψ} →
  Σ ↠⋆ Σ′ →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ↠⋆ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ′)
erase-ν★ e = erase-keep (erase-shift e)

mutual
  lookup-erase⋆-shift :
    ∀{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ}{A : Ty 0 (suc Ψ)} →
    Σ ↠⋆ Σ′ →
    ⟰ˢ Σ ∋ˢ Sˢ α ⦂ A →
    ⟰ˢ Σ′ ∋ˢ Sˢ α ⦂ A
  lookup-erase⋆-shift {α = α} e h
    with lookup-Sˢ-⟰ˢ-eq h
  ... | B , (hB , A≡⇑B) =
    Eq.subst
      (λ T → _ ∋ˢ Sˢ α ⦂ T)
      (Eq.sym A≡⇑B)
      (renameLookupˢ Sˢ (lookup-erase⋆ e hB))

  lookup-erase⋆ :
    ∀{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
    Σ ↠⋆ Σ′ →
    Σ ∋ˢ α ⦂ A →
    Σ′ ∋ˢ α ⦂ A
  lookup-erase⋆ erase-refl h = h
  lookup-erase⋆ (erase-keep e) (Z∋ˢ α≡β A≡B) =
    Z∋ˢ α≡β A≡B
  lookup-erase⋆ (erase-keep e) (S∋ˢ h) =
    S∋ˢ (lookup-erase⋆ e h)
  lookup-erase⋆ {α = Zˢ} (erase-shift e) h =
    ⊥-elim (Zˢ∉dom-⟰ˢ h)
  lookup-erase⋆ {α = Sˢ α} (erase-shift e) h =
    lookup-erase⋆-shift e h
  lookup-erase⋆ erase-dup★ (Z∋ˢ α≡β A≡★) =
    Z∋ˢ α≡β A≡★
  lookup-erase⋆ erase-dup★ (S∋ˢ (Z∋ˢ α≡β A≡★)) =
    Z∋ˢ α≡β A≡★
  lookup-erase⋆ erase-dup★ (S∋ˢ (S∋ˢ h)) =
    S∋ˢ h

mutual
  ★~-erase⋆ :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{B : Ty Δ Ψ} →
    Σ ↠⋆ Σ′ →
    Σ ⊢ `★ ~ B →
    Σ′ ⊢ `★ ~ B
  ★~-erase⋆ e ★~★ = ★~★
  ★~-erase⋆ e (★~G g) = ★~G g
  ★~-erase⋆ e (★~⇒ c d) =
    ★~⇒ (~★-erase⋆ e c) (★~-erase⋆ e d)
  ★~-erase⋆ e (A~α h eq) =
    A~α (lookup-erase⋆ e h) eq
  ★~-erase⋆ e (A~α* h c) =
    A~α* (lookup-erase⋆ e h) (★~-erase⋆ e c)
  ★~-erase⋆ e (~∀ c) =
    ~∀ (★~-erase⋆ (erase-ν★ e) c)

  ~★-erase⋆ :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{B : Ty Δ Ψ} →
    Σ ↠⋆ Σ′ →
    Σ ⊢ B ~ `★ →
    Σ′ ⊢ B ~ `★
  ~★-erase⋆ e ★~★ = ★~★
  ~★-erase⋆ e (G~★ g) = G~★ g
  ~★-erase⋆ e (⇒~★ c d) =
    ⇒~★ (★~-erase⋆ e c) (~★-erase⋆ e d)
  ~★-erase⋆ e (α~A h eq) =
    α~A (lookup-erase⋆ e h) eq
  ~★-erase⋆ e (α~A* h c) =
    α~A* (lookup-erase⋆ e h) (~★-erase⋆ e c)
  ~★-erase⋆ e (∀~ c) =
    ∀~ (~★-erase⋆ (erase-ν★ e) c)

------------------------------------------------------------------------
-- Drop the fresh top star-seal from star-consistency
------------------------------------------------------------------------

⇑ˢ-star-inv :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ} →
  `★ ≡ ⇑ˢ A →
  `★ ≡ A
⇑ˢ-star-inv {A = ＇ X} ()
⇑ˢ-star-inv {A = ｀ α} ()
⇑ˢ-star-inv {A = ‵ ι} ()
⇑ˢ-star-inv {A = `★} refl = refl
⇑ˢ-star-inv {A = A ⇒ B} ()
⇑ˢ-star-inv {A = `∀ A} ()

wkTy0-⇑ˢ-star-inv :
  ∀{Δ}{Ψ}{A : Ty 0 Ψ} →
  `★ ≡ wkTy0 {Δ = Δ} (⇑ˢ A) →
  `★ ≡ wkTy0 {Δ = Δ} A
wkTy0-⇑ˢ-star-inv {A = A} eq =
  ⇑ˢ-star-inv (trans eq (Eq.sym (wkTy0-⇑ˢ {A = A})))

renameStoreˢ-single-ν★² :
  ∀{Ψ}{Σ : Store Ψ} →
  renameStoreˢ (singleSealEnv Zˢ)
    ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ)) ≡
  ((Zˢ , ⇑ˢ `★) ∷ (Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ)
renameStoreˢ-single-ν★² {Σ = Σ} =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id Zˢ `★))
    (renameStoreˢ-single-⟰ˢ Zˢ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ))

renameˢ-single-double-open :
  ∀{Δ}{Ψ}{B : Ty (suc Δ) Ψ} →
  renameˢ (singleSealEnv Zˢ) (((⇑ˢ (⇑ˢ B)) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ B) [ ｀ Zˢ ]ᵗ)
renameˢ-single-double-open {B = B} =
  trans
    (renameˢ-[]ᵗ-seal (singleSealEnv Zˢ) (⇑ˢ (⇑ˢ B)) Zˢ)
    (cong (λ T → T [ ｀ Zˢ ]ᵗ) (renameˢ-single-⇑ˢ-id Zˢ (⇑ˢ B)))

{-# TERMINATING #-}
mutual
  ★~-drop-shift :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{B : Ty Δ Ψ} →
    ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ `★ ~ ⇑ˢ B →
    Σ ⊢ `★ ~ B
  ★~-drop-shift {B = ＇ X} (★~G ())
  ★~-drop-shift {B = `★} ★~★ = ★~★
  ★~-drop-shift {B = ｀ α} (★~G (｀ .(Sˢ α))) = ★~G (｀ α)
  ★~-drop-shift {B = ‵ ι} (★~G (‵ .ι)) = ★~G (‵ ι)
  ★~-drop-shift {B = `★ ⇒ `★} (★~G ★⇒★) = ★~G ★⇒★
  ★~-drop-shift {B = A ⇒ B} (★~⇒ c d) =
    ★~⇒ (~★-drop-shift c) (★~-drop-shift d)
  ★~-drop-shift {B = ｀ α} (A~α {α = .(Sˢ α)} (S∋ˢ h) eq)
    with lookup-Sˢ-⟰ˢ-eq h
  ... | A₀ , (h₀ , eqA) =
    A~α h₀ (wkTy0-⇑ˢ-star-inv (trans eq (cong wkTy0 eqA)))
  ★~-drop-shift {B = ｀ α} (A~α* {α = .(Sˢ α)} (S∋ˢ h) c)
    with lookup-Sˢ-⟰ˢ-eq h
  ... | A₀ , (h₀ , eqA) =
    A~α* h₀
      (★~-drop-shift
        (Eq.subst
          (λ T → _ ⊢ `★ ~ T)
          (Eq.sym (wkTy0-⇑ˢ {A = A₀}))
          (Eq.subst
            (λ T → _ ⊢ `★ ~ wkTy0 T)
            eqA
            c)))
  ★~-drop-shift {Σ = Σ} {B = `∀ B₀} (~∀ c) =
    ~∀
      (★~-erase⋆ erase-dup★
        (Eq.subst
          (λ Σ′ → Σ′ ⊢ `★ ~ ((⇑ˢ B₀) [ ｀ Zˢ ]ᵗ))
          (renameStoreˢ-single-ν★² {Σ = Σ})
          (Eq.subst
            (λ T →
              renameStoreˢ (singleSealEnv Zˢ)
                ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ)) ⊢
                `★ ~ T)
            (renameˢ-single-double-open {B = B₀})
            (~-renameˢ (singleSealEnv Zˢ) c))))

  ~★-drop-shift :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{B : Ty Δ Ψ} →
    ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ⇑ˢ B ~ `★ →
    Σ ⊢ B ~ `★
  ~★-drop-shift {B = ＇ X} (G~★ ())
  ~★-drop-shift {B = `★} ★~★ = ★~★
  ~★-drop-shift {B = ｀ α} (G~★ (｀ .(Sˢ α))) = G~★ (｀ α)
  ~★-drop-shift {B = ‵ ι} (G~★ (‵ .ι)) = G~★ (‵ ι)
  ~★-drop-shift {B = `★ ⇒ `★} (G~★ ★⇒★) = G~★ ★⇒★
  ~★-drop-shift {B = A ⇒ B} (⇒~★ c d) =
    ⇒~★ (★~-drop-shift c) (~★-drop-shift d)
  ~★-drop-shift {B = ｀ α} (α~A {α = .(Sˢ α)} (S∋ˢ h) eq)
    with lookup-Sˢ-⟰ˢ-eq h
  ... | A₀ , (h₀ , eqA) =
    α~A h₀ (wkTy0-⇑ˢ-star-inv (trans eq (cong wkTy0 eqA)))
  ~★-drop-shift {B = ｀ α} (α~A* {α = .(Sˢ α)} (S∋ˢ h) c)
    with lookup-Sˢ-⟰ˢ-eq h
  ... | A₀ , (h₀ , eqA) =
    α~A* h₀
      (~★-drop-shift
        (Eq.subst
          (λ T → _ ⊢ T ~ `★)
          (Eq.sym (wkTy0-⇑ˢ {A = A₀}))
          (Eq.subst
            (λ T → _ ⊢ wkTy0 T ~ `★)
            eqA
            c)))
  ~★-drop-shift {Σ = Σ} {B = `∀ B₀} (∀~ c) =
    ∀~
      (~★-erase⋆ erase-dup★
        (Eq.subst
          (λ Σ′ → Σ′ ⊢ ((⇑ˢ B₀) [ ｀ Zˢ ]ᵗ) ~ `★)
          (renameStoreˢ-single-ν★² {Σ = Σ})
          (Eq.subst
            (λ T →
              renameStoreˢ (singleSealEnv Zˢ)
                ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ)) ⊢
                T ~ `★)
            (renameˢ-single-double-open {B = B₀})
            (~-renameˢ (singleSealEnv Zˢ) c))))

-- Seal-consistency inversion (under unique stores)
------------------------------------------------------------------------

mutual
  seal-consistency-inv-left :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A₀ : Ty 0 Ψ}{B : Ty Δ Ψ} →
    Uniqueˢ Σ →
    Σ ∋ˢ α ⦂ A₀ →
    Σ ⊢ ｀ α ~ B →
    Σ ⊢ wkTy0 A₀ ~ B
  seal-consistency-inv-left u h α~α =
    A~α h refl
  seal-consistency-inv-left {α = α} {A₀ = A₀} u h (G~★ (｀ .α)) =
    ~★-wkTy0 {A = A₀}
  seal-consistency-inv-left u h (A~α h′ eq) =
    A~α* h′ (Eq.subst (λ T → _ ⊢ wkTy0 _ ~ T) eq (A~α h refl))
  seal-consistency-inv-left u h (A~α* h′ c) =
    A~α* h′ (seal-consistency-inv-left u h c)
  seal-consistency-inv-left u h (α~A h′ eq)
    with lookup-unique u h′ h
       | eq
  ... | eqA | refl
    rewrite eqA
    = ~-refl
  seal-consistency-inv-left u h (α~A* h′ c)
    with lookup-unique u h′ h
  ... | eqA = Eq.subst (λ T → _ ⊢ wkTy0 T ~ _) eqA c
  seal-consistency-inv-left {Σ = Σ} {α = α} {A₀ = A₀} {B = `∀ B₀} u h (~∀ c) =
    ~∀
      (Eq.subst
        (λ T →
          ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ T ~ ((⇑ˢ B₀) [ ｀ Zˢ ]ᵗ))
        (Eq.sym (TypeSubst.renameˢ-wkTy0 Sˢ A₀))
        (seal-consistency-inv-left
          (unique-shift★ u)
          (lookup-shift★ h)
          c))

  seal-consistency-inv-right :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A₀ : Ty 0 Ψ}{B : Ty Δ Ψ} →
    Uniqueˢ Σ →
    Σ ∋ˢ α ⦂ A₀ →
    Σ ⊢ B ~ ｀ α →
    Σ ⊢ B ~ wkTy0 A₀
  seal-consistency-inv-right u h c =
    ~-sym (seal-consistency-inv-left u h (~-sym c))

------------------------------------------------------------------------
-- Atomic precision transport through seal targets
------------------------------------------------------------------------

prec-leftᵃ-seal :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A₀ : Ty 0 Ψ}{B : Ty Δ Ψ} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A₀ →
  Σ ⊢ ｀ α ~ B →
  Σ ⊢ wkTy0 A₀ ~ B
prec-leftᵃ-seal =
  seal-consistency-inv-left

prec-rightᵃ-seal :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A₀ : Ty 0 Ψ}{B : Ty Δ Ψ} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A₀ →
  Σ ⊢ B ~ ｀ α →
  Σ ⊢ B ~ wkTy0 A₀
prec-rightᵃ-seal =
  seal-consistency-inv-right

Ground-nofree :
  ∀{Δ}{Ψ}{G : Ty Δ Ψ} →
  Ground G →
  NoFreeXᵈ 0 G
Ground-nofree (｀ α) = nx-seal
Ground-nofree (‵ ι) = nx-base
Ground-nofree ★⇒★ = nx-arr nx-star nx-star

{-# TERMINATING #-}
mutual
  ★~-nofree-left :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    NoFreeXᵈ 0 A →
    Σ ⊢ A ~ B →
    Σ ⊢ `★ ~ B
  ★~-nofree-left (nx-var nxX) X~X =
    ⊥-elim (<-zero-impossible nxX)
  ★~-nofree-left nx-seal α~α =
    ★~G (｀ _)
  ★~-nofree-left nx-base ι~ι =
    ★~G (‵ _)
  ★~-nofree-left nx-star ★~★ =
    ★~★
  ★~-nofree-left nx-star (★~G g) =
    ★~G g
  ★~-nofree-left nx-seal (G~★ (｀ _)) =
    ★~★
  ★~-nofree-left nx-base (G~★ (‵ _)) =
    ★~★
  ★~-nofree-left (nx-arr nxA nxB) (G~★ ★⇒★) =
    ★~★
  ★~-nofree-left nx-star (★~⇒ c d) =
    ★~⇒ c d
  ★~-nofree-left (nx-arr nxA nxB) (⇒~★ c d) =
    ★~★
  ★~-nofree-left nxA (A~α h eq) =
    ★~G (｀ _)
  ★~-nofree-left nxA (A~α* h c) =
    ★~G (｀ _)
  ★~-nofree-left nx-seal (α~A {A = A₀} h eq) =
    Eq.subst
      (λ T → _ ⊢ `★ ~ T)
      (sym eq)
      (★~-wkTy0 {A = A₀})
  ★~-nofree-left nx-seal (α~A* {A = A₀} h c) =
    ★~-nofree-left (NoFreeXᵈ-wkTy0 {A = A₀}) c
  ★~-nofree-left (nx-arr nxA nxB) (↦~↦ c d) =
    ★~⇒
      (~★-nofree-right nxA c)
      (★~-nofree-left nxB d)
  ★~-nofree-left (nx-all nxA) (∀~∀ c) =
    ~∀
      (★~-nofree-left
        (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA))
        (~-[]ᵗ-seal {α = Zˢ} (~-shift★ c)))
  ★~-nofree-left (nx-all nxA) (∀~ c) =
    ★~-drop-shift
      (★~-nofree-left
        (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxA))
        c)
  ★~-nofree-left nxA (~∀ c) =
    ~∀
      (★~-nofree-left
        (NoFreeXᵈ-⇑ˢ nxA)
        c)

  ~★-nofree-right :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    NoFreeXᵈ 0 B →
    Σ ⊢ A ~ B →
    Σ ⊢ A ~ `★
  ~★-nofree-right (nx-var nxX) X~X =
    ⊥-elim (<-zero-impossible nxX)
  ~★-nofree-right nx-seal α~α =
    G~★ (｀ _)
  ~★-nofree-right nx-base ι~ι =
    G~★ (‵ _)
  ~★-nofree-right nx-star ★~★ =
    ★~★
  ~★-nofree-right nx-seal (★~G (｀ _)) =
    ★~★
  ~★-nofree-right nx-base (★~G (‵ _)) =
    ★~★
  ~★-nofree-right (nx-arr nxA nxB) (★~G ★⇒★) =
    ★~★
  ~★-nofree-right nx-star (G~★ g) =
    G~★ g
  ~★-nofree-right (nx-arr nxA nxB) (★~⇒ c d) =
    ★~★
  ~★-nofree-right nx-star (⇒~★ c d) =
    ⇒~★ c d
  ~★-nofree-right nx-seal (A~α {A = A₀} h eq) =
    Eq.subst
      (λ T → _ ⊢ T ~ `★)
      (sym eq)
      (~★-wkTy0 {A = A₀})
  ~★-nofree-right nx-seal (A~α* {A = A₀} h c) =
    ~★-nofree-right (NoFreeXᵈ-wkTy0 {A = A₀}) c
  ~★-nofree-right nxB (α~A h eq) =
    G~★ (｀ _)
  ~★-nofree-right nxB (α~A* h c) =
    G~★ (｀ _)
  ~★-nofree-right (nx-arr nxA nxB) (↦~↦ c d) =
    ⇒~★
      (★~-nofree-left nxA c)
      (~★-nofree-right nxB d)
  ~★-nofree-right (nx-all nxB) (∀~∀ c) =
    ∀~
      (~★-nofree-right
        (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxB))
        (~-[]ᵗ-seal {α = Zˢ} (~-shift★ c)))
  ~★-nofree-right nxB (∀~ c) =
    ∀~
      (~★-nofree-right
        (NoFreeXᵈ-⇑ˢ nxB)
        c)
  ~★-nofree-right (nx-all nxB) (~∀ c) =
    ~★-drop-shift
      (~★-nofree-right
        (NoFreeXᵈ-subst-seal (NoFreeXᵈ-⇑ˢ nxB))
        c)

{-# TERMINATING #-}
mutual
  prec-leftᵃ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{X A B : Ty Δ Ψ} →
    Uniqueˢ Σ →
    Σ ⊢ X ⊑ᵃ A →
    Σ ⊢ A ~ B →
    Σ ⊢ X ~ B
  prec-leftᵃ u (tag g) c =
    ★~-nofree-left (Ground-nofree g) c
  prec-leftᵃ u (seal h) c =
    prec-leftᵃ-seal u h c
  prec-leftᵃ u (a@(_↦_ p q)) (G~★ ★⇒★) =
    ~★-nofree
      (⊑ᵃ-nofree-left a (nx-arr nx-star nx-star))
  prec-leftᵃ u (_↦_ p q) (⇒~★ c d) =
    ⇒~★ (prec-right u c p) (prec-left u q d)
  prec-leftᵃ u (_↦_ p q) (↦~↦ c d) =
    ↦~↦ (prec-right u c p) (prec-left u q d)
  prec-leftᵃ u a (A~α h eq) =
    A~α* h (Eq.subst (λ T → _ ⊢ _ ~ T) eq (prec-left u (〔 a 〕) ~-refl))
  prec-leftᵃ u a (A~α* h c) =
    A~α* h (prec-leftᵃ u a c)
  prec-leftᵃ u (_↦_ p q) (~∀ c) =
    ~∀ (prec-left (unique-shift★ u) (⊑-shift★ (〔 _↦_ p q 〕)) c)
  prec-leftᵃ u (∀ᵖ p) (∀~∀ c) =
    ∀~∀ (prec-left u p c)
  prec-leftᵃ u (∀ᵖ p) (∀~ c) =
    ∀~ (prec-left (unique-shift★ u) (⊑-[]ᵗ-seal {α = Zˢ} (⊑-shift★ p)) c)
  prec-leftᵃ u (∀ᵖ p) (~∀ c) =
    ~∀ (prec-left (unique-shift★ u) (⊑-shift★ (〔 ∀ᵖ p 〕)) c)
  prec-leftᵃ u (ν p) c =
    ∀~ (prec-left (unique-shift★ u) p (~-shift★ c))

  prec-rightᵃ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A B Y : Ty Δ Ψ} →
    Uniqueˢ Σ →
    Σ ⊢ A ~ B →
    Σ ⊢ Y ⊑ᵃ B →
    Σ ⊢ A ~ Y
  prec-rightᵃ u c (tag g) =
    ~★-nofree-right (Ground-nofree g) c
  prec-rightᵃ u c (seal h) =
    prec-rightᵃ-seal u h c
  prec-rightᵃ u (★~G ★⇒★) (a@(_↦_ p q)) =
    ★~-nofree
      (⊑ᵃ-nofree-left a (nx-arr nx-star nx-star))
  prec-rightᵃ u (★~⇒ c d) (_↦_ p q) =
    ★~⇒ (prec-left u p c) (prec-right u d q)
  prec-rightᵃ u (↦~↦ c d) (_↦_ p q) =
    ↦~↦ (prec-left u p c) (prec-right u d q)
  prec-rightᵃ u (α~A h eq) a =
    α~A* h (Eq.subst (λ T → _ ⊢ T ~ _) eq (prec-right u ~-refl (〔 a 〕)))
  prec-rightᵃ u (α~A* h c) a =
    α~A* h (prec-rightᵃ u c a)
  prec-rightᵃ u (∀~ c) (_↦_ p q) =
    ∀~ (prec-right (unique-shift★ u) c (⊑-shift★ (〔 _↦_ p q 〕)))
  prec-rightᵃ u (∀~∀ c) (∀ᵖ p) =
    ∀~∀ (prec-right u c p)
  prec-rightᵃ u (~∀ c) (∀ᵖ p) =
    ~∀ (prec-right (unique-shift★ u) c (⊑-[]ᵗ-seal {α = Zˢ} (⊑-shift★ p)))
  prec-rightᵃ u (∀~ c) (∀ᵖ p) =
    ∀~ (prec-right (unique-shift★ u) c (⊑-shift★ (〔 ∀ᵖ p 〕)))
  prec-rightᵃ u c (ν p) =
    ~∀ (prec-right (unique-shift★ u) (~-shift★ c) p)

  prec-left :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{X A B : Ty Δ Ψ} →
    Uniqueˢ Σ →
    Σ ⊢ X ⊑ A →
    Σ ⊢ A ~ B →
    Σ ⊢ X ~ B
  prec-left u id c = c
  prec-left u (p ； a) c =
    prec-left u p (prec-leftᵃ u a c)

  prec-right :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{A B Y : Ty Δ Ψ} →
    Uniqueˢ Σ →
    Σ ⊢ A ~ B →
    Σ ⊢ Y ⊑ B →
    Σ ⊢ A ~ Y
  prec-right u c id = c
  prec-right u c (p ； a) =
    prec-right u (prec-rightᵃ u c a) p

upper-bounds-consistent :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B C : Ty Δ Ψ} →
  Uniqueˢ Σ →
  Σ ⊢ A ⊑ C →
  Σ ⊢ B ⊑ C →
  Σ ⊢ A ~ B
upper-bounds-consistent u A⊑C B⊑C =
  prec-left u A⊑C (prec-right u ~-refl B⊑C)

------------------------------------------------------------------------
-- Completion note
--
-- With arrow precision covariant in both domain and codomain, the original
-- transport argument now goes through.
--
-- The proof of `upper-bounds-consistent` is factored through four transport
-- lemmas:
--   * `prec-leftᵃ` / `prec-rightᵃ` move consistency across one atomic
--     precision step.
--   * `prec-left` / `prec-right` lift those atomic lemmas through transitive
--     precision.
--
-- The key ingredients used in the atomic cases are:
--   * `⊑-nofree-*` plus `★~-nofree-left` / `~★-nofree-right` for `tag`
--   * `prec-leftᵃ-seal` / `prec-rightᵃ-seal` for `seal`
--   * componentwise recursion for `_↦_`
--   * `⊑-shift★`, `⊑-[]ᵗ-seal`, and `★~-drop-shift` / `~★-drop-shift` for
--     `∀ᵖ` and `ν`
--
-- The final theorem is then the short composition:
--   `prec-left u A⊑C (prec-right u ~-refl B⊑C)`.
------------------------------------------------------------------------
