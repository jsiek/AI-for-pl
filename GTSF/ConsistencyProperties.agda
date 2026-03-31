module ConsistencyProperties where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (sym; subst; trans; cong; cong₂)

open import Types
open import Consistency
open import TypePrecision
open import TypeSubst
  using
    ( renameLookupˢ
    ; renameˢ-ground
    ; renameˢ-substᵗ
    ; substᵗ-cong
    ; substᵗ-ground
    ; substᵗ-wkTy0
    ; substᵗ-⇑ˢ
    ; renameᵗ-⇑ˢ
    ; liftSubstˢ
    )
open import PolyCast using (substᵗ-[]ᵗ-seal)
open import Store
  using
    ( Uniqueˢ
    ; unique-ν
    ; lookup-unique
    ; _⊆ˢ_
    ; ⊆ˢ-refl
    ; drop
    ; wkLookupˢ
    ; ν-⊆ˢ
    )

------------------------------------------------------------------------
-- No free type variables (de Bruijn-depth aware)
------------------------------------------------------------------------

infix 4 _<ᵈ_

data _<ᵈ_ : ∀{Δ} → TyVar Δ → ℕ → Set where
  Z< : ∀{Δ}{d} → _<ᵈ_ {Δ = suc Δ} Zᵗ (suc d)
  S< : ∀{Δ}{d}{X : TyVar Δ} → X <ᵈ d → Sᵗ X <ᵈ suc d

data NoFreeXᵈ : ∀{Δ}{Ψ} → ℕ → Ty Δ Ψ → Set where
  nx-var :
    ∀{Δ}{Ψ}{d}{X : TyVar Δ} →
    X <ᵈ d →
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

<ᵈ-zero-impossible : ∀{Δ}{X : TyVar Δ} → X <ᵈ 0 → ⊥
<ᵈ-zero-impossible ()

<ᵈ-raise :
  ∀{Δ}{d}{X : TyVar Δ} →
  X <ᵈ d →
  X <ᵈ suc d
<ᵈ-raise Z< = Z<
<ᵈ-raise (S< p) = S< (<ᵈ-raise p)

RenPres :
  ∀{Δ}{Δ′} →
  ℕ →
  ℕ →
  Renameᵗ Δ Δ′ →
  Set
RenPres d d′ ρ = ∀{X} → X <ᵈ d → ρ X <ᵈ d′

RenPres-ext :
  ∀{Δ}{Δ′}{d}{d′}{ρ : Renameᵗ Δ Δ′} →
  RenPres d d′ ρ →
  RenPres (suc d) (suc d′) (extᵗ ρ)
RenPres-ext hρ Z< = Z<
RenPres-ext hρ (S< p) = S< (hρ p)

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
  NoFreeXᵈ-rename (λ p → S< p)

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

SubstOKᵈ :
  ∀{Δ}{Δ′}{Ψ} →
  ℕ →
  Substᵗ Δ Δ′ Ψ →
  Set
SubstOKᵈ d σ = ∀{X} → X <ᵈ suc d → NoFreeXᵈ d (σ X)

SubstOKᵈ-exts :
  ∀{Δ}{Δ′}{Ψ}{d}{σ : Substᵗ Δ Δ′ Ψ} →
  SubstOKᵈ d σ →
  SubstOKᵈ (suc d) (extsᵗ σ)
SubstOKᵈ-exts hσ {X = Zᵗ} p = nx-var Z<
SubstOKᵈ-exts hσ {X = Sᵗ X} (S< p) =
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
  V <ᵈ d →
  SubstOKᵈ d (singleTyEnv {Δ = Δ} {Ψ = Ψ} (varTy {Ψ = Ψ} V))
SubstOKᵈ-single-var v< {X = Zᵗ} p = nx-var v<
SubstOKᵈ-single-var v< {X = Sᵗ X} (S< p) = nx-var p

SubstOKᵈ-single-seal :
  ∀{Δ}{Ψ}{d}{α : Seal Ψ} →
  SubstOKᵈ d (singleTyEnv {Δ = Δ} (｀ α))
SubstOKᵈ-single-seal {X = Zᵗ} p = nx-seal
SubstOKᵈ-single-seal {X = Sᵗ X} (S< p) = nx-var p

NoFreeXᵈ-subst-var :
  ∀{Δ}{Ψ}{d}{A : Ty (suc Δ) Ψ}{X : TyVar Δ} →
  NoFreeXᵈ (suc d) A →
  X <ᵈ d →
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

<ᵈ-ctx :
  ∀{Δ}{X : TyVar Δ} →
  X <ᵈ Δ
<ᵈ-ctx {Δ = suc Δ} {X = Zᵗ} = Z<
<ᵈ-ctx {Δ = suc Δ} {X = Sᵗ X} = S< (<ᵈ-ctx {Δ = Δ} {X = X})

NoFreeXᵈ-ctx :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ} →
  NoFreeXᵈ Δ A
NoFreeXᵈ-ctx {A = ＇ X} = nx-var <ᵈ-ctx
NoFreeXᵈ-ctx {A = ｀ α} = nx-seal
NoFreeXᵈ-ctx {A = ‵ ι} = nx-base
NoFreeXᵈ-ctx {A = `★} = nx-star
NoFreeXᵈ-ctx {A = A ⇒ B} =
  nx-arr NoFreeXᵈ-ctx NoFreeXᵈ-ctx
NoFreeXᵈ-ctx {A = `∀ A} =
  nx-all NoFreeXᵈ-ctx

RenPres-0-lift0 :
  ∀{Δ}{X : TyVar 0} →
  X <ᵈ 0 →
  lift0ᵗ {Δ = Δ} X <ᵈ 0
RenPres-0-lift0 ()

NoFreeXᵈ-wkTy0 :
  ∀{Δ}{Ψ}{A : Ty 0 Ψ} →
  NoFreeXᵈ 0 (wkTy0 {Δ = Δ} A)
NoFreeXᵈ-wkTy0 {A = A} =
  NoFreeXᵈ-rename RenPres-0-lift0 (NoFreeXᵈ-ctx {A = A})

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
-- Precision transport lemmas
------------------------------------------------------------------------

renameˢ-ext-⇑ˢ :
  ∀{Δ}{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  (A : Ty Δ Ψ) →
  renameˢ (extˢ ρ) (⇑ˢ A) ≡ ⇑ˢ (renameˢ ρ A)
renameˢ-ext-⇑ˢ ρ (＇ X) = refl
renameˢ-ext-⇑ˢ ρ (｀ α) = refl
renameˢ-ext-⇑ˢ ρ (‵ ι) = refl
renameˢ-ext-⇑ˢ ρ `★ = refl
renameˢ-ext-⇑ˢ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-ext-⇑ˢ ρ A) (renameˢ-ext-⇑ˢ ρ B)
renameˢ-ext-⇑ˢ ρ (`∀ A) =
  cong `∀ (renameˢ-ext-⇑ˢ ρ A)

renameStoreˢ-ext-⟰ˢ :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) (⟰ˢ Σ) ≡ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-ext-⟰ˢ ρ [] = refl
renameStoreˢ-ext-⟰ˢ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢ ρ A))
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

renameStoreˢ-ext-ν :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ≡
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ (renameStoreˢ ρ Σ))
renameStoreˢ-ext-ν ρ Σ =
  cong₂ _∷_
    (cong₂ _,_ refl refl)
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

renameˢ-[]ᵗ-seal :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (A : Ty (suc Δ) Ψ) (α : Seal Ψ) →
  renameˢ ρ (A [ ｀ α ]ᵗ) ≡ (renameˢ ρ A) [ ｀ (ρ α) ]ᵗ
renameˢ-[]ᵗ-seal ρ A α =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar (suc _)) →
      renameˢ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ (ρ α)) X
    env Zᵗ = refl
    env (Sᵗ X) = refl

mutual
  ⊑ᵃ-wkΣ :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ⊢ A ⊑ᵃ B →
    Σ′ ⊢ A ⊑ᵃ B
  ⊑ᵃ-wkΣ w (tag g) = tag g
  ⊑ᵃ-wkΣ w (seal h) = seal (wkLookupˢ w h)
  ⊑ᵃ-wkΣ w (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} p q) =
    _↦_ {A = A} {A′ = A′} {B = B} {B′ = B′}
      (⊑-wkΣ w p)
      (⊑-wkΣ w q)
  ⊑ᵃ-wkΣ w (∀ᵖ p) = ∀ᵖ (⊑-wkΣ w p)
  ⊑ᵃ-wkΣ w (ν c) = ν (⊑-wkΣ (ν-⊆ˢ `★ w) c)

  ⊑-wkΣ :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ⊢ A ⊑ B →
    Σ′ ⊢ A ⊑ B
  ⊑-wkΣ w id = id
  ⊑-wkΣ w (p ； a) = (⊑-wkΣ w p) ； (⊑ᵃ-wkΣ w a)

mutual
  ⊑ᵃ-renameˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⊑ᵃ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ᵃ renameˢ ρ B
  ⊑ᵃ-renameˢ ρ (tag g) = tag (renameˢ-ground ρ g)
  ⊑ᵃ-renameˢ ρ (seal {α = α} {A = A} h) =
    Eq.subst
      (λ T → _ ⊢ T ⊑ᵃ ｀ (ρ α))
      (Eq.sym (TypeSubst.renameˢ-wkTy0 ρ A))
      (seal (renameLookupˢ ρ h))
  ⊑ᵃ-renameˢ ρ (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} p q) =
    _↦_ {A = renameˢ ρ A}
        {A′ = renameˢ ρ A′}
        {B = renameˢ ρ B}
        {B′ = renameˢ ρ B′}
      (⊑-renameˢ ρ p)
      (⊑-renameˢ ρ q)
  ⊑ᵃ-renameˢ ρ (∀ᵖ p) = ∀ᵖ (⊑-renameˢ ρ p)
  ⊑ᵃ-renameˢ {Σ = Σ} {A = `∀ A} {B = B} ρ (ν c) =
    ν
      (Eq.subst
        (λ Σ′ →
          Σ′ ⊢
            ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ) ⊑
            (⇑ˢ (renameˢ ρ B)))
        (renameStoreˢ-ext-ν ρ Σ)
        (Eq.subst
          (λ T →
            renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ) ⊑
              T)
          (renameˢ-ext-⇑ˢ ρ B)
          (Eq.subst
            (λ T →
              renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
                T ⊑
                renameˢ (extˢ ρ) (⇑ˢ B))
            (trans
              (renameˢ-[]ᵗ-seal (extˢ ρ) (⇑ˢ A) Zˢ)
              (cong (λ T → T [ ｀ Zˢ ]ᵗ) (renameˢ-ext-⇑ˢ ρ A)))
            (⊑-renameˢ (extˢ ρ) c))))

  ⊑-renameˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⊑ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ renameˢ ρ B
  ⊑-renameˢ ρ id = id
  ⊑-renameˢ ρ (p ； a) =
    (⊑-renameˢ ρ p) ； (⊑ᵃ-renameˢ ρ a)

exts-liftSubstˢ :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (X : TyVar (suc Δ)) →
  extsᵗ (liftSubstˢ σ) X ≡ liftSubstˢ (extsᵗ σ) X
exts-liftSubstˢ σ Zᵗ = refl
exts-liftSubstˢ σ (Sᵗ X) = renameᵗ-⇑ˢ Sᵗ (σ X)

mutual
  ⊑ᵃ-substᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⊑ᵃ B →
    Σ ⊢ substᵗ σ A ⊑ᵃ substᵗ σ B
  ⊑ᵃ-substᵗ σ (tag g) = tag (substᵗ-ground σ g)
  ⊑ᵃ-substᵗ σ (seal {α = α} {A = A} h) =
    Eq.subst
      (λ T → _ ⊢ T ⊑ᵃ ｀ α)
      (Eq.sym (substᵗ-wkTy0 σ A))
      (seal h)
  ⊑ᵃ-substᵗ σ (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} p q) =
    _↦_ {A = substᵗ σ A}
        {A′ = substᵗ σ A′}
        {B = substᵗ σ B}
        {B′ = substᵗ σ B′}
      (⊑-substᵗ σ p)
      (⊑-substᵗ σ q)
  ⊑ᵃ-substᵗ σ (∀ᵖ p) =
    ∀ᵖ (⊑-substᵗ (extsᵗ σ) p)
  ⊑ᵃ-substᵗ {Σ = Σ} {A = `∀ A} {B = B} σ (ν c) =
    ν
      (Eq.subst
        (λ T →
          ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
            ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ) ⊑
            T)
        cod-eq
        (Eq.subst
          (λ T →
            ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              T ⊑
              substᵗ liftσ (⇑ˢ B))
          dom-eq
          (⊑-substᵗ liftσ c)))
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

  ⊑-substᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⊑ B →
    Σ ⊢ substᵗ σ A ⊑ substᵗ σ B
  ⊑-substᵗ σ id = id
  ⊑-substᵗ σ (p ； a) = (⊑-substᵗ σ p) ； (⊑ᵃ-substᵗ σ a)

⊑-[]ᵗ-seal :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  Σ ⊢ A ⊑ B →
  Σ ⊢ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
⊑-[]ᵗ-seal {α = α} p =
  ⊑-substᵗ (singleTyEnv (｀ α)) p

⊑-shift★ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ A ⊑ B →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ⇑ˢ A ⊑ ⇑ˢ B
⊑-shift★ p =
  ⊑-wkΣ (drop ⊆ˢ-refl) (⊑-renameˢ Sˢ p)

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
  ★~-closed {A = ＇ X} (nx-var nxX) sX = ⊥-elim (<ᵈ-zero-impossible nxX)
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
  ~★-closed {A = ＇ X} (nx-var nxX) sX = ⊥-elim (<ᵈ-zero-impossible nxX)
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
  ★~-nofree {A = ＇ X} (nx-var nxX) = ⊥-elim (<ᵈ-zero-impossible nxX)
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
  ~★-nofree {A = ＇ X} (nx-var nxX) = ⊥-elim (<ᵈ-zero-impossible nxX)
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
-- Plan / Remaining theorems (next steps)
--
-- Plan:
-- 1) (Done) Prove precision transport through type substitution/opening:
--      ⊑-substᵗ, and specialized ⊑-[]ᵗ-seal.
-- 2) (Done) Add monotonicity/inversion helpers needed in arrow/forall cases:
--      ★~⇒-dom, ★~⇒-cod, ⇒~★-dom, ⇒~★-cod, ★~∀-open, ∀~★-open.
-- 3) Use these + transport lemmas (~ and ⊑ shift/rename/subst/wk) to
--    prove atomic precision-to-consistency transport under unique stores:
--      prec-leftᵃ / prec-rightᵃ.
-- 4) Lift to transitive precision:
--      prec-left / prec-right.
-- 5) Finish the target theorem:
--      upper-bounds-consistent.
--
-- Statements left to prove:
--
--   (Done) monotonicity/inversion helpers:
--     ★~⇒-dom :
--       ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
--       Σ ⊢ `★ ~ (A ⇒ B) →
--       Σ ⊢ A ~ `★
--     ★~⇒-cod :
--       ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
--       Σ ⊢ `★ ~ (A ⇒ B) →
--       Σ ⊢ `★ ~ B
--     ⇒~★-dom :
--       ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
--       Σ ⊢ (A ⇒ B) ~ `★ →
--       Σ ⊢ `★ ~ A
--     ⇒~★-cod :
--       ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
--       Σ ⊢ (A ⇒ B) ~ `★ →
--       Σ ⊢ B ~ `★
--     ★~∀-open :
--       ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ} →
--       Σ ⊢ `★ ~ (`∀ A) →
--       ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ `★ ~ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)
--     ∀~★-open :
--       ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ} →
--       Σ ⊢ (`∀ A) ~ `★ →
--       ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ~ `★
--
--   prec-leftᵃ :
--     ∀{Δ}{Ψ}{Σ : Store Ψ}{X A B : Ty Δ Ψ} →
--     Uniqueˢ Σ →
--     Σ ⊢ X ⊑ᵃ A →
--     Σ ⊢ A ~ B →
--     Σ ⊢ X ~ B
--
--   prec-rightᵃ :
--     ∀{Δ}{Ψ}{Σ : Store Ψ}{A B Y : Ty Δ Ψ} →
--     Uniqueˢ Σ →
--     Σ ⊢ A ~ B →
--     Σ ⊢ Y ⊑ᵃ B →
--     Σ ⊢ A ~ Y
--
--   prec-left :
--     ∀{Δ}{Ψ}{Σ : Store Ψ}{X A B : Ty Δ Ψ} →
--     Uniqueˢ Σ →
--     Σ ⊢ X ⊑ A →
--     Σ ⊢ A ~ B →
--     Σ ⊢ X ~ B
--
--   prec-right :
--     ∀{Δ}{Ψ}{Σ : Store Ψ}{A B Y : Ty Δ Ψ} →
--     Uniqueˢ Σ →
--     Σ ⊢ A ~ B →
--     Σ ⊢ Y ⊑ B →
--     Σ ⊢ A ~ Y
--
--   upper-bounds-consistent :
--     ∀{Δ}{Ψ}{Σ : Store Ψ}{A B C : Ty Δ Ψ} →
--     Uniqueˢ Σ →
--     Σ ⊢ A ⊑ C →
--     Σ ⊢ B ⊑ C →
--     Σ ⊢ A ~ B
--
-- Current blocker (for prec-leftᵃ / prec-rightᵃ):
-- - The hard branches are recursive seal-consistency cases (`α~A*` / `A~α*`),
--   where the goal reduces to deriving `★ ~ B` (or `B ~ ★`) from a premise of
--   the form `wkTy0 A ~ B` (or `B ~ wkTy0 A`).
-- - Existing lemmas `★~-wkTy0` / `~★-wkTy0` are not enough by themselves,
--   because we still need a transport/composition step from consistency with
--   `wkTy0 A` to consistency with `★`.
-- - A previous attempt to solve this with a very general `NoFreeXᵈ-open-inv`
--   lemma failed in nested-`∀` cases (non-definitional mismatch around
--   `extsᵗ (singleTyEnv ...)`), so the next step is to prove narrower,
--   composition-style lemmas tailored to these seal branches.
------------------------------------------------------------------------
