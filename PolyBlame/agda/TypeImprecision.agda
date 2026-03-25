module TypeImprecision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Data.List using (_∷_)
open import Data.Nat using (_<_; zero; suc)
open import Types public

------------------------------------------------------------------------
-- Grounds and imprecision syntax
------------------------------------------------------------------------

data Ground : Set where
  G-α    : Seal → Ground
  G-ι    : Base → Ground
  G-★⇒★  : Ground

groundTy : Ground → Ty
groundTy (G-α α)   = ｀ α
groundTy (G-ι ι)   = ‵ ι
groundTy G-★⇒★     = `★ ⇒ `★

mutual
  data CImp : Set where
    idα   : Seal → CImp
    idX   : TyVar → CImp
    idι   : Base → CImp
    _→ᵖ_  : Imp → Imp → CImp
    ∀ᵖ_   : Imp → CImp

  data Imp : Set where
    ⌈_⌉       : CImp → Imp
    id★       : Imp
    injTag    : CImp → Ground → Imp
    sealImp   : Seal → Imp → Imp
    nuImp     : Imp → Imp

------------------------------------------------------------------------
-- Type-variable renaming/substitution on imprecision
------------------------------------------------------------------------

renameGroundᵗ : Renameᵗ → Ground → Ground
renameGroundᵗ ρ (G-α α)   = G-α α
renameGroundᵗ ρ (G-ι ι)   = G-ι ι
renameGroundᵗ ρ G-★⇒★     = G-★⇒★

rename-groundTy :
  {ρ : Renameᵗ} {G : Ground} →
  renameᵗ ρ (groundTy G) ≡ groundTy (renameGroundᵗ ρ G)
rename-groundTy {G = G-α α} = refl
rename-groundTy {G = G-ι ι} = refl
rename-groundTy {G = G-★⇒★} = refl

mutual
  renameGroundˢ : Renameˢ → Ground → Ground
  renameGroundˢ ρ (G-α α)   = G-α (ρ α)
  renameGroundˢ ρ (G-ι ι)   = G-ι ι
  renameGroundˢ ρ G-★⇒★     = G-★⇒★

  renameCImpˢ : Renameˢ → CImp → CImp
  renameCImpˢ ρ (idα α)      = idα (ρ α)
  renameCImpˢ ρ (idX X)      = idX X
  renameCImpˢ ρ (idι ι)      = idι ι
  renameCImpˢ ρ (p →ᵖ q)     = renameImpˢ ρ p →ᵖ renameImpˢ ρ q
  renameCImpˢ ρ (∀ᵖ p)       = ∀ᵖ (renameImpˢ ρ p)

  renameImpˢ : Renameˢ → Imp → Imp
  renameImpˢ ρ ⌈ g ⌉         = ⌈ renameCImpˢ ρ g ⌉
  renameImpˢ ρ id★           = id★
  renameImpˢ ρ (injTag g G)  = injTag (renameCImpˢ ρ g) (renameGroundˢ ρ G)
  renameImpˢ ρ (sealImp α p) = sealImp (ρ α) (renameImpˢ ρ p)
  renameImpˢ ρ (nuImp p)     = nuImp (renameImpˢ (extˢ ρ) p)

openCImpˢ : Seal → CImp → CImp
openCImpˢ α p = renameCImpˢ (singleSealEnv α) p

openImpˢ : Seal → Imp → Imp
openImpˢ α p = renameImpˢ (singleSealEnv α) p

mutual
  renameCImpᵗ : Renameᵗ → CImp → CImp
  renameCImpᵗ ρ (idα α)      = idα α
  renameCImpᵗ ρ (idX X)      = idX (ρ X)
  renameCImpᵗ ρ (idι ι)      = idι ι
  renameCImpᵗ ρ (p →ᵖ q)     = renameImpᵗ ρ p →ᵖ renameImpᵗ ρ q
  renameCImpᵗ ρ (∀ᵖ p)       = ∀ᵖ (renameImpᵗ (extᵗ ρ) p)

  renameImpᵗ : Renameᵗ → Imp → Imp
  renameImpᵗ ρ ⌈ g ⌉         = ⌈ renameCImpᵗ ρ g ⌉
  renameImpᵗ ρ id★           = id★
  renameImpᵗ ρ (injTag g G)  = injTag (renameCImpᵗ ρ g) (renameGroundᵗ ρ G)
  renameImpᵗ ρ (sealImp α p) = sealImp α (renameImpᵗ ρ p)
  renameImpᵗ ρ (nuImp p)     = nuImp (renameImpᵗ ρ p)

renameˢ-groundTy :
  (ρ : Renameˢ) (G : Ground) →
  renameˢ ρ (groundTy G) ≡ groundTy (renameGroundˢ ρ G)
renameˢ-groundTy ρ (G-α α) = refl
renameˢ-groundTy ρ (G-ι ι) = refl
renameˢ-groundTy ρ G-★⇒★ = refl

mutual
  renameGroundᵗ-renameGroundˢ :
    {ρ : Renameᵗ} {ϱ : Renameˢ} {G : Ground} →
    renameGroundᵗ ρ (renameGroundˢ ϱ G) ≡
    renameGroundˢ ϱ (renameGroundᵗ ρ G)
  renameGroundᵗ-renameGroundˢ {ρ} {ϱ} {G-α α} = refl
  renameGroundᵗ-renameGroundˢ {ρ} {ϱ} {G-ι ι} = refl
  renameGroundᵗ-renameGroundˢ {ρ} {ϱ} {G-★⇒★} = refl

  renameCImpᵗ-renameCImpˢ :
    {ρ : Renameᵗ} {ϱ : Renameˢ} {g : CImp} →
    renameCImpᵗ ρ (renameCImpˢ ϱ g) ≡
    renameCImpˢ ϱ (renameCImpᵗ ρ g)
  renameCImpᵗ-renameCImpˢ {ρ} {ϱ} {idα α} = refl
  renameCImpᵗ-renameCImpˢ {ρ} {ϱ} {idX X} = refl
  renameCImpᵗ-renameCImpˢ {ρ} {ϱ} {idι ι} = refl
  renameCImpᵗ-renameCImpˢ {ρ} {ϱ} {p →ᵖ q} =
    cong₂ _→ᵖ_
          (renameImpᵗ-renameImpˢ {ρ = ρ} {ϱ = ϱ} {p = p})
          (renameImpᵗ-renameImpˢ {ρ = ρ} {ϱ = ϱ} {p = q})
  renameCImpᵗ-renameCImpˢ {ρ} {ϱ} {∀ᵖ p} =
    cong ∀ᵖ_ (renameImpᵗ-renameImpˢ {ρ = extᵗ ρ} {ϱ = ϱ} {p = p})

  renameImpᵗ-renameImpˢ :
    {ρ : Renameᵗ} {ϱ : Renameˢ} {p : Imp} →
    renameImpᵗ ρ (renameImpˢ ϱ p) ≡
    renameImpˢ ϱ (renameImpᵗ ρ p)
  renameImpᵗ-renameImpˢ {ρ} {ϱ} {⌈ g ⌉} =
    cong ⌈_⌉ (renameCImpᵗ-renameCImpˢ {ρ = ρ} {ϱ = ϱ} {g = g})
  renameImpᵗ-renameImpˢ {ρ} {ϱ} {id★} = refl
  renameImpᵗ-renameImpˢ {ρ} {ϱ} {injTag g G} =
    cong₂ injTag
          (renameCImpᵗ-renameCImpˢ {ρ = ρ} {ϱ = ϱ} {g = g})
          (renameGroundᵗ-renameGroundˢ {ρ = ρ} {ϱ = ϱ} {G = G})
  renameImpᵗ-renameImpˢ {ρ} {ϱ} {sealImp α p} =
    cong (sealImp (ϱ α))
         (renameImpᵗ-renameImpˢ {ρ = ρ} {ϱ = ϱ} {p = p})
  renameImpᵗ-renameImpˢ {ρ} {ϱ} {nuImp p} =
    cong nuImp
         (renameImpᵗ-renameImpˢ {ρ = ρ} {ϱ = extˢ ϱ} {p = p})

-- TODO: rename "atomize" to "mk-id"
-- Convert α type into an identity imprecision witness.
-- This is used when substituting α type variable inside
-- an imprecision witness; those uses are guarded by TySubstIsVar, so the `★`
-- branch is only α totality fallback.
atomize : Ty → CImp
atomize (＇ X)   = idX X
atomize (｀ α)   = idα α
atomize (‵ ι)   = idι ι
atomize `★       = idι `ℕ
atomize (A ⇒ B)  = (⌈ atomize A ⌉) →ᵖ (⌈ atomize B ⌉)
atomize (`∀ A)   = ∀ᵖ (⌈ atomize A ⌉)

mutual
  substCImpᵗ : Substᵗ → CImp → CImp
  substCImpᵗ σ (idα α)      = idα α
  substCImpᵗ σ (idX X)      = atomize (σ X)
  substCImpᵗ σ (idι ι)      = idι ι
  substCImpᵗ σ (p →ᵖ q)     = substImpᵗ σ p →ᵖ substImpᵗ σ q
  substCImpᵗ σ (∀ᵖ p)       = ∀ᵖ (substImpᵗ (extsᵗ σ) p)

  substImpᵗ : Substᵗ → Imp → Imp
  substImpᵗ σ ⌈ g ⌉         = ⌈ substCImpᵗ σ g ⌉
  substImpᵗ σ id★           = id★
  substImpᵗ σ (injTag g G)  = injTag (substCImpᵗ σ g) G
  substImpᵗ σ (sealImp α p) = sealImp α (substImpᵗ σ p)
  substImpᵗ σ (nuImp p)     = nuImp (substImpᵗ σ p)

Substᶜ : Set
Substᶜ = TyVar → CImp

extsᶜ : Substᶜ → Substᶜ
extsᶜ σ zero    = idX zero
extsᶜ σ (suc X) = renameCImpᵗ suc (σ X)

mutual
  substCImpᶜ : Substᶜ → CImp → CImp
  substCImpᶜ σ (idα α)      = idα α
  substCImpᶜ σ (idX X)      = σ X
  substCImpᶜ σ (idι ι)      = idι ι
  substCImpᶜ σ (p →ᵖ q)     = substImpᶜ σ p →ᵖ substImpᶜ σ q
  substCImpᶜ σ (∀ᵖ p)       = ∀ᵖ (substImpᶜ (extsᶜ σ) p)

  substImpᶜ : Substᶜ → Imp → Imp
  substImpᶜ σ ⌈ g ⌉         = ⌈ substCImpᶜ σ g ⌉
  substImpᶜ σ id★           = id★
  substImpᶜ σ (injTag g G)  = injTag (substCImpᶜ σ g) G
  substImpᶜ σ (sealImp α p) = sealImp α (substImpᶜ σ p)
  substImpᶜ σ (nuImp p)     = nuImp (substImpᶜ σ p)

subst-groundTy :
  {σ : Substᵗ} {G : Ground} →
  substᵗ σ (groundTy G) ≡ groundTy G
subst-groundTy {G = G-α α} = refl
subst-groundTy {G = G-ι ι} = refl
subst-groundTy {G = G-★⇒★} = refl

singleCEnvα : Seal → Substᶜ
singleCEnvα α zero    = idα α
singleCEnvα α (suc X) = idX X

_[_]ᴾ : Imp → Ty → Imp
p [ A ]ᴾ = substImpᵗ (singleTyEnv A) p

_[_]ᴾα : Imp → Seal → Imp
p [ α ]ᴾα = substImpᶜ (singleCEnvα α) p

------------------------------------------------------------------------
-- Typing: imprecision
------------------------------------------------------------------------

infix 4 _∣_⊢ᶜ_⦂_⊑_
infix 4 _∣_⊢ᵖ_⦂_⊑_

mutual
  data _∣_⊢ᶜ_⦂_⊑_ (Δ : TyCtx) (Σ : Store)
      : CImp → Ty → Ty → Set where

    ⊢idα : {α : Seal} {A : Ty} →
           Σ ∋ˢ α ⦂ A →
           Δ ∣ Σ ⊢ᶜ idα α ⦂ ｀ α ⊑ ｀ α

    ⊢idX : {X : TyVar} →
           X < Δ →
           Δ ∣ Σ ⊢ᶜ idX X ⦂ ＇ X ⊑ ＇ X

    ⊢idι : {ι : Base} →
           Δ ∣ Σ ⊢ᶜ idι ι ⦂ ‵ ι ⊑ ‵ ι

    ⊢→ᵖ  : {p q : Imp} {A A' B B' : Ty} →
           Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ A' →
           Δ ∣ Σ ⊢ᵖ q ⦂ B ⊑ B' →
           Δ ∣ Σ ⊢ᶜ (p →ᵖ q) ⦂ (A ⇒ B) ⊑ (A' ⇒ B')

    ⊢∀ᵖ  : {p : Imp} {A B : Ty} →
           (suc Δ) ∣ (renameStoreᵗ suc Σ) ⊢ᵖ p ⦂ A ⊑ B →
           Δ ∣ Σ ⊢ᶜ (∀ᵖ p) ⦂ `∀ A ⊑ `∀ B

  data _∣_⊢ᵖ_⦂_⊑_ (Δ : TyCtx) (Σ : Store)
      : Imp → Ty → Ty → Set where

    ⊢⌈⌉   : {g : CImp} {A B : Ty} →
            Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
            Δ ∣ Σ ⊢ᵖ ⌈ g ⌉ ⦂ A ⊑ B

    ⊢id★  : Δ ∣ Σ ⊢ᵖ id★ ⦂ `★ ⊑ `★

    ⊢tag : {g : CImp} {G : Ground} {A : Ty} →
            Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ groundTy G →
            Δ ∣ Σ ⊢ᵖ (injTag g G) ⦂ A ⊑ `★

    ⊢seal : {α : Seal} {A B : Ty} {p : Imp} →
            Σ ∋ˢ α ⦂ A →
            Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
            Δ ∣ Σ ⊢ᵖ (sealImp α p) ⦂ ｀ α ⊑ B

    ⊢ν    : {A B : Ty} {p : Imp} →
            Δ ∣ (`★ ∷ Σ) ⊢ᵖ p ⦂ ((renameˢ suc A) [ ｀ zero ]ᵗ) ⊑ (renameˢ suc B) →
            WfTy (suc Δ) Σ A →
            WfTy Δ Σ B →
            Δ ∣ Σ ⊢ᵖ (nuImp p) ⦂ `∀ A ⊑ B
