module TypeImprecision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans; subst)
open import Data.List using (_∷_)
open import Data.Nat using (_<_; zero; suc)
open import Types public
open import TypeSubst using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; lookupˢ-map-inv
  ; lookupˢ-map-renameᵗ
  ; map-renameStore-suc
  ; renameᵗ-preserves-WfTy
  ; renameᵗ-preserves-WfTy↑
  ; rename-[]ᵗ-commute
  ; renameᵗ-renameˢ
  ; renameˢ-[]ᵗ-commute
  ; renameˢ-commute-suc
  )

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

------------------------------------------------------------------------
-- Seal renaming preserves imprecision typing
------------------------------------------------------------------------

LookupRenameˢ : Renameˢ → Store → Store → Set
LookupRenameˢ ρ Σ₀ Σ₁ =
  ∀ {α A} →
  Σ₀ ∋ˢ α ⦂ A →
  Σ₁ ∋ˢ ρ α ⦂ renameˢ ρ A

lookupRenameˢ-suc :
  {ρ : Renameˢ} {Σ₀ Σ₁ : Store} →
  LookupRenameˢ ρ Σ₀ Σ₁ →
  LookupRenameˢ ρ (renameStoreᵗ suc Σ₀) (renameStoreᵗ suc Σ₁)
lookupRenameˢ-suc {ρ = ρ} {Σ₁ = Σ₁} hρ {α} {C} h with lookupˢ-map-inv h
... | A , (hA , eq) =
  Eq.subst
    (λ T → renameStoreᵗ suc Σ₁ ∋ˢ ρ α ⦂ T)
    (sym (cong (renameˢ ρ) eq))
    (Eq.subst
      (λ T → renameStoreᵗ suc Σ₁ ∋ˢ ρ α ⦂ T)
      (renameᵗ-renameˢ {ρ = suc} {ϱ = ρ} {A = A})
      (lookupˢ-map-renameᵗ (hρ hA)))

renameˢ-preserves-WfTy :
  (lift-ext :
     ∀ {ρ : Renameˢ} {Σ₀ Σ₁ : Store} →
     LookupRenameˢ ρ Σ₀ Σ₁ →
     LookupRenameˢ (extˢ ρ) (`★ ∷ Σ₀) (`★ ∷ Σ₁)) →
  {Δ : TyCtx} {ρ : Renameˢ} {Σ₀ Σ₁ : Store} {A : Ty} →
  LookupRenameˢ ρ Σ₀ Σ₁ →
  WfTy Δ Σ₀ A →
  WfTy Δ Σ₁ (renameˢ ρ A)
renameˢ-preserves-WfTy lift-ext hρ (wfX x<Δ) = wfX x<Δ
renameˢ-preserves-WfTy lift-ext hρ wfι = wfι
renameˢ-preserves-WfTy lift-ext hρ wf★ = wf★
renameˢ-preserves-WfTy lift-ext hρ (wfα hα) = wfα (hρ hα)
renameˢ-preserves-WfTy lift-ext hρ (wf⇒ hA hB) =
  wf⇒
    (renameˢ-preserves-WfTy lift-ext hρ hA)
    (renameˢ-preserves-WfTy lift-ext hρ hB)
renameˢ-preserves-WfTy lift-ext hρ (wf∀ hA) =
  wf∀ (renameˢ-preserves-WfTy lift-ext (lookupRenameˢ-suc hρ) hA)

mutual
  renameCImpˢ-preserves-typing :
    (lift-ext :
       ∀ {ρ : Renameˢ} {Σ₀ Σ₁ : Store} →
       LookupRenameˢ ρ Σ₀ Σ₁ →
       LookupRenameˢ (extˢ ρ) (`★ ∷ Σ₀) (`★ ∷ Σ₁)) →
    {Δ : TyCtx} {ρ : Renameˢ} {Σ₀ Σ₁ : Store} {g : CImp} {A B : Ty} →
    LookupRenameˢ ρ Σ₀ Σ₁ →
    Δ ∣ Σ₀ ⊢ᶜ g ⦂ A ⊑ B →
    Δ ∣ Σ₁ ⊢ᶜ renameCImpˢ ρ g ⦂ renameˢ ρ A ⊑ renameˢ ρ B
  renameCImpˢ-preserves-typing lift-ext hρ (⊢idα hα) =
    ⊢idα (hρ hα)
  renameCImpˢ-preserves-typing lift-ext hρ (⊢idX x<Δ) =
    ⊢idX x<Δ
  renameCImpˢ-preserves-typing lift-ext hρ ⊢idι = ⊢idι
  renameCImpˢ-preserves-typing lift-ext hρ (⊢→ᵖ hp hq) =
    ⊢→ᵖ
      (renameImpˢ-preserves-typing lift-ext hρ hp)
      (renameImpˢ-preserves-typing lift-ext hρ hq)
  renameCImpˢ-preserves-typing lift-ext hρ (⊢∀ᵖ hp) =
    ⊢∀ᵖ
      (renameImpˢ-preserves-typing lift-ext (lookupRenameˢ-suc hρ) hp)

  renameImpˢ-preserves-typing :
    (lift-ext :
       ∀ {ρ : Renameˢ} {Σ₀ Σ₁ : Store} →
       LookupRenameˢ ρ Σ₀ Σ₁ →
       LookupRenameˢ (extˢ ρ) (`★ ∷ Σ₀) (`★ ∷ Σ₁)) →
    {Δ : TyCtx} {ρ : Renameˢ} {Σ₀ Σ₁ : Store} {p : Imp} {A B : Ty} →
    LookupRenameˢ ρ Σ₀ Σ₁ →
    Δ ∣ Σ₀ ⊢ᵖ p ⦂ A ⊑ B →
    Δ ∣ Σ₁ ⊢ᵖ renameImpˢ ρ p ⦂ renameˢ ρ A ⊑ renameˢ ρ B
  renameImpˢ-preserves-typing lift-ext hρ (⊢⌈⌉ hg) =
    ⊢⌈⌉ (renameCImpˢ-preserves-typing lift-ext hρ hg)
  renameImpˢ-preserves-typing lift-ext hρ ⊢id★ = ⊢id★
  renameImpˢ-preserves-typing
    lift-ext {ρ = ρ} {Σ₁ = Σ₁}
    hρ (⊢tag {g = g} {G = G} {A = A} hg) =
    ⊢tag
      (Eq.subst
        (λ T → _ ∣ Σ₁ ⊢ᶜ renameCImpˢ ρ g ⦂ renameˢ ρ A ⊑ T)
        (renameˢ-groundTy ρ G)
        (renameCImpˢ-preserves-typing lift-ext hρ hg))
  renameImpˢ-preserves-typing lift-ext hρ (⊢seal hα hp) =
    ⊢seal
      (hρ hα)
      (renameImpˢ-preserves-typing lift-ext hρ hp)
  renameImpˢ-preserves-typing
    lift-ext {ρ = ρ} {Σ₀ = Σ₀} {Σ₁ = Σ₁}
    hρ (⊢ν {A = A} {B = B} hp hA hB) =
    ⊢ν
      body
      (renameˢ-preserves-WfTy lift-ext hρ hA)
      (renameˢ-preserves-WfTy lift-ext hρ hB)
    where
      body0 :
        _ ∣ (`★ ∷ Σ₁) ⊢ᵖ renameImpˢ (extˢ ρ) _ ⦂
        renameˢ (extˢ ρ) (((renameˢ suc A) [ ｀ zero ]ᵗ)) ⊑
        renameˢ (extˢ ρ) (renameˢ suc B)
      body0 =
        renameImpˢ-preserves-typing
          lift-ext
          (lift-ext hρ)
          hp

      source-eq :
        renameˢ (extˢ ρ) (((renameˢ suc A) [ ｀ zero ]ᵗ)) ≡
        ((renameˢ suc (renameˢ ρ A)) [ ｀ zero ]ᵗ)
      source-eq =
        trans
          (renameˢ-[]ᵗ-commute (extˢ ρ) (renameˢ suc A) zero)
          (cong (λ T → T [ ｀ zero ]ᵗ) (renameˢ-commute-suc ρ A))

      target-eq :
        renameˢ (extˢ ρ) (renameˢ suc B) ≡
        renameˢ suc (renameˢ ρ B)
      target-eq = renameˢ-commute-suc ρ B

      body :
        _ ∣ (`★ ∷ Σ₁) ⊢ᵖ renameImpˢ (extˢ ρ) _ ⦂
        ((renameˢ suc (renameˢ ρ A)) [ ｀ zero ]ᵗ) ⊑
        renameˢ suc (renameˢ ρ B)
      body =
        Eq.subst
          (λ T → _ ∣ (`★ ∷ Σ₁) ⊢ᵖ renameImpˢ (extˢ ρ) _ ⦂ T ⊑
                   renameˢ suc (renameˢ ρ B))
          source-eq
          (Eq.subst
            (λ T → _ ∣ (`★ ∷ Σ₁) ⊢ᵖ renameImpˢ (extˢ ρ) _ ⦂
                     renameˢ (extˢ ρ) (((renameˢ suc A) [ ｀ zero ]ᵗ)) ⊑ T)
            target-eq
            body0)

------------------------------------------------------------------------
-- Type renaming preserves imprecision typing
------------------------------------------------------------------------

mutual
  renameCImpᵗ-preserves-typing :
    {Δ Δ' : TyCtx} {Σ : Store} {g : CImp} {A B : Ty} {ρ : Renameᵗ} →
    TyRenameWf Δ Δ' ρ →
    Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
    Δ' ∣ renameStoreᵗ ρ Σ ⊢ᶜ renameCImpᵗ ρ g ⦂ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameCImpᵗ-preserves-typing hρ (⊢idα hα) =
    ⊢idα (lookupˢ-map-renameᵗ hα)
  renameCImpᵗ-preserves-typing hρ (⊢idX x<Δ) =
    ⊢idX (hρ x<Δ)
  renameCImpᵗ-preserves-typing hρ ⊢idι = ⊢idι
  renameCImpᵗ-preserves-typing hρ (⊢→ᵖ hp hq) =
    ⊢→ᵖ
      (renameImpᵗ-preserves-typing hρ hp)
      (renameImpᵗ-preserves-typing hρ hq)
  renameCImpᵗ-preserves-typing
    {Δ = Δ} {Δ' = Δ'} {Σ = Σ} {ρ = ρ}
    hρ (⊢∀ᵖ hp) =
    ⊢∀ᵖ (lift hp)
    where
      lift :
        {p : Imp} {A B : Ty} →
        (suc Δ) ∣ (renameStoreᵗ suc Σ) ⊢ᵖ p ⦂ A ⊑ B →
        (suc Δ') ∣ (renameStoreᵗ suc (renameStoreᵗ ρ Σ)) ⊢ᵖ
          renameImpᵗ (extᵗ ρ) p ⦂
          renameᵗ (extᵗ ρ) A ⊑ renameᵗ (extᵗ ρ) B
      lift hp =
        Eq.subst
          (λ S → (suc Δ') ∣ S ⊢ᵖ renameImpᵗ (extᵗ ρ) _ ⦂ _ ⊑ _)
          (map-renameStore-suc ρ Σ)
          (renameImpᵗ-preserves-typing (TyRenameWf-ext hρ) hp)

  renameImpᵗ-preserves-typing :
    {Δ Δ' : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} {ρ : Renameᵗ} →
    TyRenameWf Δ Δ' ρ →
    Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
    Δ' ∣ renameStoreᵗ ρ Σ ⊢ᵖ renameImpᵗ ρ p ⦂ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameImpᵗ-preserves-typing hρ (⊢⌈⌉ hg) =
    ⊢⌈⌉ (renameCImpᵗ-preserves-typing hρ hg)
  renameImpᵗ-preserves-typing hρ ⊢id★ = ⊢id★
  renameImpᵗ-preserves-typing {Δ' = Δ'} {Σ = Σ} {ρ = ρ}
    hρ (⊢tag {g = g} {G = G} {A = A} hg) =
    ⊢tag
      (Eq.subst
        (λ T → Δ' ∣ renameStoreᵗ ρ Σ ⊢ᶜ renameCImpᵗ ρ g ⦂ renameᵗ ρ A ⊑ T)
        (rename-groundTy {ρ = ρ} {G = G})
        (renameCImpᵗ-preserves-typing hρ hg))
  renameImpᵗ-preserves-typing hρ (⊢seal hα hp) =
    ⊢seal
      (lookupˢ-map-renameᵗ hα)
      (renameImpᵗ-preserves-typing hρ hp)
  renameImpᵗ-preserves-typing
    {Δ = Δ} {Δ' = Δ'} {Σ = Σ} {ρ = ρ}
    hρ (⊢ν {A = A} hp hA hB) =
    ⊢ν
      (lift {A = A} hp)
      (renameᵗ-preserves-WfTy↑ hA hρ)
      (renameᵗ-preserves-WfTy hB hρ)
    where
      lift :
        {p : Imp} {A B : Ty} →
        Δ ∣ (`★ ∷ Σ) ⊢ᵖ p ⦂ ((renameˢ suc A) [ ｀ zero ]ᵗ) ⊑ (renameˢ suc B) →
        Δ' ∣ (`★ ∷ renameStoreᵗ ρ Σ) ⊢ᵖ renameImpᵗ ρ p ⦂
        ((renameˢ suc (renameᵗ (extᵗ ρ) A)) [ ｀ zero ]ᵗ) ⊑
        (renameˢ suc (renameᵗ ρ B))
      lift {p = p} {A = A} {B = B} hp =
        Eq.subst
          (λ T → Δ' ∣ (`★ ∷ renameStoreᵗ ρ Σ) ⊢ᵖ
                   renameImpᵗ ρ p ⦂ T ⊑ renameˢ suc (renameᵗ ρ B))
          left-eq
          (Eq.subst
            (λ T → Δ' ∣ (`★ ∷ renameStoreᵗ ρ Σ) ⊢ᵖ
                     renameImpᵗ ρ p ⦂ renameᵗ ρ ((renameˢ suc A) [ ｀ zero ]ᵗ) ⊑ T)
            right-eq
            (renameImpᵗ-preserves-typing hρ hp))
        where
          left-eq :
            renameᵗ ρ ((renameˢ suc A) [ ｀ zero ]ᵗ) ≡
            (renameˢ suc (renameᵗ (extᵗ ρ) A)) [ ｀ zero ]ᵗ
          left-eq =
            trans
              (rename-[]ᵗ-commute ρ (renameˢ suc A) (｀ zero))
              (cong (λ T → T [ ｀ zero ]ᵗ)
                    (renameᵗ-renameˢ {ρ = extᵗ ρ} {ϱ = suc} {A = A}))

          right-eq :
            renameᵗ ρ (renameˢ suc B) ≡ renameˢ suc (renameᵗ ρ B)
          right-eq = renameᵗ-renameˢ {ρ = ρ} {ϱ = suc} {A = B}
