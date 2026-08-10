module SrcConsistRigidScratch where

-- File Charter:
--   * Root scratch model for the source-consistency rigid-gate preflight.
--   * Defines copied `...ʳ` gate and consistency judgments with the dossier's
--     rigid variable gates, leaving the live GTSFImp relation untouched.
--   * Checks local gate transport, occurrence repairs, source typing witnesses,
--     and a tiny modeled tag/untag runtime for rigid variable tags.
--   * Records the P1 totality obstruction that remains under the exact dossier
--     delta: opposite one-sided dynamic modes still have no same-side gate.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; trans; sym)

open import Types
open import TermCtx using (TermCtx; Z; S; ⇑ᶜ; _∋_⦂_)
open import Consistency
  using (Var∼; X∼X; X∼★; ★∼X; Env∼; idᶜ; extᵐ; flipᵐ;
         flipVar∼; instᵐ; genᵐ)
import GradualTerms as G
open import Primitives using (Const; Prim; constTy; primArgTy;
                              primResultTy; κℕ)

private
  variable
    Δ Δ′ : TyCtx
    A A′ B B′ C G : Ty Δ

------------------------------------------------------------------------
-- Rigid-gate consistency copy
------------------------------------------------------------------------

infix 4 _⊢_∼★ʳ _⊢★∼ʳ_ _⊢_∼ʳ_ _∼ʳ_

data _⊢_∼★ʳ {Δ : TyCtx} (μ : Env∼ Δ) : Ty Δ → Set where
  ⇒∼★ʳ : μ ⊢ (★ ⇒ ★) ∼★ʳ
  ι∼★ʳ : ∀ {ι} → μ ⊢ ‵ ι ∼★ʳ
  X∼★ᵍʳ : ∀ {X}
    → μ X ≡ X∼★
    → μ ⊢ ＇ X ∼★ʳ
  X∼★ʳ : ∀ {X}
    → μ X ≡ X∼X
    → μ ⊢ ＇ X ∼★ʳ
  ∀∼★ʳ : μ ⊢ (`∀ ★) ∼★ʳ

data _⊢★∼ʳ_ {Δ : TyCtx} (μ : Env∼ Δ) : Ty Δ → Set where
  ★∼⇒ʳ : μ ⊢★∼ʳ (★ ⇒ ★)
  ★∼ιʳ : ∀ {ι} → μ ⊢★∼ʳ ‵ ι
  ★∼Xᵍʳ : ∀ {X}
    → μ X ≡ ★∼X
    → μ ⊢★∼ʳ ＇ X
  ★∼Xʳ : ∀ {X}
    → μ X ≡ X∼X
    → μ ⊢★∼ʳ ＇ X
  ★∼∀ʳ : μ ⊢★∼ʳ (`∀ ★)

instance
  refl-instanceʳ : ∀ {A : Set} {x : A} → x ≡ x
  refl-instanceʳ = refl

  ∼★-⇒-instanceʳ : ∀ {Δ} {μ : Env∼ Δ}
    → μ ⊢ (★ ⇒ ★) ∼★ʳ
  ∼★-⇒-instanceʳ = ⇒∼★ʳ

  ∼★-ι-instanceʳ : ∀ {Δ} {μ : Env∼ Δ} {ι}
    → μ ⊢ ‵ ι ∼★ʳ
  ∼★-ι-instanceʳ = ι∼★ʳ

  ∼★-X-dyn-instanceʳ : ∀ {Δ} {μ : Env∼ Δ} {X}
    → ⦃ eq : μ X ≡ X∼★ ⦄
    → μ ⊢ ＇ X ∼★ʳ
  ∼★-X-dyn-instanceʳ ⦃ eq ⦄ = X∼★ᵍʳ eq

  ∼★-X-rigid-instanceʳ : ∀ {Δ} {μ : Env∼ Δ} {X}
    → ⦃ eq : μ X ≡ X∼X ⦄
    → μ ⊢ ＇ X ∼★ʳ
  ∼★-X-rigid-instanceʳ ⦃ eq ⦄ = X∼★ʳ eq

  ∼★-∀-instanceʳ : ∀ {Δ} {μ : Env∼ Δ}
    → μ ⊢ (`∀ ★) ∼★ʳ
  ∼★-∀-instanceʳ = ∀∼★ʳ

  ★∼-⇒-instanceʳ : ∀ {Δ} {μ : Env∼ Δ}
    → μ ⊢★∼ʳ (★ ⇒ ★)
  ★∼-⇒-instanceʳ = ★∼⇒ʳ

  ★∼-ι-instanceʳ : ∀ {Δ} {μ : Env∼ Δ} {ι}
    → μ ⊢★∼ʳ ‵ ι
  ★∼-ι-instanceʳ = ★∼ιʳ

  ★∼-X-dyn-instanceʳ : ∀ {Δ} {μ : Env∼ Δ} {X}
    → ⦃ eq : μ X ≡ ★∼X ⦄
    → μ ⊢★∼ʳ ＇ X
  ★∼-X-dyn-instanceʳ ⦃ eq ⦄ = ★∼Xᵍʳ eq

  ★∼-X-rigid-instanceʳ : ∀ {Δ} {μ : Env∼ Δ} {X}
    → ⦃ eq : μ X ≡ X∼X ⦄
    → μ ⊢★∼ʳ ＇ X
  ★∼-X-rigid-instanceʳ ⦃ eq ⦄ = ★∼Xʳ eq

  ★∼-∀-instanceʳ : ∀ {Δ} {μ : Env∼ Δ}
    → μ ⊢★∼ʳ (`∀ ★)
  ★∼-∀-instanceʳ = ★∼∀ʳ

flip-∼★ʳ : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
  → μ ⊢ G ∼★ʳ
  → flipᵐ μ ⊢★∼ʳ G
flip-∼★ʳ ⇒∼★ʳ = ★∼⇒ʳ
flip-∼★ʳ ι∼★ʳ = ★∼ιʳ
flip-∼★ʳ (X∼★ᵍʳ eq) = ★∼Xᵍʳ (cong flipVar∼ eq)
flip-∼★ʳ (X∼★ʳ eq) = ★∼Xʳ (cong flipVar∼ eq)
flip-∼★ʳ ∀∼★ʳ = ★∼∀ʳ

flip-★∼ʳ : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
  → μ ⊢★∼ʳ G
  → flipᵐ μ ⊢ G ∼★ʳ
flip-★∼ʳ ★∼⇒ʳ = ⇒∼★ʳ
flip-★∼ʳ ★∼ιʳ = ι∼★ʳ
flip-★∼ʳ (★∼Xᵍʳ eq) = X∼★ᵍʳ (cong flipVar∼ eq)
flip-★∼ʳ (★∼Xʳ eq) = X∼★ʳ (cong flipVar∼ eq)
flip-★∼ʳ ★∼∀ʳ = ∀∼★ʳ

rename∼★ʳ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {G : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → μ ⊢ G ∼★ʳ
  → μ′ ⊢ renameᵗ ρ G ∼★ʳ
rename∼★ʳ ρ eq ⇒∼★ʳ = ⇒∼★ʳ
rename∼★ʳ ρ eq ι∼★ʳ = ι∼★ʳ
rename∼★ʳ ρ eq (X∼★ᵍʳ {X = X} X★) =
  X∼★ᵍʳ (trans (eq X) X★)
rename∼★ʳ ρ eq (X∼★ʳ {X = X} XX) =
  X∼★ʳ (trans (eq X) XX)
rename∼★ʳ ρ eq ∀∼★ʳ = ∀∼★ʳ

rename★∼ʳ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {G : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → μ ⊢★∼ʳ G
  → μ′ ⊢★∼ʳ renameᵗ ρ G
rename★∼ʳ ρ eq ★∼⇒ʳ = ★∼⇒ʳ
rename★∼ʳ ρ eq ★∼ιʳ = ★∼ιʳ
rename★∼ʳ ρ eq (★∼Xᵍʳ {X = X} ★X) =
  ★∼Xᵍʳ (trans (eq X) ★X)
rename★∼ʳ ρ eq (★∼Xʳ {X = X} XX) =
  ★∼Xʳ (trans (eq X) XX)
rename★∼ʳ ρ eq ★∼∀ʳ = ★∼∀ʳ

data _⊢_∼ʳ_ {Δ : TyCtx} (μ : Env∼ Δ) :
    Ty Δ → Ty Δ → Set where

  idʳ : ∀ {A}
    → Atom A
    → μ ⊢ A ∼ʳ A

  _↦ʳ_ : ∀ {A A′ B B′}
    → flipᵐ μ ⊢ A′ ∼ʳ A
    → μ ⊢ B ∼ʳ B′
    → μ ⊢ (A ⇒ B) ∼ʳ (A′ ⇒ B′)

  ∀ᶜʳ_ : ∀ {A B}
    → extᵐ μ ⊢ A ∼ʳ B
    → μ ⊢ (`∀ A) ∼ʳ (`∀ B)

  tagʳ : ∀ {A G}
    → ⦃ Gᵍ : Ground G ⦄
    → ⦃ G∼★ : μ ⊢ G ∼★ʳ ⦄
    → μ ⊢ A ∼ʳ G
    → ⦃ Ans : NonStar A ⦄
    → μ ⊢ A ∼ʳ ★

  projʳ : ∀ {G B}
    → ⦃ Gᵍ : Ground G ⦄
    → ⦃ ★∼G : μ ⊢★∼ʳ G ⦄
    → μ ⊢ G ∼ʳ B
    → ⦃ Bns : NonStar B ⦄
    → μ ⊢ ★ ∼ʳ B

_∼ʳ_ : ∀ {Δ} → Ty Δ → Ty Δ → Set
A ∼ʳ B = idᶜ ⊢ A ∼ʳ B

refl∼ʳ : ∀ {Δ} {μ : Env∼ Δ} (A : Ty Δ) → μ ⊢ A ∼ʳ A
refl∼ʳ (＇ X) = idʳ (＇ X)
refl∼ʳ (‵ ι) = idʳ (‵ ι)
refl∼ʳ ★ = idʳ ★
refl∼ʳ (A ⇒ B) = refl∼ʳ A ↦ʳ refl∼ʳ B
refl∼ʳ (`∀ A) = ∀ᶜʳ refl∼ʳ A

idᵍʳ : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
  → Ground G
  → μ ⊢ G ∼ʳ G
idᵍʳ (＇ X) = idʳ (＇ X)
idᵍʳ (‵ ι) = idʳ (‵ ι)
idᵍʳ ★⇒★ = idʳ ★ ↦ʳ idʳ ★
idᵍʳ ∀★ = ∀ᶜʳ idʳ ★

variable-to-star-rigidʳ : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ X∼X
  → μ ⊢ ＇ X ∼ʳ ★
variable-to-star-rigidʳ eq =
  tagʳ ⦃ Gᵍ = ＇ _ ⦄ ⦃ G∼★ = X∼★ʳ eq ⦄
    (idʳ (＇ _)) ⦃ Ans = nonstar-X ⦄

star-to-variable-rigidʳ : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ X∼X
  → μ ⊢ ★ ∼ʳ ＇ X
star-to-variable-rigidʳ eq =
  projʳ ⦃ Gᵍ = ＇ _ ⦄ ⦃ ★∼G = ★∼Xʳ eq ⦄
    (idʳ (＇ _)) ⦃ Bns = nonstar-X ⦄

variable-to-star-dynʳ : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ X∼★
  → μ ⊢ ＇ X ∼ʳ ★
variable-to-star-dynʳ eq =
  tagʳ ⦃ Gᵍ = ＇ _ ⦄ ⦃ G∼★ = X∼★ᵍʳ eq ⦄
    (idʳ (＇ _)) ⦃ Ans = nonstar-X ⦄

star-to-variable-dynʳ : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X
  → μ ⊢ ★ ∼ʳ ＇ X
star-to-variable-dynʳ eq =
  projʳ ⦃ Gᵍ = ＇ _ ⦄ ⦃ ★∼G = ★∼Xᵍʳ eq ⦄
    (idʳ (＇ _)) ⦃ Bns = nonstar-X ⦄

------------------------------------------------------------------------
-- P1 obstruction: exact option A does not prove all-mode totality
------------------------------------------------------------------------

X∼X≢★∼X : X∼X ≢ ★∼X
X∼X≢★∼X ()

X∼★≢★∼X : X∼★ ≢ ★∼X
X∼★≢★∼X ()

X∼X≢X∼★ : X∼X ≢ X∼★
X∼X≢X∼★ ()

★∼X≢X∼★ : ★∼X ≢ X∼★
★∼X≢X∼★ ()

no-to-star-gate-from-opposite-dynamicʳ :
    ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X
  → μ ⊢ ＇ X ∼★ʳ
  → ⊥
no-to-star-gate-from-opposite-dynamicʳ ★X (X∼★ᵍʳ X★) =
  X∼★≢★∼X (trans (sym X★) ★X)
no-to-star-gate-from-opposite-dynamicʳ ★X (X∼★ʳ XX) =
  X∼X≢★∼X (trans (sym XX) ★X)

no-from-star-gate-from-opposite-dynamicʳ :
    ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ X∼★
  → μ ⊢★∼ʳ ＇ X
  → ⊥
no-from-star-gate-from-opposite-dynamicʳ X★ (★∼Xᵍʳ ★X) =
  ★∼X≢X∼★ (trans (sym ★X) X★)
no-from-star-gate-from-opposite-dynamicʳ X★ (★∼Xʳ XX) =
  X∼X≢X∼★ (trans (sym XX) X★)

no-var-to-star-from-opposite-dynamicʳ :
    ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X
  → μ ⊢ ＇ X ∼ʳ ★
  → ⊥
no-var-to-star-from-opposite-dynamicʳ ★X
    (tagʳ ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = G∼★ ⦄ (idʳ (＇ .Y))) =
  no-to-star-gate-from-opposite-dynamicʳ ★X G∼★

no-star-to-var-from-opposite-dynamicʳ :
    ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ X∼★
  → μ ⊢ ★ ∼ʳ ＇ X
  → ⊥
no-star-to-var-from-opposite-dynamicʳ X★
    (projʳ ⦃ Gᵍ = ＇ Y ⦄ ⦃ ★∼G = ★∼G ⦄ (idʳ (＇ .Y))) =
  no-from-star-gate-from-opposite-dynamicʳ X★ ★∼G

------------------------------------------------------------------------
-- P2(i): substitution environment statement repair, conditional on totality
------------------------------------------------------------------------

record Totalityʳ : Set₁ where
  field
    to-★ : ∀ {Δ} (μ : Env∼ Δ) (C : Ty Δ) → μ ⊢ C ∼ʳ ★
    from-★ : ∀ {Δ} (μ : Env∼ Δ) (C : Ty Δ) → μ ⊢ ★ ∼ʳ C

record SubstEnv∼ʳ {Δ Δ′ : TyCtx}
    (μ : Env∼ Δ) (ν : Env∼ Δ′) (σ : Δ ⇒ˢ Δ′) : Set where
  constructor subst-env∼ʳ
  field
    self : ∀ X → ν ⊢ σ X ∼ʳ σ X
    to-★ᵍ : ∀ X → μ X ≡ X∼★ → ν ⊢ σ X ∼ʳ ★
    from-★ᵍ : ∀ X → μ X ≡ ★∼X → ν ⊢ ★ ∼ʳ σ X
    rigid-to-★ : ∀ X → μ X ≡ X∼X → ν ⊢ σ X ∼ʳ ★
    rigid-from-★ : ∀ X → μ X ≡ X∼X → ν ⊢ ★ ∼ʳ σ X

open SubstEnv∼ʳ

total-subst-env∼ʳ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {σ : Δ ⇒ˢ Δ′}
  → Totalityʳ
  → SubstEnv∼ʳ μ ν σ
total-subst-env∼ʳ {ν = ν} {σ = σ} T =
  subst-env∼ʳ
    (λ X → refl∼ʳ (σ X))
    (λ X eq → Totalityʳ.to-★ T ν (σ X))
    (λ X eq → Totalityʳ.from-★ T ν (σ X))
    (λ X eq → Totalityʳ.to-★ T ν (σ X))
    (λ X eq → Totalityʳ.from-★ T ν (σ X))

ext-SubstEnv∼ʳ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {σ : Δ ⇒ˢ Δ′}
  → Totalityʳ
  → SubstEnv∼ʳ μ ν σ
  → SubstEnv∼ʳ (extᵐ μ) (extᵐ ν) (extsᵗ σ)
ext-SubstEnv∼ʳ T s = total-subst-env∼ʳ T

flip-SubstEnv∼ʳ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {σ : Δ ⇒ˢ Δ′}
  → Totalityʳ
  → SubstEnv∼ʳ μ ν σ
  → SubstEnv∼ʳ (flipᵐ μ) (flipᵐ ν) σ
flip-SubstEnv∼ʳ T s = total-subst-env∼ʳ T

subst-to-star-var-rigidʳ : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′} {X}
  → SubstEnv∼ʳ μ ν σ
  → μ X ≡ X∼X
  → ν ⊢ σ X ∼ʳ ★
subst-to-star-var-rigidʳ s eq = rigid-to-★ s _ eq

subst-from-star-var-rigidʳ : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′} {X}
  → SubstEnv∼ʳ μ ν σ
  → μ X ≡ X∼X
  → ν ⊢ ★ ∼ʳ σ X
subst-from-star-var-rigidʳ s eq = rigid-from-★ s _ eq

------------------------------------------------------------------------
-- P2(ii): occurrence statements weaken to dynamic-or-rigid
------------------------------------------------------------------------

ground-occurs-to-starʳ : ∀ {Δ} {μ : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → μ ⊢ G ∼★ʳ
  → X ∈ᵗ G
  → μ X ≡ X∼★ ⊎ μ X ≡ X∼X
ground-occurs-to-starʳ ⇒∼★ʳ (∈-fun-left ())
ground-occurs-to-starʳ ⇒∼★ʳ (∈-fun-right X∉A ())
ground-occurs-to-starʳ ι∼★ʳ ()
ground-occurs-to-starʳ (X∼★ᵍʳ eq) var-∈ = inj₁ eq
ground-occurs-to-starʳ (X∼★ʳ eq) var-∈ = inj₂ eq
ground-occurs-to-starʳ ∀∼★ʳ (∈-all ())

ground-occurs-from-starʳ : ∀ {Δ} {μ : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → μ ⊢★∼ʳ G
  → X ∈ᵗ G
  → μ X ≡ ★∼X ⊎ μ X ≡ X∼X
ground-occurs-from-starʳ ★∼⇒ʳ (∈-fun-left ())
ground-occurs-from-starʳ ★∼⇒ʳ (∈-fun-right X∉A ())
ground-occurs-from-starʳ ★∼ιʳ ()
ground-occurs-from-starʳ (★∼Xᵍʳ eq) var-∈ = inj₁ eq
ground-occurs-from-starʳ (★∼Xʳ eq) var-∈ = inj₂ eq
ground-occurs-from-starʳ ★∼∀ʳ (∈-all ())

------------------------------------------------------------------------
-- P2(iii): lower-bound rigid tag route, isolated at the variable case
------------------------------------------------------------------------

data VarImpʳ : Set where
  X⊑Xʳ : VarImpʳ
  X⊑★ʳ : VarImpʳ

data VarLowerʳ : Var∼ → VarImpʳ → VarImpʳ → Set where
  var-reflʳ : VarLowerʳ X∼X X⊑Xʳ X⊑Xʳ
  var-to-starʳ : VarLowerʳ X∼★ X⊑Xʳ X⊑★ʳ
  var-from-starʳ : VarLowerʳ ★∼X X⊑★ʳ X⊑Xʳ
  both-to-starʳ : VarLowerʳ X∼X X⊑★ʳ X⊑★ʳ

X⊑X≢X⊑★ʳ : X⊑Xʳ ≢ X⊑★ʳ
X⊑X≢X⊑★ʳ ()

right-star-from-var-lower-rigid-bothʳ :
  VarLowerʳ X∼X X⊑★ʳ X⊑★ʳ → X⊑★ʳ ≡ X⊑★ʳ
right-star-from-var-lower-rigid-bothʳ both-to-starʳ = refl

left-star-from-var-lower-rigid-bothʳ :
  VarLowerʳ X∼X X⊑★ʳ X⊑★ʳ → X⊑★ʳ ≡ X⊑★ʳ
left-star-from-var-lower-rigid-bothʳ both-to-starʳ = refl

right-star-from-var-lower-rigid-var-refl-blockedʳ :
  VarLowerʳ X∼X X⊑Xʳ X⊑Xʳ → X⊑Xʳ ≡ X⊑★ʳ → ⊥
right-star-from-var-lower-rigid-var-refl-blockedʳ var-reflʳ eq =
  X⊑X≢X⊑★ʳ eq

left-star-from-var-lower-rigid-var-refl-blockedʳ :
  VarLowerʳ X∼X X⊑Xʳ X⊑Xʳ → X⊑Xʳ ≡ X⊑★ʳ → ⊥
left-star-from-var-lower-rigid-var-refl-blockedʳ var-reflʳ eq =
  X⊑X≢X⊑★ʳ eq

rigid-self-ground-occurs-now-possibleʳ : ∀ {Δ} {μ : Env∼ Δ}
    {X : TyVar Δ}
  → μ X ≡ X∼X
  → μ ⊢ ＇ X ∼★ʳ
rigid-self-ground-occurs-now-possibleʳ = X∼★ʳ

------------------------------------------------------------------------
-- P2(iv): fresh consistency gains an A = ★ case
------------------------------------------------------------------------

data FreshShapeʳ {Δ : TyCtx} : Ty (suc Δ) → Set where
  fresh-varʳ : FreshShapeʳ (＇ Fin.zero)
  fresh-starʳ : FreshShapeʳ ★

consistency-to-fresh-proj-caseʳ : ∀ {Δ} {μ : Env∼ Δ}
  → FreshShapeʳ {Δ} ★
consistency-to-fresh-proj-caseʳ = fresh-starʳ

fresh-rigid-star-to-zeroʳ : ∀ {Δ} {μ : Env∼ Δ}
  → extᵐ μ ⊢ ★ ∼ʳ ＇ Fin.zero
fresh-rigid-star-to-zeroʳ = star-to-variable-rigidʳ refl

------------------------------------------------------------------------
-- Scratch source typing that uses `_∼ʳ_`
------------------------------------------------------------------------

infix 4 _∣_⊢ᴳʳ_⦂_

data _∣_⊢ᴳʳ_⦂_ (Δ : TyCtx) (Γ : TermCtx Δ) :
    G.GTerm Δ → Ty Δ → Set where

  ⊢`ʳ : ∀ {x A}
    → Γ ∋ x ⦂ A
    → Δ ∣ Γ ⊢ᴳʳ (G.` x) ⦂ A

  ⊢ƛʳ : ∀ {M A B}
    → Δ ∣ (A ∷ Γ) ⊢ᴳʳ M ⦂ B
    → Δ ∣ Γ ⊢ᴳʳ (G.ƛ A ⇒ M) ⦂ (A ⇒ B)

  ⊢·ʳ : ∀ {L M A A′ B ℓ}
    → Δ ∣ Γ ⊢ᴳʳ L ⦂ (A ⇒ B)
    → Δ ∣ Γ ⊢ᴳʳ M ⦂ A′
    → A ∼ʳ A′
    → Δ ∣ Γ ⊢ᴳʳ L G.·[ ℓ ] M ⦂ B

  ⊢·★ʳ : ∀ {L M A′ ℓ}
    → Δ ∣ Γ ⊢ᴳʳ L ⦂ ★
    → Δ ∣ Γ ⊢ᴳʳ M ⦂ A′
    → A′ ∼ʳ ★
    → Δ ∣ Γ ⊢ᴳʳ L G.·[ ℓ ] M ⦂ ★

  ⊢Λʳ : ∀ {M A} {zero∈A : Fin.zero ∈ᵗ A}
    → G.Value M
    → (suc Δ) ∣ ⇑ᶜ Γ ⊢ᴳʳ M ⦂ A
    → Δ ∣ Γ ⊢ᴳʳ G.Λ M ⦂ (`∀ A)

  ⊢•ʳ : ∀ {M B A}
    → Δ ∣ Γ ⊢ᴳʳ M ⦂ (`∀ B)
    → Δ ∣ Γ ⊢ᴳʳ M G.`[ A ] ⦂ B [ A ]ᵗ

  ⊢$ʳ : ∀ (κ : Const)
    → Δ ∣ Γ ⊢ᴳʳ G.$ κ ⦂ constTy κ

  ⊢⊕ʳ : ∀ {L M A B ℓ}
    → (op : Prim)
    → Δ ∣ Γ ⊢ᴳʳ L ⦂ A
    → A ∼ʳ primArgTy op
    → Δ ∣ Γ ⊢ᴳʳ M ⦂ B
    → B ∼ʳ primArgTy op
    → Δ ∣ Γ ⊢ᴳʳ L G.⊕[ op at ℓ ] M ⦂ primResultTy op

Z∼★-idʳ : idᶜ {Δ = 1} ⊢ ＇ Fin.zero ∼ʳ ★
Z∼★-idʳ = variable-to-star-rigidʳ refl

★∼Z-idʳ : idᶜ {Δ = 1} ⊢ ★ ∼ʳ ＇ Fin.zero
★∼Z-idʳ = star-to-variable-rigidʳ refl

Z∼★-id-anyʳ : ∀ {Δ}
  → idᶜ {Δ = suc Δ} ⊢ ＇ Fin.zero ∼ʳ ★
Z∼★-id-anyʳ = variable-to-star-rigidʳ refl

★∼Z-id-anyʳ : ∀ {Δ}
  → idᶜ {Δ = suc Δ} ⊢ ★ ∼ʳ ＇ Fin.zero
★∼Z-id-anyʳ = star-to-variable-rigidʳ refl

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

★∼ℕʳ : ★ ∼ʳ ℕ₀
★∼ℕʳ = projʳ ⦃ Gᵍ = ‵ `ℕ ⦄ ⦃ ★∼G = ★∼ιʳ ⦄
  (idʳ (‵ `ℕ)) ⦃ Bns = nonstar-ι ⦄

X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X = ＇ Fin.zero ⇒ ＇ Fin.zero

blocked-termʳ : G.GTerm 0
blocked-termʳ =
  G.Λ (G.ƛ ＇ Fin.zero ⇒ ((G.ƛ ★ ⇒ G.` 0) G.·[ 0 ] G.` 0))

blocked-typingʳ :
  0 ∣ [] ⊢ᴳʳ blocked-termʳ ⦂ `∀ (＇ Fin.zero ⇒ ★)
blocked-typingʳ =
  ⊢Λʳ {zero∈A = ∈-fun-left var-∈}
    (G.ƛ ＇ Fin.zero ⇒ ((G.ƛ ★ ⇒ G.` 0) G.·[ 0 ] G.` 0))
    (⊢ƛʳ (⊢·ʳ (⊢ƛʳ (⊢`ʳ Z)) (⊢`ʳ Z) ★∼Z-idʳ))

blocked-compile-argument-castʳ :
  idᶜ {Δ = 1} ⊢ ＇ Fin.zero ∼ʳ ★
blocked-compile-argument-castʳ = Z∼★-idʳ

roundInnerᴳʳ : ∀ {Δ} → G.GTerm Δ
roundInnerᴳʳ =
  G.Λ
    (G.ƛ ＇ Fin.zero ⇒
      ((G.ƛ ＇ Fin.zero ⇒ G.` 0) G.·[ 80 ]
        (((G.ƛ ★ ⇒ G.` 0) G.·[ 81 ] G.` 0))))

roundInner-typingʳ : ∀ {Δ} {Γ : TermCtx Δ}
  → Δ ∣ Γ ⊢ᴳʳ roundInnerᴳʳ ⦂ `∀ X⇒X
roundInner-typingʳ =
  ⊢Λʳ {zero∈A = ∈-fun-left var-∈}
    (G.ƛ ＇ Fin.zero ⇒
      ((G.ƛ ＇ Fin.zero ⇒ G.` 0) G.·[ 80 ]
        (((G.ƛ ★ ⇒ G.` 0) G.·[ 81 ] G.` 0))))
    (⊢ƛʳ
      (⊢·ʳ
        (⊢ƛʳ (⊢`ʳ Z))
        (⊢·ʳ (⊢ƛʳ (⊢`ʳ Z)) (⊢`ʳ Z) ★∼Z-id-anyʳ)
        Z∼★-id-anyʳ))

Pᴳʳ : G.GTerm 0
Pᴳʳ =
  (((G.Λ
      (G.ƛ ＇ Fin.zero ⇒
        ((roundInnerᴳʳ {Δ = 1} G.`[ ＇ Fin.zero ])
          G.·[ 82 ] G.` 0)))
    G.`[ ★ ])
    G.·[ 83 ] G.$ (κℕ 0))

P-typingʳ : 0 ∣ [] ⊢ᴳʳ Pᴳʳ ⦂ ★
P-typingʳ =
  ⊢·ʳ
    (⊢•ʳ
      (⊢Λʳ {zero∈A = ∈-fun-left var-∈}
        (G.ƛ ＇ Fin.zero ⇒
          ((roundInnerᴳʳ {Δ = 1} G.`[ ＇ Fin.zero ])
            G.·[ 82 ] G.` 0))
        (⊢ƛʳ
          (⊢·ʳ (⊢•ʳ roundInner-typingʳ) (⊢`ʳ Z)
            (idʳ (＇ Fin.zero))))))
    (⊢$ʳ (κℕ 0))
    ★∼ℕʳ

Qᴳʳ : G.GTerm 0
Qᴳʳ =
  (G.ƛ ★ ⇒
    ((roundInnerᴳʳ {Δ = 0} G.`[ ★ ]) G.·[ 82 ] G.` 0))
  G.·[ 83 ] G.$ (κℕ 0)

Q-typingʳ : 0 ∣ [] ⊢ᴳʳ Qᴳʳ ⦂ ★
Q-typingʳ =
  ⊢·ʳ
    (⊢ƛʳ
      (⊢·ʳ (⊢•ʳ roundInner-typingʳ) (⊢`ʳ Z) (idʳ ★)))
    (⊢$ʳ (κℕ 0))
    ★∼ℕʳ

------------------------------------------------------------------------
-- P3 modeled rigid tag runtime
------------------------------------------------------------------------

data CastNameʳ : Set where
  Xtagʳ : CastNameʳ
  Ytagʳ : CastNameʳ

data MiniTermʳ : Set where
  payloadʳ : MiniTermʳ
  blameʳ : MiniTermʳ
  tagʳ[_]_ : CastNameʳ → MiniTermʳ → MiniTermʳ
  untagʳ[_]_ : CastNameʳ → MiniTermʳ → MiniTermʳ

infix 2 _—→miniʳ_

data _—→miniʳ_ : MiniTermʳ → MiniTermʳ → Set where
  tag-untagʳ :
    untagʳ[ Xtagʳ ] (tagʳ[ Xtagʳ ] payloadʳ) —→miniʳ payloadʳ

  tag-untag-badʳ :
    untagʳ[ Ytagʳ ] (tagʳ[ Xtagʳ ] payloadʳ) —→miniʳ blameʳ

same-rigid-tag-traceʳ :
  untagʳ[ Xtagʳ ] (tagʳ[ Xtagʳ ] payloadʳ) —→miniʳ payloadʳ
same-rigid-tag-traceʳ = tag-untagʳ

different-rigid-tag-traceʳ :
  untagʳ[ Ytagʳ ] (tagʳ[ Xtagʳ ] payloadʳ) —→miniʳ blameʳ
different-rigid-tag-traceʳ = tag-untag-badʳ
