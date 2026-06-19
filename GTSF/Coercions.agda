-- This is based on the cambridge22 notes.

module Coercions where

-- File Charter:
--   * Raw coercion syntax, endpoint functions, duality, renaming/substitution,
--     and the redesigned telescope-indexed coercion typing judgment.
--   * Regular type variables and seals are separate de Bruijn namespaces; `∀`
--     binds regular type variables, while `sealᵉ` telescope entries bind seals.
--   * Coercion metatheory lives in `proof/CoercionProperties.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)

open import Types

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Seal binders in coercions
------------------------------------------------------------------------

insertTyVar : TyVar → TyVar → TyVar
insertTyVar zero X = suc X
insertTyVar (suc X) zero = zero
insertTyVar (suc X) (suc Y) = suc (insertTyVar X Y)

openTyVarWithSeal : TyVar → TyVar → Ty
openTyVarWithSeal zero zero = `α zero
openTyVarWithSeal zero (suc X) = `X X
openTyVarWithSeal (suc X) zero = `X zero
openTyVarWithSeal (suc X) (suc Y) = ⇑ᵗ (openTyVarWithSeal X Y)

openTyWithSealAt : TyVar → Ty → Ty
openTyWithSealAt X (`X Y) = openTyVarWithSeal X Y
openTyWithSealAt X (`α α) = `α (suc α)
openTyWithSealAt X (‵ ι) = ‵ ι
openTyWithSealAt X ★ = ★
openTyWithSealAt X (A ⇒ B) = openTyWithSealAt X A ⇒ openTyWithSealAt X B
openTyWithSealAt X (`∀ A) = `∀ (openTyWithSealAt (suc X) A)

openTyWithSeal : Ty → Ty
openTyWithSeal = openTyWithSealAt zero

closeSealWithTyAt : TyVar → Ty → Ty
closeSealWithTyAt X (`X Y) = `X (insertTyVar X Y)
closeSealWithTyAt X (`α zero) = `X X
closeSealWithTyAt X (`α (suc α)) = `α α
closeSealWithTyAt X (‵ ι) = ‵ ι
closeSealWithTyAt X ★ = ★
closeSealWithTyAt X (A ⇒ B) = closeSealWithTyAt X A ⇒ closeSealWithTyAt X B
closeSealWithTyAt X (`∀ A) = `∀ (closeSealWithTyAt (suc X) A)

closeSealWithTy : Ty → Ty
closeSealWithTy = closeSealWithTyAt zero

dropSeal : Ty → Ty
dropSeal (`X X) = `X X
dropSeal (`α zero) = `α zero
dropSeal (`α (suc α)) = `α α
dropSeal (‵ ι) = ‵ ι
dropSeal ★ = ★
dropSeal (A ⇒ B) = dropSeal A ⇒ dropSeal B
dropSeal (`∀ A) = `∀ (dropSeal A)

------------------------------------------------------------------------
-- Raw coercions
------------------------------------------------------------------------

data Coercion : Set where
 id : Ty → Coercion
 _︔_ : Coercion → Coercion → Coercion
 _↦_ : Coercion → Coercion → Coercion
 `∀ : Coercion → Coercion
 _! : Ty → Coercion
 _？ : Ty → Coercion
 seal : Ty → SealVar → Coercion
 unseal : SealVar → Ty → Coercion
 gen : Coercion → Coercion
 inst : Coercion → Coercion

------------------------------------------------------------------------
-- Source and target type of a coercion
------------------------------------------------------------------------

src : Coercion → Ty
tgt : Coercion → Ty

src (id A) = A
src (c ︔ d) = src c
src (c ↦ d) = tgt c ⇒ src d
src (`∀ c) = `∀ (src c)
src (G !) = G
src (G ？) = ★
src (seal A α) = A
src (unseal α A) = `α α
src (gen c) = dropSeal (src c)
src (inst c) = `∀ (closeSealWithTy (src c))

tgt (id A) = A
tgt (c ︔ d) = tgt d
tgt (c ↦ d) = src c ⇒ tgt d
tgt (`∀ c) = `∀ (tgt c)
tgt (G !) = ★
tgt (H ？) = H
tgt (seal A α) = `α α
tgt (unseal α B) = B
tgt (gen c) = `∀ (closeSealWithTy (tgt c))
tgt (inst c) = dropSeal (tgt c)

------------------------------------------------------------------------
-- Inert coercions, i.e., part of a value
------------------------------------------------------------------------

data Inert : Coercion → Set where
  _! : (G : Ty) → Inert (G !)
  seal : (A : Ty) → (α : SealVar) → Inert (seal A α)
  _↦_ : (c d : Coercion) → Inert (c ↦ d)
  `∀ : (c : Coercion) → Inert (`∀ c)
  gen : (c : Coercion) → Inert (gen c)

------------------------------------------------------------------------
-- reveal/conceal B α C generate coercions between B[α] and B[C]
------------------------------------------------------------------------

mutual
  reveal : Ty → SealVar → Ty → Coercion
  reveal (`X X) α C = id (`X X)
  reveal (`α β) α C with α ≟ β
  reveal (`α .α) α C | yes refl = unseal α C
  reveal (`α β) α C | no neq = id (`α β)
  reveal (‵ ι) α C = id (‵ ι)
  reveal ★ α C = id ★
  reveal (A ⇒ B) α C = conceal A α C ↦ reveal B α C
  reveal (`∀ A) α C = `∀ (reveal A α (⇑ᵗ C))

  conceal : Ty → SealVar → Ty → Coercion
  conceal (`X X) α C = id (`X X)
  conceal (`α β) α C with α ≟ β
  conceal (`α .α) α C | yes refl = seal C α
  conceal (`α β) α C | no neq = id (`α β)
  conceal (‵ ι) α C = id (‵ ι)
  conceal ★ α C = id ★
  conceal (A ⇒ B) α C = reveal A α C ↦ conceal B α C
  conceal (`∀ A) α C = `∀ (conceal A α (⇑ᵗ C))

------------------------------------------------------------------------
-- Renaming and substitution
------------------------------------------------------------------------

renameᶜ : Renameᵗ → Renameˢ → Coercion → Coercion
renameᶜ ρ σ (id A) = id (rename ρ σ A)
renameᶜ ρ σ (p ︔ q) = renameᶜ ρ σ p ︔ renameᶜ ρ σ q
renameᶜ ρ σ (A !) = rename ρ σ A !
renameᶜ ρ σ (A ？) = rename ρ σ A ？
renameᶜ ρ σ (unseal α A) = unseal (σ α) (rename ρ σ A)
renameᶜ ρ σ (seal A α) = seal (rename ρ σ A) (σ α)
renameᶜ ρ σ (p ↦ q) = renameᶜ ρ σ p ↦ renameᶜ ρ σ q
renameᶜ ρ σ (`∀ p) = `∀ (renameᶜ (extᵗ ρ) σ p)
renameᶜ ρ σ (gen p) = gen (renameᶜ ρ (extˢ σ) p)
renameᶜ ρ σ (inst p) = inst (renameᶜ ρ (extˢ σ) p)

renameᵗᶜ : Renameᵗ → Coercion → Coercion
renameᵗᶜ ρ = renameᶜ ρ idˢ

renameˢᶜ : Renameˢ → Coercion → Coercion
renameˢᶜ σ = renameᶜ idᵗ σ

liftSubstᵗOverSeal : Substᵗ → Substᵗ
liftSubstᵗOverSeal σ X = ⇑ˢ (σ X)

substᵗᶜ : Substᵗ → Coercion → Coercion
substᵗᶜ σ (id A) = id (substᵗ σ A)
substᵗᶜ σ (p ︔ q) = substᵗᶜ σ p ︔ substᵗᶜ σ q
substᵗᶜ σ (A !) = substᵗ σ A !
substᵗᶜ σ (A ？) = substᵗ σ A ？
substᵗᶜ σ (unseal α A) = unseal α (substᵗ σ A)
substᵗᶜ σ (seal A α) = seal (substᵗ σ A) α
substᵗᶜ σ (p ↦ q) = substᵗᶜ σ p ↦ substᵗᶜ σ q
substᵗᶜ σ (`∀ p) = `∀ (substᵗᶜ (extSubstᵗ σ) p)
substᵗᶜ σ (gen p) = gen (substᵗᶜ (liftSubstᵗOverSeal σ) p)
substᵗᶜ σ (inst p) = inst (substᵗᶜ (liftSubstᵗOverSeal σ) p)

⇑ᶜ : Coercion → Coercion
⇑ᶜ = renameᵗᶜ suc

⇑ˢᶜ : Coercion → Coercion
⇑ˢᶜ = renameˢᶜ suc

_[_]ᶜ : Coercion → SealVar → Coercion
c [ α ]ᶜ = renameˢᶜ (singleRenameˢ α) c

_[_]ᵀᶜ : Coercion → SealVar → Coercion
c [ α ]ᵀᶜ = substᵗᶜ (singleTyEnv (`α α)) c

------------------------------------------------------------------------
-- Duality
------------------------------------------------------------------------

infix 8 -_

data SealUse : Set where
  neutral : SealUse
  tag-use : SealUse
  seal-use : SealUse

ModeEnv : Set
ModeEnv = SealVar → SealUse

neutralMode : ModeEnv
neutralMode α = neutral

bindTag : ModeEnv → ModeEnv
bindTag μ zero = tag-use
bindTag μ (suc α) = μ α

bindSeal : ModeEnv → ModeEnv
bindSeal μ zero = seal-use
bindSeal μ (suc α) = μ α

dualTag : ModeEnv → Ty → Coercion
dualTag μ (`α α) with μ α
dualTag μ (`α α) | tag-use = seal ★ α
dualTag μ (`α α) | neutral = (`α α) ？
dualTag μ (`α α) | seal-use = (`α α) ？
dualTag μ (`X X) = (`X X) ？
dualTag μ (‵ ι) = (‵ ι) ？
dualTag μ ★ = ★ ？
dualTag μ (A ⇒ B) = (A ⇒ B) ？
dualTag μ (`∀ A) = (`∀ A) ？

dualUntag : ModeEnv → Ty → Coercion
dualUntag μ (`α α) with μ α
dualUntag μ (`α α) | tag-use = unseal α ★
dualUntag μ (`α α) | neutral = (`α α) !
dualUntag μ (`α α) | seal-use = (`α α) !
dualUntag μ (`X X) = (`X X) !
dualUntag μ (‵ ι) = (‵ ι) !
dualUntag μ ★ = ★ !
dualUntag μ (A ⇒ B) = (A ⇒ B) !
dualUntag μ (`∀ A) = (`∀ A) !

dualSeal : ModeEnv → Ty → SealVar → Coercion
dualSeal μ A α with μ α
dualSeal μ A α | seal-use = (`α α) !
dualSeal μ A α | neutral = unseal α A
dualSeal μ A α | tag-use = unseal α A

dualUnseal : ModeEnv → SealVar → Ty → Coercion
dualUnseal μ α A with μ α
dualUnseal μ α A | seal-use = (`α α) ？
dualUnseal μ α A | neutral = seal A α
dualUnseal μ α A | tag-use = seal A α

dual : ModeEnv → Coercion → Coercion
dual μ (id A) = id A
dual μ (c ︔ d) = dual μ d ︔ dual μ c
dual μ (c ↦ d) = dual μ c ↦ dual μ d
dual μ (`∀ c) = `∀ (dual μ c)
dual μ (G !) = dualTag μ G
dual μ (G ？) = dualUntag μ G
dual μ (seal A α) = dualSeal μ A α
dual μ (unseal α A) = dualUnseal μ α A
dual μ (gen c) = inst (dual (bindTag μ) c)
dual μ (inst c) = gen (dual (bindSeal μ) c)

-_ : Coercion → Coercion
- c = dual neutralMode c

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

data TagAllowed (μ : ModeEnv) : Ty → Set where
  tagSeal : ∀ {α} →
    μ α ≡ tag-use →
    TagAllowed μ (`α α)

  tagIota : ∀ {ι} →
    TagAllowed μ (‵ ι)

  tagFun :
    TagAllowed μ (★ ⇒ ★)

infix 4 _∣_⊢_∶_=⇒_

data _∣_⊢_∶_=⇒_ : ModeEnv → Telescope → Coercion → Ty → Ty → Set where

  cast-id : ∀ {μ Γ A}
    → WfTy Γ A
     --------------------------
    → μ ∣ Γ ⊢ id A ∶ A =⇒ A

  cast-seal : ∀ {μ Γ α A}
    → WfTy Γ A
    → μ α ≡ seal-use
    → Γ ∋α α ⦂ A
     -----------------------------------
    → μ ∣ Γ ⊢ seal A α ∶ A =⇒ `α α

  cast-unseal : ∀ {μ Γ α A}
    → WfTy Γ A
    → μ α ≡ seal-use
    → Γ ∋α α ⦂ A
     -------------------------------------
    → μ ∣ Γ ⊢ unseal α A ∶ `α α =⇒ A

  cast-seq : ∀ {μ Γ A B C s t}
    → μ ∣ Γ ⊢ s ∶ A =⇒ B
    → μ ∣ Γ ⊢ t ∶ B =⇒ C
     -------------------------
    → μ ∣ Γ ⊢ (s ︔ t) ∶ A =⇒ C

  cast-tag : ∀ {μ Γ G}
    → WfTy Γ G
    → Ground G
    → TagAllowed μ G
     -------------------------
    → μ ∣ Γ ⊢ G ! ∶ G =⇒ ★

  cast-untag : ∀ {μ Γ H}
    → WfTy Γ H
    → Ground H
    → TagAllowed μ H
     --------------------------
    → μ ∣ Γ ⊢ H ？ ∶ ★ =⇒ H

  cast-fun : ∀ {μ Γ A A′ B B′ s t}
    → μ ∣ Γ ⊢ s ∶ A′ =⇒ A
    → μ ∣ Γ ⊢ t ∶ B =⇒ B′
     ---------------------------------------
    → μ ∣ Γ ⊢ (s ↦ t) ∶ (A ⇒ B) =⇒ (A′ ⇒ B′)

  cast-all : ∀ {μ Γ A B s}
    → μ ∣ tyᵉ ∷ Γ ⊢ s ∶ A =⇒ B
     --------------------------------------
    → μ ∣ Γ ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

  cast-inst : ∀ {μ Γ A B s}
    → WfTy (tyᵉ ∷ Γ) A
    → WfTy Γ B
    → occursᵗ zero A ≡ true
    → bindSeal μ ∣ sealᵉ ★ ∷ Γ ⊢ s ∶ openTyWithSeal A =⇒ ⇑ˢ B
     -----------------------------------------------
    → μ ∣ Γ ⊢ inst s ∶ (`∀ A) =⇒ B

  cast-gen : ∀ {μ Γ A B s}
    → WfTy Γ A
    → WfTy (tyᵉ ∷ Γ) B
    → occursᵗ zero B ≡ true
    → bindTag μ ∣ sealᵉ ★ ∷ Γ ⊢ s ∶ ⇑ˢ A =⇒ openTyWithSeal B
     ----------------------------------------------
    → μ ∣ Γ ⊢ gen s ∶ A =⇒ (`∀ B)
