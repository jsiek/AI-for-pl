-- This is based on the cambridge22 notes.

module Coercions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no)

open import Types

Label = ℕ

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
 seal : Ty → TyVar → Coercion
 unseal : TyVar → Ty → Coercion
 gen : Ty → Coercion → Coercion
 inst : Ty → Coercion → Coercion


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
src (unseal α A) = ＇ α
src (gen A c) = A
src (inst B c) = `∀ (src c)

tgt (id A) = A
tgt (c ︔ d) = tgt d
tgt (c ↦ d) = src c ⇒ tgt d
tgt (`∀ c) = `∀ (tgt c)
tgt (G !) = ★
tgt (H ？) = H
tgt (seal A α) = ＇ α
tgt (unseal α B) = B
tgt (gen A c) = `∀ (tgt c)
tgt (inst B c) = B

------------------------------------------------------------------------
-- Inert coercions, i.e., part of a value
------------------------------------------------------------------------

data Inert : Coercion → Set where
  _! : (G : Ty) → Inert (G !)
  seal : (A : Ty) → (α : TyVar) → Inert (seal A α)
  _↦_ : (c d : Coercion) → Inert (c ↦ d)
  `∀ : (c : Coercion) → Inert (`∀ c)
  gen : (A : Ty) → (c : Coercion) → Inert (gen A c)

------------------------------------------------------------------------
-- reveal/conceal B α C generate coercions between B[α] and B[C]
------------------------------------------------------------------------

mutual
  reveal : Ty → TyVar → Ty → Coercion
  reveal (＇ β) α C with α ≟ β
  reveal (＇ .α) α C | yes refl = unseal α C
  reveal (＇ β) α C | no neq = id (＇ β)
  reveal (‵ ι) α C = id (‵ ι)
  reveal ★ α C = id ★
  reveal (A ⇒ B) α C = conceal A α C ↦ reveal B α C
  reveal (`∀ A) α C = `∀ (reveal A (suc α) (⇑ᵗ C))

  conceal : Ty → TyVar → Ty → Coercion
  conceal (＇ β) α C with α ≟ β
  conceal (＇ .α) α C | yes refl = seal C α
  conceal (＇ β) α C | no neq = id (＇ β)
  conceal (‵ ι) α C = id (‵ ι)
  conceal ★ α C = id ★
  conceal (A ⇒ B) α C = reveal A α C ↦ conceal B α C
  conceal (`∀ A) α C = `∀ (conceal A (suc α) (⇑ᵗ C))

------------------------------------------------------------------------
-- Renaming Type Variables
------------------------------------------------------------------------

renameᶜ : Renameᵗ → Coercion → Coercion
renameᶜ ρ (id A) = id (renameᵗ ρ A)
renameᶜ ρ (p ︔ q) = renameᶜ ρ p ︔ renameᶜ ρ q
renameᶜ ρ (A !) = renameᵗ ρ A !
renameᶜ ρ (A ？) = renameᵗ ρ A ？
renameᶜ ρ (unseal α A) = unseal (ρ α) (renameᵗ ρ A)
renameᶜ ρ (seal A α) = seal (renameᵗ ρ A) (ρ α)
renameᶜ ρ (p ↦ q) = renameᶜ ρ p ↦ renameᶜ ρ q
renameᶜ ρ (`∀ p) = `∀ (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (gen A p) = gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (inst B p) = inst (renameᵗ ρ B) (renameᶜ (extᵗ ρ) p)

data DualMode : Set where
  tag-to-seal seal-to-tag : DualMode

DualEnv : Set
DualEnv = TyVar → DualMode

tag-to-sealᵈ : DualEnv
tag-to-sealᵈ X = tag-to-seal

seal-to-tagᵈ : DualEnv
seal-to-tagᵈ X = seal-to-tag

extᵈ : DualEnv → DualEnv
extᵈ μ zero = tag-to-seal
extᵈ μ (suc X) = μ X

genᵈ : DualEnv → DualEnv
genᵈ μ zero = tag-to-seal
genᵈ μ (suc X) = μ X

instᵈ : DualEnv → DualEnv
instᵈ μ zero = seal-to-tag
instᵈ μ (suc X) = μ X

mode≤ : DualMode → DualMode → Bool
mode≤ tag-to-seal tag-to-seal = true
mode≤ tag-to-seal seal-to-tag = false
mode≤ seal-to-tag tag-to-seal = false
mode≤ seal-to-tag seal-to-tag = true

ModeIncl : DualEnv → DualEnv → Set
ModeIncl μ ν = ∀ X → mode≤ (μ X) (ν X) ≡ true

modeIncl-refl : ∀ {μ} → ModeIncl μ μ
modeIncl-refl {μ} X with μ X
modeIncl-refl X | tag-to-seal = refl
modeIncl-refl X | seal-to-tag = refl

tagModeAllowed : DualMode → Bool
tagModeAllowed tag-to-seal = true
tagModeAllowed seal-to-tag = false

sealModeAllowed : DualMode → Bool
sealModeAllowed tag-to-seal = false
sealModeAllowed seal-to-tag = true

tagTyAllowed : DualEnv → Ty → Bool
tagTyAllowed μ (＇ α) = tagModeAllowed (μ α)
tagTyAllowed μ (‵ ι) = true
tagTyAllowed μ ★ = true
tagTyAllowed μ (A ⇒ B) = true
tagTyAllowed μ (`∀ A) = true

dualTag : DualEnv → Ty → Coercion
dualTag μ (＇ α) = seal ★ α
dualTag μ (‵ ι) = (‵ ι) ？
dualTag μ ★ = ★ ？
dualTag μ (A ⇒ B) = (A ⇒ B) ？
dualTag μ (`∀ A) = (`∀ A) ？

dualUntag : DualEnv → Ty → Coercion
dualUntag μ (＇ α) = unseal α ★
dualUntag μ (‵ ι) = (‵ ι) !
dualUntag μ ★ = ★ !
dualUntag μ (A ⇒ B) = (A ⇒ B) !
dualUntag μ (`∀ A) = (`∀ A) !

dualSeal : DualEnv → Ty → TyVar → Coercion
dualSeal μ A α = (＇ α) !

dualUnseal : DualEnv → TyVar → Ty → Coercion
dualUnseal μ α A = (＇ α) ？

infix 8 -_

dual : DualEnv → Coercion → Coercion
dual μ (id A) = id A
dual μ (c ︔ d) = dual μ d ︔ dual μ c
dual μ (c ↦ d) = dual μ c ↦ dual μ d
dual μ (`∀ c) = `∀ (dual (extᵈ μ) c)
dual μ (G !) = dualTag μ G
dual μ (G ？) = dualUntag μ G
dual μ (seal A α) = dualSeal μ A α
dual μ (unseal α A) = dualUnseal μ α A
dual μ (gen A c) = inst A (dual (genᵈ μ) c)
dual μ (inst B c) = gen B (dual (instᵈ μ) c)

-_ : Coercion → Coercion
-_ = dual tag-to-sealᵈ

⇑ᶜ : Coercion → Coercion
⇑ᶜ = renameᶜ suc

_[_]ᶜ : Coercion → TyVar → Coercion
c [ X ]ᶜ = renameᶜ (singleRenameᵗ X) c


-- Phil: What about the restriction that we don't allow
--  X to ★ casts.

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶_=⇒_

data _∣_∣_⊢_∶_=⇒_ : DualEnv → TyCtx → Store → Coercion → Ty → Ty → Set where

  cast-id : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{A : Ty}
    → WfTy Δ A
    -- fvs(A) ∩ dom(Σ) = ∅
     -------------------
    → μ ∣ Δ ∣ Σ ⊢ id A ∶ A =⇒ A

  cast-seal : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     ---------------------------
    → μ ∣ Δ ∣ Σ ⊢ seal A α ∶ A =⇒ (＇ α)

  cast-unseal : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     -----------------------------
    → μ ∣ Δ ∣ Σ ⊢ unseal α A ∶ (＇ α) =⇒ A

  -- Phil: s and t have different Σ's, they combine, with side condition
  cast-seq : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{A B C : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C
     -------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ︔ t) ∶ A =⇒ C

  cast-tag : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{G : Ty}
    → WfTy Δ G
    → Ground G
    → tagTyAllowed μ G ≡ true
    -- If G is α, then α ∉ dom(Σ)
     ---------------------
    → μ ∣ Δ ∣ Σ ⊢ G ! ∶ G =⇒ ★

  cast-untag : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{H : Ty}
    → WfTy Δ H
    → Ground H
    → tagTyAllowed μ H ≡ true
     -----------------------
    → μ ∣ Δ ∣ Σ ⊢ H ？ ∶ ★ =⇒ H

  cast-fun : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A′ =⇒ A
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ B′
     ---------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) =⇒ (A′ ⇒ B′)

  cast-all : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A =⇒ B
     ----------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

  -- ν̅ 
  cast-inst : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ B
    → instᵈ μ ∣ suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A =⇒ ⇑ᵗ B
     ----------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (inst B s) ∶ (`∀ A) =⇒ B

  -- ν
  cast-gen : ∀{μ : DualEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ A
    → genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A =⇒ B
     ----------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (gen A s) ∶ A =⇒ (`∀ B)

infix 4 _∣_⊢_∶_=⇒_

_∣_⊢_∶_=⇒_ : TyCtx → Store → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ A =⇒ B = ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

  
