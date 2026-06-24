-- This is based on the cambridge22 notes.

module Coercions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true; _∧_)
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

data Mode : Set where
  id-only tag-or-id seal-or-id : Mode

ModeEnv : Set
ModeEnv = TyVar → Mode

id-onlyᵈ : ModeEnv
id-onlyᵈ X = id-only

tag-or-idᵈ : ModeEnv
tag-or-idᵈ X = tag-or-id

seal-or-idᵈ : ModeEnv
seal-or-idᵈ X = seal-or-id

extᵈ : ModeEnv → ModeEnv
extᵈ μ zero = id-only
extᵈ μ (suc X) = μ X

genᵈ : ModeEnv → ModeEnv
genᵈ μ zero = tag-or-id
genᵈ μ (suc X) = μ X

instᵈ : ModeEnv → ModeEnv
instᵈ μ zero = seal-or-id
instᵈ μ (suc X) = μ X

mode≤ : Mode → Mode → Bool
mode≤ id-only id-only = true
mode≤ id-only tag-or-id = true
mode≤ id-only seal-or-id = true
mode≤ tag-or-id id-only = false
mode≤ tag-or-id tag-or-id = true
mode≤ tag-or-id seal-or-id = false
mode≤ seal-or-id id-only = false
mode≤ seal-or-id tag-or-id = false
mode≤ seal-or-id seal-or-id = true

ModeIncl : ModeEnv → ModeEnv → Set
ModeIncl μ ν = ∀ X → mode≤ (μ X) (ν X) ≡ true

modeIncl-refl : ∀ {μ} → ModeIncl μ μ
modeIncl-refl {μ} X with μ X
modeIncl-refl X | id-only = refl
modeIncl-refl X | tag-or-id = refl
modeIncl-refl X | seal-or-id = refl

idModeAllowed : Mode → Bool
idModeAllowed id-only = true
idModeAllowed tag-or-id = true
idModeAllowed seal-or-id = true

tagModeAllowed : Mode → Bool
tagModeAllowed id-only = false
tagModeAllowed tag-or-id = true
tagModeAllowed seal-or-id = false

sealModeAllowed : Mode → Bool
sealModeAllowed id-only = false
sealModeAllowed tag-or-id = false
sealModeAllowed seal-or-id = true

idTyAllowed : ModeEnv → Ty → Bool
idTyAllowed μ (＇ α) = idModeAllowed (μ α)
idTyAllowed μ (‵ ι) = true
idTyAllowed μ ★ = true
idTyAllowed μ (A ⇒ B) = idTyAllowed μ A ∧ idTyAllowed μ B
idTyAllowed μ (`∀ A) = idTyAllowed (extᵈ μ) A

tagTyAllowed : ModeEnv → Ty → Bool
tagTyAllowed μ (＇ α) = tagModeAllowed (μ α)
tagTyAllowed μ (‵ ι) = true
tagTyAllowed μ ★ = true
tagTyAllowed μ (A ⇒ B) = true
tagTyAllowed μ (`∀ A) = true

dualTag : ModeEnv → Ty → Coercion
dualTag μ (＇ α) = seal ★ α
dualTag μ (‵ ι) = (‵ ι) ？
dualTag μ ★ = ★ ？
dualTag μ (A ⇒ B) = (A ⇒ B) ？
dualTag μ (`∀ A) = (`∀ A) ？

dualUntag : ModeEnv → Ty → Coercion
dualUntag μ (＇ α) = unseal α ★
dualUntag μ (‵ ι) = (‵ ι) !
dualUntag μ ★ = ★ !
dualUntag μ (A ⇒ B) = (A ⇒ B) !
dualUntag μ (`∀ A) = (`∀ A) !

dualSeal : ModeEnv → Ty → TyVar → Coercion
dualSeal μ A α = (＇ α) !

dualUnseal : ModeEnv → TyVar → Ty → Coercion
dualUnseal μ α A = (＇ α) ？

infix 8 -_

dual : ModeEnv → Coercion → Coercion
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
-_ = dual tag-or-idᵈ

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

data _∣_∣_⊢_∶_=⇒_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set where

  cast-id : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A : Ty}
    → WfTy Δ A
    → idTyAllowed μ A ≡ true
     -------------------
    → μ ∣ Δ ∣ Σ ⊢ id A ∶ A =⇒ A

  cast-seal : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     ---------------------------
    → μ ∣ Δ ∣ Σ ⊢ seal A α ∶ A =⇒ (＇ α)

  cast-unseal : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     -----------------------------
    → μ ∣ Δ ∣ Σ ⊢ unseal α A ∶ (＇ α) =⇒ A

  -- Phil: s and t have different Σ's, they combine, with side condition
  cast-seq : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B C : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C
     -------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ︔ t) ∶ A =⇒ C

  cast-tag : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{G : Ty}
    → WfTy Δ G
    → Ground G
    → tagTyAllowed μ G ≡ true
    -- If G is α, then α ∉ dom(Σ)
     ---------------------
    → μ ∣ Δ ∣ Σ ⊢ G ! ∶ G =⇒ ★

  cast-untag : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{H : Ty}
    → WfTy Δ H
    → Ground H
    → tagTyAllowed μ H ≡ true
     -----------------------
    → μ ∣ Δ ∣ Σ ⊢ H ？ ∶ ★ =⇒ H

  cast-fun : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A′ =⇒ A
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ B′
     ---------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) =⇒ (A′ ⇒ B′)

  cast-all : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A =⇒ B
     ----------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

  -- ν̅ 
  cast-inst : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ B
    → occurs zero A ≡ true
    → instᵈ μ ∣ suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A =⇒ ⇑ᵗ B
     ----------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (inst B s) ∶ (`∀ A) =⇒ B

  -- ν
  cast-gen : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ A
    → occurs zero B ≡ true
    → genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A =⇒ B
     ----------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (gen A s) ∶ A =⇒ (`∀ B)

infix 4 _∣_⊢_∶_=⇒_

_∣_⊢_∶_=⇒_ : TyCtx → Store → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ A =⇒ B = ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

  
