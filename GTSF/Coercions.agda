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
import Data.List.Membership.DecPropositional as ListMembership

open import Types

infix 4 _≟StoreEntry_
_≟StoreEntry_ : (x y : TyVar × Ty) → Dec (x ≡ y)
(α , A) ≟StoreEntry (β , B) with α ≟ β | A ≟Ty B
(α , A) ≟StoreEntry (.α , .A) | yes refl | yes refl = yes refl
(α , A) ≟StoreEntry (β , B) | no α≢β | _ =
  no (λ { refl → α≢β refl })
(α , A) ≟StoreEntry (.α , B) | yes refl | no A≢B =
  no (λ { refl → A≢B refl })

open ListMembership _≟_ using (_∈?_)
open ListMembership _≟StoreEntry_ using () renaming (_∈?_ to _∈Store?_)

Label = ℕ

------------------------------------------------------------------------
-- Raw coercions
------------------------------------------------------------------------

data Coercion : Set where
 id : Ty → Coercion
 _︔_ : Coercion → Coercion → Coercion
 _↦_ : Coercion → Coercion → Coercion
 `∀ : Coercion → Coercion
 _! : Ty → Coercion -- replace Ty with Gnd
 _？ : Ty → Coercion -- replace Ty with Gnd
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

dualTag : Store → Store → Ty → Coercion
dualTag Σ Π (＇ α) with α ∈? domˢ Σ -- could be Π 
dualTag Σ Π (＇ α) | yes _ = seal ★ α
dualTag Σ Π (＇ α) | no _ = (＇ α) ？
dualTag Σ Π (‵ ι) = (‵ ι) ？
dualTag Σ Π ★ = ★ ？
dualTag Σ Π (A ⇒ B) = (A ⇒ B) ？
dualTag Σ Π (`∀ A) = (`∀ A) ？

dualUntag : Store → Store → Ty → Coercion
dualUntag Σ Π (＇ α) with α ∈? domˢ Σ
dualUntag Σ Π (＇ α) | yes _ = unseal α ★
dualUntag Σ Π (＇ α) | no _ = (＇ α) !
dualUntag Σ Π (‵ ι) = (‵ ι) !
dualUntag Σ Π ★ = ★ !
dualUntag Σ Π (A ⇒ B) = (A ⇒ B) !
dualUntag Σ Π (`∀ A) = (`∀ A) !

dualSeal : Store → Store → Ty → TyVar → Coercion
dualSeal Σ Π A α with (α , A) ∈Store? Π 
dualSeal Σ Π A α | yes _ = (＇ α) !
dualSeal Σ Π A α | no _ = unseal α A

dualUnseal : Store → Store → TyVar → Ty → Coercion
dualUnseal Σ Π α A with  (α , A) ∈Store? Π 
dualUnseal Σ Π α A | yes _ = (＇ α) ？
dualUnseal Σ Π α A | no _ = seal A α

infix 8 -_

dual : Store → Store → Coercion → Coercion
dual Σ Π (id A) = id A
dual Σ Π (c ︔ d) = dual Σ Π d ︔ dual Σ Π c
dual Σ Π (c ↦ d) = dual Σ Π c ↦ dual Σ Π d
dual Σ Π (`∀ c) = `∀ (dual (⟰ᵗ Σ) (⟰ᵗ Π) c)
dual Σ Π (G !) = dualTag Σ Π G
dual Σ Π (G ？) = dualUntag Σ Π G
dual Σ Π (seal A α) = dualSeal Σ Π A α
dual Σ Π (unseal α A) = dualUnseal Σ Π α A
dual Σ Π (gen A c) = inst A (dual ((0 , ★) ∷ Σ) (⟰ᵗ Π) c)
dual Σ Π (inst B c) = gen B (dual (⟰ᵗ Σ) ((0 , ★) ∷ Π) c)

-_ : Coercion → Coercion
-_ = dual [] []

⇑ᶜ : Coercion → Coercion
⇑ᶜ = renameᶜ suc

_[_]ᶜ : Coercion → TyVar → Coercion
c [ X ]ᶜ = renameᶜ (singleRenameᵗ X) c


data tagAllowed : Ty → Store → Set where

   tagAlpha : ∀{α Σ}
     → α ∈ domˢ Σ
     → tagAllowed (＇ α) Σ
     
   tagIota : ∀{ι Σ} → tagAllowed (‵ ι) Σ

   tagFun : ∀{Σ} → tagAllowed (★ ⇒ ★) Σ


------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

-- Δ ∣ Σ ∣ Π ⊢ c ∶ A =⇒ B
-- α ∈ Σ means α can appear in tags and id, but not seal
-- α ∈ Π means α can appear in seal and id, but not tag

infix 4 _∣_∣_⊢_∶_=⇒_

data _∣_∣_⊢_∶_=⇒_ : TyCtx → Store → Store → Coercion → Ty → Ty → Set where

  cast-id : ∀{Δ : TyCtx}{Σ Π : Store}{A : Ty}
    → WfTy Δ A
     --------------------------
    → Δ ∣ Σ ∣ Π ⊢ id A ∶ A =⇒ A

  cast-seal : ∀{Δ : TyCtx}{Σ Π : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Π
     -----------------------------------
    → Δ ∣ Σ ∣ Π ⊢ seal A α ∶ A =⇒ (＇ α)

  cast-unseal : ∀{Δ : TyCtx}{Σ Π : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Π
     -------------------------------------
    → Δ ∣ Σ ∣ Π ⊢ unseal α A ∶ (＇ α) =⇒ A

  cast-seq : ∀{Δ : TyCtx}{Σ Π : Store}{A B C : Ty}{s t : Coercion}
    → Δ ∣ Σ ∣ Π ⊢ s ∶ A =⇒ B
    → Δ ∣ Σ ∣ Π ⊢ t ∶ B =⇒ C
     -------------------------
    → Δ ∣ Σ ∣ Π ⊢ (s ︔ t) ∶ A =⇒ C

  cast-tag : ∀{Δ : TyCtx}{Σ Π : Store}{G : Ty}
    → WfTy Δ G
    → Ground G
    → tagAllowed G Σ
     -------------------------
    → Δ ∣ Σ ∣ Π ⊢ G ! ∶ G =⇒ ★

  cast-untag : ∀{Δ : TyCtx}{Σ Π : Store}{H : Ty}
    → WfTy Δ H
    → Ground H
    → tagAllowed H Σ
     --------------------------
    → Δ ∣ Σ ∣ Π ⊢ H ？ ∶ ★ =⇒ H

  cast-fun : ∀{Δ : TyCtx}{Σ Π : Store}{A A′ B B′ : Ty}{s t : Coercion}
    → Δ ∣ Σ ∣ Π ⊢ s ∶ A′ =⇒ A
    → Δ ∣ Σ ∣ Π ⊢ t ∶ B =⇒ B′
     ---------------------------------------
    → Δ ∣ Σ ∣ Π ⊢ (s ↦ t) ∶ (A ⇒ B) =⇒ (A′ ⇒ B′)

  cast-all : ∀{Δ : TyCtx}{Σ Π : Store}{A B : Ty}{s : Coercion}
    → suc Δ ∣ ⟰ᵗ Σ ∣ ⟰ᵗ Π ⊢ s ∶ A =⇒ B
     --------------------------------------
    → Δ ∣ Σ ∣ Π ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

  -- ν̅ 
  cast-inst : ∀{Δ : TyCtx}{Σ Π : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ B
    → occurs 0 A ≡ true
    → suc Δ ∣ ⟰ᵗ Σ ∣ (0 , ★) ∷ ⟰ᵗ Π ⊢ s ∶ A =⇒ ⇑ᵗ B
     -----------------------------------------------
    → Δ ∣ Σ ∣ Π ⊢ (inst B s) ∶ (`∀ A) =⇒ B

  -- ν
  cast-gen : ∀{Δ : TyCtx}{Σ Π : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ A
    → occurs 0 B ≡ true
    → suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ∣ ⟰ᵗ Π ⊢ s ∶ ⇑ᵗ A =⇒ B
     ----------------------------------------------
    → Δ ∣ Σ ∣ Π ⊢ (gen A s) ∶ A =⇒ (`∀ B)


  
