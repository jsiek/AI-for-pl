-- File Charter:
--   * Raw coercion syntax, type-variable renaming, and coercion typing.
--   * Primary exports are `Coercion`, `renameᶜ`, and `_∣_⊢_∶_=⇒_`.
--   * Depends on labels and core type syntax.
--   * This is based on the cambridge22 notes.

module Coercions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin.Subset using (Subset; Side; inside; outside; _∈_)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no)

open import Label
open import Types

------------------------------------------------------------------------
-- Raw coercions
------------------------------------------------------------------------

data Coercion (Δ : TyCtx) : Set where
 id : Ty Δ → Coercion Δ
 _︔_ : Coercion Δ → Coercion Δ → Coercion Δ
 _↦_ : Coercion Δ → Coercion Δ → Coercion Δ
 `∀ : Coercion (suc Δ) → Coercion Δ
 _! : Ty Δ → Coercion Δ
 _？_ : Ty Δ → Label → Coercion Δ
 seal : Ty Δ → TyVar Δ → Coercion Δ
 unseal : TyVar Δ → Ty Δ → Coercion Δ
 gen : Ty Δ → Coercion (suc Δ) → Coercion Δ
 inst : Ty Δ → Coercion (suc Δ) → Coercion Δ


-- ------------------------------------------------------------------------
-- -- Source and target type of a coercion
-- ------------------------------------------------------------------------

-- src : Coercion → Ty
-- tgt : Coercion → Ty

-- src (id A) = A
-- src (c ︔ d) = src c
-- src (c ↦ d) = tgt c ⇒ src d
-- src (`∀ c) = `∀ (src c)
-- src (G !) = G
-- src (G ？ ℓ) = ★
-- src (seal A α) = A
-- src (unseal α A) = ＇ α
-- src (gen A c) = A
-- src (inst B c) = `∀ (src c)

-- tgt (id A) = A
-- tgt (c ︔ d) = tgt d
-- tgt (c ↦ d) = src c ⇒ tgt d
-- tgt (`∀ c) = `∀ (tgt c)
-- tgt (G !) = ★
-- tgt (H ？ ℓ) = H
-- tgt (seal A α) = ＇ α
-- tgt (unseal α B) = B
-- tgt (gen A c) = `∀ (tgt c)
-- tgt (inst B c) = B

-- ------------------------------------------------------------------------
-- -- Inert coercions, i.e., part of a value
-- ------------------------------------------------------------------------

-- data Inert : Coercion → Set where
--   _! : (G : Ty) → Inert (G !)
--   seal : (A : Ty) → (α : TyVar) → Inert (seal A α)
--   _↦_ : (c d : Coercion) → Inert (c ↦ d)
--   `∀ : (c : Coercion) → Inert (`∀ c)
--   gen : (A : Ty) → (c : Coercion) → Inert (gen A c)

-- ------------------------------------------------------------------------
-- -- reveal/conceal B α C generate coercions between B[α] and B[C]
-- ------------------------------------------------------------------------

-- mutual
--   reveal : Ty → TyVar → Ty → Coercion
--   reveal (＇ β) α C with α ≟ β
--   reveal (＇ .α) α C | yes refl = unseal α C
--   reveal (＇ β) α C | no neq = id (＇ β)
--   reveal (‵ ι) α C = id (‵ ι)
--   reveal ★ α C = id ★
--   reveal (A ⇒ B) α C = conceal A α C ↦ reveal B α C
--   reveal (`∀ A) α C = `∀ (reveal A (suc α) (⇑ᵗ C))

--   conceal : Ty → TyVar → Ty → Coercion
--   conceal (＇ β) α C with α ≟ β
--   conceal (＇ .α) α C | yes refl = seal C α
--   conceal (＇ β) α C | no neq = id (＇ β)
--   conceal (‵ ι) α C = id (‵ ι)
--   conceal ★ α C = id ★
--   conceal (A ⇒ B) α C = reveal A α C ↦ conceal B α C
--   conceal (`∀ A) α C = `∀ (conceal A (suc α) (⇑ᵗ C))

-- ------------------------------------------------------------------------
-- -- Renaming Type Variables
-- ------------------------------------------------------------------------

renameᶜ : ∀{Δ}{Δ′} → Renameᵗ Δ Δ′ → Coercion Δ → Coercion Δ′
renameᶜ ρ (id A) = id (renameᵗ ρ A)
renameᶜ ρ (p ︔ q) = renameᶜ ρ p ︔ renameᶜ ρ q
renameᶜ ρ (A !) = renameᵗ ρ A !
renameᶜ ρ (A ？ ℓ) = renameᵗ ρ A ？ ℓ
renameᶜ ρ (unseal α A) = unseal (ρ α) (renameᵗ ρ A)
renameᶜ ρ (seal A α) = seal (renameᵗ ρ A) (ρ α)
renameᶜ ρ (p ↦ q) = renameᶜ ρ p ↦ renameᶜ ρ q
renameᶜ ρ (`∀ p) = `∀ (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (gen A p) = gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (inst B p) = inst (renameᵗ ρ B) (renameᶜ (extᵗ ρ) p)

⇑ᶜ : ∀ {Δ} → Coercion Δ → Coercion (suc Δ)
⇑ᶜ = renameᶜ λ z → Zᵗ

-- _[_]ᶜ : ∀ {Δ} → Coercion (suc Δ) → TyVar Δ → Coercion Δ
-- c [ X ]ᶜ = renameᶜ (singleRenameᵗ X) c

-- ------------------------------------------------------------------------
-- -- Typing
-- ------------------------------------------------------------------------

infix 4 _∣_⊢_∶_=⇒_

data _∣_⊢_∶_=⇒_ (Δ : TyCtx) (Ψ : Subset Δ) : Coercion Δ → Ty Δ → Ty Δ → Set where

  cast-id : ∀{A : Ty Δ}
     -------------------
    → Δ ∣ Ψ ⊢ id A ∶ A =⇒ A

  cast-seal : ∀{α : TyVar Δ}{A : Ty Δ}
    → tyVarToFin α ∈ Ψ
     ---------------------------
    → Δ ∣ Ψ ⊢ seal A α ∶ A =⇒ (＇ α)

  cast-unseal : ∀{α : TyVar Δ}{A : Ty Δ}
    → tyVarToFin α ∈ Ψ
     -----------------------------
    → Δ ∣ Ψ ⊢ unseal α A ∶ (＇ α) =⇒ A

  cast-seq : ∀{A B C : Ty Δ}{s t : Coercion Δ}
    → Δ ∣ Ψ ⊢ s ∶ A =⇒ B
    → Δ ∣ Ψ ⊢ t ∶ B =⇒ C
     -------------------------
    → Δ ∣ Ψ ⊢ (s ︔ t) ∶ A =⇒ C

  cast-tag : ∀{G : Ty Δ}
    → Ground G
     ---------------------
    → Δ ∣ Ψ ⊢ G ! ∶ G =⇒ `★

  cast-untag : ∀{H : Ty Δ}{ℓ : Label}
    → Ground H
     -----------------------
    → Δ ∣ Ψ ⊢ H ？ ℓ ∶ `★ =⇒ H

  cast-fun : ∀{A A′ B B′ : Ty Δ}{s t : Coercion Δ}
    → Δ ∣ Ψ ⊢ s ∶ A′ =⇒ A
    → Δ ∣ Ψ ⊢ t ∶ B =⇒ B′
     ---------------------------------------
    → Δ ∣ Ψ ⊢ (s ↦ t) ∶ (A ⇒ B) =⇒ (A′ ⇒ B′)

  -- cast-all : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
  --   → {occA : occurs zero A ≡ true}
  --   → {occB : occurs zero B ≡ true}
  --   → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A =⇒ B
  --    ----------------------------------
  --   → Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

  cast-all : ∀{A B : Ty (suc Δ)}{s : Coercion (suc Δ)}
    -- → {occA : occurs zero A ≡ true}
    -- → {occB : occurs zero B ≡ true}
    → suc Δ ∣ (outside ∷ Ψ) ⊢ s ∶ A =⇒ B
     ----------------------------------
    → Δ ∣ Ψ ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

--   cast-inst : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
--     → {occA : occurs zero A ≡ true}
--     → WfTy Δ B
--     → suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A =⇒ ⇑ᵗ B
--      --------------------------------
--     → Δ ∣ Σ ⊢ (inst B s) ∶ (`∀ A) =⇒ B

  cast-inst : ∀{A : Ty (suc Δ)}{B : Ty Δ}{s : Coercion (suc Δ)}
    -- → {occA : occurs zero A ≡ true}
    → suc Δ ∣ (inside ∷ Ψ) ⊢ s ∶ A =⇒ wkTy B
     --------------------------------
    → Δ ∣ Ψ ⊢ (inst B s) ∶ (`∀ A) =⇒ B

--   cast-gen : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
--     → {occB : occurs zero B ≡ true}
--     → WfTy Δ A
--     → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A =⇒ B
--      ----------------------------------
--     → Δ ∣ Σ ⊢ (gen A s) ∶ A =⇒ (`∀ B)

  cast-gen : ∀{A : Ty Δ}{B : Ty (suc Δ)}{s : Coercion (suc Δ)}
    -- → {occB : occurs zero B ≡ true}
    → suc Δ ∣ (inside ∷ Ψ) ⊢ s ∶ wkTy A =⇒ B
     ----------------------------------
    → Δ ∣ Ψ ⊢ (gen A s) ∶ A =⇒ (`∀ B)
