module Coercions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true; _∧_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using
  (ℕ; _<_; _≤_; _+_; _∸_; zero; suc; z<s; s<s; s≤s⁻¹)
open import Data.Nat.Properties using
  (_≟_; ≤-refl; ≤-trans; +-assoc; +-comm; +-monoʳ-≤; +-monoˡ-≤;
   +-suc; m+[n∸m]≡n; m≤m+n; m≤n+m; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import TyStore

------------------------------------------------------------------------
-- Coercions
------------------------------------------------------------------------

data Coercion : Set where
 id : Coercion
 _︔_ : Coercion → Coercion → Coercion -- sequence (composition)
 _↦_ : Coercion → Coercion → Coercion
 `∀ : Coercion → Coercion
 _! : Tag → Coercion -- inject
 _？ : Tag → Coercion -- project
 seal : TyVar → Coercion
 unseal : TyVar → Coercion
 gen : Coercion → Coercion  -- generalize
 inst : Coercion → Coercion -- instantiate

------------------------------------------------------------------------
-- Inert coercions, i.e., part of a value
------------------------------------------------------------------------

data Inert : Coercion → Set where
  _! : (G : Tag) → Inert (G !)
  seal : (α : TyVar) → Inert (seal α)
  _↦_ : (c d : Coercion) → Inert (c ↦ d)
  `∀ : (c : Coercion) → Inert (`∀ c)
  gen : (c : Coercion) → Inert (gen c)

------------------------------------------------------------------------
-- reveal/conceal B α C generate coercions between B[α] and B[C]
------------------------------------------------------------------------

mutual
  reveal : Ty → TyVar → Ty → Coercion
  reveal (＇ β) α C with α ≟ β
  reveal (＇ .α) α C | yes refl = unseal α
  reveal (＇ β) α C | no neq = id
  reveal (‵ ι) α C = id
  reveal ★ α C = id
  reveal (A ⇒ B) α C = conceal A α C ↦ reveal B α C
  reveal (`∀ A) α C = `∀ (reveal A (suc α) (⇑ᵗ C))

  conceal : Ty → TyVar → Ty → Coercion
  conceal (＇ β) α C with α ≟ β
  conceal (＇ .α) α C | yes refl = seal α
  conceal (＇ β) α C | no neq = id
  conceal (‵ ι) α C = id
  conceal ★ α C = id
  conceal (A ⇒ B) α C = reveal A α C ↦ conceal B α C
  conceal (`∀ A) α C = `∀ (conceal A (suc α) (⇑ᵗ C))

------------------------------------------------------------------------
-- Renaming type variables in coercions
------------------------------------------------------------------------

renameᶜ : Renameᵗ → Coercion → Coercion
renameᶜ ρ id = id
renameᶜ ρ (p ︔ q) = renameᶜ ρ p ︔ renameᶜ ρ q
renameᶜ ρ (G !) = renameᵍ ρ G !
renameᶜ ρ (H ？) = renameᵍ ρ H ？
renameᶜ ρ (unseal α) = unseal (ρ α)
renameᶜ ρ (seal α) = seal (ρ α)
renameᶜ ρ (p ↦ q) = renameᶜ ρ p ↦ renameᶜ ρ q
renameᶜ ρ (`∀ p) = `∀ (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (gen p) = gen (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (inst p) = inst (renameᶜ (extᵗ ρ) p)

⇑ᶜ : Coercion → Coercion
⇑ᶜ = renameᶜ suc

_[_]ᶜ : Coercion → TyVar → Coercion
c [ X ]ᶜ = renameᶜ (singleRenameᵗ X) c



-- -- Correspondence with the cambridge25 notes: the term-narrowing rules
-- -- there type the structural indices p, q under `Γ | ∅` (no seal store,
-- -- so p and q cannot contain seal or unseal coercions) while the
-- -- cast-composed indices r, s, t are typed under `Γ | Φ`.  This Agda
-- -- development instead types every coercion against the full store and
-- -- encodes the ∅-versus-Φ split as a mode environment: `tag-or-idᵈ`
-- -- (the `∶ᶜ` judgments used for p and q) forbids seal/unseal at every
-- -- variable, playing the role of ∅, while a general `μ` may grant
-- -- `seal-or-id` at store variables, playing the role of Φ.  The
-- -- per-variable `Mode` records how that variable's imprecision is
-- -- mediated: by nothing (`id-only`), by tags (`tag-or-id`), or by
-- -- seals (`seal-or-id`); tag- and seal-mediation are deliberately
-- -- incomparable in `mode≤`, which is what makes normal coercions
-- -- canonical per mode environment (`narrowing-determinedᵐ`).

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

tagModeAllowed : Mode → Bool
tagModeAllowed id-only = false
tagModeAllowed tag-or-id = true
tagModeAllowed seal-or-id = false

sealModeAllowed : Mode → Bool
sealModeAllowed id-only = false
sealModeAllowed tag-or-id = false
sealModeAllowed seal-or-id = true

tagAllowed : ModeEnv → Tag → Bool
tagAllowed μ (＇ α) = tagModeAllowed (μ α)
tagAllowed μ (‵ ι) = true
tagAllowed μ ★⇒★ = true

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶_=⇒_

data _∣_∣_⊢_∶_=⇒_ : ModeEnv → TyCtx → TyStore → Coercion → Ty → Ty → Set where

  cast-id : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{A : Ty}
    → WfTy Δ A
     ------------------------
    → μ ∣ Δ ∣ Σ ⊢ id ∶ A =⇒ A

  cast-seal : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     ---------------------------------
    → μ ∣ Δ ∣ Σ ⊢ seal α ∶ A =⇒ (＇ α)

  cast-unseal : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     -----------------------------------
    → μ ∣ Δ ∣ Σ ⊢ unseal α ∶ (＇ α) =⇒ A

  cast-seq : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{A B C : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C
     -----------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ︔ t) ∶ A =⇒ C

  cast-tag : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{G : Tag} {A : Ty}
    → WfTag Δ G
    → tagAllowed μ G ≡ true
    → G ꞉ A
     -------------------------
    → μ ∣ Δ ∣ Σ ⊢ G ! ∶ A =⇒ ★

  cast-untag : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{H : Tag}{B : Ty}
    → WfTag Δ H
    → tagAllowed μ H ≡ true
    → H ꞉ B
     --------------------------
    → μ ∣ Δ ∣ Σ ⊢ H ？ ∶ ★ =⇒ B

  cast-fun : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{A A′ B B′ : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A′ =⇒ A
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ B′
     -------------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) =⇒ (A′ ⇒ B′)

  cast-all : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{A B : Ty}{s : Coercion}
    → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A =⇒ B
     --------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

  -- ν̅ 
  cast-inst : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{A B : Ty}{s : Coercion}
    → WfTy Δ B
    → zero ∈ᵗ A
    → instᵈ μ ∣ suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A =⇒ ⇑ᵗ B
     --------------------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (inst s) ∶ (`∀ A) =⇒ B

  -- ν
  cast-gen : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : TyStore}{A B : Ty}{s : Coercion}
    → WfTy Δ A
    → zero ∈ᵗ B
    → genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A =⇒ B
     ---------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (gen s) ∶ A =⇒ (`∀ B)

infix 4 _∣_⊢_∶_=⇒_

_∣_⊢_∶_=⇒_ : TyCtx → TyStore → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ A =⇒ B = ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

  
