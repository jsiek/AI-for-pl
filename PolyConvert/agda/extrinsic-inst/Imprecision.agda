module Imprecision where

-- File Charter:
--   * Raw PolyConvert type-imprecision syntax plus its typing judgment.
--   * Defines the context modes, lookup judgment, and raw evidence operations
--     used directly by reduction.
--   * Proof engineering for algebraic properties belongs in `proof/`.

open import Types

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

data VarPrec : Set where
  X⊑X X⊑★ : VarPrec

VarPrecCtx : Set
VarPrecCtx = List VarPrec

extend-X⊑X : ℕ → VarPrecCtx → VarPrecCtx
extend-X⊑X n Γ = (replicate n X⊑X) ++ Γ

infix 4 _∋_∶_
data _∋_∶_ : VarPrecCtx → TyVar → VarPrec → Set where
  here : ∀ {Γ m} → (m ∷ Γ) ∋ zero ∶ m
  there : ∀ {Γ X m m′} → Γ ∋ X ∶ m → (m′ ∷ Γ) ∋ suc X ∶ m

∋→< : ∀ {Γ X m} → Γ ∋ X ∶ m → X < length Γ
∋→< here = z<s
∋→< (there x∈) = s<s (∋→< x∈)

------------------------------------------------------------------------
-- Raw imprecision evidence
------------------------------------------------------------------------

data Imp : Set where
  id★ : Imp
  ‵_! : TyVar → Imp
  _! : Imp → Imp
  idₓ_ : TyVar → Imp
  idₛ_ : Seal → Imp
  idι_ : Base → Imp
  _↦_ : Imp → Imp → Imp
  ‵∀_ : Imp → Imp
  ν_ : Imp → Imp

src⊑ : Imp → Ty
src⊑ id★ = ★
src⊑ (‵ X !) = ＇ X
src⊑ (p !) = src⊑ p
src⊑ (idₓ X) = ＇ X
src⊑ (idₛ α) = ｀ α
src⊑ (idι ι) = ‵ ι
src⊑ (p ↦ q) = src⊑ p ⇒ src⊑ q
src⊑ (‵∀ p) = `∀ (src⊑ p)
src⊑ (ν p) = `∀ (src⊑ p)

tgt⊑ : Imp → Ty
tgt⊑ id★ = ★
tgt⊑ (‵ X !) = ★
tgt⊑ (p !) = ★
tgt⊑ (idₓ X) = ＇ X
tgt⊑ (idₛ α) = ｀ α
tgt⊑ (idι ι) = ‵ ι
tgt⊑ (p ↦ q) = tgt⊑ p ⇒ tgt⊑ q
tgt⊑ (‵∀ p) = `∀ (tgt⊑ p)
tgt⊑ (ν p) = dropTyFrom zero (tgt⊑ p)

------------------------------------------------------------------------
-- Raw imprecision operations used by reduction
------------------------------------------------------------------------

rename⊑ : Renameᵗ → Imp → Imp
rename⊑ ρ id★ = id★
rename⊑ ρ (‵ X !) = ‵ (ρ X) !
rename⊑ ρ (p !) = rename⊑ ρ p !
rename⊑ ρ (idₓ X) = idₓ (ρ X)
rename⊑ ρ (idₛ α) = idₛ α
rename⊑ ρ (idι ι) = idι ι
rename⊑ ρ (p ↦ q) =
  (rename⊑ ρ p) ↦ (rename⊑ ρ q)
rename⊑ ρ (‵∀ p) = ‵∀ (rename⊑ (extᵗ ρ) p)
rename⊑ ρ (ν p) =
  ν (rename⊑ (extᵗ ρ) p)

⇑⊑ : Imp → Imp
⇑⊑ = rename⊑ suc

Subst⊑ : Set
Subst⊑ = TyVar → VarPrec → Imp

ren⊑ : Renameᵗ → Subst⊑
ren⊑ ρ X X⊑X = idₓ (ρ X)
ren⊑ ρ X X⊑★ = ‵ (ρ X) !

id⊑ : Subst⊑
id⊑ = ren⊑ (λ X → X)

exts⊑ : Subst⊑ → Subst⊑
exts⊑ σ zero m = id⊑ zero m
exts⊑ σ (suc X) m = rename⊑ suc (σ X m)

subst⊑ᵢ : Subst⊑ → Imp → Imp
subst⊑ᵢ σ id★ = id★
subst⊑ᵢ σ (‵ X !) = σ X X⊑★
subst⊑ᵢ σ (p !) = subst⊑ᵢ σ p !
subst⊑ᵢ σ (idₓ X) = σ X X⊑X
subst⊑ᵢ σ (idₛ α) = idₛ α
subst⊑ᵢ σ (idι ι) = idι ι
subst⊑ᵢ σ (p ↦ q) =
  (subst⊑ᵢ σ p) ↦ (subst⊑ᵢ σ q)
subst⊑ᵢ σ (‵∀ p) = ‵∀ (subst⊑ᵢ (exts⊑ σ) p)
subst⊑ᵢ σ (ν p) = ν (subst⊑ᵢ (exts⊑ σ) p)

singleImpEnv : Imp → Subst⊑
singleImpEnv p zero m = p
singleImpEnv p (suc X) X⊑X = idₓ X
singleImpEnv p (suc X) X⊑★ = ‵ X !

infixl 8 _[_]⊑ᵢ
_[_]⊑ᵢ : Imp → Imp → Imp
p [ q ]⊑ᵢ = subst⊑ᵢ (singleImpEnv q) p

-- reflImp is for the idₓ_ case of subst⊑
reflImp : Ty → Imp
reflImp (＇ X) = idₓ X
reflImp (｀ α) = idₛ α
reflImp (‵ ι) = idι ι
reflImp ★ = id★
reflImp (A ⇒ B) = (reflImp A) ↦ (reflImp B)
reflImp (`∀ A) = ‵∀ (reflImp A)

-- starImp is for the ‵_! case of subst⊑
starImp : Ty → Imp
starImp (＇ X) = ‵ X !
starImp (｀ α) = (idₛ α) !
starImp (‵ ι) = (idι ι) !
starImp ★ = id★
starImp (A ⇒ B) = ((starImp A) ↦ (starImp B)) !
starImp (`∀ A) = ν (starImp A)

subst⊑ : Substᵗ → Imp → Imp
subst⊑ σ id★ = id★
subst⊑ σ (‵ X !) = starImp (σ X)
subst⊑ σ (p !) = (subst⊑ σ p) !
subst⊑ σ (idₓ X) = reflImp (σ X)
subst⊑ σ (idₛ α) = idₛ α
subst⊑ σ (idι ι) = idι ι
subst⊑ σ (p ↦ q) = (subst⊑ σ p) ↦ (subst⊑ σ q)
subst⊑ σ (‵∀ p) = ‵∀ (subst⊑ (extsᵗ σ) p)
subst⊑ σ (ν p) = ν (subst⊑ (extsᵗ σ) p)

substAt⊑ : TyVar → Ty → Imp → Imp
substAt⊑ k T = subst⊑ (substVarFrom k T)

infixl 8 _[_]⊑
_[_]⊑ : Imp → Ty → Imp
p [ T ]⊑ = subst⊑ (singleTyEnv T) p

------------------------------------------------------------------------
-- Imprecision typing judgment
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⊑_
data _∣_⊢_⦂_⊑_ (Ψ : SealCtx) (Φ : VarPrecCtx) : Imp → Ty → Ty → Set where
  ⊢★-⊑-★ :
    ---------------------
    Ψ ∣ Φ ⊢ id★ ⦂ ★ ⊑ ★

  ⊢X-⊑-★ : ∀ {X} →
    Φ ∋ X ∶ X⊑★ →
    --------------------------
    Ψ ∣ Φ ⊢ ‵ X ! ⦂ ＇ X ⊑ ★

  ⊢A-⊑-★ : ∀ {A G p} →
    Ground G →
    Ψ ∣ Φ ⊢ p ⦂ A ⊑ G →
    ------------------------
    Ψ ∣ Φ ⊢ p ! ⦂ A ⊑ ★

  ⊢X-⊑-X : ∀ {X} →
    Φ ∋ X ∶ X⊑X →
    -----------------------------
    Ψ ∣ Φ ⊢ idₓ X ⦂ ＇ X ⊑ ＇ X

  ⊢α-⊑-α : ∀ {α} →
    WfTy (length Φ) Ψ (｀ α) →
    -----------------------------
    Ψ ∣ Φ ⊢ idₛ α ⦂ ｀ α ⊑ ｀ α

  ⊢ι-⊑-ι : ∀ {ι} →
    ----------------------------
    Ψ ∣ Φ ⊢ idι ι ⦂ ‵ ι ⊑ ‵ ι

  ⊢A⇒B-⊑-A′⇒B′ : ∀ {A A′ B B′ p q} →
    Ψ ∣ Φ ⊢ p ⦂ A ⊑ A′ →
    Ψ ∣ Φ ⊢ q ⦂ B ⊑ B′ →
    ---------------------------------------------
    Ψ ∣ Φ ⊢ p ↦ q ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ⊢∀A-⊑-∀B : ∀ {A B p} →
    {occA : occurs zero A ≡ true} →
    {occB : occurs zero B ≡ true} →
    Ψ ∣ X⊑X ∷ Φ ⊢ p ⦂ A ⊑ B →
    -----------------------------------
    Ψ ∣ Φ ⊢ ‵∀ p ⦂ (`∀ A) ⊑ (`∀ B)

  ⊢∀A-⊑-B : ∀ {A B p} →
    occurs zero A ≡ true →
    WfTy (length Φ) Ψ B →
    Ψ ∣ X⊑★ ∷ Φ ⊢ p ⦂ A ⊑ ⇑ᵗ B →
    -----------------------------
    Ψ ∣ Φ ⊢ ν p ⦂ (`∀ A) ⊑ B

infix 4 _∣_⊢_⦂_⊒_
_∣_⊢_⦂_⊒_ : SealCtx → VarPrecCtx → Imp → Ty → Ty → Set
Ψ ∣ Φ ⊢ p ⦂ A ⊒ B = Ψ ∣ Φ ⊢ p ⦂ B ⊑ A

-- A is a lower bound of B and C
lb : SealCtx → VarPrecCtx → Ty → Ty → Ty → Set
lb Ψ Φ A B C = ∃[ p ] ∃[ q ] (Ψ ∣ Φ ⊢ p ⦂ A ⊑ B) × (Ψ ∣ Φ ⊢ q ⦂ A ⊑ C)

-- A is a greatest lower bound of B and C
glb : SealCtx → VarPrecCtx → Ty → Ty → Ty → Set
glb Ψ Φ A B C = lb Ψ Φ A B C × (∀ A′ → lb Ψ Φ A′ B C → ∃[ p ] Ψ ∣ Φ ⊢ p ⦂ A′ ⊑ A)

-- A is an upper bound of B and C
ub : SealCtx → VarPrecCtx → Ty → Ty → Ty → Set
ub Ψ Φ A B C = ∃[ p ] ∃[ q ] (Ψ ∣ Φ ⊢ p ⦂ B ⊑ A) × (Ψ ∣ Φ ⊢ q ⦂ C ⊑ A)

-- A is a least upper bound of B and C
lub : SealCtx → VarPrecCtx → Ty → Ty → Ty → Set
lub Ψ Φ A B C = ub Ψ Φ A B C × (∀ A′ → ub Ψ Φ A′ B C → ∃[ p ] Ψ ∣ Φ ⊢ p ⦂ A ⊑ A′)
