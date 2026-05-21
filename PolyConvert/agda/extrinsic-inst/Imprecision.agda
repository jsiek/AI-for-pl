module Imprecision where

-- File Charter:
--   * Raw PolyConvert type-imprecision syntax plus its typing judgment.
--   * Defines the context modes, lookup judgment, and raw evidence operations
--     used directly by reduction.
--   * Proof engineering for algebraic properties belongs in `proof/`.

open import Types

open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)

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
  ★-⊑-★ : Imp
  X-⊑-★ : TyVar → Imp
  A-⊑-★ : Imp → Imp
  X-⊑-X : TyVar → Imp
  α-⊑-α : Seal → Imp
  ι-⊑-ι : Base → Imp
  A⇒B-⊑-A′⇒B′ : Imp → Imp → Imp
  ∀A-⊑-∀B : Imp → Imp
  ∀A-⊑-B : Imp → Imp

src⊑ : Imp → Ty
src⊑ ★-⊑-★ = ★
src⊑ (X-⊑-★ X) = ＇ X
src⊑ (A-⊑-★ p) = src⊑ p
src⊑ (X-⊑-X X) = ＇ X
src⊑ (α-⊑-α α) = ｀ α
src⊑ (ι-⊑-ι ι) = ‵ ι
src⊑ (A⇒B-⊑-A′⇒B′ p q) = src⊑ p ⇒ src⊑ q
src⊑ (∀A-⊑-∀B p) = `∀ (src⊑ p)
src⊑ (∀A-⊑-B p) = `∀ (src⊑ p)

tgt⊑ : Imp → Ty
tgt⊑ ★-⊑-★ = ★
tgt⊑ (X-⊑-★ X) = ★
tgt⊑ (A-⊑-★ p) = ★
tgt⊑ (X-⊑-X X) = ＇ X
tgt⊑ (α-⊑-α α) = ｀ α
tgt⊑ (ι-⊑-ι ι) = ‵ ι
tgt⊑ (A⇒B-⊑-A′⇒B′ p q) = tgt⊑ p ⇒ tgt⊑ q
tgt⊑ (∀A-⊑-∀B p) = `∀ (tgt⊑ p)
tgt⊑ (∀A-⊑-B p) = dropTyFrom zero (tgt⊑ p)

------------------------------------------------------------------------
-- Raw imprecision operations used by reduction
------------------------------------------------------------------------

renameImp : Renameᵗ → Imp → Imp
renameImp ρ ★-⊑-★ = ★-⊑-★
renameImp ρ (X-⊑-★ X) = X-⊑-★ (ρ X)
renameImp ρ (A-⊑-★ p) = A-⊑-★ (renameImp ρ p)
renameImp ρ (X-⊑-X X) = X-⊑-X (ρ X)
renameImp ρ (α-⊑-α α) = α-⊑-α α
renameImp ρ (ι-⊑-ι ι) = ι-⊑-ι ι
renameImp ρ (A⇒B-⊑-A′⇒B′ p q) =
  A⇒B-⊑-A′⇒B′ (renameImp ρ p) (renameImp ρ q)
renameImp ρ (∀A-⊑-∀B p) = ∀A-⊑-∀B (renameImp (extᵗ ρ) p)
renameImp ρ (∀A-⊑-B p) =
  ∀A-⊑-B (renameImp (extᵗ ρ) p)

⇑⊑ : Imp → Imp
⇑⊑ = renameImp suc

Subst⊑ : Set
Subst⊑ = TyVar → VarPrec → Imp

ren⊑ : Renameᵗ → Subst⊑
ren⊑ ρ X X⊑X = X-⊑-X (ρ X)
ren⊑ ρ X X⊑★ = X-⊑-★ (ρ X)

id⊑ : Subst⊑
id⊑ = ren⊑ (λ X → X)

exts⊑ : Subst⊑ → Subst⊑
exts⊑ σ zero m = id⊑ zero m
exts⊑ σ (suc X) m = renameImp suc (σ X m)

subst⊑ : Subst⊑ → Imp → Imp
subst⊑ σ ★-⊑-★ = ★-⊑-★
subst⊑ σ (X-⊑-★ X) = σ X X⊑★
subst⊑ σ (A-⊑-★ p) = A-⊑-★ (subst⊑ σ p)
subst⊑ σ (X-⊑-X X) = σ X X⊑X
subst⊑ σ (α-⊑-α α) = α-⊑-α α
subst⊑ σ (ι-⊑-ι ι) = ι-⊑-ι ι
subst⊑ σ (A⇒B-⊑-A′⇒B′ p q) =
  A⇒B-⊑-A′⇒B′ (subst⊑ σ p) (subst⊑ σ q)
subst⊑ σ (∀A-⊑-∀B p) = ∀A-⊑-∀B (subst⊑ (exts⊑ σ) p)
subst⊑ σ (∀A-⊑-B p) = ∀A-⊑-B (subst⊑ (exts⊑ σ) p)

singleImpEnv : Imp → Subst⊑
singleImpEnv p zero m = p
singleImpEnv p (suc X) X⊑X = X-⊑-X X
singleImpEnv p (suc X) X⊑★ = X-⊑-★ X

infixl 8 _[_]⊑ᵢ
_[_]⊑ᵢ : Imp → Imp → Imp
p [ q ]⊑ᵢ = subst⊑ (singleImpEnv q) p

-- reflImp is for the X-⊑-X case of substImp
reflImp : Ty → Imp
reflImp (＇ X) = X-⊑-X X
reflImp (｀ α) = α-⊑-α α
reflImp (‵ ι) = ι-⊑-ι ι
reflImp ★ = ★-⊑-★
reflImp (A ⇒ B) = A⇒B-⊑-A′⇒B′ (reflImp A) (reflImp B)
reflImp (`∀ A) = ∀A-⊑-∀B (reflImp A)

-- starImp is for the X-⊑-★ case of substImp
starImp : Ty → Imp
starImp (＇ X) = X-⊑-★ X
starImp (｀ α) = A-⊑-★ (α-⊑-α α)
starImp (‵ ι) = A-⊑-★ (ι-⊑-ι ι)
starImp ★ = ★-⊑-★
starImp (A ⇒ B) = A-⊑-★ (A⇒B-⊑-A′⇒B′ (starImp A) (starImp B))
starImp (`∀ A) = ∀A-⊑-B (starImp A)

substImp : Substᵗ → Imp → Imp
substImp σ ★-⊑-★ = ★-⊑-★
substImp σ (X-⊑-★ X) = starImp (σ X)
substImp σ (A-⊑-★ p) = A-⊑-★ (substImp σ p)
substImp σ (X-⊑-X X) = reflImp (σ X)
substImp σ (α-⊑-α α) = α-⊑-α α
substImp σ (ι-⊑-ι ι) = ι-⊑-ι ι
substImp σ (A⇒B-⊑-A′⇒B′ p q) = A⇒B-⊑-A′⇒B′ (substImp σ p) (substImp σ q)
substImp σ (∀A-⊑-∀B p) = ∀A-⊑-∀B (substImp (extsᵗ σ) p)
substImp σ (∀A-⊑-B p) = ∀A-⊑-B (substImp (extsᵗ σ) p)

substAtImp : TyVar → Ty → Imp → Imp
substAtImp k T = substImp (substVarFrom k T)

infixl 8 _[_]⊑
_[_]⊑ : Imp → Ty → Imp
p [ T ]⊑ = substImp (singleTyEnv T) p

------------------------------------------------------------------------
-- Imprecision typing judgment
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⊑_
data _∣_⊢_⦂_⊑_ (Ψ : SealCtx) (Γ : VarPrecCtx) : Imp → Ty → Ty → Set where
  ⊢★-⊑-★ :
    ---------------------
    Ψ ∣ Γ ⊢ ★-⊑-★ ⦂ ★ ⊑ ★

  ⊢X-⊑-★ : ∀ {X} →
    Γ ∋ X ∶ X⊑★ →
    --------------------------
    Ψ ∣ Γ ⊢ X-⊑-★ X ⦂ ＇ X ⊑ ★

  ⊢A-⊑-★ : ∀ {A G p} →
    Ground G →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
    ------------------------
    Ψ ∣ Γ ⊢ A-⊑-★ p ⦂ A ⊑ ★

  ⊢X-⊑-X : ∀ {X} →
    Γ ∋ X ∶ X⊑X →
    -----------------------------
    Ψ ∣ Γ ⊢ X-⊑-X X ⦂ ＇ X ⊑ ＇ X

  ⊢α-⊑-α : ∀ {α} →
    WfTy (length Γ) Ψ (｀ α) →
    -----------------------------
    Ψ ∣ Γ ⊢ α-⊑-α α ⦂ ｀ α ⊑ ｀ α

  ⊢ι-⊑-ι : ∀ {ι} →
    ----------------------------
    Ψ ∣ Γ ⊢ ι-⊑-ι ι ⦂ ‵ ι ⊑ ‵ ι

  ⊢A⇒B-⊑-A′⇒B′ : ∀ {A A′ B B′ p q} →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ A′ →
    Ψ ∣ Γ ⊢ q ⦂ B ⊑ B′ →
    ---------------------------------------------
    Ψ ∣ Γ ⊢ A⇒B-⊑-A′⇒B′ p q ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ⊢∀A-⊑-∀B : ∀ {A B p} →
    Ψ ∣ X⊑X ∷ Γ ⊢ p ⦂ A ⊑ B →
    -----------------------------------
    Ψ ∣ Γ ⊢ ∀A-⊑-∀B p ⦂ (`∀ A) ⊑ (`∀ B)

  ⊢∀A-⊑-B : ∀ {A B p} →
    WfTy (length Γ) Ψ B →
    Ψ ∣ X⊑★ ∷ Γ ⊢ p ⦂ A ⊑ ⇑ᵗ B →
    -----------------------------
    Ψ ∣ Γ ⊢ ∀A-⊑-B p ⦂ (`∀ A) ⊑ B

infix 4 _∣_⊢_⦂_⊒_
_∣_⊢_⦂_⊒_ : SealCtx → VarPrecCtx → Imp → Ty → Ty → Set
Ψ ∣ Γ ⊢ p ⦂ A ⊒ B = Ψ ∣ Γ ⊢ p ⦂ B ⊑ A
