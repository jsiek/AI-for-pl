module Imprecision where

-- File Charter:
--   * Raw PolyConvert type-imprecision syntax plus its typing judgment.
--   * Defines the context modes, lookup judgment, and raw evidence operations
--     used directly by reduction.
--   * Proof engineering for algebraic properties belongs in `proof/`.

open import Types

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

data VarPrec : Set where
  X⊑X X⊑★ : VarPrec

VarPrecCtx : Set
VarPrecCtx = List VarPrec

plains : ℕ → VarPrecCtx → VarPrecCtx
plains n Γ = (replicate n X⊑X) ++ Γ

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
  ∀A-⊑-B : Ty → Imp → Imp

src⊑ : Imp → Ty
src⊑ ★-⊑-★ = ★
src⊑ (X-⊑-★ X) = ＇ X
src⊑ (A-⊑-★ p) = src⊑ p
src⊑ (X-⊑-X X) = ＇ X
src⊑ (α-⊑-α α) = ｀ α
src⊑ (ι-⊑-ι ι) = ‵ ι
src⊑ (A⇒B-⊑-A′⇒B′ p q) = src⊑ p ⇒ src⊑ q
src⊑ (∀A-⊑-∀B p) = `∀ (src⊑ p)
src⊑ (∀A-⊑-B B p) = `∀ (src⊑ p)

tgt⊑ : Imp → Ty
tgt⊑ ★-⊑-★ = ★
tgt⊑ (X-⊑-★ X) = ★
tgt⊑ (A-⊑-★ p) = ★
tgt⊑ (X-⊑-X X) = ＇ X
tgt⊑ (α-⊑-α α) = ｀ α
tgt⊑ (ι-⊑-ι ι) = ‵ ι
tgt⊑ (A⇒B-⊑-A′⇒B′ p q) = tgt⊑ p ⇒ tgt⊑ q
tgt⊑ (∀A-⊑-∀B p) = `∀ (tgt⊑ p)
tgt⊑ (∀A-⊑-B B p) = B

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
renameImp ρ (∀A-⊑-B B p) =
  ∀A-⊑-B (renameᵗ ρ B) (renameImp (extᵗ ρ) p)

reflImp : Ty → Imp
reflImp (＇ X) = X-⊑-X X
reflImp (｀ α) = α-⊑-α α
reflImp (‵ ι) = ι-⊑-ι ι
reflImp ★ = ★-⊑-★
reflImp (A ⇒ B) = A⇒B-⊑-A′⇒B′ (reflImp A) (reflImp B)
reflImp (`∀ A) = ∀A-⊑-∀B (reflImp A)

starImp : Ty → Imp
starImp (＇ X) = X-⊑-★ X
starImp (｀ α) = A-⊑-★ (α-⊑-α α)
starImp (‵ ι) = A-⊑-★ (ι-⊑-ι ι)
starImp ★ = ★-⊑-★
starImp (A ⇒ B) =
  A-⊑-★ (A⇒B-⊑-A′⇒B′ (starImp A) (starImp B))
starImp (`∀ A) = ∀A-⊑-B ★ (starImp A)

substImp : Substᵗ → Imp → Imp
substImp σ ★-⊑-★ = ★-⊑-★
substImp σ (X-⊑-★ X) = starImp (σ X)
substImp σ (A-⊑-★ p) = A-⊑-★ (substImp σ p)
substImp σ (X-⊑-X X) = reflImp (σ X)
substImp σ (α-⊑-α α) = α-⊑-α α
substImp σ (ι-⊑-ι ι) = ι-⊑-ι ι
substImp σ (A⇒B-⊑-A′⇒B′ p q) =
  A⇒B-⊑-A′⇒B′ (substImp σ p) (substImp σ q)
substImp σ (∀A-⊑-∀B p) = ∀A-⊑-∀B (substImp (extsᵗ σ) p)
substImp σ (∀A-⊑-B B p) =
  ∀A-⊑-B (substᵗ σ B) (substImp (extsᵗ σ) p)

substPlainAtImp : TyVar → Ty → Imp → Imp
substPlainAtImp k T = substImp (substVarFrom k T)

infixl 8 _[_]⊑
_[_]⊑ : Imp → Ty → Imp
p [ T ]⊑ = substImp (singleTyEnv T) p

------------------------------------------------------------------------
-- Imprecision typing judgment
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⊑_
data _∣_⊢_⦂_⊑_ (Ψ : SealCtx) (Γ : VarPrecCtx) : Imp → Ty → Ty → Set where
  ⊢★-⊑-★ :
    Ψ ∣ Γ ⊢ ★-⊑-★ ⦂ ★ ⊑ ★

  ⊢X-⊑-★ : ∀ {X} →
    Γ ∋ X ∶ X⊑★ →
    Ψ ∣ Γ ⊢ X-⊑-★ X ⦂ ＇ X ⊑ ★

  ⊢A-⊑-★ : ∀ {A G p} →
    Ground G →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
    Ψ ∣ Γ ⊢ A-⊑-★ p ⦂ A ⊑ ★

  ⊢X-⊑-X : ∀ {X} →
    Γ ∋ X ∶ X⊑X →
    Ψ ∣ Γ ⊢ X-⊑-X X ⦂ ＇ X ⊑ ＇ X

  ⊢α-⊑-α : ∀ {α} →
    WfTy (length Γ) Ψ (｀ α) →
    Ψ ∣ Γ ⊢ α-⊑-α α ⦂ ｀ α ⊑ ｀ α

  ⊢ι-⊑-ι : ∀ {ι} →
    Ψ ∣ Γ ⊢ ι-⊑-ι ι ⦂ ‵ ι ⊑ ‵ ι

  ⊢A⇒B-⊑-A′⇒B′ : ∀ {A A′ B B′ p q} →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ A′ →
    Ψ ∣ Γ ⊢ q ⦂ B ⊑ B′ →
    Ψ ∣ Γ ⊢ A⇒B-⊑-A′⇒B′ p q ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ⊢∀A-⊑-∀B : ∀ {A B p} →
    Ψ ∣ (X⊑X ∷ Γ) ⊢ p ⦂ A ⊑ B →
    Ψ ∣ Γ ⊢ ∀A-⊑-∀B p ⦂ (`∀ A) ⊑ (`∀ B)

  ⊢∀A-⊑-B : ∀ {A B p} →
    WfTy (length Γ) Ψ B →
    Ψ ∣ (X⊑★ ∷ Γ) ⊢ p ⦂ A ⊑ ⇑ᵗ B →
    Ψ ∣ Γ ⊢ ∀A-⊑-B B p ⦂ (`∀ A) ⊑ B

infix 4 _∣_⊢_⦂_⊒_
_∣_⊢_⦂_⊒_ : SealCtx → VarPrecCtx → Imp → Ty → Ty → Set
Ψ ∣ Γ ⊢ p ⦂ A ⊒ B = Ψ ∣ Γ ⊢ p ⦂ B ⊑ A

src⊑-correct :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  src⊑ p ≡ A
src⊑-correct ⊢★-⊑-★ = refl
src⊑-correct (⊢X-⊑-★ xν) = refl
src⊑-correct (⊢A-⊑-★ g p⊢) = src⊑-correct p⊢
src⊑-correct (⊢X-⊑-X x∈) = refl
src⊑-correct (⊢α-⊑-α wfα) = refl
src⊑-correct ⊢ι-⊑-ι = refl
src⊑-correct (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  cong₂ _⇒_ (src⊑-correct p⊢) (src⊑-correct q⊢)
src⊑-correct (⊢∀A-⊑-∀B p⊢) = cong `∀ (src⊑-correct p⊢)
src⊑-correct (⊢∀A-⊑-B wfB p⊢) = cong `∀ (src⊑-correct p⊢)

tgt⊑-correct :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  tgt⊑ p ≡ B
tgt⊑-correct ⊢★-⊑-★ = refl
tgt⊑-correct (⊢X-⊑-★ xν) = refl
tgt⊑-correct (⊢A-⊑-★ g p⊢) = refl
tgt⊑-correct (⊢X-⊑-X x∈) = refl
tgt⊑-correct (⊢α-⊑-α wfα) = refl
tgt⊑-correct ⊢ι-⊑-ι = refl
tgt⊑-correct (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  cong₂ _⇒_ (tgt⊑-correct p⊢) (tgt⊑-correct q⊢)
tgt⊑-correct (⊢∀A-⊑-∀B p⊢) = cong `∀ (tgt⊑-correct p⊢)
tgt⊑-correct (⊢∀A-⊑-B wfB p⊢) = refl

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

⊑-src-wf :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  WfTy (length Γ) Ψ A
⊑-src-wf ⊢★-⊑-★ = wf★
⊑-src-wf (⊢X-⊑-★ xν) = wfVar (∋→< xν)
⊑-src-wf (⊢A-⊑-★ g p⊢) = ⊑-src-wf p⊢
⊑-src-wf (⊢X-⊑-X x∈) = wfVar (∋→< x∈)
⊑-src-wf (⊢α-⊑-α wfα) = wfα
⊑-src-wf ⊢ι-⊑-ι = wfBase
⊑-src-wf (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  wf⇒ (⊑-src-wf p⊢) (⊑-src-wf q⊢)
⊑-src-wf (⊢∀A-⊑-∀B p⊢) = wf∀ (⊑-src-wf p⊢)
⊑-src-wf (⊢∀A-⊑-B wfB p⊢) = wf∀ (⊑-src-wf p⊢)

⊑-tgt-wf :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  WfTy (length Γ) Ψ B
⊑-tgt-wf ⊢★-⊑-★ = wf★
⊑-tgt-wf (⊢X-⊑-★ xν) = wf★
⊑-tgt-wf (⊢A-⊑-★ g p⊢) = wf★
⊑-tgt-wf (⊢X-⊑-X x∈) = wfVar (∋→< x∈)
⊑-tgt-wf (⊢α-⊑-α wfα) = wfα
⊑-tgt-wf ⊢ι-⊑-ι = wfBase
⊑-tgt-wf (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  wf⇒ (⊑-tgt-wf p⊢) (⊑-tgt-wf q⊢)
⊑-tgt-wf (⊢∀A-⊑-∀B p⊢) = wf∀ (⊑-tgt-wf p⊢)
⊑-tgt-wf (⊢∀A-⊑-B wfB p⊢) = wfB
