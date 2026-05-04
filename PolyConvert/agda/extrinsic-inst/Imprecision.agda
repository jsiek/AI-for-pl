module Imprecision where

-- File Charter:
--   * Raw PolyConvert type-imprecision syntax plus its typing judgment.
--   * Defines the context modes, lookup judgment, and raw evidence operations
--     used directly by reduction.
--   * Proof engineering for algebraic properties belongs in `proof/`.

open import Types

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

data VarMode : Set where
  plain ν-bound : VarMode

ICtx : Set
ICtx = List VarMode

plains : ℕ → ICtx → ICtx
plains zero Γ = Γ
plains (suc n) Γ = plain ∷ plains n Γ

infix 4 _∋_∶_
data _∋_∶_ : ICtx → TyVar → VarMode → Set where
  here : ∀ {Γ m} → (m ∷ Γ) ∋ zero ∶ m
  there : ∀ {Γ X m m′} → Γ ∋ X ∶ m → (m′ ∷ Γ) ∋ suc X ∶ m

∋→< : ∀ {Γ X m} → Γ ∋ X ∶ m → X < length Γ
∋→< here = z<s
∋→< (there x∈) = s<s (∋→< x∈)

------------------------------------------------------------------------
-- Raw imprecision evidence
------------------------------------------------------------------------

data Imp : Set where
  ★⊑★ : Imp
  X⊑★ : TyVar → Imp
  A⊑★ : Imp → Imp
  X⊑X : TyVar → Imp
  α⊑α : Seal → Imp
  ι⊑ι : Base → Imp
  A⇒B⊑A′⇒B′ : Imp → Imp → Imp
  `∀A⊑∀B : Imp → Imp
  `∀A⊑B : Ty → Imp → Imp

src⊑ : Imp → Ty
src⊑ ★⊑★ = ★
src⊑ (X⊑★ X) = ＇ X
src⊑ (A⊑★ p) = src⊑ p
src⊑ (X⊑X X) = ＇ X
src⊑ (α⊑α α) = ｀ α
src⊑ (ι⊑ι ι) = ‵ ι
src⊑ (A⇒B⊑A′⇒B′ p q) = src⊑ p ⇒ src⊑ q
src⊑ (`∀A⊑∀B p) = `∀ (src⊑ p)
src⊑ (`∀A⊑B B p) = `∀ (src⊑ p)

tgt⊑ : Imp → Ty
tgt⊑ ★⊑★ = ★
tgt⊑ (X⊑★ X) = ★
tgt⊑ (A⊑★ p) = ★
tgt⊑ (X⊑X X) = ＇ X
tgt⊑ (α⊑α α) = ｀ α
tgt⊑ (ι⊑ι ι) = ‵ ι
tgt⊑ (A⇒B⊑A′⇒B′ p q) = tgt⊑ p ⇒ tgt⊑ q
tgt⊑ (`∀A⊑∀B p) = `∀ (tgt⊑ p)
tgt⊑ (`∀A⊑B B p) = B

------------------------------------------------------------------------
-- Raw imprecision operations used by reduction
------------------------------------------------------------------------

renameImp : Renameᵗ → Imp → Imp
renameImp ρ ★⊑★ = ★⊑★
renameImp ρ (X⊑★ X) = X⊑★ (ρ X)
renameImp ρ (A⊑★ p) = A⊑★ (renameImp ρ p)
renameImp ρ (X⊑X X) = X⊑X (ρ X)
renameImp ρ (α⊑α α) = α⊑α α
renameImp ρ (ι⊑ι ι) = ι⊑ι ι
renameImp ρ (A⇒B⊑A′⇒B′ p q) =
  A⇒B⊑A′⇒B′ (renameImp ρ p) (renameImp ρ q)
renameImp ρ (`∀A⊑∀B p) = `∀A⊑∀B (renameImp (extᵗ ρ) p)
renameImp ρ (`∀A⊑B B p) =
  `∀A⊑B (renameᵗ ρ B) (renameImp (extᵗ ρ) p)

reflImp : Ty → Imp
reflImp (＇ X) = X⊑X X
reflImp (｀ α) = α⊑α α
reflImp (‵ ι) = ι⊑ι ι
reflImp ★ = ★⊑★
reflImp (A ⇒ B) = A⇒B⊑A′⇒B′ (reflImp A) (reflImp B)
reflImp (`∀ A) = `∀A⊑∀B (reflImp A)

starImp : Ty → Imp
starImp (＇ X) = X⊑★ X
starImp (｀ α) = A⊑★ (α⊑α α)
starImp (‵ ι) = A⊑★ (ι⊑ι ι)
starImp ★ = ★⊑★
starImp (A ⇒ B) =
  A⊑★ (A⇒B⊑A′⇒B′ (starImp A) (starImp B))
starImp (`∀ A) = `∀A⊑B ★ (starImp A)

substImp : Substᵗ → Imp → Imp
substImp σ ★⊑★ = ★⊑★
substImp σ (X⊑★ X) = starImp (σ X)
substImp σ (A⊑★ p) = A⊑★ (substImp σ p)
substImp σ (X⊑X X) = reflImp (σ X)
substImp σ (α⊑α α) = α⊑α α
substImp σ (ι⊑ι ι) = ι⊑ι ι
substImp σ (A⇒B⊑A′⇒B′ p q) =
  A⇒B⊑A′⇒B′ (substImp σ p) (substImp σ q)
substImp σ (`∀A⊑∀B p) = `∀A⊑∀B (substImp (extsᵗ σ) p)
substImp σ (`∀A⊑B B p) =
  `∀A⊑B (substᵗ σ B) (substImp (extsᵗ σ) p)

substPlainAtImp : TyVar → Ty → Imp → Imp
substPlainAtImp k T = substImp (plainSubstVarFrom k T)

infixl 8 _[_]⊑
_[_]⊑ : Imp → Ty → Imp
p [ T ]⊑ = substImp (singleTyEnv T) p

------------------------------------------------------------------------
-- Imprecision typing judgment
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⊑_
data _∣_⊢_⦂_⊑_ (Ψ : SealCtx) (Γ : ICtx) : Imp → Ty → Ty → Set where
  ⊑-★★ :
    Ψ ∣ Γ ⊢ ★⊑★ ⦂ ★ ⊑ ★

  ⊑-★ν : ∀ {X} →
    Γ ∋ X ∶ ν-bound →
    Ψ ∣ Γ ⊢ X⊑★ X ⦂ ＇ X ⊑ ★

  ⊑-★ : ∀ {A G p} →
    Ground G →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
    Ψ ∣ Γ ⊢ A⊑★ p ⦂ A ⊑ ★

  ⊑-＇ : ∀ {X} →
    Γ ∋ X ∶ plain →
    Ψ ∣ Γ ⊢ X⊑X X ⦂ ＇ X ⊑ ＇ X

  ⊑-｀ : ∀ {α} →
    WfTy (length Γ) Ψ (｀ α) →
    Ψ ∣ Γ ⊢ α⊑α α ⦂ ｀ α ⊑ ｀ α

  ⊑-‵ : ∀ {ι} →
    Ψ ∣ Γ ⊢ ι⊑ι ι ⦂ ‵ ι ⊑ ‵ ι

  ⊑-⇒ : ∀ {A A′ B B′ p q} →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ A′ →
    Ψ ∣ Γ ⊢ q ⦂ B ⊑ B′ →
    Ψ ∣ Γ ⊢ A⇒B⊑A′⇒B′ p q ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ⊑-∀ : ∀ {A B p} →
    Ψ ∣ (plain ∷ Γ) ⊢ p ⦂ A ⊑ B →
    Ψ ∣ Γ ⊢ `∀A⊑∀B p ⦂ (`∀ A) ⊑ (`∀ B)

  ⊑-ν : ∀ {A B p} →
    WfTy (length Γ) Ψ B →
    .(occurs zero A ≡ true) →
    Ψ ∣ (ν-bound ∷ Γ) ⊢ p ⦂ A ⊑ ⇑ᵗ B →
    Ψ ∣ Γ ⊢ `∀A⊑B B p ⦂ (`∀ A) ⊑ B

infix 4 _∣_⊢_⦂_⊒_
_∣_⊢_⦂_⊒_ : SealCtx → ICtx → Imp → Ty → Ty → Set
Ψ ∣ Γ ⊢ p ⦂ A ⊒ B = Ψ ∣ Γ ⊢ p ⦂ B ⊑ A

src⊑-correct :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  src⊑ p ≡ A
src⊑-correct ⊑-★★ = refl
src⊑-correct (⊑-★ν xν) = refl
src⊑-correct (⊑-★ g p⊢) = src⊑-correct p⊢
src⊑-correct (⊑-＇ x∈) = refl
src⊑-correct (⊑-｀ wfα) = refl
src⊑-correct ⊑-‵ = refl
src⊑-correct (⊑-⇒ p⊢ q⊢) =
  cong₂ _⇒_ (src⊑-correct p⊢) (src⊑-correct q⊢)
src⊑-correct (⊑-∀ p⊢) = cong `∀ (src⊑-correct p⊢)
src⊑-correct (⊑-ν wfB occ p⊢) = cong `∀ (src⊑-correct p⊢)

tgt⊑-correct :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  tgt⊑ p ≡ B
tgt⊑-correct ⊑-★★ = refl
tgt⊑-correct (⊑-★ν xν) = refl
tgt⊑-correct (⊑-★ g p⊢) = refl
tgt⊑-correct (⊑-＇ x∈) = refl
tgt⊑-correct (⊑-｀ wfα) = refl
tgt⊑-correct ⊑-‵ = refl
tgt⊑-correct (⊑-⇒ p⊢ q⊢) =
  cong₂ _⇒_ (tgt⊑-correct p⊢) (tgt⊑-correct q⊢)
tgt⊑-correct (⊑-∀ p⊢) = cong `∀ (tgt⊑-correct p⊢)
tgt⊑-correct (⊑-ν wfB occ p⊢) = refl

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

⊑-src-wf :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  WfTy (length Γ) Ψ A
⊑-src-wf ⊑-★★ = wf★
⊑-src-wf (⊑-★ν xν) = wfVar (∋→< xν)
⊑-src-wf (⊑-★ g p⊢) = ⊑-src-wf p⊢
⊑-src-wf (⊑-＇ x∈) = wfVar (∋→< x∈)
⊑-src-wf (⊑-｀ wfα) = wfα
⊑-src-wf ⊑-‵ = wfBase
⊑-src-wf (⊑-⇒ p⊢ q⊢) =
  wf⇒ (⊑-src-wf p⊢) (⊑-src-wf q⊢)
⊑-src-wf (⊑-∀ p⊢) = wf∀ (⊑-src-wf p⊢)
⊑-src-wf (⊑-ν wfB occ p⊢) = wf∀ (⊑-src-wf p⊢)

⊑-tgt-wf :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  WfTy (length Γ) Ψ B
⊑-tgt-wf ⊑-★★ = wf★
⊑-tgt-wf (⊑-★ν xν) = wf★
⊑-tgt-wf (⊑-★ g p⊢) = wf★
⊑-tgt-wf (⊑-＇ x∈) = wfVar (∋→< x∈)
⊑-tgt-wf (⊑-｀ wfα) = wfα
⊑-tgt-wf ⊑-‵ = wfBase
⊑-tgt-wf (⊑-⇒ p⊢ q⊢) =
  wf⇒ (⊑-tgt-wf p⊢) (⊑-tgt-wf q⊢)
⊑-tgt-wf (⊑-∀ p⊢) = wf∀ (⊑-tgt-wf p⊢)
⊑-tgt-wf (⊑-ν wfB occ p⊢) = wfB
