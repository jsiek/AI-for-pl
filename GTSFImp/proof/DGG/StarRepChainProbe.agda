module proof.DGG.StarRepChainProbe where

-- File Charter:
--   * Records the concrete M3 star-representation chain assembly.
--   * The source has `Xᴸ` at center `a` with store representation `＇ X`,
--     and `X` at center `b` with representation `★`.
--   * The target has only `Y` at center `a`; no target variable is aligned
--     with source `X`.
--   * The output rebuilds the inner `X` seal source-only at its `⊑★`
--     obligation, then pairs the outer `Xᴸ/Y` seals and consumes the
--     target tag only in the input derivation.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ;
   id; _!)
open import Conversion using (seal)
open import CastTerms using (Term; _⟨_⟩; _↓_; $)
open import Imprecision
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; TagRebaseAtᴸ; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   RebaseAt; store-rep-imp)

private
  Xᴸ : TyVar 2
  Xᴸ = Fin.zero

  X : TyVar 2
  X = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

------------------------------------------------------------------------
-- Stores, embeddings, and the three-center world
------------------------------------------------------------------------

source-store : TyStore 2
source-store =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

target-store : TyStore 1
target-store = store-bind store-empty ★

probe-μ : ImpEnv 3
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★
probe-μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

ηᴸ-ab : 2 ↪ᵗ 3
ηᴸ-ab = keep (keep (skip empty))

ηᴿ-a : 1 ↪ᵗ 3
ηᴿ-a = keep (skip (skip empty))

-- Placement table (a = 0, b = 1, c = 2):
--
--             Xᴸ   X    Y
--   W          a   b    a
--
-- Center `b` has no target variable.  All three marks are `X⊑★`.

W : World 2 1 3
W = world ηᴸ-ab ηᴿ-a probe-μ source-store target-store

------------------------------------------------------------------------
-- Store typing and casts
------------------------------------------------------------------------

Xᴸ∈ : source-store ∋ Xᴸ ⦂ ＇ X
Xᴸ∈ = Z∋ refl

X∈ : source-store ∋ X ⦂ ★
X∈ = S-bind∋ (Z∋ refl) refl

Y∈ : target-store ∋ Y ⦂ ★
Y∈ = Z∋ refl

source-Xᴸ-seal-⊢ :
  source-store Conv.⊢↓[ just Xᴸ ] seal Xᴸ (＇ X)
source-Xᴸ-seal-⊢ = Conv.⊢↓-sealˣ Xᴸ∈

source-X-seal-⊢ : source-store Conv.⊢↓[ just X ] seal X ★
source-X-seal-⊢ = Conv.⊢↓-sealˣ X∈

target-Y-seal-⊢ : target-store Conv.⊢↓[ just Y ] seal Y ★
target-Y-seal-⊢ = Conv.⊢↓-sealˣ Y∈

private
  source-env : Env∼ 2
  source-env Fin.zero = X∼★
  source-env (Fin.suc Fin.zero) = X∼★

  target-env : Env∼ 1
  target-env Fin.zero = X∼★

  ℕ!ᴸ : source-env ⊢ (‵ `ℕ) ∼ ★
  ℕ!ᴸ = id (‵ `ℕ) !

  ℕ!ᴿ : target-env ⊢ (‵ `ℕ) ∼ ★
  ℕ!ᴿ = id (‵ `ℕ) !

  Y! : target-env ⊢ ＇ Y ∼ ★
  Y! = id (＇ Y) !

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

source-core : Term 2
source-core = ($ (κℕ 0)) ⟨ ℕ!ᴸ ⟩

source-inner : Term 2
source-inner = source-core ↓ seal X ★

M : Term 2
M = source-inner ↓ seal Xᴸ (＇ X)

target-core : Term 1
target-core = ($ (κℕ 0)) ⟨ ℕ!ᴿ ⟩

target-sealed : Term 1
target-sealed = target-core ↓ seal Y ★

N : Term 1
N = target-sealed ⟨ Y! ⟩

------------------------------------------------------------------------
-- Type obligations and rebases
------------------------------------------------------------------------

q : ＇ Xᴸ ⊑ᵂ⟨ W ⟩ ＇ Y
q = X⊑X

input-type : ＇ Xᴸ ⊑ᵂ⟨ W ⟩ ★
input-type = X⊑★ refl

inner-type : ＇ X ⊑ᵂ⟨ W ⟩ ★
inner-type = X⊑★ refl

no-inner-name-obligation : ¬ (＇ X ⊑ᵂ⟨ W ⟩ ＇ Y)
no-inner-name-obligation ()

Xᴸ-Y-rep : CTI2.StoreRepImp W Xᴸ Y
Xᴸ-Y-rep = store-rep-imp ★⊑★

outer-rebase : RebaseAt W W Xᴸ Y
outer-rebase = CTI2.sameWorldRebaseAt refl Xᴸ-Y-rep

X-no-target-at-b : ∀ (Y′ : TyVar 1)
  → toRenameᵗ (CTI2.ηᴿʷ W) Y′ ≢ toRenameᵗ (CTI2.ηᴸʷ W) X
X-no-target-at-b Fin.zero ()

X-no-target-occupant : CTI2.NoTargetOccupantAtSource W X
X-no-target-occupant (Y′ , eq) = X-no-target-at-b Y′ eq

X-star-rep : CTI2.resolveVar source-store X ⊑ᵂ⟨ W ⟩ ★
X-star-rep = ★⊑★

inner-source-only-rebase : TagRebaseAtᴸ W W (just X) nothing
inner-source-only-rebase =
  CTI2.tag-rebase-onlyᴸ refl X-no-target-at-b X-star-rep

------------------------------------------------------------------------
-- The concrete input and inversion output
------------------------------------------------------------------------

base² : W ∣ [] ⊢² source-core ⊑ target-core ∶ ★⊑★
base² =
  CTI2.cast⊑cast² ℕ!ᴸ ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

inner-source² : W ∣ [] ⊢² source-inner ⊑ target-core ∶ inner-type
inner-source² =
  CTI2.conceal⊑²-seal-star-open
    X-no-target-occupant
    (λ Z eq → eq) inner-source-only-rebase CTI2.same-[]
    source-X-seal-⊢ base² inner-type

output : W ∣ [] ⊢² M ⊑ target-sealed ∶ q
output =
  CTI2.conceal⊑conceal²
    (CTI2.matched-seal-nonstar nonstar-X)
    (λ Z eq → eq) outer-rebase CTI2.same-[]
    source-Xᴸ-seal-⊢ target-Y-seal-⊢ inner-source² q

input : W ∣ [] ⊢² M ⊑ N ∶ input-type
input = CTI2.⊑cast² Y! output input-type
