module proof.DGG.CenterCrossingProbe where

-- File Charter:
--   * Records the target-seal variable geometry that previously needed
--     a moved old target center in bare right-injection inversion.
--   * M2 removes that freedom: `RebaseAt` freezes every old target
--     variable, so the old outer paired and target-wrapper premises are
--     underivable at constructor formation time.
--   * The stable inner target-seal input remains derivable and documents
--     the source-only parking shape that survived the redesign.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ;
   id; _!)
open import Conversion using (seal)
open import CastTerms
import CastTerms as CTerms
open import Imprecision
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Inversion.SpineValueDef as SVD
open CTI2 using
  (World; world; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   rebase-at; same-runtime; store-rep-imp; ηᴸʷ; ηᴿʷ)

private
  X₀ : TyVar 2
  X₀ = Fin.zero

  X₁ : TyVar 2
  X₁ = Fin.suc Fin.zero

  Y₀ : TyVar 2
  Y₀ = Fin.zero

  Y₁ : TyVar 2
  Y₁ = Fin.suc Fin.zero

  a : TyVar 3
  a = Fin.zero

  b : TyVar 3
  b = Fin.suc Fin.zero

  c : TyVar 3
  c = Fin.suc (Fin.suc Fin.zero)

------------------------------------------------------------------------
-- Stores, embeddings, and worlds
------------------------------------------------------------------------

source-store : TyStore 2
source-store = store-bind (store-bind store-empty ★) ★

target-store : TyStore 2
target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

probe-μ : ImpEnv 3
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★
probe-μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

ηᴸ-ab : 2 ↪ᵗ 3
ηᴸ-ab = keep (keep (skip empty))

ηᴸ-ac : 2 ↪ᵗ 3
ηᴸ-ac = keep (skip (keep empty))

ηᴿ-ac : 2 ↪ᵗ 3
ηᴿ-ac = keep (skip (keep empty))

ηᴿ-bc : 2 ↪ᵗ 3
ηᴿ-bc = skip (keep (keep empty))

-- Placement table:
--
--             X₀  X₁  Y₀  Y₁
--   W          a   b   a   c
--   W′         a   b   b   c
--   Wᵖ         a   c   b   c

W : World 2 2 3
W = world ηᴸ-ab ηᴿ-ac probe-μ source-store target-store

W′ : World 2 2 3
W′ = world ηᴸ-ab ηᴿ-bc probe-μ source-store target-store

Wᵖ : World 2 2 3
Wᵖ = world ηᴸ-ac ηᴿ-bc probe-μ source-store target-store

------------------------------------------------------------------------
-- Store typing, casts, and terms
------------------------------------------------------------------------

X₀∈ : source-store ∋ X₀ ⦂ ★
X₀∈ = Z∋ refl

X₁∈ : source-store ∋ X₁ ⦂ ★
X₁∈ = S-bind∋ (Z∋ refl) refl

Y₀∈ : target-store ∋ Y₀ ⦂ ＇ Y₁
Y₀∈ = Z∋ refl

Y₁∈ : target-store ∋ Y₁ ⦂ ★
Y₁∈ = S-bind∋ (Z∋ refl) refl

source-env : Env∼ 2
source-env Fin.zero = X∼★
source-env (Fin.suc Fin.zero) = X∼★

target-env : Env∼ 2
target-env Fin.zero = X∼★
target-env (Fin.suc Fin.zero) = X∼★

X₁! : source-env ⊢ (＇ X₁) ∼ ★
X₁! = id (＇ X₁) !

Y₀id : target-env ⊢ (＇ Y₀) ∼ (＇ Y₀)
Y₀id = id (＇ Y₀)

Y₀! : target-env ⊢ (＇ Y₀) ∼ ★
Y₀! = Y₀id !

ℕ!ᴸ : source-env ⊢ (‵ `ℕ) ∼ ★
ℕ!ᴸ = id (‵ `ℕ) !

ℕ!ᴿ : target-env ⊢ (‵ `ℕ) ∼ ★
ℕ!ᴿ = id (‵ `ℕ) !

V₀ : Term 2
V₀ = ($ (κℕ 0)) ⟨ ℕ!ᴸ ⟩

V : Term 2
V = V₀ ↓ seal X₁ ★

U₀ : Term 2
U₀ = ($ (κℕ 0)) ⟨ ℕ!ᴿ ⟩

U : Term 2
U = U₀ ↓ seal Y₁ ★

------------------------------------------------------------------------
-- Rebase witnesses
------------------------------------------------------------------------

X₀-Y₀-rep : CTI2.StoreRepImp W X₀ Y₀
X₀-Y₀-rep = store-rep-imp ★⊑★

no-center-crossing-target : ∀ {Xᴸ} → RebaseAt W′ W Xᴸ Y₀ → ⊥
no-center-crossing-target rb
    with CTI2.RebaseAt.ηᴿ-frozen rb Y₀
no-center-crossing-target rb | ()

no-center-crossing-paired : RebaseAt W′ W X₀ Y₀ → ⊥
no-center-crossing-paired = no-center-crossing-target

no-center-crossing-outerᴿ :
  CTI2.RebaseAtᴿ W′ W (just Y₀) → ⊥
no-center-crossing-outerᴿ (CTI2.rebase-varᴿ rb) =
  no-center-crossing-target rb

X₁-Y₀-rep : CTI2.StoreRepImp W′ X₁ Y₀
X₁-Y₀-rep = store-rep-imp ★⊑★

rb-target-input : RebaseAt Wᵖ W′ X₁ Y₀
rb-target-input =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} X₀≢ → refl
       ; {Fin.suc Fin.zero} X₁≢ → ⊥-elim (X₁≢ refl) })
    (λ _ → refl) refl X₁-Y₀-rep

X₁-Y₁-rep : CTI2.StoreRepImp Wᵖ X₁ Y₁
X₁-Y₁-rep = store-rep-imp ★⊑★

rb-inner : RebaseAt Wᵖ Wᵖ X₁ Y₁
rb-inner = CTI2.sameWorldRebaseAt refl X₁-Y₁-rep

------------------------------------------------------------------------
-- Checkpoint 1: the target-seal call-site premise is derivable
------------------------------------------------------------------------

p-inner : ＇ X₁ ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y₁
p-inner = X⊑X

p-input : ＇ X₁ ⊑ᵂ⟨ W′ ⟩ ＇ Y₀
p-input = X⊑X

q-out : ＇ X₀ ⊑ᵂ⟨ W ⟩ ＇ Y₀
q-out = X⊑X

base² : Wᵖ ∣ [] ⊢² V₀ ⊑ U₀ ∶ ★⊑★
base² =
  CTI2.cast⊑cast² ℕ!ᴸ ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

inner² : Wᵖ ∣ [] ⊢² V ⊑ U ∶ p-inner
inner² =
  CTI2.conceal⊑conceal²
    (CTI2.matched-seal-star-partner
      (CTI2.rep★-nonvar-tag nonvar-base))
    (λ Z eq → eq) rb-inner CTI2.same-[]
    (CTI2.⊢↓-sealˣ X₁∈) (CTI2.⊢↓-sealˣ Y₁∈) base² p-inner

input-target-seal-variable :
  W′ ∣ [] ⊢² V ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ p-input
input-target-seal-variable =
  CTI2.⊑conceal² (λ Z eq → eq) (CTI2.rebase-varᴿ rb-target-input)
    CTI2.same-[] (CTI2.⊢↓-sealˣ Y₀∈) inner² p-input

source-spine : SVD.SpineValue V
source-spine =
  SVD.sv-seal (SVD.sv-cast (SVD.sv-$ (κℕ 0)) CTerms.inj)

inert-X₁! : Inert X₁!
inert-X₁! = CTerms.inj

target-base-value : Value U₀
target-base-value = CTerms.$ (κℕ 0) CTerms.《 CTerms.inj 》

target-value : Value U
target-value =
  target-base-value CTerms.↓ (CTerms.seal {X = Y₁} {R = ★})

target-outer-value : Value (U ↓ seal Y₀ (＇ Y₁))
target-outer-value =
  target-value CTerms.↓ (CTerms.seal {X = Y₀} {R = ＇ Y₁})

source-outer-spine :
  SVD.SpineValue ((V ⟨ X₁! ⟩) ↓ seal X₀ ★)
source-outer-spine =
  SVD.sv-seal (SVD.sv-cast source-spine inert-X₁!)
