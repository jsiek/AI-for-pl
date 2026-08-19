module MismatchProbeScratch where

-- Root-level scratch for the ExtraCastRight² projection-mismatch probe.
-- It constructs a v2 CTI input whose right value is tagged at ℕ, whose extra
-- target projection checks a distinct variable ground, and whose requested
-- output type imprecision is still derivable.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; Var∼; X∼★; ★∼X; _⊢_∼_; _⊢_∼★; _⊢★∼_; _↪ᵗ_;
   empty; keep; skip; id; idᵍ; _!; ？_)
open import Conversion using (seal)
open import Imprecision
open import CastTerms using
  (Term; Value; $; _⟨_⟩; _↓_; blame; _《_》; inj; seal)
open import Reduction
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   world;
   _⊑ᵂ⟨_⟩_;
   RebaseAt;
   store-rep-imp)
open CTI2 using (_∣_⊢²_⊑_∶_)

private
  Z : TyVar 2
  Z = Fin.zero

  U : TyVar 2
  U = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

source-store : TyStore 2
source-store = store-bind (store-bind store-empty (‵ `ℕ)) ★

target-store : TyStore 1
target-store = store-bind store-empty ★

source-U∋ : source-store ∋ U ⦂ ‵ `ℕ
source-U∋ = S-bind∋ (Z∋ refl) refl

source-η : 2 ↪ᵗ 2
source-η = keep (keep empty)

target-η-U : 1 ↪ᵗ 2
target-η-U = skip (keep empty)

imp-env-dyn : ImpEnv 2
imp-env-dyn Fin.zero = X⊑★
imp-env-dyn (Fin.suc Fin.zero) = X⊑★

probe-world : World 2 1 2
probe-world = world source-η target-η-U imp-env-dyn source-store target-store

target-env-tag : Env∼ 1
target-env-tag _ = X∼★

target-env-proj : Env∼ 1
target-env-proj _ = ★∼X

ℕ! : target-env-tag ⊢ (‵ `ℕ) ∼ ★
ℕ! = id (‵ `ℕ) !

Y? : target-env-proj ⊢ ★ ∼ ＇ Y
Y? = ？ (idᵍ (＇ Y))

source-U-seal-typed : source-store Conv.⊢↓[ just U ] seal U (‵ `ℕ)
source-U-seal-typed = Conv.⊢↓-sealˣ source-U∋

U-Y-representation : CTX.StoreRepImp probe-world U Y
U-Y-representation = store-rep-imp ι⊑★

U-Y-rebase : RebaseAt probe-world probe-world U Y
U-Y-rebase = CTX.sameWorldRebaseAt refl U-Y-representation

probe-p : ＇ U ⊑ᵂ⟨ probe-world ⟩ ★
probe-p = X⊑★ refl

probe-q : ＇ U ⊑ᵂ⟨ probe-world ⟩ ＇ Y
probe-q = X⊑X

source-term : Term 2
source-term = ($ (κℕ 0)) ↓ seal U (‵ `ℕ)

target-untagged : Term 1
target-untagged = $ (κℕ 0)

target-tagged : Term 1
target-tagged = target-untagged ⟨ ℕ! ⟩

mismatch-term : Term 1
mismatch-term = target-tagged ⟨ Y? ⟩

source-value : Value source-term
source-value = ($ (κℕ 0)) ↓ seal

target-untagged-value : Value target-untagged
target-untagged-value = $ (κℕ 0)

target-tagged-value : Value target-tagged
target-tagged-value = target-untagged-value 《 inj 》

InputRelation : Set
InputRelation =
  CTI2._∣_⊢²_⊑_∶_ probe-world [] source-term target-tagged
    {A = ＇ U} {B = ★} probe-p

InputPackage : Set
InputPackage =
  Value source-term
    × (Value target-tagged
    × ((target-env-proj ⊢ ★ ∼ ＇ Y)
    × (＇ U ⊑ᵂ⟨ probe-world ⟩ ＇ Y)))

input-package-without-live-premise : InputPackage
input-package-without-live-premise =
  source-value ,
  target-tagged-value ,
  Y? ,
  probe-q

ℕ-type : Ty 1
ℕ-type = ‵ `ℕ

Y-type : Ty 1
Y-type = ＇ Y

ℕ≢Y : ℕ-type ≢ Y-type
ℕ≢Y ()

mismatch-steps-to-blame : mismatch-term —↠[ keep ∷ [] ] blame
mismatch-steps-to-blame =
  mismatch-term
  —→[ keep ]⟨
    pure-step
      (tag-untag-bad
        {μ = target-env-tag}
        {ν = target-env-proj}
        {G = ‵ `ℕ}
        {H = ＇ Y}
        ⦃ Gᵍ = ‵ `ℕ ⦄
        ⦃ Hᵍ = ＇ Y ⦄
        ⦃ G∼★ = Consistency.ι∼★ ⦄
        ⦃ ★∼H = Consistency.★∼Xᵍ refl ⦄
        ⦃ Gns = nonstar-ι ⦄
        ⦃ Hns = nonstar-X ⦄
        target-untagged-value ℕ≢Y)
  ⟩
  blame ∎[]

blame-not-value : ∀ {Δ} → Value (blame {Δ}) → ⊥
blame-not-value ()

mismatch-not-value : Value mismatch-term → ⊥
mismatch-not-value (v 《 () 》)

const-no-pure-step : ∀ {Δ} {N : Term Δ}
  → $ {Δ = Δ} (κℕ 0) —→ N
  → ⊥
const-no-pure-step ()

const-no-step : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → $ {Δ = Δ} (κℕ 0) —→[ χ ] N
  → ⊥
const-no-step (pure-step step) = const-no-pure-step step

blame-no-pure-step : ∀ {Δ} {N : Term Δ}
  → blame {Δ} —→ N
  → ⊥
blame-no-pure-step ()

blame-no-step : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → blame {Δ} —→[ χ ] N
  → ⊥
blame-no-step (pure-step step) = blame-no-pure-step step

blame-no-value-reduct : ∀ {Δ Δ′} {χs : StoreChanges Δ Δ′}
    {N : Term Δ′}
  → blame {Δ} —↠[ χs ] N
  → Value N
  → ⊥
blame-no-value-reduct ↠-refl vN = blame-not-value vN
blame-no-value-reduct (↠-step step rest) vN =
  blame-no-step step

inner-tag-no-pure-step : ∀ {N : Term 1}
  → target-tagged —→ N
  → ⊥
inner-tag-no-pure-step (ground v ℕ≢ℕ) = ℕ≢ℕ refl

inner-tag-no-step : ∀ {Δ′} {χ : StoreChange 1 Δ′} {N : Term Δ′}
  → target-tagged —→[ χ ] N
  → ⊥
inner-tag-no-step (pure-step step) = inner-tag-no-pure-step step
inner-tag-no-step (ξ-⟨⟩ step refl) = const-no-step step

mismatch-no-value-reduct : ∀ {Δ′} {χs : StoreChanges 1 Δ′}
    {N : Term Δ′}
  → mismatch-term —↠[ χs ] N
  → Value N
  → ⊥
mismatch-no-value-reduct ↠-refl vN = mismatch-not-value vN
mismatch-no-value-reduct
    (↠-step (pure-step (expand v G≢G)) rest) vN =
  G≢G refl
mismatch-no-value-reduct
    (↠-step (pure-step (tag-untag-bad v G≢H)) rest) vN =
  blame-no-value-reduct rest vN
mismatch-no-value-reduct
    (↠-step (ξ-⟨⟩ step refl) rest) vN =
  inner-tag-no-step step

mismatch-violates-provenance : ∀ {Δ′} {χs : StoreChanges 1 Δ′}
    {N : Term Δ′}
  → mismatch-term —↠[ χs ] N
  → Value N
  → ⊥
mismatch-violates-provenance = mismatch-no-value-reduct
