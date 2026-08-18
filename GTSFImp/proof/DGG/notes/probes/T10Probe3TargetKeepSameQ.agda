module T10Probe3TargetKeepSameQ where

-- File Charter:
--   * Calibration probe for the D7 target keep-step same-`q` question.
--   * Builds a paired source/target reveal over matching sealed `ℕ` values.
--   * The relation before the target `conceal-reveal` keep step uses
--     exactly `q = ℕ ⊑ᵂ ℕ`; the checked counterexample shows that after
--     only the target step, the same-`q` relation is underivable.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import TyStore using (store-empty; _∋_⦂_; Z∋)
open import Imprecision using (ImpEnv; X⊑X; ι⊑ι)
import Conversion as Conv
import CastTerms as CT
open import CastTerms using (Term; Value; $; _↓_; _↑_)
open import Primitives using (κℕ)
import Reduction as R

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CompilePreservesImprecision2 as CPI2


empty-μ : ImpEnv 0
empty-μ ()

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

W₀ : CTI2.World 0 0 0
W₀ = CPI2.initialWorld empty-μ store-empty

W : CTI2.World 1 1 1
W = CTI2.bothBindWorld X⊑X W₀ ℕ₀ ℕ₀

X : TyVar 1
X = Fin.zero

Y : TyVar 1
Y = Fin.zero

ℕ₁ : Ty 1
ℕ₁ = ‵ `ℕ

source-entry : CTI2.sourceStoreʷ W ∋ X ⦂ ℕ₁
source-entry = Z∋ refl

target-entry : CTI2.targetStoreʷ W ∋ Y ⦂ ℕ₁
target-entry = Z∋ refl

source-seal-typed :
  CTI2.sourceStoreʷ W Conv.⊢↓[ just X ] Conv.seal X ℕ₁
source-seal-typed = Conv.⊢↓-sealˣ source-entry

target-seal-typed :
  CTI2.targetStoreʷ W Conv.⊢↓[ just Y ] Conv.seal Y ℕ₁
target-seal-typed = Conv.⊢↓-sealˣ target-entry

source-unseal-typed :
  CTI2.sourceStoreʷ W Conv.⊢↑[ just X ] Conv.unseal X ℕ₁
source-unseal-typed = Conv.⊢↑-unsealˣ source-entry

target-unseal-typed :
  CTI2.targetStoreʷ W Conv.⊢↑[ just Y ] Conv.unseal Y ℕ₁
target-unseal-typed = Conv.⊢↑-unsealˣ target-entry

q : ℕ₁ CTI2.⊑ᵂ⟨ W ⟩ ℕ₁
q = ι⊑ι

sealed-q : (＇ X) CTI2.⊑ᵂ⟨ W ⟩ (＇ Y)
sealed-q = X⊑X

partnered-representation : CTI2.StoreRepImp W X Y
partnered-representation = CTI2.store-rep-imp q

same-rebase : CTI2.RebaseAt W W X Y
same-rebase = CTI2.sameWorldRebaseAt refl partnered-representation

mono-refl : CTI2.ImpEnvMono W W
mono-refl _ eq = eq

source-value : Term 1
source-value = $ (κℕ 0)

target-value : Term 1
target-value = $ (κℕ 0)

source-value-value : Value source-value
source-value-value = $ (κℕ 0)

target-value-value : Value target-value
target-value-value = $ (κℕ 0)

source-sealed : Term 1
source-sealed = source-value ↓ Conv.seal X ℕ₁

target-sealed : Term 1
target-sealed = target-value ↓ Conv.seal Y ℕ₁

source-sealed-value : Value source-sealed
source-sealed-value = source-value-value CT.↓ CT.seal

target-sealed-value : Value target-sealed
target-sealed-value = target-value-value CT.↓ CT.seal

source-revealed : Term 1
source-revealed = source-sealed ↑ Conv.unseal X ℕ₁

target-revealed : Term 1
target-revealed = target-sealed ↑ Conv.unseal Y ℕ₁

base-relation : W CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ q
base-relation = CTI2.κ⊑κ² (κℕ 0) q

matched-conceal-partner :
  CTI2.MatchedConcealPartnerOK W source-value
    (Conv.seal X ℕ₁) (just Y) target-value
matched-conceal-partner = CTI2.matched-seal-nonstar nonstar-ι

sealed-relation :
  W CTI2.∣ [] ⊢² source-sealed ⊑ target-sealed ∶ sealed-q
sealed-relation =
  CTI2.conceal⊑conceal² matched-conceal-partner mono-refl
    same-rebase CTI2.same-[] source-seal-typed target-seal-typed
    base-relation sealed-q

before-target-keep :
  W CTI2.∣ [] ⊢² source-revealed ⊑ target-revealed ∶ q
before-target-keep =
  CTI2.reveal⊑reveal² mono-refl same-rebase CTI2.same-[]
    source-unseal-typed target-unseal-typed sealed-relation q

target-keep-step : target-revealed R.—→[ R.keep ] target-value
target-keep-step = R.pure-step (R.conceal-reveal target-value-value)

target-keep-value : Value target-value
target-keep-value = target-value-value

source-sealed-to-representation-empty :
  ∀ {W′ : CTI2.World 1 1 1}
  → (＇ X) CTI2.⊑ᵂ⟨ W′ ⟩ ℕ₁
  → ⊥
source-sealed-to-representation-empty ()

same-q-after-target-only-empty :
  W CTI2.∣ [] ⊢² source-revealed ⊑ target-value ∶ q → ⊥
same-q-after-target-only-empty
    (CTI2.reveal⊑² {W′ = W′} {p = p} mono rb same c⊢ rel q′) =
  source-sealed-to-representation-empty {W′ = W′} p

after-both-peel-same-q :
  W CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ q
after-both-peel-same-q = base-relation
