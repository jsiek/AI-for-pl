module T10Probe2SourceRevealStillSealed where

-- File Charter:
--   * Calibration probe for the D2b source conceal-reveal question.
--   * Sets up a concrete partnered source/target seal with representation
--     `ℕ`, records the source `conceal-reveal` step, and checks whether
--     the post-reveal source representation type can still relate to the
--     sealed target type.
--   * The checked emptiness lemma shows the one-sided post-reveal shape
--     `ℕ ⊑ᵂ ＇Y` is not expressible in the current relation.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import TyStore using (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import Imprecision using (ImpEnv; X⊑X; ι⊑ι)
open import Conversion using (seal; unseal)
open import CastTerms using (Term; Value; $; _↓_; _↑_)
open import Primitives using (κℕ)
open import Reduction using (_—→_; conceal-reveal)

import Conversion as Conv
import proof.DGG.CtxImp as CTI2
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

source-store : TyStore 1
source-store = store-bind store-empty ℕ₀

target-store : TyStore 1
target-store = store-bind store-empty ℕ₀

source-entry : CTI2.sourceStoreʷ W ∋ X ⦂ ℕ₁
source-entry = Z∋ refl

target-entry : CTI2.targetStoreʷ W ∋ Y ⦂ ℕ₁
target-entry = Z∋ refl

source-seal-typed :
  CTI2.sourceStoreʷ W Conv.⊢↓[ just X ] seal X ℕ₁
source-seal-typed = Conv.⊢↓-sealˣ source-entry

source-unseal-typed :
  CTI2.sourceStoreʷ W Conv.⊢↑[ just X ] unseal X ℕ₁
source-unseal-typed = Conv.⊢↑-unsealˣ source-entry

target-seal-typed :
  CTI2.targetStoreʷ W Conv.⊢↓[ just Y ] seal Y ℕ₁
target-seal-typed = Conv.⊢↓-sealˣ target-entry

partnered-representation : CTI2.StoreRepImp W X Y
partnered-representation = CTI2.store-rep-imp ι⊑ι

sealed-before-peel : (＇ X) CTI2.⊑ᵂ⟨ W ⟩ (＇ Y)
sealed-before-peel = X⊑X

source-value : Term 1
source-value = $ (κℕ 0)

source-value-value : Value source-value
source-value-value = $ (κℕ 0)

source-sealed : Term 1
source-sealed = source-value ↓ seal X ℕ₁

source-revealed : Term 1
source-revealed = source-sealed ↑ unseal X ℕ₁

source-conceal-reveal-step : source-revealed —→ source-value
source-conceal-reveal-step = conceal-reveal source-value-value

post-source-reveal-still-sealed-empty :
  ℕ₁ CTI2.⊑ᵂ⟨ W ⟩ (＇ Y) → ⊥
post-source-reveal-still-sealed-empty ()
