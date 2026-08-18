module TargetStripNonvarCounterScratch where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl; sym)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import Consistency using (_↪ᵗ_; empty; keep)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SpineValueDef using (SpineValue; sv-seal; sv-$)
open import proof.DGG.Inversion.TargetStripDef using
  (TargetSealTerminusData)
open import proof.DGG.Inversion.TargetStripDef as TSD
open import proof.DGG.Inversion.TargetStripProof using
  (seal-descent-at-var-nonvar)
open CTI2 using
  (World; world; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   sourceStoreʷ; store-rep-imp)

X : TyVar 1
X = Fin.zero

Y : TyVar 1
Y = Fin.zero

storeℕ : TyStore 1
storeℕ = store-bind store-empty (‵ `ℕ)

η : 1 ↪ᵗ 1
η = keep empty

μ : ImpEnv 1
μ Fin.zero = X⊑X

W : World 1 1 1
W = world η η μ storeℕ storeℕ

mono-refl : CTI2.ImpEnvMono W W
mono-refl Z eq = eq

X∈ℕ : storeℕ ∋ X ⦂ ‵ `ℕ
X∈ℕ = Z∋ refl

Y∈ℕ : storeℕ ∋ Y ⦂ ‵ `ℕ
Y∈ℕ = Z∋ refl

X-Y-rep : CTI2.StoreRepImp W X Y
X-Y-rep = store-rep-imp ι⊑ι

rb : RebaseAt W W X Y
rb = CTI2.sameWorldRebaseAt refl X-Y-rep

q : ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
q = X⊑X

V : Term 1
V = $ (κℕ 0) ↓ seal X (‵ `ℕ)

U : Term 1
U = $ (κℕ 0)

svV : SpineValue V
svV = sv-seal (sv-$ (κℕ 0))

vU : Value U
vU = $ (κℕ 0)

D : W ∣ [] ⊢² V ⊑ U ↓ seal Y (‵ `ℕ) ∶ q
D =
  CTI2.conceal⊑conceal² mono-refl rb CTI2.same-[]
    (Conv.⊢↓-sealˣ X∈ℕ) (Conv.⊢↓-sealˣ Y∈ℕ)
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) q

package :
  sourceStoreʷ W ∋ X ⦂ ★ →
  TargetSealTerminusData W [] V (＇ X) U X Y (‵ `ℕ)
package X∈★ =
  seal-descent-at-var-nonvar nonvar-base nonstar-ι
    svV vU mono-refl rb CTI2.same-[] X∈★ Y∈ℕ D

no-source-star : ∀ {Z : TyVar 1} → storeℕ ∋ Z ⦂ ★ → ⊥
no-source-star {Fin.zero} (Z∋ ())

counterexample-premise-impossible : sourceStoreʷ W ∋ X ⦂ ★ → ⊥
counterexample-premise-impossible = no-source-star

contradiction :
  sourceStoreʷ W ∋ X ⦂ ★ →
  ⊥
contradiction X∈★ =
  no-source-star {Z = TSD.TargetSealTerminusData.Y★ (package X∈★)}
    (subst≡
      (λ Σ → Σ ∋ TSD.TargetSealTerminusData.Y★ (package X∈★) ⦂ ★)
      (sym (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime
          (TSD.TargetSealTerminusData.boundary★ (package X∈★)))))
      (TSD.TargetSealTerminusData.target∈★ (package X∈★)))
