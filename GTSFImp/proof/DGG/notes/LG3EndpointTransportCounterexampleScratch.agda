module LG3EndpointTransportCounterexampleScratch where

-- File Charter:
--   * Notes-only LG-3 counterexample scratch.
--   * Exhibits a non-empty paired `cast⊑cast²` / target `expand` cell where
--     the requested post-source midpoint witness is not derivable.
--   * Calibrates the supervisor multi-step ruling: the full target composite
--     lands at a final inert-cast value that is related by the paired premise.
--   * Does not edit the live CTI relation or any proof surface.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (store-empty; store-bind)
open import Consistency using
  (Env∼; Var∼; ★∼X; _⊢_∼_; _↦_; id; idᵍ; _!; ？_; flipᵐ;
   _↪ᵗ_; keep; empty)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; _⊢_⊑_; ★⊑★; ι⊑ι; X⊑★; ι⊑★;
   ⇒⊑⇒; ⇒⊑★)
open import CastTerms using (Term; Value; ƛ_; $; _⟨_⟩; _《_》; inj; fun)
open import Primitives using (κℕ)
import Reduction as R
open import Reduction using
  (_—→_; _—↠[_]_; _—→[_]⟨_⟩_; _—↠[_]⟨_⟩_; _∎[];
   keep; pure-step; ξ-⟨⟩; expand; tag-untag)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   world;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


X : Fin.Fin 1
X = Fin.zero

precise-env : ImpEnv 1
precise-env X = X⊑X

cast-env : Env∼ 1
cast-env X = ★∼X

W : World 1 1 1
W = world (keep empty) (keep empty) precise-env
  (store-bind store-empty ★) (store-bind store-empty ★)

ℕ : Ty 1
ℕ = ‵ `ℕ

XTy : Ty 1
XTy = ＇ X

G : Ty 1
G = ★ ⇒ ★

C : Ty 1
C = ★ ⇒ ℕ

A : Ty 1
A = XTy ⇒ ℕ

B : Ty 1
B = XTy ⇒ ℕ

X! : flipᵐ cast-env ⊢ XTy ∼ ★
X! = id (＇ X) !

ℕ! : cast-env ⊢ ℕ ∼ ★
ℕ! = id (‵ `ℕ) !

ℕ? : cast-env ⊢ ★ ∼ ℕ
ℕ? = ？ (idᵍ (‵ `ℕ))

source-cast : cast-env ⊢ C ∼ A
source-cast = X! ↦ id (‵ `ℕ)

target-residual : cast-env ⊢ G ∼ B
target-residual = X! ↦ ℕ?

target-expand-cast : cast-env ⊢ ★ ∼ B
target-expand-cast = ？ target-residual

target-tag : cast-env ⊢ G ∼ ★
target-tag = idᵍ ★⇒★ !

p★ : C ⊑ᵂ⟨ W ⟩ ★
p★ = ⇒⊑★ ★⊑★ ι⊑★

pG : C ⊑ᵂ⟨ W ⟩ G
pG = ⇒⊑⇒ ★⊑★ ι⊑★

qB : A ⊑ᵂ⟨ W ⟩ B
qB = ⇒⊑⇒ X⊑X ι⊑ι

no-post-source-midpoint : A ⊑ᵂ⟨ W ⟩ G → ⊥
no-post-source-midpoint (⇒⊑⇒ (X⊑★ ()) _)

source-core : Term 1
source-core = ƛ ($ (κℕ 0))

target-ground-core : Term 1
target-ground-core = ƛ (($ (κℕ 0)) ⟨ ℕ! ⟩)

target-star-value : Term 1
target-star-value = target-ground-core ⟨ target-tag ⟩

source-core-value : Value source-core
source-core-value = ƛ ($ (κℕ 0))

target-ground-core-value : Value target-ground-core
target-ground-core-value =
  ƛ (($ (κℕ 0)) ⟨ ℕ! ⟩)

target-star-value-value : Value target-star-value
target-star-value-value = target-ground-core-value 《 inj 》

source-casted-value : Value (source-core ⟨ source-cast ⟩)
source-casted-value = source-core-value 《 fun 》

body-rel : W ∣ (CTX.ctx-imp ★ ★ ★⊑★ ∷ []) ⊢²
  $ (κℕ 0) ⊑ ($ (κℕ 0)) ⟨ ℕ! ⟩ ∶ ι⊑★
body-rel =
  CTI2.⊑cast² ℕ! (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ι⊑★

source-to-ground-core : W ∣ [] ⊢²
  source-core ⊑ target-ground-core ∶ pG
source-to-ground-core = CTI2.ƛ⊑ƛ² body-rel

source-to-target-star-value : W ∣ [] ⊢²
  source-core ⊑ target-star-value ∶ p★
source-to-target-star-value =
  CTI2.⊑cast² target-tag source-to-ground-core p★

paired-expand-cell-nonempty : W ∣ [] ⊢²
  source-core ⟨ source-cast ⟩
  ⊑ target-star-value ⟨ target-expand-cast ⟩ ∶ qB
paired-expand-cell-nonempty =
  CTI2.cast⊑cast² source-cast target-expand-cast
    source-to-target-star-value qB

target-expand-step :
  target-star-value ⟨ target-expand-cast ⟩ —→
  target-star-value ⟨ ？ (idᵍ ★⇒★) ⟩ ⟨ target-residual ⟩
target-expand-step =
  expand target-star-value-value
    (λ ())

target-expand-composite :
  target-star-value ⟨ target-expand-cast ⟩
    —↠[ R.keep R.∷ R.keep R.∷ R.[] ]
  target-ground-core ⟨ target-residual ⟩
target-expand-composite =
  target-star-value ⟨ target-expand-cast ⟩
    —→[ keep ]⟨ pure-step target-expand-step ⟩
  target-star-value ⟨ ？ (idᵍ ★⇒★) ⟩ ⟨ target-residual ⟩
    —→[ keep ]⟨
      ξ-⟨⟩
        (pure-step
          (tag-untag target-ground-core-value))
        refl
    ⟩
  target-ground-core ⟨ target-residual ⟩ ∎[]

target-end-value : Value (target-ground-core ⟨ target-residual ⟩)
target-end-value = target-ground-core-value 《 fun 》

paired-expand-end-relation : W ∣ [] ⊢²
  source-core ⟨ source-cast ⟩
  ⊑ target-ground-core ⟨ target-residual ⟩ ∶ qB
paired-expand-end-relation =
  CTI2.cast⊑cast² source-cast target-residual
    source-to-ground-core qB
