{-# OPTIONS --safe #-}

module TrustedLambdaCatchupProbe where

-- File Charter:
--   * Constructs a closed gradual-source imprecision pair whose compiled
--     right argument is a polymorphic value under an instantiation cast.
--   * Records the exact two allocation steps forced by the trusted reduction
--     semantics.
--   * Imports only the public language definitions directly under GTSFImp.

open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (store-empty; store-bind)
open import Consistency
open import Conversion
import Imprecision as I
import GradualTerms as G
open import GradualTerms
  using (GTerm)
  renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
open import Compile using (compile)
open import CastTerms
open import Reduction
import TermCtx as T

------------------------------------------------------------------------
-- The smallest source-side binder mismatch that leaves a target Λ
------------------------------------------------------------------------

Dyn² : Ty 0
Dyn² = ★ ⇒ ★ ⇒ ★

source-body : Ty 2
source-body = ＇ 1 ⇒ ＇ 0 ⇒ ＇ 1

source-inner : Ty 1
source-inner = `∀ source-body

Source : Ty 0
Source = `∀ source-inner

target-body : Ty 1
target-body = ★ ⇒ ＇ 0 ⇒ ★

Target : Ty 0
Target = `∀ target-body

source-value : G.GTerm 0
source-value =
  G.Λ (G.Λ (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1))

target-value : G.GTerm 0
target-value = G.Λ (G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 1)

source-body-⊢ : 2 ∣ [] ⊢ᴳ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1
    ⦂ source-body
source-body-⊢ = G.⊢ƛ (G.⊢ƛ (G.⊢` (T.S T.Z)))

source-inner-⊢ : 1 ∣ [] ⊢ᴳ
    G.Λ (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1) ⦂ source-inner
source-inner-⊢ =
  G.⊢Λ {zero∈A = ∈-fun-right (∉-var (≢→≢ᶠ (λ ())))
    (∈-fun-left var-∈)}
    (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1) source-body-⊢

source-value-⊢ : 0 ∣ [] ⊢ᴳ source-value ⦂ Source
source-value-⊢ =
  G.⊢Λ {zero∈A = ∈-all (∈-fun-left var-∈)}
    (G.Λ (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1)) source-inner-⊢

target-value-⊢ : 0 ∣ [] ⊢ᴳ target-value ⦂ Target
target-value-⊢ =
  G.⊢Λ {zero∈A = ∈-fun-right (∉-star)
    (∈-fun-left var-∈)}
    (G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 1)
    (G.⊢ƛ (G.⊢ƛ (G.⊢` (T.S T.Z))))

target-body↑ : Ty 2
target-body↑ = renameᵗ (extᵗ Fin.suc) target-body

source-body⊑target-body↑ :
  I.extᵐ (I.instᵐ (I.idᵐ {Δ = 0})) I.⊢
    source-body ⊑ target-body↑
source-body⊑target-body↑ =
  I.⇒⊑⇒ (I.X⊑★ refl)
    (I.⇒⊑⇒ I.X⊑X (I.X⊑★ refl))

source-inner⊑liftTarget :
  I.instᵐ (I.idᵐ {Δ = 0}) I.⊢ source-inner ⊑ ⇑ᵗ Target
source-inner⊑liftTarget = I.∀⊑∀ source-body⊑target-body↑

Source⊑Target : I.idᵐ I.⊢ Source ⊑ Target
Source⊑Target =
  I.∀⊑ nonvar-all (∈-all (∈-fun-left var-∈))
    source-inner⊑liftTarget

source-body⊑target-body↑ᴳ :
  I.extᵐ (I.instᵐ (I.idᵐ {Δ = 0})) GTI.∣ [] ⊢ᴳ
    (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1)
    ⊑ (G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 1)
    ⦂ source-body ⊑ target-body↑ ∶
      source-body⊑target-body↑
source-body⊑target-body↑ᴳ =
  GTI.ƛ⊑ƛᴳ (GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ (GTI.Sⁱ GTI.Zⁱ)))

source-inner⊑lift-target-valueᴳ :
  I.instᵐ (I.idᵐ {Δ = 0}) GTI.∣ [] ⊢ᴳ
    (G.Λ (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1))
    ⊑ G.⇑ᵗᴳ target-value ⦂ source-inner ⊑ ⇑ᵗ Target ∶
      source-inner⊑liftTarget
source-inner⊑lift-target-valueᴳ =
  GTI.Λ⊑Λᴳ GTI.lift-[]
    (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1)
    (G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 1)
    (∈-fun-right (∉-var (≢→≢ᶠ (λ ()))) (∈-fun-left var-∈))
    (∈-fun-right ∉-star (∈-fun-left var-∈))
    source-body⊑target-body↑ᴳ

source-value⊑target-valueᴳ :
  I.idᵐ GTI.∣ [] ⊢ᴳ source-value ⊑ target-value
    ⦂ Source ⊑ Target ∶ Source⊑Target
source-value⊑target-valueᴳ =
  GTI.Λ⊑ᴳ nonvar-all (∈-all (∈-fun-left var-∈))
    GTI.lift-[]
    (G.Λ (G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 1))
    target-value-⊢ source-inner⊑lift-target-valueᴳ

------------------------------------------------------------------------
-- A source context that makes only the right operand instantiate Target
------------------------------------------------------------------------

Source⊑Dyn² : I.idᵐ I.⊢ Source ⊑ Dyn²
Source⊑Dyn² =
  I.∀⊑ nonvar-all (∈-all (∈-fun-left var-∈))
    (I.∀⊑ nonvar-fun
      (∈-fun-right (∉-var (≢→≢ᶠ (λ ()))) (∈-fun-left var-∈))
      (I.⇒⊑⇒ (I.X⊑★ refl)
        (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl))))

left-use : G.GTerm 0
left-use = G.ƛ Source ⇒ G.` 0

right-use : G.GTerm 0
right-use = G.ƛ Dyn² ⇒ G.` 0

left-use-⊢ : 0 ∣ [] ⊢ᴳ left-use ⦂ Source ⇒ Source
left-use-⊢ = G.⊢ƛ (G.⊢` T.Z)

right-use-⊢ : 0 ∣ [] ⊢ᴳ right-use ⦂ Dyn² ⇒ Dyn²
right-use-⊢ = G.⊢ƛ (G.⊢` T.Z)

left-use⊑right-useᴳ :
  I.idᵐ GTI.∣ [] ⊢ᴳ left-use ⊑ right-use
    ⦂ Source ⇒ Source ⊑ Dyn² ⇒ Dyn² ∶
      I.⇒⊑⇒ Source⊑Dyn² Source⊑Dyn²
left-use⊑right-useᴳ = GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ)

source-refl : Source ∼ Source
source-refl =
  ∀ᶜ (∀ᶜ
    (id (＇ 1) ↦ (id (＇ 0) ↦ id (＇ 1))))

dyn-to-target-body :
  genᵐ (idᶜ {Δ = 0}) ⊢ ⇑ᵗ Dyn² ∼ target-body
dyn-to-target-body =
  id ★ ↦ ((id (＇ 0) !) ↦ id ★)

dyn-to-target : Dyn² ∼ Target
dyn-to-target =
  gen_ ⦃ Bnv = nonvar-fun ⦄
    ⦃ z∈B = ∈-fun-right ∉-star (∈-fun-left var-∈) ⦄
    dyn-to-target-body (λ ())

left-program : G.GTerm 0
left-program = left-use G.·[ 0 ] source-value

right-program : G.GTerm 0
right-program = right-use G.·[ 0 ] target-value

left-program-⊢ : 0 ∣ [] ⊢ᴳ left-program ⦂ Source
left-program-⊢ = G.⊢· left-use-⊢ source-value-⊢ source-refl

right-program-⊢ : 0 ∣ [] ⊢ᴳ right-program ⦂ Dyn²
right-program-⊢ = G.⊢· right-use-⊢ target-value-⊢ dyn-to-target

left-program⊑right-programᴳ :
  I.idᵐ GTI.∣ [] ⊢ᴳ left-program ⊑ right-program
    ⦂ Source ⊑ Dyn² ∶ Source⊑Dyn²
left-program⊑right-programᴳ =
  GTI.·⊑·ᴳ left-use⊑right-useᴳ source-value⊑target-valueᴳ
    source-refl dyn-to-target

------------------------------------------------------------------------
-- Exact compile image and the forced target allocation prefix
------------------------------------------------------------------------

target-inst-body : instᵐ (idᶜ {Δ = 0}) ⊢ target-body ∼ ⇑ᵗ Dyn²
target-inst-body =
  id ★ ↦ (？ (id (＇ 0)) ↦ id ★)

target-inst : Target ∼ Dyn²
target-inst =
  inst_ ⦃ Anv = nonvar-fun ⦄
    ⦃ z∈A = ∈-fun-right ∉-star (∈-fun-left var-∈) ⦄
    target-inst-body (λ ())

targetᵀ : Term 0
targetᵀ = Λ (ƛ (ƛ (` 1)))

sourceᵀ : Term 0
sourceᵀ = Λ (Λ (ƛ (ƛ (` 1))))

left-compile-exact :
  proj₁ (compile {Σ = store-empty} left-program-⊢)
    ≡ (ƛ (` 0)) · (sourceᵀ ⟨ symᶜ source-refl ⟩)
left-compile-exact = refl

right-compile-exact :
  proj₁ (compile {Σ = store-empty} right-program-⊢)
    ≡ (ƛ (` 0)) · (targetᵀ ⟨ target-inst ⟩)
right-compile-exact = refl

left-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢
    (ƛ (` 0)) · (sourceᵀ ⟨ symᶜ source-refl ⟩) ⦂ Source
left-compiled-⊢ = proj₂ (compile {Σ = store-empty} left-program-⊢)

right-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢
    (ƛ (` 0)) · (targetᵀ ⟨ target-inst ⟩) ⦂ Dyn²
right-compiled-⊢ = proj₂ (compile {Σ = store-empty} right-program-⊢)

left-after-β : Term 0
left-after-β = sourceᵀ ⟨ symᶜ source-refl ⟩

left-β-step :
  (ƛ (` 0)) · (sourceᵀ ⟨ symᶜ source-refl ⟩)
    —→[ keep ] left-after-β
left-β-step =
  pure-step (β ((Λ (Λ (ƛ (ƛ (` 1))))) 《 all 》))

left-program-to-value :
  (ƛ (` 0)) · (sourceᵀ ⟨ symᶜ source-refl ⟩)
    —↠[ keep ∷ [] ] left-after-β
left-program-to-value =
  (ƛ (` 0)) · (sourceᵀ ⟨ symᶜ source-refl ⟩)
  —→[ keep ]⟨ left-β-step ⟩
  left-after-β ∎[]

target-inst-redex : Term 0
target-inst-redex = targetᵀ ⟨ target-inst ⟩

target-after-inst : Term 1
target-after-inst =
  (CastTerms._⟨_⟩)
    ((CastTerms.Term._↑_)
      (⇑ᵗᵐ targetᵀ
        ⦂∀ applyBody (bind ★) target-body [ ＇ Fin.zero ])
      (〖 Fin.zero , ★ ↑ target-body 〗))
    (↑ᶜ (target-inst-body [ ★/0 ]ᶜ))

target-inst-step :
  target-inst-redex —→[ bind ★ ] target-after-inst
target-inst-step =
  β-inst ⦃ z∈A = ∈-fun-right ∉-star (∈-fun-left var-∈) ⦄
    (Λ (ƛ (ƛ (` 1)))) (λ ())

targetᵀ-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ targetᵀ ⦂ Target
targetᵀ-⊢ =
  ⊢Λ (ƛ (ƛ (` 1))) (⊢ƛ (⊢ƛ (⊢` (T.S T.Z))))

target-inst-redex-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ target-inst-redex ⦂ Dyn²
target-inst-redex-⊢ = ⊢⟨⟩ targetᵀ-⊢ target-inst

target-store-after-inst :
  applyStore (bind ★) store-empty ≡ store-bind store-empty ★
target-store-after-inst = refl

target-type-app : Term 1
target-type-app =
  ⇑ᵗᵐ targetᵀ
    ⦂∀ applyBody (bind ★) target-body [ ＇ Fin.zero ]

target-type-app-after-Λ : Term 2
target-type-app-after-Λ =
  (CastTerms.Term._↑_) (⇑ᵗᵐ (ƛ (ƛ (` 1))))
    (〖 Fin.zero , ⇑ᵗ (＇ Fin.zero) ↑
      applyBody (bind ★) target-body 〗)

target-Λ-step :
  target-type-app —→[ bind (＇ Fin.zero) ] target-type-app-after-Λ
target-Λ-step = β-Λ (ƛ (ƛ (` 1)))

target-after-two : Term 2
target-after-two =
  (CastTerms.Term._⟨_⟩)
    ((CastTerms.Term._↑_) target-type-app-after-Λ
      (rename↑ Fin.suc (〖 Fin.zero , ★ ↑ target-body 〗)))
    (applyConsistency (bind (＇ Fin.zero))
      (↑ᶜ (target-inst-body [ ★/0 ]ᶜ)))

target-second-step :
  target-after-inst —→[ bind (＇ Fin.zero) ] target-after-two
target-second-step =
  ξ-⟨⟩ (ξ-reveal target-Λ-step refl) refl

target-two-step :
  target-inst-redex
    —↠[ bind ★ ∷ bind (＇ Fin.zero) ∷ [] ] target-after-two
target-two-step =
  target-inst-redex
  —→[ bind ★ ]⟨ target-inst-step ⟩
  target-after-inst
  —→[ bind (＇ Fin.zero) ]⟨ target-second-step ⟩
  target-after-two ∎[]

right-after-inst : Term 1
right-after-inst = ⇑ᵗᵐ (ƛ (` 0)) · target-after-inst

right-after-two : Term 2
right-after-two = ⇑ᵗᵐ (⇑ᵗᵐ (ƛ (` 0))) · target-after-two

right-program-first-step :
  (ƛ (` 0)) · target-inst-redex
    —→[ bind ★ ] right-after-inst
right-program-first-step =
  ξ-·₂ (ƛ (` 0)) target-inst-step refl

right-program-second-step :
  right-after-inst —→[ bind (＇ Fin.zero) ] right-after-two
right-program-second-step =
  ξ-·₂ (ƛ (` 0)) target-second-step refl

right-program-two-step :
  (ƛ (` 0)) · target-inst-redex
    —↠[ bind ★ ∷ bind (＇ Fin.zero) ∷ [] ] right-after-two
right-program-two-step =
  (ƛ (` 0)) · target-inst-redex
  —→[ bind ★ ]⟨ right-program-first-step ⟩
  right-after-inst
  —→[ bind (＇ Fin.zero) ]⟨ right-program-second-step ⟩
  right-after-two ∎[]

target-after-two-value : Value target-after-two
target-after-two-value =
  (((ƛ (ƛ (` 1))) ↑ fun) ↑ fun) 《 fun 》

right-program-third-step :
  right-after-two —→[ keep ] target-after-two
right-program-third-step = pure-step (β target-after-two-value)

right-program-to-value :
  (ƛ (` 0)) · target-inst-redex
    —↠[ bind ★ ∷ bind (＇ Fin.zero) ∷ keep ∷ [] ] target-after-two
right-program-to-value =
  (ƛ (` 0)) · target-inst-redex
  —→[ bind ★ ]⟨ right-program-first-step ⟩
  right-after-inst
  —→[ bind (＇ Fin.zero) ]⟨ right-program-second-step ⟩
  right-after-two
  —→[ keep ]⟨ right-program-third-step ⟩
  target-after-two ∎[]

target-store-after-two :
  applyStore (bind (＇ Fin.zero))
      (applyStore (bind ★) store-empty)
    ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
target-store-after-two = refl
