module proof.DGG.Catchup.InstCatchupRightProof where

-- File Charter:
--   * Proves the checked right-instantiation catch-up auxiliaries stated in
--     InstCatchupRightDef.
--   * Provides the concrete right-only continuation world extensions and the
--     direct allocation redexes for each target polymorphic value view.
--   * Does not register or stitch the full InstCatchupRight² driver.

import Data.Fin as Fin
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Consistency using
  (∀ᶜ_; _[_]ᶜ; inst_; gen_; ↑ᶜ_; close-instᶜ)
open import Conversion using (`∀↑_; `∀↓_; 〖_,_↑_〗)
import CastTerms as CT
open import CastTerms using
  (Value; RevealValue; _⟨_⟩; _⦂∀_[_]; _↑_; _↓_; Λ_; ⇑ᵗᵐ)
open import Reduction using
  ( _—↠[_]_; _—→[_]⟨_⟩_; _∎[]; bind; keep; applyBody
  ; pure-step; β-inst; β-Λ; β-∀; β-gen; β-reveal-∀; β-conceal-∀
  )

open import proof.DGG.Catchup.InstCatchupRightDef
  using
    ( RightBindWorldExtendᴿᵀ
    ; RightBindKeepWorldExtendᴿᵀ
    ; RightBindRightBindWorldExtendᴿᵀ
    ; RightBindTransport⊑ᵂᵀ
    ; RightBindMapCtxᴿᵀ
    ; InstCastAllocPrefixᵀ
    ; TypeAppΛStepᵀ
    ; TypeApp∀Stepᵀ
    ; TypeAppGenStepᵀ
    ; TypeAppRevealStepᵀ
    ; TypeAppConcealStepᵀ
    ; AllValueViewStepCatalogᵀ
    )
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.Parked.ParkedWorldDef as PWD
import proof.DGG.Parked.ParkedWorldLemma as PWL


right-bind-world-extendᴿ : RightBindWorldExtendᴿᵀ
right-bind-world-extendᴿ fresh =
  PWL.right-only-parked→world-extendᴿ
    (PWD.evolve-right-bind {fresh = fresh} PWD.evolve-refl)


right-bind-keep-world-extendᴿ : RightBindKeepWorldExtendᴿᵀ
right-bind-keep-world-extendᴿ fresh =
  PWL.right-only-parked→world-extendᴿ
    (PWD.evolve-right-bind {fresh = fresh}
      (PWD.evolve-keepᴿ PWD.evolve-refl))


right-bind-right-bind-world-extendᴿ :
  RightBindRightBindWorldExtendᴿᵀ
right-bind-right-bind-world-extendᴿ freshB freshC =
  PWL.right-only-parked→world-extendᴿ
    (PWD.evolve-right-bind {fresh = freshB}
      (PWD.evolve-right-bind {fresh = freshC} PWD.evolve-refl))


right-bind-transport⊑ᵂ : RightBindTransport⊑ᵂᵀ
right-bind-transport⊑ᵂ {W = W} {B′ = B′} fresh p =
  ECR.transport⊑ᵂ
    (right-bind-world-extendᴿ {W = W} {B = B′} fresh) p


right-bind-mapCtxᴿ : RightBindMapCtxᴿᵀ
right-bind-mapCtxᴿ {W = W} {B = B} fresh γ =
  ECR.mapCtxᴿ (right-bind-world-extendᴿ {W = W} {B = B} fresh) γ


generated-reveal-value : ∀ {Δ} {X : TyVar Δ} {R B : Ty Δ}
  → NonVar B
  → X ∈ᵗ B
  → RevealValue (〖 X , R ↑ B 〗)
generated-reveal-value nonvar-base ()
generated-reveal-value nonvar-star ()
generated-reveal-value nonvar-fun X∈B = CT.fun
generated-reveal-value nonvar-all X∈B = CT.all


inst-cast-alloc-prefix : InstCastAllocPrefixᵀ
inst-cast-alloc-prefix {V = V} {A = A} {c = c} vV B≢★ =
  V ⟨ (inst c) B≢★ ⟩
    —→[ bind ★ ]⟨ β-inst vV B≢★ ⟩
  (⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ Fin.zero ] ↑
    〖 Fin.zero , ★ ↑ A 〗 ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩) ∎[]


type-app-Λ-step : TypeAppΛStepᵀ
type-app-Λ-step {A = A} {B = B} {V = V} vV =
  (Λ V) ⦂∀ B [ A ]
    —→[ bind A ]⟨ β-Λ vV ⟩
  (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) ∎[]


type-app-∀-step : TypeApp∀Stepᵀ
type-app-∀-step {D = D} {A = A} {B = B} {V = V} {c = c} vV =
  (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ D ]
    —→[ keep ]⟨ pure-step (β-∀ vV refl) ⟩
  ((V ⦂∀ A [ D ]) ⟨ c [ D ]ᶜ ⟩) ∎[]


type-app-gen-step : TypeAppGenStepᵀ
type-app-gen-step {C = C} {B = B} {V = V} {c = c} vV A≢★ safe =
  (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ]
    —→[ bind C ]⟨ β-gen vV A≢★ safe ⟩
  (⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 Fin.zero , ⇑ᵗ C ↑ B 〗) ∎[]


type-app-reveal-step : TypeAppRevealStepᵀ
type-app-reveal-step {A = A} {B = B} {C = C} {V = V} {c = c} vV =
  (V ↑ `∀↑ c) ⦂∀ B [ A ]
    —→[ bind A ]⟨ β-reveal-∀ vV ⟩
  (((⇑ᵗᵐ V ⦂∀ applyBody (bind A) C [ ＇ Fin.zero ]) ↑ c)
    ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) ∎[]


type-app-conceal-step : TypeAppConcealStepᵀ
type-app-conceal-step {A = A} {B = B} {C = C} {V = V} {c = c} vV =
  (V ↓ `∀↓ c) ⦂∀ B [ A ]
    —→[ bind A ]⟨ β-conceal-∀ vV ⟩
  ((⇑ᵗᵐ V ⦂∀ applyBody (bind A) C [ ＇ Fin.zero ] ↓ c)
    ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) ∎[]


all-value-view-step-catalog : AllValueViewStepCatalogᵀ
all-value-view-step-catalog =
  type-app-Λ-step ,
  type-app-∀-step ,
  type-app-gen-step ,
  type-app-reveal-step ,
  type-app-conceal-step
