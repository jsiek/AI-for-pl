{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxStrictLambdaProducerProbe where

-- File Charter:
--   * Checks the relation-side value-ready child for the trusted target
--     beta-inst; beta-Lambda trace in the two-Ctx design.
--   * Keeps alpha := star and beta := alpha as direct memberships, and keeps
--     the lambda parameter's exact edge-scoped term entry.
--   * Builds the canonical reveal-first instantiation spine and records the
--     exact first generated reveal.  The current edge-scoped CTI has no rule
--     that absorbs that composite conversion, so the probe stops there.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ★; ＇_; _⇒_; ⇑ᵗ; _[_]ᵗ)
open import TyStore using (_∋_⦂_; Z∋; S-bind∋)
import Imprecision as I
open import Conversion using (Conv↑; _⊢↑_; 〖_,_↑_〗)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; ⇑ᵉᵗ; Term; Value; `_; ƛ_; _↑_)
open import Reduction using (bind; applyTy)
open import proof.TypeSafety.Preservation using
  (replace-zero-open; structural-reveal-typing)
open import proof.DGG.notes.probes.TwoCtxFreshBehindPlanProbe
open import proof.DGG.notes.probes.TwoCtxEdgeIndexedModeProbe using
  (ExactAliasEdgeᵉ; edge-head)
import proof.DGG.notes.probes.TwoCtxEdgeScopedCTIProbe as EdgeCTI
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef using
  (InstantiationSpine; []ⁱ; _▻ⁱ_; reveal-frame; type-transport-frame;
   mapInstantiationSpine; lambda-ready-child-spine)


producer-edge : ExactAliasEdgeᵉ
  target-alpha-contextᶠ target-alpha-beta-contextᶠ
  target-alphaᶠ target-betaᶠ target-alpha⁺ᶠ
producer-edge = edge-head refl

module ProducerCTI =
  EdgeCTI.EdgeScopedCTI fresh-behind-alpha-focusᶠ producer-edge

open ProducerCTI


stable-X-star : ScopedType stable (＇ source-Xᶠ) ★
stable-X-star = scoped-type view-star (I.X⊑★ refl)

alpha-direct :
  Σᵉ target-alpha-beta-contextᶠ ∋ target-alpha⁺ᶠ ⦂ ★
alpha-direct = S-bind∋ (Z∋ refl) refl

alpha-boundary :
  ExactTargetBoundary stable target-alpha⁺ᶠ ★ stable-X-star
alpha-boundary = direct-target alpha-direct

alpha-mode : Mode
alpha-mode = push-focus stable target-alpha⁺ᶠ

alpha-valid : ValidMode alpha-mode
alpha-valid = push-valid stable-valid alpha-boundary

alpha-type : ScopedType alpha-mode
  (＇ source-Xᶠ) (＇ target-alpha⁺ᶠ)
alpha-type = focused-var

beta-direct :
  Σᵉ target-alpha-beta-contextᶠ ∋ target-betaᶠ
    ⦂ ＇ target-alpha⁺ᶠ
beta-direct = Z∋ refl

beta-boundary : ExactTargetBoundary alpha-mode target-betaᶠ
  (＇ target-alpha⁺ᶠ) alpha-type
beta-boundary = direct-target beta-direct

beta-mode : Mode
beta-mode = push-focus alpha-mode target-betaᶠ

beta-valid : ValidMode beta-mode
beta-valid = push-valid alpha-valid beta-boundary

beta-type : ScopedType beta-mode (＇ source-Xᶠ) (＇ target-betaᶠ)
beta-type = focused-var

beta-function-type : ScopedType beta-mode
  ((＇ source-Xᶠ) ⇒ (＇ source-Xᶠ))
  ((＇ target-betaᶠ) ⇒ (＇ target-betaᶠ))
beta-function-type = scoped-fun beta-type beta-type

alpha-function-type : ScopedType alpha-mode
  ((＇ source-Xᶠ) ⇒ (＇ source-Xᶠ))
  ((＇ target-alpha⁺ᶠ) ⇒ (＇ target-alpha⁺ᶠ))
alpha-function-type = scoped-fun alpha-type alpha-type


parameter-scope : ScopedWorld
  ⟨ Δᵉ (⇑ᵉᵗ empty-contextᶠ) ,
    Σᵉ (⇑ᵉᵗ empty-contextᶠ) , (＇ source-Xᶠ) ∷ [] ⟩
  ⟨ Δᵉ target-alpha-beta-contextᶠ ,
    Σᵉ target-alpha-beta-contextᶠ , (＇ target-betaᶠ) ∷ [] ⟩
parameter-scope = scoped-bind {S = scoped-root} beta-valid beta-type

parameter-entry :
  ScopedEntry parameter-scope zero beta-valid beta-type
parameter-entry = entry-here {S = scoped-root}

parameter-relation : ScopedCTI beta-mode beta-valid parameter-scope
  (` zero) (` zero) beta-type
parameter-relation = var⊑var parameter-entry

value-ready-source : Term (suc zero)
value-ready-source = ƛ (` zero)

value-ready-target : Term (suc (suc zero))
value-ready-target = ƛ (` zero)

value-ready-source-value : Value value-ready-source
value-ready-source-value = ƛ (` zero)

value-ready-target-value : Value value-ready-target
value-ready-target-value = ƛ (` zero)

value-ready-body-relation : ScopedCTI beta-mode beta-valid scoped-root
  value-ready-source value-ready-target beta-function-type
value-ready-body-relation =
  lambda⊑lambda {S = scoped-root} parameter-relation


record StrictLambdaChildProvenance : Set where
  constructor strict-lambda-child-provenance
  field
    alpha-membership :
      Σᵉ target-alpha-beta-contextᶠ ∋ target-alpha⁺ᶠ ⦂ ★
    beta-membership :
      Σᵉ target-alpha-beta-contextᶠ ∋ target-betaᶠ
        ⦂ ＇ target-alpha⁺ᶠ
    child-entry : ScopedEntry parameter-scope zero beta-valid beta-type
    child-relation : ScopedCTI beta-mode beta-valid scoped-root
      value-ready-source value-ready-target beta-function-type
    source-value : Value value-ready-source
    target-value : Value value-ready-target

value-ready-child : StrictLambdaChildProvenance
value-ready-child =
  strict-lambda-child-provenance alpha-direct beta-direct parameter-entry
    value-ready-body-relation value-ready-source-value
    value-ready-target-value


alpha-body-type : Ty (suc zero)
alpha-body-type =
  (＇ target-alphaᶠ) ⇒ (＇ target-alphaᶠ)

stable-body-type : Ty (suc zero)
stable-body-type = ★ ⇒ ★

alpha-generated-reveal : Conv↑ (suc zero) alpha-body-type stable-body-type
alpha-generated-reveal =
  〖 target-alphaᶠ , ★ ↑ alpha-body-type 〗

alpha-reveal-typed :
  Σᵉ target-alpha-contextᶠ ⊢↑ alpha-generated-reveal
alpha-reveal-typed =
  structural-reveal-typing alpha-body-type (Z∋ refl)

alpha-tail : InstantiationSpine alpha-body-type stable-body-type
alpha-tail = reveal-frame alpha-generated-reveal ▻ⁱ []ⁱ

beta-body-type : Ty (suc (suc zero))
beta-body-type =
  (＇ target-betaᶠ) ⇒ (＇ target-betaᶠ)

beta-generated-reveal : Conv↑ (suc (suc zero)) beta-body-type
  ((＇ target-alpha⁺ᶠ) ⇒ (＇ target-alpha⁺ᶠ))
beta-generated-reveal =
  〖 target-betaᶠ , ⇑ᵗ (＇ target-alphaᶠ) ↑ beta-body-type 〗

beta-reveal-typed :
  Σᵉ target-alpha-beta-contextᶠ ⊢↑ beta-generated-reveal
beta-reveal-typed = structural-reveal-typing beta-body-type beta-direct

reveal-first-spine : InstantiationSpine beta-body-type
  (applyTy (bind (＇ target-alphaᶠ)) stable-body-type)
reveal-first-spine =
  lambda-ready-child-spine
    {B = beta-body-type} {X = target-alphaᶠ} alpha-tail

reveal-first-spine-shape : reveal-first-spine ≡
  reveal-frame beta-generated-reveal ▻ⁱ
  type-transport-frame
    (replace-zero-open beta-body-type (＇ target-alphaᶠ)) ▻ⁱ
  mapInstantiationSpine (bind (＇ target-alphaᶠ)) alpha-tail
reveal-first-spine-shape = refl


-- The next relation required by reveal-frame absorption is exactly:
--
--   ScopedCTI alpha-mode alpha-valid scoped-root
--     value-ready-source (value-ready-target ↑ beta-generated-reveal)
--     alpha-function-type
--
-- `target-reveal` only constructs a direct `unseal Y R` at source type
-- `＇ source-X`.  The required conversion is the generated function
-- conversion
--
--   makeConceal beta alpha (beta) ↦↑ unseal beta alpha
--
-- at source type `source-X ⇒ source-X`.  No current constructor produces
-- that relation from `value-ready-body-relation` and `beta-reveal-typed`.
