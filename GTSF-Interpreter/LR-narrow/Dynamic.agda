module LR-narrow.Dynamic where

-- File Charter:
--   * Defines observable dynamic-tag agreement for the active logical
--     relation.
--   * Treats paired variable seals as equal through the current Kripke world.
--   * Leaves recursive payload relatedness to `LogicalRelation`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _<_)

open import ImprecisionWf
open import Interpreter using
  ( Tag
  ; SealName
  ; TypeEnvironment
  ; Value
  ; base-tag
  ; function-tag
  ; lookup
  ; seal-name
  ; tagOf
  ; tagged
  ; variable-tag
  )
open import LR-narrow.Atoms using (lookup-atom; relation)
open import LR-narrow.World
open import Types using (Ground; Ty; TyCtx)

data TagEqualityAt
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w) :
    ∀ {Gᴾ Gᴵ : Ty}
    → Φ ∣ Δᴾ ⊢ Gᴾ ⊑ Gᴵ ⊣ Δᴵ
    → Tag → Tag → Set₁ where

  variable-tags-equal : ∀
      {X Y : ℕ} {left-seal right-seal : SealName}
      {assumption∈ : (X ˣ⊑ˣ Y) ∈ Φ}
      {X< : X < Δᴾ} {Y< : Y < Δᴵ}
    → lookup (right-types I) X ≡ just (seal-name right-seal)
    → lookup (left-types I) Y ≡ just (seal-name left-seal)
    → bindings w ∋ left-seal ↔ right-seal ∶
        relation (lookup-atom assumption∈ (atoms I))
    → TagEqualityAt I (idˣ assumption∈ X< Y<)
        (variable-tag (seal-name left-seal))
        (variable-tag (seal-name right-seal))

  base-tags-equal : ∀ {ι}
    → TagEqualityAt I (idι {ι = ι}) (base-tag ι) (base-tag ι)

  function-tags-equal :
    TagEqualityAt I (id★ ↦ id★) function-tag function-tag

record GroundTagAgreement
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w)
    {Gᴾ Gᴵ : Ty} (q : Φ ∣ Δᴾ ⊢ Gᴾ ⊑ Gᴵ ⊣ Δᴵ)
    (gᴵ : Ground Gᴵ) (gᴾ : Ground Gᴾ)
    (left-types right-types : TypeEnvironment) : Set₁ where
  constructor ground-tag-agreement
  field
    left-tag : Tag
    right-tag : Tag
    left-tag-result : tagOf left-types gᴵ ≡ just left-tag
    right-tag-result : tagOf right-types gᴾ ≡ just right-tag
    tags-equal : TagEqualityAt I q left-tag right-tag

open GroundTagAgreement public

record DynamicPayloadShape
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w)
    (Vᴵ Vᴾ : Value) : Set₁ where
  constructor dynamic-payload-shape
  field
    precise-ground : Ty
    imprecise-ground : Ty
    precise-ground-proof : Ground precise-ground
    imprecise-ground-proof : Ground imprecise-ground
    dynamic-left-types : TypeEnvironment
    dynamic-right-types : TypeEnvironment
    dynamic-left-payload : Value
    dynamic-right-payload : Value
    dynamic-left-shape :
      Vᴵ ≡ tagged imprecise-ground-proof dynamic-left-types
        dynamic-left-payload
    dynamic-right-shape :
      Vᴾ ≡ tagged precise-ground-proof dynamic-right-types
        dynamic-right-payload
    payload-imprecision :
      Φ ∣ Δᴾ ⊢ precise-ground ⊑ imprecise-ground ⊣ Δᴵ
    payload-tags-agree :
      GroundTagAgreement I payload-imprecision
        imprecise-ground-proof precise-ground-proof
        dynamic-left-types dynamic-right-types

open DynamicPayloadShape public
