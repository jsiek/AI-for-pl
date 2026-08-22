module LR-narrow.Context.DynamicPayloadIntroduction where

-- File Charter:
--   * Proves the three fundamental introduction cases for dynamic payloads.
--   * Covers base, function, and paired-variable runtime ground tags.
--   * Constructs tag agreement explicitly and reuses the supplied recursive
--     payload relation without changing its logical index.

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ImprecisionWf using (_ˣ⊑ˣ_; idˣ; idι; id★; _↦_)
open import Interpreter using
  ( SealName
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
open import LR-narrow.Dynamic
open import LR-narrow.LogicalRelation using
  (DynamicPayloadRelated; ValueNarrowing; tags-and-payload)
open import LR-narrow.World
open import Types using (Base; TyCtx; ★⇒★)
import Types

private
  tag-of-variable : ∀ {θ : TypeEnvironment} {X : ℕ} {name}
    → lookup θ X ≡ just name
    → tagOf θ (Types.＇ X) ≡ just (variable-tag name)
  tag-of-variable {θ = []} ()
  tag-of-variable {θ = name ∷ θ} {X = zero} refl = refl
  tag-of-variable {θ = name ∷ θ} {X = suc X} name-eq =
    tag-of-variable {θ = θ} {X = X} name-eq

dynamic-payload-base : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} w}
    {k} {ι : Base} {θᴵ θᴾ : TypeEnvironment} {Uᴵ Uᴾ : Value}
  → ValueNarrowing (idι {ι = ι}) I k Uᴵ Uᴾ
  → DynamicPayloadRelated I k
      (tagged (Types.‵ ι) θᴵ Uᴵ)
      (tagged (Types.‵ ι) θᴾ Uᴾ)
dynamic-payload-base payload-related =
  tags-and-payload idι
    (ground-tag-agreement (base-tag _) (base-tag _)
      refl refl base-tags-equal)
    payload-related

dynamic-payload-function : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} w}
    {k} {θᴵ θᴾ : TypeEnvironment} {Uᴵ Uᴾ : Value}
  → ValueNarrowing (id★ ↦ id★) I k Uᴵ Uᴾ
  → DynamicPayloadRelated I k
      (tagged ★⇒★ θᴵ Uᴵ) (tagged ★⇒★ θᴾ Uᴾ)
dynamic-payload-function payload-related =
  tags-and-payload (id★ ↦ id★)
    (ground-tag-agreement function-tag function-tag
      refl refl function-tags-equal)
    payload-related

dynamic-payload-variable : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} w}
    {k X Y} {X< : X < Δᴾ} {Y< : Y < Δᴵ}
    {assumption∈ : (X ˣ⊑ˣ Y) ∈ Φ}
    {left-seal right-seal : SealName} {Uᴵ Uᴾ : Value}
  → lookup (left-types I) Y ≡ just (seal-name left-seal)
  → lookup (right-types I) X ≡ just (seal-name right-seal)
  → bindings w ∋ left-seal ↔ right-seal ∶
      relation (lookup-atom assumption∈ (atoms I))
  → ValueNarrowing (idˣ assumption∈ X< Y<) I k Uᴵ Uᴾ
  → DynamicPayloadRelated I k
      (tagged (Types.＇ Y) (left-types I) Uᴵ)
      (tagged (Types.＇ X) (right-types I) Uᴾ)
dynamic-payload-variable {I = I} {X = X} {Y = Y}
    {left-seal = left-seal} {right-seal = right-seal}
    left-name right-name binding payload-related =
  tags-and-payload (idˣ _ _ _)
    (ground-tag-agreement
      (variable-tag (seal-name left-seal))
      (variable-tag (seal-name right-seal))
      (tag-of-variable {θ = left-types I} {X = Y} left-name)
      (tag-of-variable {θ = right-types I} {X = X} right-name)
      (variable-tags-equal right-name left-name binding))
    payload-related
