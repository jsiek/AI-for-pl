{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxFreshBehindPlanProbe where

-- File Charter:
--   * Instantiates the live SourceFreshBehindPlan at the strict-Lambda
--     producer geometry.
--   * Checks a target-star allocation followed by a source binder and keeps
--     beta := alpha in the boundary-scoped alias layer.
--   * Contains fixtures only; the general plan, interpreter, and laws live in
--     proof.DGG.SourceFreshBehindPlan.

open import Data.List using ([])
open import Data.Nat using (suc; zero)
open import Data.Sum using (inj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl)

open import Types using (TyVar; ★; ＇_)
open import TyStore using (store-empty; store-bind; lookupStore)
open import Consistency using (empty; keep; skip; id↪ᵗ; toRenameᵗ)
import Imprecision
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; ⇑ᵉᵗ)
open import proof.DGG.World
open import proof.DGG.SourceFreshBehindPlan
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe


-- Exact producer geometry: alpha is allocated as a direct target star, then
-- the source binder is commuted behind alpha.  Beta := alpha is kept out of
-- the stable history and represented by the boundary-scoped alias focus.

empty-contextᶠ : Ctx
empty-contextᶠ = ⟨ zero , store-empty , [] ⟩

target-alpha-contextᶠ : Ctx
target-alpha-contextᶠ =
  ⟨ suc zero , store-bind store-empty ★ , [] ⟩

target-alpha-worldᶠ : empty-contextᶠ ⊑ᶜ target-alpha-contextᶠ
target-alpha-worldᶠ =
  bind-right-rawᶜ emptyᶜ ★ (inj₁ refl) refl

fresh-behind-alpha-planᶠ :
  SourceFreshBehindPlan target-alpha-worldᶠ
fresh-behind-alpha-planᶠ =
  source-fresh-behind-target-star source-fresh-here refl

stable-worldᶠ : ⇑ᵉᵗ empty-contextᶠ ⊑ᶜ target-alpha-contextᶠ
stable-worldᶠ = insertSourceFreshBehind fresh-behind-alpha-planᶠ

stable-source-embeddingᶠ : ηᴸᶜ stable-worldᶠ ≡ skip (keep empty)
stable-source-embeddingᶠ = refl

stable-target-embeddingᶠ : ηᴿᶜ stable-worldᶠ ≡ keep (skip empty)
stable-target-embeddingᶠ = refl

stable-old-centersᶠ :
  sourceFreshBehind-oldCenters fresh-behind-alpha-planᶠ
    ≡ keep (skip id↪ᵗ)
stable-old-centersᶠ = refl

source-Xᶠ : TyVar (Δᵉ (⇑ᵉᵗ empty-contextᶠ))
source-Xᶠ = Fin.zero

target-alphaᶠ : TyVar (Δᵉ target-alpha-contextᶠ)
target-alphaᶠ = Fin.zero

source-alpha-separatedᶠ :
  toRenameᵗ (ηᴸᶜ stable-worldᶠ) source-Xᶠ
    ≢ toRenameᵗ (ηᴿᶜ stable-worldᶠ) target-alphaᶠ
source-alpha-separatedᶠ ()

source-X-selfᶠ :
  lookupStore (Σᵉ (⇑ᵉᵗ empty-contextᶠ)) source-Xᶠ ≡ ＇ source-Xᶠ
source-X-selfᶠ = refl

source-alpha-representationsᶠ :
  lookupStore (Σᵉ (⇑ᵉᵗ empty-contextᶠ)) source-Xᶠ
    ⊑ᵀ⟨ stable-worldᶠ ⟩
  lookupStore (Σᵉ target-alpha-contextᶠ) target-alphaᶠ
source-alpha-representationsᶠ = Imprecision.X⊑★ refl

fresh-behind-alpha-focusᶠ :
  TargetNameFocusᶠ₀ stable-worldᶠ source-Xᶠ target-alphaᶠ
fresh-behind-alpha-focusᶠ =
  target-name-focusᶠ₀ source-alpha-separatedᶠ source-X-selfᶠ
    source-alpha-representationsᶠ

target-alpha-beta-contextᶠ : Ctx
target-alpha-beta-contextᶠ =
  ⟨ suc (suc zero) ,
    store-bind (store-bind store-empty ★) (＇ target-alphaᶠ) , [] ⟩

fresh-behind-alpha-boundaryᶠ :
  TargetAliasBoundaryᶠ₀ fresh-behind-alpha-focusᶠ
    target-alpha-beta-contextᶠ
fresh-behind-alpha-boundaryᶠ = target-alias-rawᶠ₀ refl

target-betaᶠ : TyVar (Δᵉ target-alpha-beta-contextᶠ)
target-betaᶠ = Fin.zero

target-alpha⁺ᶠ : TyVar (Δᵉ target-alpha-beta-contextᶠ)
target-alpha⁺ᶠ = Fin.suc target-alphaᶠ

target-beta-entryᶠ :
  lookupStore (Σᵉ target-alpha-beta-contextᶠ) target-betaᶠ
    ≡ ＇ target-alpha⁺ᶠ
target-beta-entryᶠ = refl

target-alpha-entryᶠ :
  lookupStore (Σᵉ target-alpha-beta-contextᶠ) target-alpha⁺ᶠ ≡ ★
target-alpha-entryᶠ = refl

fresh-behind-alias-surfaceᶠ :
  BoundaryTypeImprecisionᶠ₀ fresh-behind-alpha-boundaryᶠ
    (＇ source-Xᶠ) (＇ target-betaᶠ)
fresh-behind-alias-surfaceᶠ = Imprecision.X⊑X
