module proof.Catchup.Simulation.NuImprecisionSimulationCore where

-- File Charter:
--   * Builds composition, framing, allocation-prefix, and terminal helpers
--     over the stable weak one-step result and transport interfaces.
--   * Defines structural world embeddings and proves their exhaustive mutual
--     action on ordinary and quotiented no-runtime-bullet imprecision.
--   * Lifts weak-result type transport through the `∀`-permutation
--     quotient used by paired narrowing/widening casts.
--   * Proves that adjacent type-name swapping permutes arbitrary coercion-mode
--     stacks, including seal permissions and crossed `gen`/`inst` orders.
--   * Derives both orientations of the adjacent-`∀` crossed-body relation
--     from structural embeddings, with no syntax-specific imprecision rule.
--   * Ends at the direct-swap residual lemmas; allocation and active
--     universal catch-up cases live in the downstream simulation modules.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
import Relation.Binary.HeterogeneousEquality as HE

open import Types
open import Ctx using (⤊ᵗ)
open import Coercions using
  ( Coercion
  ; ModeIncl
  ; ModeEnv
  ; Mode
  ; id-only
  ; tag-or-id
  ; seal-or-id
  ; _!
  ; mode≤
  ; extᵈ
  ; gen
  ; genᵈ
  ; id-onlyᵈ
  ; id-only≤tag-or-idᵈ
  ; inst
  ; instᵈ
  ; renameᶜ
  ; sealModeAllowed
  ; tag-or-idᵈ
  ; `∀
  ; ⇑ᶜ
  ; _[_]ᶜ
  )
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; open-conceal-conversion
  ; open-reveal-conversion
  ; reveal-all
  ; rename-reveal-conversion
  ; rename-conceal-conversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ForallPermutation using
  ( _≈∀_
  ; quotientᵖ
  ; swap01ᵗ
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  ; _∣_⊢_⊑ᵖ_⊣_
  )
open import ImprecisionWf
open import NarrowWiden using
  ( narrow-mode-relax
  ; narrow-renameᵗ
  ; narrow-weaken
  ; widen-mode-relax
  ; widen-renameᵗ
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
import Coercions as C
import NarrowWiden as NW
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; applyCoercion
  ; applyStore
  ; applyStores
  ; applyCoercionUnderTyBinder
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; blame-·₁
  ; blame-·₂
  ; blame-⟨⟩
  ; blame-ν
  ; keep
  ; β-gen•
  ; β-inst
  ; β-Λ•
  ; β-∀•
  ; pure-step
  ; ν-step
  ; ξ-⟨⟩
  ; ξ-ν
  ; ↠-refl
  ; ↠-step
  ; _—→[_]_
  ; _—↠[_]_
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; no•-`
  ; no•-ƛ
  ; no•-·
  ; no•-Λ
  ; no•-ν
  ; no•-$
  ; no•-⊕
  ; no•-⟨⟩
  ; no•-blame
  ; ok-no
  ; ok-•
  ; ok-·₁
  ; ok-·₂
  ; ok-ν
  ; ok-⊕₁
  ; ok-⊕₂
  ; ok-⟨⟩
  ; blame
  ; Term
  ; Value
  ; `_
  ; ƛ_
  ; _·_
  ; Λ_
  ; ν
  ; renameᵗᵐ
  ; ⇑ᵗᵐ
  ; _•
  ; $
  ; _⊕[_]_
  ; _⟨_⟩
  )
open import Primitives using (κℕ; addℕ)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; StoreImpEntry
  ; StoreCorresponds
  ; correspondence-stored
  ; correspondence-linked
  ; LiftStoreⁱ
  ; lift-store-[]
  ; lift-store-∷
  ; lift-store-left
  ; lift-store-right
  ; lift-store-link
  ; LiftLeftStoreⁱ
  ; lift-left-store-[]
  ; lift-left-store-∷
  ; lift-left-store-left
  ; lift-left-store-right
  ; lift-left-store-link
  ; LiftRightStoreⁱ
  ; lift-right-store-[]
  ; lift-right-store-∷
  ; lift-right-store-left
  ; lift-right-store-right
  ; lift-right-store-link
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; leftStoreⁱ-lift
  ; rightStoreⁱ-lift
  ; leftStoreⁱ-lift-left
  ; rightStoreⁱ-lift-left
  ; leftStoreⁱ-lift-right
  ; rightStoreⁱ-lift-right
  ; store-matched
  ; store-left
  ; store-right
  ; store-link
  )
open import proof.Store.Correspondence.NuImprecisionCrossedStore using
  ( crossedStoreⁱ
  ; crossedStoreⁱ-new-old
  ; crossedStoreⁱ-old-new
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; ctx-imp
  ; LiftCtxⁱ
  ; lift-ctx-[]
  ; lift-ctx-∷
  ; LiftLeftCtxⁱ
  ; lift-left-ctx-[]
  ; lift-left-ctx-∷
  ; LiftRightCtxⁱ
  ; lift-right-ctx-[]
  ; lift-right-ctx-∷
  ; leftCtxⁱ
  ; rightCtxⁱ
  ; leftCtxⁱ-lift
  ; rightCtxⁱ-lift
  ; leftCtxⁱ-lift-left
  ; rightCtxⁱ-lift-left
  ; leftCtxⁱ-lift-right
  ; rightCtxⁱ-lift-right
  )
open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (narrowing; widening)
open import QuotientedTermImprecision
open import ConversionIndexCompatibility
open import QuotientImprecisionCompatibility using
  ( ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  )
open import
  proof.Quotient.NuImprecisionQuotientEliminationCompatibilityRename
  using
  ( reduction-closed-paired-compatible-rename-leftᵢ
  ; reduction-closed-paired-compatible-rename²ᵢ
  ; reduction-closed-quotient-compatible-rename-leftᵢ
  ; reduction-closed-quotient-compatible-rename²ᵢ
  )
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _↦ˢ_
  ; ∀ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  ; νˢ-injective
  ; _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercionUnderTyBinders
  ; cast-shape-rename
  ; imprecision-composition-shape-transport
  ; rename-assm²-target-ext-idᵢ
  ; rename-assm²-∀-leftᵢ
  ; shape-lift∀ᵢ
  ; shape-rename
  ; shape-rename-left
  ; shape-rename-left-atᵢ
  ; shape-source-liftνᵢ
  ; shape-subst-source
  ; shape-subst-target
  ; shape-target-lift-rightᵢ
  ; ⊑-rename-leftᵢ
  ; ⊑-rename-left-atᵢ
  )
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using
  ( quotient-boundary-square-rename-left
  ; quotient-boundary-square-rename²
  )
open import proof.Core.Properties.ConversionIndexCompatibilityProperties using
  ( replace-left-rename-leftᵢ
  ; replace-left-rename²ᵢ
  ; replace-left-source-shape
  ; replace-left-target-shape
  ; replace-left-transport-endpoints
  ; replace-paired-evidence-shape
  ; replace-paired-rename-leftᵢ
  ; replace-paired-rename²ᵢ
  ; replace-paired-source-shape
  ; replace-paired-target-shape
  ; replace-paired-transport-endpoints
  ; replace-right-rename-leftᵢ
  ; replace-right-rename²ᵢ
  ; replace-right-source-shape
  ; replace-right-target-shape
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  ; transport-imprecision-endpoints
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
open import proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-composeⁱ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingPrefixProof
  using (rel-store-embedding-prefix-invⁱ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingProof using
  (rel-store-embedding-correspondenceⁱ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( nu-term-imprecision-transport-typesᵀ
  ; transportAllType-to-raw≅
  ; transportArrowType-to-raw≅
  ; transportSourceNuType-to-raw≅
  ; transportType-transportAllType-to-raw≅
  ; transportType-transportArrowType-to-raw≅
  ; transportType-transportSourceNuType-to-raw≅
  ; weak-one-step-reindex-preserves-transportᵀ
  ; weak-one-step-reindexᵀ
  ; weak-result-transport-arrow-termsᵀ
  )
open import
  proof.Core.Equality.HeterogeneousEqualityTransport
  using (subst-to-≅; subst²-to-≅)
open import proof.OneStep.NuImprecisionOneStepRelated using
  ( weak-one-step-indexed-outcome-relatedᵀ
  ; weak-one-step-indexed-relatedᵀ
  ; weak-one-step-related-transportᵀ
  ; weak-one-step-related-type-coherenceᵀ
  ; weak-one-step-relatedᵀ
  )
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-store-result; lift-left-store-result; lift-right-store-result)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import Store using (StoreIncl; StoreIncl-drop; StoreIncl-refl)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-ext
  ; cast-gen
  ; cast-inst
  ; cast-tag-or-id
  ; cast-weaken
  ; weakenCastᵈ
  ; forget
  ; _∣_∣_⊢_⦂_
  ; ⊢•
  ; ⊢⟨⟩↑
  )
open import proof.Core.Properties.CastImprecision using
  ( RightCastCtxCompatible
  ; seal★-ext-shift
  ; seal★-gen-shift
  ; widening⇒⊑ᵢ
  ; ⊑-transʳ-castᵢ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( rename-assm²-composeᵢ
  ; rename-assm²-congᵢ
  ; rename-assm²-crossed-left∀∀ᵢ
  ; rename-assm²-crossed-right∀∀ᵢ
  ; rename-assm²-crossed-double∀∀ᵢ
  ; rename-assm²-swapLeft∀∀ᵢ
  ; rename-assm²-swapRight∀∀ᵢ
  ; ⊑-crossed-body-lift∀∀ᵢ
  ; ⊑-crossed-left-body-lift∀∀ᵢ
  ; ⊑-crossed-double-lift∀∀ᵢ
  ; ⊑-ν∀-to-∀νᵢ
  ; ⊑-swapLeft01∀∀ᵢ
  ; ⊑-swapRight01∀∀ᵢ
  ; swap01ᵢ
  ; swap01ᵢ-after-suc
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( ∀ᵢᶜ
  ; rename-assm²ᵢ
  ; rename-assm²-∀ᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-source-νᵢ
  ; rename-assm²-target-rightᵢ
  ; ⊑-rename-at²ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-open∀ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import proof.Core.Permutation.ForallPermutationProperties using
  ( ≈∀-double-swap
  ; ≈∀-double-swap-sym
  ; ≈∀-renameᵗ
  ; ⊑→⊑ᵖ
  ; ⊑ᵖ-rename-leftᵢ
  ; ⊑ᵖ-rename²ᵢ
  )
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (weak-one-step-transport-quotientᵀ)
open import proof.Core.Properties.NarrowWidenBinderProperties using
  ( allocate-all-narrowing
  ; allocate-all-widening
  ; allocate-gen-narrowing
  ; open-all-narrowing
  ; open-all-widening
  )
open import proof.Core.Properties.NarrowWidenStoreInvariantDef
  using (StoreDetWf)
open import proof.Core.Properties.NuTermProperties using
  ( modeRename-left-inverse
  ; open0-ext-suc-cancelᵐ
  ; renameStoreᵗ-ext-suc-cons-comm
  ; renameᵗᵐ-compose
  ; renameᵗᵐ-cong
  ; renameᵗᵐ-ext-suc-comm
  ; renameᵗᵐ-id
  ; renameᵗᵐ-preserves-No•
  ; renameᵗᵐ-preserves-Value
  )
open import proof.DGG.Core.NuProgress using
  ( AllView
  ; av-Λ
  ; av-∀
  ; av-gen
  ; canonical-∀
  ; runtime-value-no•
  )
open import proof.DGG.Core.NuPreservation using
  ( runtime-ν
  ; runtime-⟨⟩
  ; value-no-step
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-inst
  ; applyCoercions-preserves-Inert
  ; applyCoercionUnderTyBinders-preserves-Inert
  ; applyCoercionUnderTyBinders-reflects-Inert
  ; applyCoercionUnderTyBinders
  ; applyTerm-preserves-No•
  ; applyTerm-preserves-Value
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyStores-++
  ; applyTyVar
  ; applyTyVars
  ; applyTyVars-++
  ; applyTy-∀
  ; applyTyUnderTyBinder
  ; applyTyCtxs-++
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
  ; applyTysUnderTyBinders-⇑ᵗ
  ; applyTys-++
  ; applyTys-⇒
  ; applyTys-★
  ; applyTys-∀
  ; cast-↠
  ; wfTy-applyTys
  ; ·₁-↠
  ; ·₂-↠
  ; ν-↠
  ; ↠-trans
  )
open import proof.Core.Properties.CoercionProperties using
  ( ModeIncl-ext
  ; ModeIncl-gen
  ; ModeIncl-inst
  ; ModeRename
  ; modeRename-id-only
  ; open0-ext-suc-cancelᶜ
  ; renameᶜ-preserves-Inert
  ; renameᶜ-reflects-Inert
  )
open import proof.Core.Properties.TypePreservation using
  ( applyWidenInstUnderTyBinder-typing
  ; CastModeRenamer
  ; castModeRenamer-ext
  ; castModeRenamer-seal★
  ; seal★-inst
  ; seal★-weaken
  ; castModeRenamer-suc
  ; modeRename-suc-weakenCast
  ; preservation
  ; term-weaken
  ; typing-renameᵀ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  ( apply-fixed-narrows-typing
  ; apply-narrows-typing
  ; apply-spine-narrows-typing
  )
open import proof.Core.Properties.StoreProperties using
  (∈-renameStoreᵗ; renameStoreᵗ-incl)
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; RenameLeftInverse-ext-suc-pred
  ; RenameLeftInverse-suc
  ; TyPermutation
  ; TyPermutation-ext
  ; TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; backward
  ; backward-forward
  ; forward
  ; forward-backward
  ; forward-wf
  ; predᵗ
  ; occurs-zero-rename-ext
  ; rename-cong
  ; renameᵗ-compose
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-ground
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  ; renameStoreᵗ-compose
  ; renameStoreᵗ-ext-suc-comm
  )

store-incl-insert-second :
  ∀ {Σ α β A B} →
  StoreIncl ((α , A) ∷ Σ) ((α , A) ∷ (β , B) ∷ Σ)
store-incl-insert-second (here refl) = here refl
store-incl-insert-second (there x∈) = there (there x∈)

apply-reveal-under-ty-binder :
  ∀ {χ μ Δ Σ Aν B C c} →
  RevealConversion μ (suc Δ)
    ((zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ)
    zero (⇑ᵗ Aν) c C (⇑ᵗ B) →
  ∃[ μ′ ]
    RevealConversion μ′ (suc (applyTyCtx χ Δ))
      ((zero , ⇑ᵗ (applyTy χ Aν)) ∷ ⟰ᵗ (applyStore χ Σ))
      zero (⇑ᵗ (applyTy χ Aν))
      (applyCoercionUnderTyBinder χ c)
      (applyTyUnderTyBinder χ C) (⇑ᵗ (applyTy χ B))
apply-reveal-under-ty-binder {χ = keep} {μ = μ} c↑ = μ , c↑
apply-reveal-under-ty-binder
    {χ = bind Aχ} {μ = μ} {Δ = Δ} {Σ = Σ}
    {Aν = Aν} {B = B} {C = C} {c = c} c↑ =
  (λ Y → μ (predᵗ Y)) ,
  weaken-reveal-conversion store-incl-insert-second
    (subst
      (λ T → RevealConversion (λ Y → μ (predᵗ Y))
        (suc (suc Δ))
        ((zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ (⟰ᵗ Σ))
        zero (⇑ᵗ (⇑ᵗ Aν))
        (renameᶜ (extᵗ suc) c)
        (renameᵗ (extᵗ suc) C) T)
      (renameᵗ-ext-suc-comm suc B)
      (subst
        (λ T → RevealConversion (λ Y → μ (predᵗ Y))
          (suc (suc Δ))
          ((zero , T) ∷ ⟰ᵗ (⟰ᵗ Σ))
          zero T (renameᶜ (extᵗ suc) c)
          (renameᵗ (extᵗ suc) C)
          (renameᵗ (extᵗ suc) (⇑ᵗ B)))
        (renameᵗ-ext-suc-comm suc Aν)
        (subst
          (λ Σ′ → RevealConversion (λ Y → μ (predᵗ Y))
            (suc (suc Δ)) Σ′ zero
            (renameᵗ (extᵗ suc) (⇑ᵗ Aν))
            (renameᶜ (extᵗ suc) c)
            (renameᵗ (extᵗ suc) C)
            (renameᵗ (extᵗ suc) (⇑ᵗ B)))
          renamed-store
          (rename-reveal-conversion
            (TyRenameWf-ext TyRenameWf-suc)
            (modeRename-left-inverse
              {ρ = extᵗ suc} {ψ = predᵗ}
              RenameLeftInverse-ext-suc-pred)
            c↑))))
  where
    renamed-store :
      renameStoreᵗ (extᵗ suc)
          ((zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ)
        ≡ (zero , renameᵗ (extᵗ suc) (⇑ᵗ Aν)) ∷
          ⟰ᵗ (⟰ᵗ Σ)
    renamed-store =
      cong₂ _∷_ refl (renameStoreᵗ-ext-suc-comm suc Σ)

apply-reveal-under-ty-binders :
  ∀ {χs μ Δ Σ Aν B C c} →
  RevealConversion μ (suc Δ)
    ((zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ)
    zero (⇑ᵗ Aν) c C (⇑ᵗ B) →
  ∃[ μ′ ]
    RevealConversion μ′ (suc (applyTyCtxs χs Δ))
      ((zero , ⇑ᵗ (applyTys χs Aν)) ∷
        ⟰ᵗ (applyStores χs Σ))
      zero (⇑ᵗ (applyTys χs Aν))
      (applyCoercionUnderTyBinders χs c)
      (applyTysUnderTyBinders χs C) (⇑ᵗ (applyTys χs B))
apply-reveal-under-ty-binders {χs = []} {μ = μ} c↑ = μ , c↑
apply-reveal-under-ty-binders {χs = χ ∷ χs} c↑
    with apply-reveal-under-ty-binder {χ = χ} c↑
apply-reveal-under-ty-binders {χs = χ ∷ χs} c↑
    | μ′ , c′↑ =
  apply-reveal-under-ty-binders {χs = χs} c′↑

apply-widen-inst-under-ty-binders :
  ∀ {χs μ Δ Σ c B C} →
  CastMode μ →
  SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ) →
  instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
    ⊢ c ∶ C ⊑ ⇑ᵗ B →
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ (instᵈ μ′)
      ((zero , ★) ∷ ⟰ᵗ (applyStores χs Σ)) ×
    (instᵈ μ′ ∣ suc (applyTyCtxs χs Δ)
      ∣ (zero , ★) ∷ ⟰ᵗ (applyStores χs Σ)
      ⊢ applyCoercionUnderTyBinders χs c
        ∶ applyTysUnderTyBinders χs C ⊑
          ⇑ᵗ (applyTys χs B))
apply-widen-inst-under-ty-binders {χs = []} {μ = μ}
    mode seal★ c⊑ =
  μ , mode , seal★ , c⊑
apply-widen-inst-under-ty-binders {χs = keep ∷ χs}
    mode seal★ c⊑
    with applyWidenInstUnderTyBinder-typing
      {χ = keep} mode seal★ c⊑
apply-widen-inst-under-ty-binders {χs = keep ∷ χs}
    mode seal★ c⊑
    | μ′ , mode′ , seal★′ , c′⊑ =
  apply-widen-inst-under-ty-binders
    {χs = χs} mode′ seal★′ c′⊑
apply-widen-inst-under-ty-binders {χs = bind A ∷ χs}
    mode seal★ c⊑
    with applyWidenInstUnderTyBinder-typing
      {χ = bind A} mode seal★ c⊑
apply-widen-inst-under-ty-binders {χs = bind A ∷ χs}
    mode seal★ c⊑
    | μ′ , mode′ , seal★′ , c′⊑ =
  apply-widen-inst-under-ty-binders
    {χs = χs} mode′ seal★′ c′⊑

apply-reveal-conversion :
  ∀ {χ μ Δ Σ α X c A B} →
  RevealConversion μ Δ Σ α X c A B →
  ∃[ μ′ ] ∃[ α′ ] ∃[ X′ ]
    RevealConversion μ′ (applyTyCtx χ Δ) (applyStore χ Σ)
      α′ X′ (applyCoercion χ c) (applyTy χ A) (applyTy χ B)
apply-reveal-conversion {χ = keep} {μ = μ} {α = α} {X = X} c↑ =
  μ , α , X , c↑
apply-reveal-conversion
    {χ = bind Aχ} {μ = μ} {α = α} {X = X} c↑ =
  weakenCastᵈ μ , suc α , ⇑ᵗ X ,
  weaken-reveal-conversion StoreIncl-drop
    (rename-reveal-conversion TyRenameWf-suc
      modeRename-suc-weakenCast c↑)

apply-conceal-conversion :
  ∀ {χ μ Δ Σ α X c A B} →
  ConcealConversion μ Δ Σ α X c A B →
  ∃[ μ′ ] ∃[ α′ ] ∃[ X′ ]
    ConcealConversion μ′ (applyTyCtx χ Δ) (applyStore χ Σ)
      α′ X′ (applyCoercion χ c) (applyTy χ A) (applyTy χ B)
apply-conceal-conversion {χ = keep} {μ = μ} {α = α} {X = X} c↓ =
  μ , α , X , c↓
apply-conceal-conversion
    {χ = bind Aχ} {μ = μ} {α = α} {X = X} c↓ =
  weakenCastᵈ μ , suc α , ⇑ᵗ X ,
  weaken-conceal-conversion StoreIncl-drop
    (rename-conceal-conversion TyRenameWf-suc
      modeRename-suc-weakenCast c↓)

apply-reveal-conversions :
  ∀ {χs μ Δ Σ α X c A B} →
  RevealConversion μ Δ Σ α X c A B →
  ∃[ μ′ ] ∃[ α′ ] ∃[ X′ ]
    RevealConversion μ′ (applyTyCtxs χs Δ) (applyStores χs Σ)
      α′ X′ (applyCoercions χs c)
      (applyTys χs A) (applyTys χs B)
apply-reveal-conversions {χs = []} {μ = μ} {α = α} {X = X} c↑ =
  μ , α , X , c↑
apply-reveal-conversions {χs = χ ∷ χs} c↑
    with apply-reveal-conversion {χ = χ} c↑
apply-reveal-conversions {χs = χ ∷ χs} c↑
    | μ′ , α′ , X′ , c′↑ =
  apply-reveal-conversions {χs = χs} c′↑

apply-conceal-conversions :
  ∀ {χs μ Δ Σ α X c A B} →
  ConcealConversion μ Δ Σ α X c A B →
  ∃[ μ′ ] ∃[ α′ ] ∃[ X′ ]
    ConcealConversion μ′ (applyTyCtxs χs Δ) (applyStores χs Σ)
      α′ X′ (applyCoercions χs c)
      (applyTys χs A) (applyTys χs B)
apply-conceal-conversions {χs = []} {μ = μ} {α = α} {X = X} c↓ =
  μ , α , X , c↓
apply-conceal-conversions {χs = χ ∷ χs} c↓
    with apply-conceal-conversion {χ = χ} c↓
apply-conceal-conversions {χs = χ ∷ χs} c↓
    | μ′ , α′ , X′ , c′↓ =
  apply-conceal-conversions {χs = χs} c′↓

------------------------------------------------------------------------
-- General weak one-step simulation result
------------------------------------------------------------------------


rename-assm²-idᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ (λ X → X) (λ X → X) a ∈ Φ
rename-assm²-idᵢ {a = X ˣ⊑★} a∈ = a∈
rename-assm²-idᵢ {a = X ˣ⊑ˣ Y} a∈ = a∈

⊑-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
⊑-rename-idᵢ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} p =
  subst
    (λ T → Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ)
    (renameᵗ-id B)
    (subst
      (λ S → Φ ∣ Δᴸ
        ⊢ S ⊑ renameᵗ (λ X → X) B ⊣ Δᴿ)
      (renameᵗ-id A)
      (⊑-renameᵗ²ᵢ rename-assm²-idᵢ
        (λ X<Δ → X<Δ) (λ X<Δ → X<Δ) p))

⊑-rename-id-shapeᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-rename-idᵢ p ⌋ ≡ ⌊ p ⌋
⊑-rename-id-shapeᵢ {A = A} {B = B} p =
  trans
    (shape-subst-target
      (renameᵗ-id B)
      (subst
        (λ S → _ ∣ _ ⊢ S ⊑ _ ⊣ _)
        (renameᵗ-id A)
        renamed))
    (trans
      (shape-subst-source
        (renameᵗ-id A) renamed)
      (shape-rename
        rename-assm²-idᵢ
        (λ X<Δ → X<Δ)
        (λ X<Δ → X<Δ)
        p))
  where
  renamed =
    ⊑-renameᵗ²ᵢ rename-assm²-idᵢ
      (λ X<Δ → X<Δ) (λ X<Δ → X<Δ) p

replace-left-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  p [ α ↦ X ]ᴸ q →
  ⊑-rename-idᵢ p [ α ↦ X ]ᴸ ⊑-rename-idᵢ q
replace-left-rename-idᵢ {p = p} {q = q} replace =
  replace-left-target-shape (⊑-rename-id-shapeᵢ q)
    (replace-left-source-shape
      (⊑-rename-id-shapeᵢ p) replace)

replace-right-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  p [ β ↦ X′ ]ᴿ q →
  ⊑-rename-idᵢ p [ β ↦ X′ ]ᴿ ⊑-rename-idᵢ q
replace-right-rename-idᵢ {p = p} {q = q} replace =
  replace-right-target-shape (⊑-rename-id-shapeᵢ q)
    (replace-right-source-shape
      (⊑-rename-id-shapeᵢ p) replace)

replace-paired-rename-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  ⊑-rename-idᵢ p
    [ α ↦ X ⊑⟨ ⊑-rename-idᵢ pX ⟩ X′ ↤ β ]ᴾ
  ⊑-rename-idᵢ q
replace-paired-rename-idᵢ {pX = pX} {p = p} {q = q} replace =
  replace-paired-target-shape (⊑-rename-id-shapeᵢ q)
    (replace-paired-source-shape (⊑-rename-id-shapeᵢ p)
      (replace-paired-evidence-shape
        (⊑-rename-id-shapeᵢ pX) replace))

replace-left-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
  p [ α ↦ X ]ᴸ q →
  ⊑-target-lift-rightᵢ p
    [ α ↦ X ]ᴸ
  ⊑-target-lift-rightᵢ q
replace-left-target-lift-rightᵢ
    {A = A} {B = B} {X = X} {p = p} {q = q} replace =
  replace-left-target-shape
    (trans (shape-target-lift-rightᵢ q)
      (sym transported-q-shape))
    (replace-left-source-shape
      (trans (shape-target-lift-rightᵢ p)
        (sym transported-p-shape))
      transported)
  where
  renamed-p = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc p
  renamed-q = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc q
  transported =
    replace-left-transport-endpoints
      (renameᵗ-id A) refl (renameᵗ-id B) (renameᵗ-id X)
      (replace-left-rename²ᵢ rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc replace)
  transported-p-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-p)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc p)
  transported-q-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id B) refl renamed-q)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc q)

replace-right-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  p [ β ↦ X′ ]ᴿ q →
  ⊑-target-lift-rightᵢ p
    [ suc β ↦ ⇑ᵗ X′ ]ᴿ
  ⊑-target-lift-rightᵢ q
replace-right-target-lift-rightᵢ
    {A = A} {p = p} {q = q} replace =
  replace-right-target-shape
    (trans (shape-target-lift-rightᵢ q)
      (sym transported-q-shape))
    (replace-right-source-shape
      (trans (shape-target-lift-rightᵢ p)
        (sym transported-p-shape))
      transported)
  where
  renamed-p = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc p
  renamed-q = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc q
  transported =
    replace-right-transport-endpoints
      (renameᵗ-id A) refl refl refl
      (replace-right-rename²ᵢ rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc replace)
  transported-p-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-p)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc p)
  transported-q-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-q)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc q)

replace-paired-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  ⊑-target-lift-rightᵢ p
    [ α ↦ X
    ⊑⟨ ⊑-target-lift-rightᵢ pX ⟩
    ⇑ᵗ X′ ↤ suc β ]ᴾ
  ⊑-target-lift-rightᵢ q
replace-paired-target-lift-rightᵢ
    {A = A} {B = B} {X = X}
    {pX = pX} {p = p} {q = q} replace =
  replace-paired-target-shape
    (trans (shape-target-lift-rightᵢ q)
      (sym transported-q-shape))
    (replace-paired-source-shape
      (trans (shape-target-lift-rightᵢ p)
        (sym transported-p-shape))
      (replace-paired-evidence-shape
        (trans (shape-target-lift-rightᵢ pX)
          (sym transported-pX-shape))
        transported))
  where
  renamed-pX = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc pX
  renamed-p = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc p
  renamed-q = ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
    (λ X<Δ → X<Δ) TyRenameWf-suc q
  transported =
    replace-paired-transport-endpoints
      (renameᵗ-id A) refl (renameᵗ-id B) refl
      (renameᵗ-id X) refl
      (replace-paired-rename²ᵢ rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc replace)
  transported-pX-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id X) refl renamed-pX)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc pX)
  transported-p-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id A) refl renamed-p)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc p)
  transported-q-shape =
    trans
      (shape-transport-imprecision-endpoints
        (renameᵗ-id B) refl renamed-q)
      (shape-rename rename-assm²-target-rightᵢ
        (λ X<Δ → X<Δ) TyRenameWf-suc q)

renameᵗ-ext-id :
  ∀ A →
  renameᵗ (extᵗ (λ X → X)) A ≡ A
renameᵗ-ext-id A =
  trans
    (rename-cong
      (λ { zero → refl
         ; (suc X) → refl })
      A)
    (renameᵗ-id A)

ext-id-pointwise : ∀ X → extᵗ (λ Y → Y) X ≡ X
ext-id-pointwise zero = refl
ext-id-pointwise (suc X) = refl

renameᵗᵐ-ext-id : ∀ M → renameᵗᵐ (extᵗ (λ X → X)) M ≡ M
renameᵗᵐ-ext-id M =
  trans (renameᵗᵐ-cong ext-id-pointwise M) (renameᵗᵐ-id M)

⊑-rename-id-all-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ
⊑-rename-id-all-bodyᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} p =
  subst
    (λ T → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ T ⊣ suc Δᴿ)
    (renameᵗ-ext-id B)
    (subst
      (λ S → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ S ⊑
        renameᵗ (extᵗ (λ X → X)) B ⊣ suc Δᴿ)
      (renameᵗ-ext-id A)
      (⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᵢ rename-assm²-idᵢ)
        (TyRenameWf-ext (λ X<Δ → X<Δ))
        (TyRenameWf-ext (λ X<Δ → X<Δ)) p))

transport-arrow-⊑ᵢ :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ A₀′ A₁′ B₀ B₁ B₀′ B₁′}
    {p : Φ ∣ Δᴸ ⊢ A₀ ⊑ A₀′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B₀ ⊑ B₀′ ⊣ Δᴿ} →
  (eqA : A₀ ≡ A₁) → (eqA′ : A₀′ ≡ A₁′) →
  (eqB : B₀ ≡ B₁) → (eqB′ : B₀′ ≡ B₁′) →
  subst
    (λ T → Φ ∣ Δᴸ ⊢ A₁ ⇒ B₁ ⊑ T ⊣ Δᴿ)
    (cong₂ _⇒_ eqA′ eqB′)
    (subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ A₀′ ⇒ B₀′ ⊣ Δᴿ)
      (cong₂ _⇒_ eqA eqB) (p ↦ q))
    ≡
  subst (λ T → Φ ∣ Δᴸ ⊢ A₁ ⊑ T ⊣ Δᴿ) eqA′
      (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ A₀′ ⊣ Δᴿ) eqA p)
    ↦
  subst (λ T → Φ ∣ Δᴸ ⊢ B₁ ⊑ T ⊣ Δᴿ) eqB′
      (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B₀′ ⊣ Δᴿ) eqB q)
transport-arrow-⊑ᵢ refl refl refl refl = refl

⊑-rename-id-arrowᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  ⊑-rename-idᵢ (p ↦ q) ≡ ⊑-rename-idᵢ p ↦ ⊑-rename-idᵢ q
⊑-rename-id-arrowᵢ {A = A} {A′ = A′} {B = B} {B′ = B′} p q =
  transport-arrow-⊑ᵢ
    (renameᵗ-id A) (renameᵗ-id A′)
    (renameᵗ-id B) (renameᵗ-id B′)

transport-all-⊑ᵢ :
  ∀ {Φ Δᴸ Δᴿ A₀ A₁ B₀ B₁}
    {p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A₀ ⊑ B₀ ⊣ suc Δᴿ} →
  (eqA : A₀ ≡ A₁) → (eqB : B₀ ≡ B₁) →
  subst
    (λ T → Φ ∣ Δᴸ ⊢ `∀ A₁ ⊑ T ⊣ Δᴿ)
    (cong `∀ eqB)
    (subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ `∀ B₀ ⊣ Δᴿ)
      (cong `∀ eqA) (∀ⁱ p))
    ≡ ∀ⁱ
      (subst (λ T → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A₁ ⊑ T ⊣ suc Δᴿ)
        eqB
        (subst
          (λ S → ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ S ⊑ B₀ ⊣ suc Δᴿ)
          eqA p))
transport-all-⊑ᵢ refl refl = refl

transport-ν-⊑ᵢ :
  ∀ {Φ Δᴸ Δᴿ C₀ C₁ B}
    {{safe₀ : NonVar C₀}}
    {{safe₁ : NonVar C₁}}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C₀ ⊑ B ⊣ Δᴿ} →
  (eqC : C₀ ≡ C₁) →
  (occ : occurs zero C₀ ≡ true) →
  subst
    (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
    (cong `∀ eqC) (ν safe₀ occ p)
  ≡ ν safe₁
      (trans (sym (cong (occurs zero) eqC)) occ)
      (subst
        (λ S → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
        eqC p)
transport-ν-⊑ᵢ {{safe₀}} {{safe₁}} refl occ
    rewrite nonVar-unique safe₀ safe₁ =
  refl

equality-proof-unique :
  ∀ {A : Set} {x y : A}
    (p q : x ≡ y) →
  p ≡ q
equality-proof-unique refl refl = refl

⊑-rename-id-allᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
  ⊑-rename-idᵢ (∀ⁱ p) ≡ ∀ⁱ (⊑-rename-id-all-bodyᵢ p)
⊑-rename-id-allᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} p =
  trans outer-equalities
    (transport-all-⊑ᵢ (renameᵗ-ext-id A) (renameᵗ-ext-id B))
  where
  outer-equalities =
    cong₂
      (λ eqA eqB →
        subst (λ T → Φ ∣ Δᴸ ⊢ `∀ A ⊑ T ⊣ Δᴿ) eqB
          (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑
            renameᵗ (λ X → X) (`∀ B) ⊣ Δᴿ) eqA
            (⊑-renameᵗ²ᵢ rename-assm²-idᵢ
              (λ X<Δ → X<Δ) (λ X<Δ → X<Δ) (∀ⁱ p))))
      (equality-proof-unique
        (renameᵗ-id (`∀ A)) (cong `∀ (renameᵗ-ext-id A)))
      (equality-proof-unique
        (renameᵗ-id (`∀ B)) (cong `∀ (renameᵗ-ext-id B)))

⊑-rename-id-source-nuᵢ :
  ∀ {Φ Δᴸ Δᴿ C B}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ) →
  SourceNuIndex (⊑-rename-idᵢ (ν safe occ p))
⊑-rename-id-source-nuᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {C = C} {B = B}
    safe occ p =
  sourceNuIndex-reindex (sym outer-equalities) transported
  where
  renamed-body =
    ⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᴸᵢ rename-assm²-idᵢ)
      (TyRenameWf-ext (λ X<Δ → X<Δ))
      (λ X<Δ → X<Δ)
      p

  raw-shape =
    source-nu-index
      (renameNonVar (extᵗ (λ X → X)) safe)
      (trans (occurs-zero-rename-ext (λ X → X) C) occ)
      renamed-body refl

  transported =
    sourceNuIndex-transport
      (renameᵗ-ext-id C) (renameᵗ-id B) raw-shape

  outer-equalities =
    cong₂
      (λ eqC eqB →
        subst (λ T → Φ ∣ Δᴸ ⊢ `∀ C ⊑ T ⊣ Δᴿ) eqB
          (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑
            renameᵗ (λ X → X) B ⊣ Δᴿ) eqC
            (⊑-renameᵗ²ᵢ rename-assm²-idᵢ
              (λ X<Δ → X<Δ) (λ X<Δ → X<Δ)
              (ν safe occ p))))
      (equality-proof-unique
        (renameᵗ-id (`∀ C)) (cong `∀ (renameᵗ-ext-id C)))
      (equality-proof-unique
        (renameᵗ-id B) (renameᵗ-id B))

shape-rename-id-all-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  ⌊ ⊑-rename-id-all-bodyᵢ q ⌋ ≡ ⌊ q ⌋
shape-rename-id-all-bodyᵢ {C = C} {C′ = C′} q =
  trans
    (shape-subst-target (renameᵗ-ext-id C′)
      (subst
        (λ S → _ ∣ _ ⊢ S ⊑
          renameᵗ (extᵗ (λ X → X)) C′ ⊣ _)
        (renameᵗ-ext-id C) renamed))
    (trans
      (shape-subst-source (renameᵗ-ext-id C) renamed)
      (shape-rename
        (rename-assm²-⇑ᵢ rename-assm²-idᵢ)
        (TyRenameWf-ext (λ X<Δ → X<Δ))
        (TyRenameWf-ext (λ X<Δ → X<Δ)) q))
  where
  renamed =
    ⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᵢ rename-assm²-idᵢ)
      (TyRenameWf-ext (λ X<Δ → X<Δ))
      (TyRenameWf-ext (λ X<Δ → X<Δ)) q

shape-rename-id-source-nu-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) →
  ⌊ sourceNuBody (⊑-rename-id-source-nuᵢ safe occ q) ⌋ ≡
    ⌊ q ⌋
shape-rename-id-source-nu-bodyᵢ safe occ q =
  νˢ-injective
    (trans
      (sym (cong ⌊_⌋ (sourceNuIndexEquality index)))
      (⊑-rename-id-shapeᵢ (ν safe occ q)))
  where
  index = ⊑-rename-id-source-nuᵢ safe occ q

replace-paired-rename-id-all-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {A⇑⊑A′⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ pB →
  ⊑-rename-id-all-bodyᵢ q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ ⊑-rename-id-all-bodyᵢ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ (⊑-rename-idᵢ pB)
replace-paired-rename-id-all-bodyᵢ
    {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} {q = q} replace =
  replace-paired-target-shape target-shape
    (replace-paired-source-shape
      (shape-rename-id-all-bodyᵢ q)
      (replace-paired-evidence-shape
        (shape-rename-id-all-bodyᵢ A⇑⊑A′⇑)
        replace))
  where
  target-shape =
    trans
      (shape-lift∀ᵢ (⊑-rename-idᵢ pB))
      (trans
        (⊑-rename-id-shapeᵢ pB)
        (sym (shape-lift∀ᵢ pB)))

replace-left-rename-id-source-nu-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true) →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
  sourceNuBody (⊑-rename-id-source-nuᵢ safe occ q)
    [ zero ↦ ⇑ᵗ A ]ᴸ
  ⊑-source-liftνᵢ (⊑-rename-idᵢ pB)
replace-left-rename-id-source-nu-bodyᵢ
    {pB = pB} {q = q} safe occ replace =
  replace-left-target-shape target-shape
    (replace-left-source-shape
      (shape-rename-id-source-nu-bodyᵢ safe occ q)
      replace)
  where
  target-shape =
    trans
      (shape-source-liftνᵢ (⊑-rename-idᵢ pB))
      (trans
        (⊑-rename-id-shapeᵢ pB)
        (sym (shape-source-liftνᵢ pB)))

replace-right-rename-id-right-bodyᵢ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
  pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
  ⊑-rename-idᵢ pC [ zero ↦ ⇑ᵗ A ]ᴿ
  ⊑-target-lift-rightᵢ (⊑-rename-idᵢ pB)
replace-right-rename-id-right-bodyᵢ
    {pB = pB} {pC = pC} replace =
  replace-right-target-shape target-shape
    (replace-right-source-shape
      (⊑-rename-id-shapeᵢ pC)
      replace)
  where
  target-shape =
    trans
      (shape-target-lift-rightᵢ (⊑-rename-idᵢ pB))
      (trans
        (⊑-rename-id-shapeᵢ pB)
        (sym (shape-target-lift-rightᵢ pB)))



value-source-multistep-refl :
  ∀ {χs V N} →
  Value V →
  V —↠[ χs ] N →
  (χs ≡ []) × (N ≡ V)
value-source-multistep-refl vV ↠-refl = refl , refl
value-source-multistep-refl vV (↠-step V→L L↠N) =
  ⊥-elim (value-no-step vV V→L)

source-value-indexed-outcome-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ V N′ A B χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  WeakOneStepIndexedOutcome
    {M = V} {N′ = N′} {χ = χ} {ρ = ρ} p →
  ∃[ result ]
    sourceChanges (weakIndexedResult result) ≡ [] ×
    sourceResult (weakIndexedResult result) ≡ V
source-value-indexed-outcome-relatedᵀ vV
    (indexed-outcome-related result)
    with value-source-multistep-refl vV
      (sourceCatchup (weakIndexedResult result))
source-value-indexed-outcome-relatedᵀ vV
    (indexed-outcome-related result)
    | refl , result-eq =
  result , refl , result-eq
source-value-indexed-outcome-relatedᵀ vV
    (indexed-outcome-source-blame source↠)
    with value-source-multistep-refl vV source↠
source-value-indexed-outcome-relatedᵀ vV
    (indexed-outcome-source-blame source↠)
    | changes-eq , result-eq =
  ⊥-elim (value-blame-impossible
    (subst Value (sym result-eq) vV))
  where
  value-blame-impossible : Value blame → ⊥
  value-blame-impossible ()


forget-weak-indexed-outcome :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  WeakOneStepOutcome ρ M N′ A B χ
forget-weak-indexed-outcome
    (indexed-outcome-related result) =
  outcome-related
    (weakIndexedResult result)
    (weakIndexedTransport result)
    (weakIndexedTypeCoherence result)
forget-weak-indexed-outcome
    (indexed-outcome-source-blame source↠) =
  outcome-source-blame source↠

forget-weak-all-outcome :
  ∀ {Φ Δᴸ Δᴿ N N₁′ C C′ χ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepAllOutcome
    {N = N} {N₁′ = N₁′} {χ = χ} {ρ = ρ} q →
  WeakOneStepOutcome ρ N N₁′ (`∀ C) (`∀ C′) χ
forget-weak-all-outcome
    (all-outcome-related result transport coherence) =
  outcome-related (weakResult result) transport coherence
forget-weak-all-outcome
    (all-outcome-source-blame source↠) =
  outcome-source-blame source↠

forget-weak-arrow-outcome :
  ∀ {Φ Δᴸ Δᴿ L L₁′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepArrowOutcome
    {L = L} {L₁′ = L₁′} {χ = χ} {ρ = ρ} pA pB →
  WeakOneStepOutcome ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ
forget-weak-arrow-outcome
    (arrow-outcome-related result transport coherence) =
  outcome-related (weakArrowResult result) transport coherence
forget-weak-arrow-outcome
    (arrow-outcome-source-blame source↠) =
  outcome-source-blame source↠

weak-indexed-arrow-resultᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (indexed : WeakOneStepIndexedResult
    {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} (pA ↦ pB)) →
  WeakOneStepArrowResult pA pB
weak-indexed-arrow-resultᵀ {A′ = A′} {B′ = B′} {χ = χ} indexed =
  weak-arrow-result base canonical
  where
  base = weakIndexedResult indexed
  coherence = weakIndexedTypeCoherence indexed

  target-eq =
    trans
      (cong (applyTys (targetTailChanges base))
        (applyTys-⇒ (χ ∷ []) A′ B′))
      (applyTys-⇒ (targetTailChanges base)
        (applyTy χ A′) (applyTy χ B′))

  canonical =
    nu-term-imprecision-transport-typesᵀ
      (applyTys-⇒ (sourceChanges base) _ _)
      target-eq
      (transportArrowCoherent coherence _ _)
      (canonicalIndexedResults indexed)

weak-indexed-arrow-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepIndexedOutcome
    {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} (pA ↦ pB) →
  WeakOneStepArrowOutcome pA pB
weak-indexed-arrow-outcomeᵀ
    (indexed-outcome-related indexed) =
  arrow-outcome-related
    (weak-indexed-arrow-resultᵀ indexed)
    (weakIndexedTransport indexed)
    (weakIndexedTypeCoherence indexed)
weak-indexed-arrow-outcomeᵀ
    (indexed-outcome-source-blame source↠) =
  arrow-outcome-source-blame source↠

weak-indexed-all-resultᵀ :
  ∀ {Φ Δᴸ Δᴿ N N₁′ C C′ χ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (indexed : WeakOneStepIndexedResult
    {M = N} {N′ = N₁′} {χ = χ} {ρ = ρ} (∀ⁱ q)) →
  WeakOneStepAllResult q
weak-indexed-all-resultᵀ {C′ = C′} {χ = χ} indexed =
  weak-all-result base canonical
  where
  base = weakIndexedResult indexed
  coherence = weakIndexedTypeCoherence indexed

  target-eq =
    trans
      (cong (applyTys (targetTailChanges base))
        (applyTy-∀ χ C′))
      (applyTys-∀ (targetTailChanges base)
        (applyTyUnderTyBinder χ C′))

  canonical =
    nu-term-imprecision-transport-typesᵀ
      (applyTys-∀ (sourceChanges base) _)
      target-eq
      (transportAllCoherent coherence _)
      (canonicalIndexedResults indexed)

weak-indexed-all-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ N N₁′ C C′ χ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepIndexedOutcome
    {M = N} {N′ = N₁′} {χ = χ} {ρ = ρ} (∀ⁱ q) →
  WeakOneStepAllOutcome q
weak-indexed-all-outcomeᵀ
    (indexed-outcome-related indexed) =
  all-outcome-related
    (weak-indexed-all-resultᵀ indexed)
    (weakIndexedTransport indexed)
    (weakIndexedTypeCoherence indexed)
weak-indexed-all-outcomeᵀ
    (indexed-outcome-source-blame source↠) =
  all-outcome-source-blame source↠


weak-result-right-wf-silent :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M V′ A B keep) →
  LeftSilentInvariant result →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  StoreWf (resultRightCtx result) (rightStoreⁱ (resultStore result))
weak-result-right-wf-silent result
    (left-silent-invariant refl target-eq) wfΣ′ =
  subst
    (λ Δ → StoreWf Δ (rightStoreⁱ (resultStore result)))
    (sym (targetCtxResult result))
    (subst
      (StoreWf _)
      (sym (targetStoreResult result)) wfΣ′)



forget-left-catchup :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  LeftCatchupResult
    {M = M} {V′ = V′} {A = A} {B = B} {ρ = ρ} →
  LeftSilentResult
    {M = M} {V′ = V′} {A = A} {B = B} {ρ = ρ}
forget-left-catchup
    (left-catchup result (left-catchup-invariant silent final)) =
  left-silent result silent






generalize-left-indexed-all-catchup :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} (∀ⁱ q)
generalize-left-indexed-all-catchup
    (left-indexed-all-catchup indexed invariant) =
  left-indexed-catchup indexed invariant

specialize-left-indexed-all-catchup :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} (∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q
specialize-left-indexed-all-catchup
    (left-indexed-catchup indexed invariant) =
  left-indexed-all-catchup indexed invariant

forget-left-indexed-all-catchup :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q →
  LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q
forget-left-indexed-all-catchup catchup =
  left-all-catchup
    (weak-indexed-all-resultᵀ (catchupIndexedAllResult catchup))
    (catchupIndexedAllInvariant catchup)

forget-left-all-catchup :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q →
  LeftCatchupResult {M = N} {V′ = V′} {ρ = ρ}
forget-left-all-catchup (left-all-catchup result invariant) =
  left-catchup (weakResult result) invariant

weak-result-source-all :
  ∀ {Φ Δᴸ Δᴿ N N₁′ C B′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ N N₁′ (`∀ C) B′ χ) →
  ∃[ q′ ]
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑ targetResult inner
      ⦂ `∀ (applyTysUnderTyBinders (sourceChanges inner) C)
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ q′)
weak-result-source-all {C = C} inner =
  subst
    (λ T → ∃[ q′ ]
      (resultCtx inner
        ∣ resultLeftCtx inner
        ∣ resultRightCtx inner
        ∣ resultStore inner ∣ []
        ⊢ᴺ sourceResult inner ⊑ targetResult inner
        ⦂ `∀ (applyTysUnderTyBinders (sourceChanges inner) C)
          ⊑ T ∶ q′))
    (targetTypeResult inner)
    (subst
      (λ S → ∃[ q′ ]
        (resultCtx inner
          ∣ resultLeftCtx inner
          ∣ resultRightCtx inner
          ∣ resultStore inner ∣ []
          ⊢ᴺ sourceResult inner ⊑ targetResult inner
          ⦂ S ⊑ resultTargetType inner ∶ q′))
      (trans (sourceTypeResult inner)
        (applyTys-∀ (sourceChanges inner) C))
      (resultType inner , relatedResults inner))

weak-result-target-all :
  ∀ {Φ Δᴸ Δᴿ N N₁′ B C′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ N N₁′ B (`∀ C′) χ) →
  ∃[ q′ ]
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) B
        ⊑ `∀
            (applyTysUnderTyBinders (targetTailChanges inner)
              (applyTyUnderTyBinder χ C′))
      ∶ q′)
weak-result-target-all {C′ = C′} {χ = χ} inner =
  subst
    (λ T → ∃[ q′ ]
      (resultCtx inner
        ∣ resultLeftCtx inner
        ∣ resultRightCtx inner
        ∣ resultStore inner ∣ []
        ⊢ᴺ sourceResult inner ⊑ targetResult inner
        ⦂ applyTys (sourceChanges inner) _ ⊑ T ∶ q′))
    (trans (targetTypeResult inner)
      (trans
        (cong (applyTys (targetTailChanges inner))
          (applyTy-∀ χ C′))
        (applyTys-∀ (targetTailChanges inner)
          (applyTyUnderTyBinder χ C′))))
    (subst
      (λ S → ∃[ q′ ]
        (resultCtx inner
          ∣ resultLeftCtx inner
          ∣ resultRightCtx inner
          ∣ resultStore inner ∣ []
          ⊢ᴺ sourceResult inner ⊑ targetResult inner
          ⦂ S ⊑ resultTargetType inner ∶ q′))
      (sourceTypeResult inner)
      (resultType inner , relatedResults inner))

weak-result-source-reveal :
  ∀ {Φ Δᴸ Δᴿ N N′ X Y χ A B C c μ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ N N′ X Y χ) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) c C (⇑ᵗ B) →
  ∃[ μ′ ]
    RevealConversion μ′ (suc (resultLeftCtx inner))
      ((zero , ⇑ᵗ (applyTys (sourceChanges inner) A)) ∷
        ⟰ᵗ (leftStoreⁱ (resultStore inner)))
      zero (⇑ᵗ (applyTys (sourceChanges inner) A))
      (applyCoercionUnderTyBinders (sourceChanges inner) c)
      (applyTysUnderTyBinders (sourceChanges inner) C)
      (⇑ᵗ (applyTys (sourceChanges inner) B))
weak-result-source-reveal {A = A} {B = B} {C = C} {c = c} inner c↑
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} c↑
weak-result-source-reveal {A = A} {B = B} {C = C} {c = c} inner c↑
    | μ′ , c′↑ =
  μ′ ,
  subst
    (λ Δ → RevealConversion μ′ (suc Δ)
      ((zero , ⇑ᵗ (applyTys (sourceChanges inner) A)) ∷
        ⟰ᵗ (leftStoreⁱ (resultStore inner)))
      zero (⇑ᵗ (applyTys (sourceChanges inner) A))
      (applyCoercionUnderTyBinders (sourceChanges inner) c)
      (applyTysUnderTyBinders (sourceChanges inner) C)
      (⇑ᵗ (applyTys (sourceChanges inner) B)))
    (sym (sourceCtxResult inner))
    (subst
      (λ Σ → RevealConversion μ′
        (suc (applyTyCtxs (sourceChanges inner) _))
        ((zero , ⇑ᵗ (applyTys (sourceChanges inner) A)) ∷ ⟰ᵗ Σ)
        zero (⇑ᵗ (applyTys (sourceChanges inner) A))
        (applyCoercionUnderTyBinders (sourceChanges inner) c)
        (applyTysUnderTyBinders (sourceChanges inner) C)
        (⇑ᵗ (applyTys (sourceChanges inner) B)))
      (sym (sourceStoreResult inner)) c′↑)

weak-result-target-reveal :
  ∀ {Φ Δᴸ Δᴿ N N′ X Y A B C c μ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (χ : StoreChange) →
  (inner : WeakOneStepResult ρ N N′ X Y χ) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) c C (⇑ᵗ B) →
  ∃[ μ′ ]
    RevealConversion μ′ (suc (resultRightCtx inner))
      ((zero ,
        ⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ A))) ∷
        ⟰ᵗ (rightStoreⁱ (resultStore inner)))
      zero
      (⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ A)))
      (applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder χ c))
      (applyTysUnderTyBinders (targetTailChanges inner)
        (applyTyUnderTyBinder χ C))
      (⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ B)))
weak-result-target-reveal
    {A = A} {B = B} {C = C} {c = c} χ inner c↑
    with apply-reveal-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} c↑
weak-result-target-reveal
    {A = A} {B = B} {C = C} {c = c} χ inner c↑
    | μ′ , c′↑ =
  μ′ ,
  subst
    (λ Δ → RevealConversion μ′ (suc Δ)
      ((zero ,
        ⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ A))) ∷
        ⟰ᵗ (rightStoreⁱ (resultStore inner)))
      zero
      (⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ A)))
      (applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder χ c))
      (applyTysUnderTyBinders (targetTailChanges inner)
        (applyTyUnderTyBinder χ C))
      (⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ B))))
    (sym (targetCtxResult inner))
    (subst
      (λ Σ → RevealConversion μ′
        (suc (applyTyCtxs (targetTailChanges inner)
          (applyTyCtx χ _)))
        ((zero ,
          ⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ A))) ∷
          ⟰ᵗ Σ)
        zero
        (⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ A)))
        (applyCoercionUnderTyBinders (targetTailChanges inner)
          (applyCoercionUnderTyBinder χ c))
        (applyTysUnderTyBinders (targetTailChanges inner)
          (applyTyUnderTyBinder χ C))
        (⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ B))))
      (sym (targetStoreResult inner)) c′↑)

weak-result-source-widen-inst :
  ∀ {Φ Δᴸ Δᴿ N N′ X Y χ B C c μ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ N N′ X Y χ) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ c ∶ C ⊑ ⇑ᵗ B →
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ (instᵈ μ′)
      ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore inner))) ×
    (instᵈ μ′ ∣ suc (resultLeftCtx inner)
      ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore inner))
      ⊢ applyCoercionUnderTyBinders (sourceChanges inner) c
        ∶ applyTysUnderTyBinders (sourceChanges inner) C
          ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
weak-result-source-widen-inst
    {B = B} {C = C} {c = c} inner mode seal★ c⊑
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ c⊑
weak-result-source-widen-inst
    {B = B} {C = C} {c = c} inner mode seal★ c⊑
    | μ′ , mode′ , seal★′ , c′⊑ =
  μ′ , mode′ ,
  subst
    (λ Σ → SealModeStore★ (instᵈ μ′) ((zero , ★) ∷ ⟰ᵗ Σ))
    (sym (sourceStoreResult inner)) seal★′ ,
  subst
    (λ Δ → instᵈ μ′ ∣ suc Δ
      ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore inner))
      ⊢ applyCoercionUnderTyBinders (sourceChanges inner) c
        ∶ applyTysUnderTyBinders (sourceChanges inner) C
          ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
    (sym (sourceCtxResult inner))
    (subst
      (λ Σ → instᵈ μ′
        ∣ suc (applyTyCtxs (sourceChanges inner) _)
        ∣ (zero , ★) ∷ ⟰ᵗ Σ
        ⊢ applyCoercionUnderTyBinders (sourceChanges inner) c
          ∶ applyTysUnderTyBinders (sourceChanges inner) C
            ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
      (sym (sourceStoreResult inner)) c′⊑)

weak-result-target-widen-inst :
  ∀ {Φ Δᴸ Δᴿ N N′ X Y B C c μ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (χ : StoreChange) →
  (inner : WeakOneStepResult ρ N N′ X Y χ) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ c ∶ C ⊑ ⇑ᵗ B →
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ (instᵈ μ′)
      ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ (resultStore inner))) ×
    (instᵈ μ′ ∣ suc (resultRightCtx inner)
      ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ (resultStore inner))
      ⊢ applyCoercionUnderTyBinders (targetTailChanges inner)
          (applyCoercionUnderTyBinder χ c)
        ∶ applyTysUnderTyBinders (targetTailChanges inner)
            (applyTyUnderTyBinder χ C)
          ⊑ ⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ B)))
weak-result-target-widen-inst
    {B = B} {C = C} {c = c} χ inner mode seal★ c⊑
    with apply-widen-inst-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} mode seal★ c⊑
weak-result-target-widen-inst
    {B = B} {C = C} {c = c} χ inner mode seal★ c⊑
    | μ′ , mode′ , seal★′ , c′⊑ =
  μ′ , mode′ ,
  subst
    (λ Σ → SealModeStore★ (instᵈ μ′) ((zero , ★) ∷ ⟰ᵗ Σ))
    (sym (targetStoreResult inner)) seal★′ ,
  subst
    (λ Δ → instᵈ μ′ ∣ suc Δ
      ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ (resultStore inner))
      ⊢ applyCoercionUnderTyBinders (targetTailChanges inner)
          (applyCoercionUnderTyBinder χ c)
        ∶ applyTysUnderTyBinders (targetTailChanges inner)
            (applyTyUnderTyBinder χ C)
          ⊑ ⇑ᵗ (applyTys (targetTailChanges inner) (applyTy χ B)))
    (sym (targetCtxResult inner))
    (subst
      (λ Σ → instᵈ μ′
        ∣ suc (applyTyCtxs (targetTailChanges inner)
          (applyTyCtx χ _))
        ∣ (zero , ★) ∷ ⟰ᵗ Σ
        ⊢ applyCoercionUnderTyBinders (targetTailChanges inner)
            (applyCoercionUnderTyBinder χ c)
          ∶ applyTysUnderTyBinders (targetTailChanges inner)
              (applyTyUnderTyBinder χ C)
            ⊑ ⇑ᵗ
                (applyTys (targetTailChanges inner) (applyTy χ B)))
      (sym (targetStoreResult inner)) c′⊑)

lift-store-left-zero⊥ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} {A} →
  LiftStoreⁱ Ψ ρ ρ′ →
  (zero , A) ∈ leftStoreⁱ ρ′ → ⊥
lift-store-left-zero⊥ lift-store-[] ()
lift-store-left-zero⊥ (lift-store-∷ shape liftρ) (here ())
lift-store-left-zero⊥ (lift-store-∷ shape liftρ) (there x∈) =
  lift-store-left-zero⊥ liftρ x∈
lift-store-left-zero⊥ (lift-store-left liftρ) (here ())
lift-store-left-zero⊥ (lift-store-left liftρ) (there x∈) =
  lift-store-left-zero⊥ liftρ x∈
lift-store-left-zero⊥ (lift-store-right liftρ) x∈ =
  lift-store-left-zero⊥ liftρ x∈
lift-store-left-zero⊥ (lift-store-link shape liftρ) x∈ =
  lift-store-left-zero⊥ liftρ x∈

lift-store-right-zero⊥ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} {B} →
  LiftStoreⁱ Ψ ρ ρ′ →
  (zero , B) ∈ rightStoreⁱ ρ′ → ⊥
lift-store-right-zero⊥ lift-store-[] ()
lift-store-right-zero⊥ (lift-store-∷ shape liftρ) (here ())
lift-store-right-zero⊥ (lift-store-∷ shape liftρ) (there x∈) =
  lift-store-right-zero⊥ liftρ x∈
lift-store-right-zero⊥ (lift-store-left liftρ) x∈ =
  lift-store-right-zero⊥ liftρ x∈
lift-store-right-zero⊥ (lift-store-right liftρ) (here ())
lift-store-right-zero⊥ (lift-store-right liftρ) (there x∈) =
  lift-store-right-zero⊥ liftρ x∈
lift-store-right-zero⊥ (lift-store-link shape liftρ) x∈ =
  lift-store-right-zero⊥ liftρ x∈

swap01-lift-left-obstruction :
  ∀ {Φ Ψ Ω Δᴸ Δᴿ Θᴸ Θᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ′ : StoreImp Ω (suc Θᴸ) (suc Θᴿ)} {A} →
  (suc zero , A) ∈ leftStoreⁱ ρ →
  LiftStoreⁱ Ω ρ₀ ρ′ →
  leftStoreⁱ ρ′ ≡ renameStoreᵗ swap01ᵗ (leftStoreⁱ ρ) →
  ⊥
swap01-lift-left-obstruction {A = A} x∈ liftρ eq =
  lift-store-left-zero⊥ liftρ
    (subst
      ((zero , renameᵗ swap01ᵗ A) ∈_)
      (sym eq) (∈-renameStoreᵗ swap01ᵗ x∈))

swap01-lift-right-obstruction :
  ∀ {Φ Ψ Ω Δᴸ Δᴿ Θᴸ Θᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ′ : StoreImp Ω (suc Θᴸ) (suc Θᴿ)} {B} →
  (suc zero , B) ∈ rightStoreⁱ ρ →
  LiftStoreⁱ Ω ρ₀ ρ′ →
  rightStoreⁱ ρ′ ≡ renameStoreᵗ swap01ᵗ (rightStoreⁱ ρ) →
  ⊥
swap01-lift-right-obstruction {B = B} x∈ liftρ eq =
  lift-store-right-zero⊥ liftρ
    (subst
      ((zero , renameᵗ swap01ᵗ B) ∈_)
      (sym eq) (∈-renameStoreᵗ swap01ᵗ x∈))

left-right-store-commuteⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᴸ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  ∃[ ρ× ]
    LiftRightStoreⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρᴸ ρ× ×
    LiftLeftStoreⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρᴿ ρ×
left-right-store-commuteⁱ lift-left-store-[] lift-right-store-[] =
  [] , lift-right-store-[] , lift-left-store-[]
left-right-store-commuteⁱ
    (lift-left-store-∷ {p′ = pᴸ} shapeᴸ liftᴸ)
    (lift-right-store-∷ shapeᴿ liftᴿ)
    with left-right-store-commuteⁱ liftᴸ liftᴿ
left-right-store-commuteⁱ
    (lift-left-store-∷ {p′ = pᴸ} shapeᴸ liftᴸ)
    (lift-right-store-∷ shapeᴿ liftᴿ)
    | ρ× , rightᴸ , leftᴿ =
  store-matched _ _ _ _ (⊑-target-lift-rightᵢ pᴸ) ∷ ρ× ,
  lift-right-store-∷ (shape-target-lift-rightᵢ pᴸ) rightᴸ ,
  lift-left-store-∷
    (trans (shape-target-lift-rightᵢ pᴸ)
      (trans shapeᴸ (sym shapeᴿ)))
    leftᴿ
left-right-store-commuteⁱ
    (lift-left-store-left liftᴸ)
    (lift-right-store-left liftᴿ)
    with left-right-store-commuteⁱ liftᴸ liftᴿ
left-right-store-commuteⁱ
    (lift-left-store-left {hA′ = hAᴸ} liftᴸ)
    (lift-right-store-left liftᴿ)
    | ρ× , rightᴸ , leftᴿ =
  store-left _ _ hAᴸ ∷ ρ× ,
  lift-right-store-left rightᴸ ,
  lift-left-store-left leftᴿ
left-right-store-commuteⁱ
    (lift-left-store-right liftᴸ)
    (lift-right-store-right liftᴿ)
    with left-right-store-commuteⁱ liftᴸ liftᴿ
left-right-store-commuteⁱ
    (lift-left-store-right liftᴸ)
    (lift-right-store-right {hB′ = hBᴿ} liftᴿ)
    | ρ× , rightᴸ , leftᴿ =
  store-right _ _ hBᴿ ∷ ρ× ,
  lift-right-store-right rightᴸ ,
  lift-left-store-right leftᴿ
left-right-store-commuteⁱ
    (lift-left-store-link {p′ = pᴸ} shapeᴸ liftᴸ)
    (lift-right-store-link shapeᴿ liftᴿ)
    with left-right-store-commuteⁱ liftᴸ liftᴿ
left-right-store-commuteⁱ
    (lift-left-store-link {p′ = pᴸ} shapeᴸ liftᴸ)
    (lift-right-store-link shapeᴿ liftᴿ)
    | ρ× , rightᴸ , leftᴿ =
  store-link _ _ _ _ (⊑-target-lift-rightᵢ pᴸ) ∷ ρ× ,
  lift-right-store-link (shape-target-lift-rightᵢ pᴸ) rightᴸ ,
  lift-left-store-link
    (trans (shape-target-lift-rightᵢ pᴸ)
      (trans shapeᴸ (sym shapeᴿ)))
    leftᴿ

left-right-ctx-commuteⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴸ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γᴸ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ∃[ γ× ]
    LiftRightCtxⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γᴸ γ× ×
    LiftLeftCtxⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γᴿ γ×
left-right-ctx-commuteⁱ lift-left-ctx-[] lift-right-ctx-[] =
  [] , lift-right-ctx-[] , lift-left-ctx-[]
left-right-ctx-commuteⁱ
    (lift-left-ctx-∷ {p′ = pᴸ} shapeᴸ liftᴸ)
    (lift-right-ctx-∷ shapeᴿ liftᴿ)
    with left-right-ctx-commuteⁱ liftᴸ liftᴿ
left-right-ctx-commuteⁱ
    (lift-left-ctx-∷ {p′ = pᴸ} shapeᴸ liftᴸ)
    (lift-right-ctx-∷ shapeᴿ liftᴿ)
    | γ× , rightᴸ , leftᴿ =
  ctx-imp _ _ (⊑-target-lift-rightᵢ pᴸ) ∷ γ× ,
  lift-right-ctx-∷ (shape-target-lift-rightᵢ pᴸ) rightᴸ ,
  lift-left-ctx-∷
    (trans (shape-target-lift-rightᵢ pᴸ)
      (trans shapeᴸ (sym shapeᴿ)))
    leftᴿ

⇑ᴸᵢ-⇑ᴿᵢ-commute :
  ∀ Φ → ⇑ᴸᵢ (⇑ᴿᵢ Φ) ≡ ⇑ᴿᵢ (⇑ᴸᵢ Φ)
⇑ᴸᵢ-⇑ᴿᵢ-commute [] = refl
⇑ᴸᵢ-⇑ᴿᵢ-commute ((X ˣ⊑★) ∷ Φ) =
  cong ((suc X ˣ⊑★) ∷_) (⇑ᴸᵢ-⇑ᴿᵢ-commute Φ)
⇑ᴸᵢ-⇑ᴿᵢ-commute ((X ˣ⊑ˣ Y) ∷ Φ) =
  cong ((suc X ˣ⊑ˣ suc Y) ∷_) (⇑ᴸᵢ-⇑ᴿᵢ-commute Φ)

left-right-store-commute-left-lastⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᴸ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  ∃[ ρ× ]
    LiftRightStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴸ ρ× ×
    LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴿ ρ×
left-right-store-commute-left-lastⁱ {Φ = Φ} liftᴸ liftᴿ
    rewrite ⇑ᴸᵢ-⇑ᴿᵢ-commute Φ =
  left-right-store-commuteⁱ liftᴸ liftᴿ

left-right-ctx-commute-left-lastⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴸ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γᴸ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ∃[ γ× ]
    LiftRightCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) γᴸ γ× ×
    LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) γᴿ γ×
left-right-ctx-commute-left-lastⁱ {Φ = Φ} liftᴸ liftᴿ
    rewrite ⇑ᴸᵢ-⇑ᴿᵢ-commute Φ =
  left-right-ctx-commuteⁱ liftᴸ liftᴿ

left-right-store-factorⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ× : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      (suc Δᴸ) (suc Δᴿ)} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᴸ →
  LiftRightStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴸ ρ× →
  ∃[ ρᴿ ]
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ ×
    LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴿ ρ×
left-right-store-factorⁱ
    lift-left-store-[] lift-right-store-[] =
  [] , lift-right-store-[] , lift-left-store-[]
left-right-store-factorⁱ
    (lift-left-store-∷ {p = p} shapeᴸ liftᴸ)
    (lift-right-store-∷ shape× lift×)
    with left-right-store-factorⁱ liftᴸ lift×
left-right-store-factorⁱ
    (lift-left-store-∷ {p = p} shapeᴸ liftᴸ)
    (lift-right-store-∷ shape× lift×)
    | ρᴿ , right , left =
  store-matched _ _ _ _ (⊑-target-lift-rightᵢ p) ∷ ρᴿ ,
  lift-right-store-∷ (shape-target-lift-rightᵢ p) right ,
  lift-left-store-∷
    (trans shape×
      (trans shapeᴸ (sym (shape-target-lift-rightᵢ p))))
    left
left-right-store-factorⁱ
    (lift-left-store-left {hA = hA} liftᴸ)
    (lift-right-store-left lift×)
    with left-right-store-factorⁱ liftᴸ lift×
left-right-store-factorⁱ
    (lift-left-store-left {hA = hA} liftᴸ)
    (lift-right-store-left lift×)
    | ρᴿ , right , left =
  store-left _ _ hA ∷ ρᴿ ,
  lift-right-store-left right , lift-left-store-left left
left-right-store-factorⁱ
    (lift-left-store-right liftᴸ)
    (lift-right-store-right {hB′ = hB×} lift×)
    with left-right-store-factorⁱ liftᴸ lift×
left-right-store-factorⁱ
    (lift-left-store-right liftᴸ)
    (lift-right-store-right {hB′ = hB×} lift×)
    | ρᴿ , right , left =
  store-right _ _ hB× ∷ ρᴿ ,
  lift-right-store-right right , lift-left-store-right left
left-right-store-factorⁱ
    (lift-left-store-link {p = p} shapeᴸ liftᴸ)
    (lift-right-store-link shape× lift×)
    with left-right-store-factorⁱ liftᴸ lift×
left-right-store-factorⁱ
    (lift-left-store-link {p = p} shapeᴸ liftᴸ)
    (lift-right-store-link shape× lift×)
    | ρᴿ , right , left =
  store-link _ _ _ _ (⊑-target-lift-rightᵢ p) ∷ ρᴿ ,
  lift-right-store-link (shape-target-lift-rightᵢ p) right ,
  lift-left-store-link
    (trans shape×
      (trans shapeᴸ (sym (shape-target-lift-rightᵢ p))))
    left

left-right-ctx-factorⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴸ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ× : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      (suc Δᴸ) (suc Δᴿ)} →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γᴸ →
  LiftRightCtxⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) γᴸ γ× →
  ∃[ γᴿ ]
    LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ ×
    LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) γᴿ γ×
left-right-ctx-factorⁱ lift-left-ctx-[] lift-right-ctx-[] =
  [] , lift-right-ctx-[] , lift-left-ctx-[]
left-right-ctx-factorⁱ
    (lift-left-ctx-∷ {p = p} shapeᴸ liftᴸ)
    (lift-right-ctx-∷ shape× lift×)
    with left-right-ctx-factorⁱ liftᴸ lift×
left-right-ctx-factorⁱ
    (lift-left-ctx-∷ {p = p} shapeᴸ liftᴸ)
    (lift-right-ctx-∷ shape× lift×)
    | γᴿ , right , left =
  ctx-imp _ _ (⊑-target-lift-rightᵢ p) ∷ γᴿ ,
  lift-right-ctx-∷ (shape-target-lift-rightᵢ p) right ,
  lift-left-ctx-∷
    (trans shape×
      (trans shapeᴸ (sym (shape-target-lift-rightᵢ p))))
    left

right-store-prefix-factorⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ⁺ᴿ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftRightStoreⁱ Ψ ρ⁺ ρ⁺ᴿ →
  ∃[ ρ₀ᴿ ]
    LiftRightStoreⁱ Ψ ρ₀ ρ₀ᴿ × StoreImpPrefix ρ₀ᴿ ρ⁺ᴿ
right-store-prefix-factorⁱ prefix-reflⁱ liftρ =
  _ , liftρ , prefix-reflⁱ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-∷ shape liftρ)
    with right-store-prefix-factorⁱ prefix liftρ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-∷ shape liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-left liftρ)
    with right-store-prefix-factorⁱ prefix liftρ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-left liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-right liftρ)
    with right-store-prefix-factorⁱ prefix liftρ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-right liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-link shape liftρ)
    with right-store-prefix-factorⁱ prefix liftρ
right-store-prefix-factorⁱ
    (prefix-∷ⁱ prefix) (lift-right-store-link shape liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ

data RelStoreRenameⁱ
    {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    (τ σ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Θᴸ τ)
    (hσ : TyRenameWf Δᴿ Θᴿ σ) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ Θᴸ Θᴿ → Set₁ where
  rel-store-rename-[] :
    RelStoreRenameⁱ τ σ assm hτ hσ [] []

  rel-store-rename-matched :
    ∀ {ρ ρ′ α α′ A A′ β β′ B B′ p} →
    (eqα : α′ ≡ τ α) → (eqA : A′ ≡ renameᵗ τ A) →
    (eqβ : β′ ≡ σ β) → (eqB : B′ ≡ renameᵗ σ B) →
    RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
    RelStoreRenameⁱ τ σ assm hτ hσ
      (store-matched α A β B p ∷ ρ)
      (store-matched α′ A′ β′ B′
        (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p) ∷ ρ′)

  rel-store-rename-left :
    ∀ {ρ ρ′ α α′ A A′ hA hA′} →
    α′ ≡ τ α → A′ ≡ renameᵗ τ A →
    RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
    RelStoreRenameⁱ τ σ assm hτ hσ
      (store-left α A hA ∷ ρ)
      (store-left α′ A′ hA′ ∷ ρ′)

  rel-store-rename-right :
    ∀ {ρ ρ′ β β′ B B′ hB hB′} →
    β′ ≡ σ β → B′ ≡ renameᵗ σ B →
    RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
    RelStoreRenameⁱ τ σ assm hτ hσ
      (store-right β B hB ∷ ρ)
      (store-right β′ B′ hB′ ∷ ρ′)

  rel-store-rename-link :
    ∀ {ρ ρ′ α α′ A A′ β β′ B B′ p} →
    (eqα : α′ ≡ τ α) → (eqA : A′ ≡ renameᵗ τ A) →
    (eqβ : β′ ≡ σ β) → (eqB : B′ ≡ renameᵗ σ B) →
    RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
    RelStoreRenameⁱ τ σ assm hτ hσ
      (store-link α A β B p ∷ ρ)
      (store-link α′ A′ β′ B′
        (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p) ∷ ρ′)

⊑-rename-at-shapeᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ A A′ B B′}
    (assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Θᴸ τ)
    (hσ : TyRenameWf Δᴿ Θᴿ σ)
    (eqA : A′ ≡ renameᵗ τ A)
    (eqB : B′ ≡ renameᵗ σ B)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-rename-at²ᵢ assm hτ hσ eqA eqB p ⌋ ≡ ⌊ p ⌋
⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p =
  trans
    (shape-subst-target (sym eqB)
      (subst
        (λ T → _ ∣ _ ⊢ T ⊑ renameᵗ _ _ ⊣ _)
        (sym eqA)
        (⊑-renameᵗ²ᵢ assm hτ hσ p)))
    (trans
      (shape-subst-source
        (sym eqA)
        (⊑-renameᵗ²ᵢ assm hτ hσ p))
      (shape-rename assm hτ hσ p))

rel-store-rename-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  RelStoreEmbeddingⁱ τ σ ρ ρ′
rel-store-rename-embeddingⁱ rel-store-rename-[] =
  rel-store-embedding-[]
rel-store-rename-embeddingⁱ
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ) =
  rel-store-embedding-matched eqα eqA eqβ eqB
    (⊑-rename-at-shapeᵢ _ _ _ eqA eqB _)
    (rel-store-rename-embeddingⁱ renameρ)
rel-store-rename-embeddingⁱ
    (rel-store-rename-left eqα eqA renameρ) =
  rel-store-embedding-left eqα eqA
    (rel-store-rename-embeddingⁱ renameρ)
rel-store-rename-embeddingⁱ
    (rel-store-rename-right eqβ eqB renameρ) =
  rel-store-embedding-right eqβ eqB
    (rel-store-rename-embeddingⁱ renameρ)
rel-store-rename-embeddingⁱ
    (rel-store-rename-link eqα eqA eqβ eqB renameρ) =
  rel-store-embedding-link eqα eqA eqβ eqB
    (⊑-rename-at-shapeᵢ _ _ _ eqA eqB _)
    (rel-store-rename-embeddingⁱ renameρ)

leftStoreⁱ-rel-embedding :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ renameStoreᵗ τ (leftStoreⁱ ρ)
leftStoreⁱ-rel-embedding rel-store-embedding-[] = refl
leftStoreⁱ-rel-embedding
    (rel-store-embedding-matched eqα eqA eqβ eqB shape emb) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA) (leftStoreⁱ-rel-embedding emb)
leftStoreⁱ-rel-embedding
    (rel-store-embedding-left eqα eqA emb) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA) (leftStoreⁱ-rel-embedding emb)
leftStoreⁱ-rel-embedding (rel-store-embedding-right eqβ eqB emb) =
  leftStoreⁱ-rel-embedding emb
leftStoreⁱ-rel-embedding
    (rel-store-embedding-link eqα eqA eqβ eqB shape emb) =
  leftStoreⁱ-rel-embedding emb

rightStoreⁱ-rel-embedding :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ renameStoreᵗ σ (rightStoreⁱ ρ)
rightStoreⁱ-rel-embedding rel-store-embedding-[] = refl
rightStoreⁱ-rel-embedding
    (rel-store-embedding-matched eqα eqA eqβ eqB shape emb) =
  cong₂ _∷_ (cong₂ _,_ eqβ eqB) (rightStoreⁱ-rel-embedding emb)
rightStoreⁱ-rel-embedding (rel-store-embedding-left eqα eqA emb) =
  rightStoreⁱ-rel-embedding emb
rightStoreⁱ-rel-embedding
    (rel-store-embedding-right eqβ eqB emb) =
  cong₂ _∷_ (cong₂ _,_ eqβ eqB) (rightStoreⁱ-rel-embedding emb)
rightStoreⁱ-rel-embedding
    (rel-store-embedding-link eqα eqA eqβ eqB shape emb) =
  rightStoreⁱ-rel-embedding emb

rel-store-rename-prefix-invⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′⁺ : StoreImp Ψ Θᴸ Θᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ⁺ ρ′⁺ →
  ∃[ ρ₀′ ]
    RelStoreRenameⁱ τ σ assm hτ hσ ρ₀ ρ₀′ ×
    StoreImpPrefix ρ₀′ ρ′⁺
rel-store-rename-prefix-invⁱ prefix-reflⁱ renameρ =
  _ , renameρ , prefix-reflⁱ
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ)
    with rel-store-rename-prefix-invⁱ prefix renameρ
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-left eqα eqA renameρ)
    with rel-store-rename-prefix-invⁱ prefix renameρ
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-left eqα eqA renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-right eqβ eqB renameρ)
    with rel-store-rename-prefix-invⁱ prefix renameρ
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-right eqβ eqB renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-link eqα eqA eqβ eqB renameρ)
    with rel-store-rename-prefix-invⁱ prefix renameρ
rel-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-rename-link eqα eqA eqβ eqB renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′

rel-store-rename-matched∈ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {α A β B p} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  store-matched α A β B p ∈ ρ →
  ∃[ α′ ] α′ ≡ τ α × ∃[ A′ ] ∃[ eqA ]
  ∃[ β′ ] β′ ≡ σ β × ∃[ B′ ] ∃[ eqB ]
    store-matched α′ A′ β′ B′
      (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p) ∈ ρ′
rel-store-rename-matched∈ⁱ
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ)
    (here refl) =
  _ , eqα , _ , eqA , _ , eqβ , _ , eqB , here refl
rel-store-rename-matched∈ⁱ
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ)
    (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′
rel-store-rename-matched∈ⁱ
    (rel-store-rename-left eqα eqA renameρ) (here ())
rel-store-rename-matched∈ⁱ
    (rel-store-rename-left eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′
rel-store-rename-matched∈ⁱ
    (rel-store-rename-right eqβ eqB renameρ) (here ())
rel-store-rename-matched∈ⁱ
    (rel-store-rename-right eqβ eqB renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′
rel-store-rename-matched∈ⁱ
    (rel-store-rename-link eqα eqA eqβ eqB renameρ) (here ())
rel-store-rename-matched∈ⁱ
    (rel-store-rename-link eqα eqA eqβ eqB renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′

rel-store-rename-link∈ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {α A β B p} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  store-link α A β B p ∈ ρ →
  ∃[ α′ ] α′ ≡ τ α × ∃[ A′ ] ∃[ eqA ]
  ∃[ β′ ] β′ ≡ σ β × ∃[ B′ ] ∃[ eqB ]
    store-link α′ A′ β′ B′
      (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p) ∈ ρ′
rel-store-rename-link∈ⁱ
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ)
    (here ())
rel-store-rename-link∈ⁱ
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ)
    (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′
rel-store-rename-link∈ⁱ
    (rel-store-rename-left eqα eqA renameρ) (here ())
rel-store-rename-link∈ⁱ
    (rel-store-rename-left eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′
rel-store-rename-link∈ⁱ
    (rel-store-rename-right eqβ eqB renameρ) (here ())
rel-store-rename-link∈ⁱ
    (rel-store-rename-right eqβ eqB renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′
rel-store-rename-link∈ⁱ
    (rel-store-rename-link eqα eqA eqβ eqB renameρ)
    (here refl) =
  _ , eqα , _ , eqA , _ , eqβ , _ , eqB , here refl
rel-store-rename-link∈ⁱ
    (rel-store-rename-link eqα eqA eqβ eqB renameρ)
    (there p∈) =
  let α′ , eqα′ , A′ , eqA′ ,
        β′ , eqβ′ , B′ , eqB′ , p∈′ =
        rel-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ ,
  β′ , eqβ′ , B′ , eqB′ , there p∈′

rel-store-rename-correspondenceⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {α A β B p} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  StoreCorresponds ρ α A β B p →
  ∃[ α′ ] α′ ≡ τ α × ∃[ A′ ] ∃[ eqA ]
  ∃[ β′ ] β′ ≡ σ β × ∃[ B′ ] ∃[ eqB ]
    StoreCorresponds ρ′ α′ A′ β′ B′
      (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p)
rel-store-rename-correspondenceⁱ renameρ
    (correspondence-stored p∈) =
  let α′ , eqα , A′ , eqA , β′ , eqβ , B′ , eqB , p∈′ =
        rel-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα , A′ , eqA , β′ , eqβ , B′ , eqB ,
  correspondence-stored p∈′
rel-store-rename-correspondenceⁱ renameρ
    (correspondence-linked p∈) =
  let α′ , eqα , A′ , eqA , β′ , eqβ , B′ , eqB , p∈′ =
        rel-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα , A′ , eqA , β′ , eqβ , B′ , eqB ,
  correspondence-linked p∈′

record RelWorldPermutationⁱ
    {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    (πᴸ : TyPermutation Δᴸ Θᴸ)
    (πᴿ : TyPermutation Δᴿ Θᴿ)
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ)
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} : Set₁ where
  constructor rel-world-permutation
  field
    left-cast-renamer : CastModeRenamer (forward πᴸ)
    right-cast-renamer : CastModeRenamer (forward πᴿ)
    store-permutation : RelStoreRenameⁱ
      (forward πᴸ) (forward πᴿ) assm
      (forward-wf πᴸ) (forward-wf πᴿ) ρ ρ′
    ctx-permutation : RelCtxRenameⁱ
      (forward πᴸ) (forward πᴿ) assm
      (forward-wf πᴸ) (forward-wf πᴿ) γ γ′

open RelWorldPermutationⁱ public

record StoreProjectionEmbeddingⁱ
    {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    (τ σ : Renameᵗ)
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (ρ′ : StoreImp Ψ Θᴸ Θᴿ) : Set where
  constructor store-projection-embedding
  field
    left-store-inclusion :
      StoreIncl (renameStoreᵗ τ (leftStoreⁱ ρ)) (leftStoreⁱ ρ′)
    right-store-inclusion :
      StoreIncl (renameStoreᵗ σ (rightStoreⁱ ρ)) (rightStoreⁱ ρ′)

open StoreProjectionEmbeddingⁱ public

rel-store-embedding-projectionⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  StoreProjectionEmbeddingⁱ τ σ ρ ρ′
rel-store-embedding-projectionⁱ emb =
  store-projection-embedding
    (λ {x} x∈ → subst (x ∈_)
      (sym (leftStoreⁱ-rel-embedding emb)) x∈)
    (λ {x} x∈ → subst (x ∈_)
      (sym (rightStoreⁱ-rel-embedding emb)) x∈)

record RelWorldEmbeddingⁱ
    {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    (τ σ ψ φ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Θᴸ τ)
    (hσ : TyRenameWf Δᴿ Θᴿ σ)
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} : Set₁ where
  constructor rel-world-embedding
  field
    left-embedding-inverse : RenameLeftInverse τ ψ
    right-embedding-inverse : RenameLeftInverse σ φ
    left-embedding-cast-renamer : CastModeRenamer τ
    right-embedding-cast-renamer : CastModeRenamer σ
    store-embedding : RelStoreEmbeddingⁱ τ σ ρ ρ′
    embedding-context : RelCtxRenameⁱ τ σ assm hτ hσ γ γ′

open RelWorldEmbeddingⁱ public

rel-ctx-rename-lookupⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {x A B p} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  γ ∋ x ⦂ ctx-imp A B p →
  ∃[ A′ ] ∃[ B′ ] ∃[ eqA ] ∃[ eqB ]
    γ′ ∋ x ⦂ ctx-imp A′ B′
      (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p)
rel-ctx-rename-lookupⁱ
    (rel-ctx-rename-∷ eqA eqB renameγ) Z =
  _ , _ , eqA , eqB , Z
rel-ctx-rename-lookupⁱ
    (rel-ctx-rename-∷ eqA eqB renameγ) (S x∈) =
  let A′ , B′ , eqA′ , eqB′ , x∈′ =
        rel-ctx-rename-lookupⁱ renameγ x∈ in
  A′ , B′ , eqA′ , eqB′ , S x∈′

rel-world-x-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {x A B p} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  γ ∋ x ⦂ ctx-imp A B p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (` x)
      ⊑ renameᵗᵐ (forward πᴿ) (` x)
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p
rel-world-x-permuteᵀ perm x∈
    with rel-ctx-rename-lookupⁱ (ctx-permutation perm) x∈
rel-world-x-permuteᵀ perm x∈ | A′ , B′ , refl , refl , x∈′ =
  x⊑xᵀ x∈′

rel-world-permutation-ctx-∷ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {A B p} →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′}
    {γ = ctx-imp A B p ∷ γ}
    {γ′ = ctx-imp
      (renameᵗ (forward πᴸ) A)
      (renameᵗ (forward πᴿ) B)
      (⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p)
      ∷ γ′}
rel-world-permutation-ctx-∷ⁱ perm =
  rel-world-permutation
    (left-cast-renamer perm) (right-cast-renamer perm)
    (store-permutation perm)
    (rel-ctx-rename-∷ refl refl (ctx-permutation perm))

rel-world-ƛ-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {N N′ A A′ B B′ pA pB} →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣
      ctx-imp
        (renameᵗ (forward πᴸ) A)
        (renameᵗ (forward πᴿ) A′)
        (⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) pA)
        ∷ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) N
      ⊑ renameᵗᵐ (forward πᴿ) N′
    ⦂ renameᵗ (forward πᴸ) B ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) pB →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (ƛ N)
      ⊑ renameᵗᵐ (forward πᴿ) (ƛ N′)
    ⦂ renameᵗ (forward πᴸ) (A ⇒ B)
      ⊑ renameᵗ (forward πᴿ) (A′ ⇒ B′)
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ)
        (pA ↦ pB)
rel-world-ƛ-permuteᵀ {πᴸ = πᴸ} {πᴿ = πᴿ}
    perm hA hA′ N⊑N′ =
  ƛ⊑ƛᵀ
    (renameᵗ-preserves-WfTy hA (forward-wf πᴸ))
    (renameᵗ-preserves-WfTy hA′ (forward-wf πᴿ)) N⊑N′

rel-world-·-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {L L′ M M′ A A′ B B′ pA pB} →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) L
      ⊑ renameᵗᵐ (forward πᴿ) L′
    ⦂ renameᵗ (forward πᴸ) (A ⇒ B)
      ⊑ renameᵗ (forward πᴿ) (A′ ⇒ B′)
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ)
        (pA ↦ pB) →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) A′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) pA →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (L · M)
      ⊑ renameᵗᵐ (forward πᴿ) (L′ · M′)
    ⦂ renameᵗ (forward πᴸ) B ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) pB
rel-world-·-permuteᵀ L⊑L′ M⊑M′ = ·⊑·ᵀ L⊑L′ M⊑M′

rel-world-κ-permuteᵀ :
  ∀ {Ψ Θᴸ Θᴿ} {ρ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Ψ Θᴸ Θᴿ} {n} →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ ∣ γ
    ⊢ᴺ $ (κℕ n) ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
rel-world-κ-permuteᵀ = κ⊑κᵀ

rel-world-⊕-permuteᵀ :
  ∀ {Ψ Θᴸ Θᴿ} {ρ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Ψ Θᴸ Θᴿ} {L L′ M M′} →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ ∣ γ
    ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ ∣ γ
    ⊢ᴺ L ⊕[ addℕ ] M ⊑ L′ ⊕[ addℕ ] M′
    ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
rel-world-⊕-permuteᵀ L⊑L′ M⊑M′ = ⊕⊑⊕ᵀ L⊑L′ M⊑M′

rel-store-rename-lift∀ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  ∃[ ρ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    RelStoreRenameⁱ
      (extᵗ τ) (extᵗ σ) (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) ρ∀ ρ′∀
rel-store-rename-lift∀ⁱ rel-store-rename-[] lift-store-[] =
  [] , lift-store-[] , rel-store-rename-[]
rel-store-rename-lift∀ⁱ
    (rel-store-rename-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-store-∷ {p′ = p∀} shape∀ liftρ)
    with rel-store-rename-lift∀ⁱ renameρ liftρ
rel-store-rename-lift∀ⁱ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-rename-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-store-∷
      {A = A} {B = B} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-matched (suc α′) (⇑ᵗ A′) (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) eqA∀ eqB∀ p∀)
      ∷ ρ′∀ ,
  lift-store-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftρ′ ,
  rel-store-rename-matched
    (cong suc eqα) eqA∀ (cong suc eqβ) eqB∀ renameρ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-rename-lift∀ⁱ
    (rel-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-store-left liftρ)
    with rel-store-rename-lift∀ⁱ renameρ liftρ
rel-store-rename-lift∀ⁱ {τ = τ}
    (rel-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-store-left {A = A} liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-left liftρ′ ,
  rel-store-rename-left (cong suc eqα) eqA∀ renameρ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-rename-lift∀ⁱ
    (rel-store-rename-right {β′ = β′} {B′ = B′} {hB′ = hB′}
      eqβ eqB renameρ)
    (lift-store-right liftρ)
    with rel-store-rename-lift∀ⁱ renameρ liftρ
rel-store-rename-lift∀ⁱ {σ = σ}
    (rel-store-rename-right {β′ = β′} {B′ = B′} {hB′ = hB′}
      eqβ eqB renameρ)
    (lift-store-right {B = B} liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-right (suc β′) (⇑ᵗ B′)
      (renameᵗ-preserves-WfTy hB′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-right liftρ′ ,
  rel-store-rename-right (cong suc eqβ) eqB∀ renameρ∀
  where
  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-rename-lift∀ⁱ
    (rel-store-rename-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-store-link {p′ = p∀} shape∀ liftρ)
    with rel-store-rename-lift∀ⁱ renameρ liftρ
rel-store-rename-lift∀ⁱ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-rename-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-store-link
      {A = A} {B = B} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-link (suc α′) (⇑ᵗ A′) (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) eqA∀ eqB∀ p∀)
      ∷ ρ′∀ ,
  lift-store-link
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftρ′ ,
  rel-store-rename-link
    (cong suc eqα) eqA∀ (cong suc eqβ) eqB∀ renameρ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))

rel-store-embedding-lift∀ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  ∃[ ρ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    RelStoreEmbeddingⁱ (extᵗ τ) (extᵗ σ) ρ∀ ρ′∀
rel-store-embedding-lift∀ⁱ
    rel-store-embedding-[] lift-store-[] =
  [] , lift-store-[] , rel-store-embedding-[]
rel-store-embedding-lift∀ⁱ {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-∷ {p′ = p∀} shape∀ liftρ)
    with rel-store-embedding-lift∀ⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift∀ⁱ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-∷
      {A = A} {B = B} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-matched (suc α′) (⇑ᵗ A′) (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) eqA∀ eqB∀ p∀)
      ∷ ρ′∀ ,
  lift-store-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀ (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-matched
    (cong suc eqα) eqA∀ (cong suc eqβ) eqB∀
    (⊑-rename-at-shapeᵢ
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
      eqA∀ eqB∀ p∀)
    emb∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-embedding-lift∀ⁱ {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-store-left liftρ)
    with rel-store-embedding-lift∀ⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift∀ⁱ {τ = τ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-store-left {A = A} liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-left liftρ′ ,
  rel-store-embedding-left (cong suc eqα) eqA∀ emb∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-embedding-lift∀ⁱ {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-store-right liftρ)
    with rel-store-embedding-lift∀ⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift∀ⁱ {σ = σ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-store-right {B = B} liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-right (suc β′) (⇑ᵗ B′)
      (renameᵗ-preserves-WfTy hB′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-right liftρ′ ,
  rel-store-embedding-right (cong suc eqβ) eqB∀ emb∀
  where
  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-embedding-lift∀ⁱ {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-link {p′ = p∀} shape∀ liftρ)
    with rel-store-embedding-lift∀ⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift∀ⁱ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-link
      {A = A} {B = B} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-link (suc α′) (⇑ᵗ A′) (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) eqA∀ eqB∀ p∀)
      ∷ ρ′∀ ,
  lift-store-link
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀ (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-link
    (cong suc eqα) eqA∀ (cong suc eqβ) eqB∀
    (⊑-rename-at-shapeᵢ
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
      eqA∀ eqB∀ p∀)
    emb∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))

rel-ctx-rename-lift∀ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  ∃[ γ′∀ ]
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    RelCtxRenameⁱ
      (extᵗ τ) (extᵗ σ) (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) γ∀ γ′∀
rel-ctx-rename-lift∀ⁱ rel-ctx-rename-[] lift-ctx-[] =
  [] , lift-ctx-[] , rel-ctx-rename-[]
rel-ctx-rename-lift∀ⁱ
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-ctx-∷ {p′ = p∀} shape∀ liftγ)
    with rel-ctx-rename-lift∀ⁱ renameγ liftγ
rel-ctx-rename-lift∀ⁱ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-ctx-∷ {A = A} {B = B} {p′ = p∀} shape∀ liftγ)
    | γ′∀ , liftγ′ , renameγ∀ =
  ctx-imp (⇑ᵗ A′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) eqA∀ eqB∀ p∀)
      ∷ γ′∀ ,
  lift-ctx-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftγ′ ,
  rel-ctx-rename-∷ eqA∀ eqB∀ renameγ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))

rel-world-permutation-lift∀ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  ∃[ ρ′∀ ] ∃[ γ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    RelWorldPermutationⁱ
      (TyPermutation-ext πᴸ) (TyPermutation-ext πᴿ)
      (rename-assm²-⇑ᵢ assm)
      {ρ = ρ∀} {ρ′ = ρ′∀} {γ = γ∀} {γ′ = γ′∀}
rel-world-permutation-lift∀ⁱ perm liftρ liftγ
    with rel-store-rename-lift∀ⁱ (store-permutation perm) liftρ
       | rel-ctx-rename-lift∀ⁱ (ctx-permutation perm) liftγ
rel-world-permutation-lift∀ⁱ perm liftρ liftγ
    | ρ′∀ , liftρ′ , renameρ∀
    | γ′∀ , liftγ′ , renameγ∀ =
  ρ′∀ , γ′∀ , liftρ′ , liftγ′ ,
  rel-world-permutation
    (castModeRenamer-ext (left-cast-renamer perm))
    (castModeRenamer-ext (right-cast-renamer perm))
    renameρ∀ renameγ∀

rel-world-embedding-lift∀ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  ∃[ ρ′∀ ] ∃[ γ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    RelWorldEmbeddingⁱ
      (extᵗ τ) (extᵗ σ) (extᵗ ψ) (extᵗ φ)
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
      {ρ = ρ∀} {ρ′ = ρ′∀} {γ = γ∀} {γ′ = γ′∀}
rel-world-embedding-lift∀ⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ liftγ
    with rel-store-embedding-lift∀ⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      (store-embedding emb) liftρ
       | rel-ctx-rename-lift∀ⁱ (embedding-context emb) liftγ
rel-world-embedding-lift∀ⁱ emb liftρ liftγ
    | ρ′∀ , liftρ′ , embρ∀
    | γ′∀ , liftγ′ , renameγ∀ =
  ρ′∀ , γ′∀ , liftρ′ , liftγ′ ,
  rel-world-embedding
    (RenameLeftInverse-ext (left-embedding-inverse emb))
    (RenameLeftInverse-ext (right-embedding-inverse emb))
    (castModeRenamer-ext (left-embedding-cast-renamer emb))
    (castModeRenamer-ext (right-embedding-cast-renamer emb))
    embρ∀ renameγ∀

rel-store-rename-lift-leftⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  ∃[ ρ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    RelStoreRenameⁱ
      (extᵗ τ) σ (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ ρν ρ′ν
rel-store-rename-lift-leftⁱ
    rel-store-rename-[] lift-left-store-[] =
  [] , lift-left-store-[] , rel-store-rename-[]
rel-store-rename-lift-leftⁱ
    (rel-store-rename-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-left-store-∷ {p′ = pν} shapeν liftρ)
    with rel-store-rename-lift-leftⁱ renameρ liftρ
rel-store-rename-lift-leftⁱ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-rename-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-left-store-∷
      {A = A} {B = B} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-matched (suc α′) (⇑ᵗ A′) β′ B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ ρ′ν ,
  lift-left-store-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftρ′ ,
  rel-store-rename-matched
    (cong suc eqα) eqAν eqβ eqB renameρν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-rename-lift-leftⁱ
    (rel-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-left-store-left liftρ)
    with rel-store-rename-lift-leftⁱ renameρ liftρ
rel-store-rename-lift-leftⁱ {τ = τ}
    (rel-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-left-store-left {A = A} liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′ν ,
  lift-left-store-left liftρ′ ,
  rel-store-rename-left (cong suc eqα) eqAν renameρν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-rename-lift-leftⁱ
    (rel-store-rename-right {β′ = β′} {B′ = B′} {hB′ = hB′}
      eqβ eqB renameρ)
    (lift-left-store-right liftρ)
    with rel-store-rename-lift-leftⁱ renameρ liftρ
rel-store-rename-lift-leftⁱ
    (rel-store-rename-right {β′ = β′} {B′ = B′} {hB′ = hB′}
      eqβ eqB renameρ)
    (lift-left-store-right liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-right β′ B′ hB′ ∷ ρ′ν ,
  lift-left-store-right liftρ′ ,
  rel-store-rename-right eqβ eqB renameρν
rel-store-rename-lift-leftⁱ
    (rel-store-rename-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-left-store-link {p′ = pν} shapeν liftρ)
    with rel-store-rename-lift-leftⁱ renameρ liftρ
rel-store-rename-lift-leftⁱ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-rename-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-left-store-link
      {A = A} {B = B} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-link (suc α′) (⇑ᵗ A′) β′ B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ ρ′ν ,
  lift-left-store-link
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftρ′ ,
  rel-store-rename-link (cong suc eqα) eqAν eqβ eqB renameρν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

rel-store-embedding-lift-leftⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  ∃[ ρ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    RelStoreEmbeddingⁱ (extᵗ τ) σ ρν ρ′ν
rel-store-embedding-lift-leftⁱ
    rel-store-embedding-[] lift-left-store-[] =
  [] , lift-left-store-[] , rel-store-embedding-[]
rel-store-embedding-lift-leftⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-∷ {p′ = pν} shapeν liftρ)
    with rel-store-embedding-lift-leftⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-leftⁱ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-∷
      {A = A} {B = B} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , embν =
  store-matched (suc α′) (⇑ᵗ A′) β′ B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ ρ′ν ,
  lift-left-store-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-matched
    (cong suc eqα) eqAν eqβ eqB
    (⊑-rename-at-shapeᵢ
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ eqAν eqB pν)
    embν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-embedding-lift-leftⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-left-store-left liftρ)
    with rel-store-embedding-lift-leftⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-leftⁱ {τ = τ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-left-store-left {A = A} liftρ)
    | ρ′ν , liftρ′ , embν =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′ν ,
  lift-left-store-left liftρ′ ,
  rel-store-embedding-left (cong suc eqα) eqAν embν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-embedding-lift-leftⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-left-store-right liftρ)
    with rel-store-embedding-lift-leftⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-leftⁱ
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-left-store-right liftρ)
    | ρ′ν , liftρ′ , embν =
  store-right β′ B′ hB′ ∷ ρ′ν ,
  lift-left-store-right liftρ′ ,
  rel-store-embedding-right eqβ eqB embν
rel-store-embedding-lift-leftⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-link {p′ = pν} shapeν liftρ)
    with rel-store-embedding-lift-leftⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-leftⁱ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-link
      {A = A} {B = B} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , embν =
  store-link (suc α′) (⇑ᵗ A′) β′ B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ ρ′ν ,
  lift-left-store-link
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-link (cong suc eqα) eqAν eqβ eqB
    (⊑-rename-at-shapeᵢ
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ eqAν eqB pν)
    embν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

rel-ctx-rename-lift-leftⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  ∃[ γ′ν ]
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    RelCtxRenameⁱ
      (extᵗ τ) σ (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ γν γ′ν
rel-ctx-rename-lift-leftⁱ rel-ctx-rename-[] lift-left-ctx-[] =
  [] , lift-left-ctx-[] , rel-ctx-rename-[]
rel-ctx-rename-lift-leftⁱ
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-left-ctx-∷ {p′ = pν} shapeν liftγ)
    with rel-ctx-rename-lift-leftⁱ renameγ liftγ
rel-ctx-rename-lift-leftⁱ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-left-ctx-∷
      {A = A} {B = B} {p′ = pν} shapeν liftγ)
    | γ′ν , liftγ′ , renameγν =
  ctx-imp (⇑ᵗ A′) B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ γ′ν ,
  lift-left-ctx-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftγ′ ,
  rel-ctx-rename-∷ eqAν eqB renameγν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

rel-world-permutation-lift-leftⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  ∃[ ρ′ν ] ∃[ γ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    RelWorldPermutationⁱ (TyPermutation-ext πᴸ) πᴿ
      (rename-assm²-⇑ᴸᵢ assm)
      {ρ = ρν} {ρ′ = ρ′ν} {γ = γν} {γ′ = γ′ν}
rel-world-permutation-lift-leftⁱ perm liftρ liftγ
    with rel-store-rename-lift-leftⁱ
      (store-permutation perm) liftρ
       | rel-ctx-rename-lift-leftⁱ (ctx-permutation perm) liftγ
rel-world-permutation-lift-leftⁱ perm liftρ liftγ
    | ρ′ν , liftρ′ , renameρν
    | γ′ν , liftγ′ , renameγν =
  ρ′ν , γ′ν , liftρ′ , liftγ′ ,
  rel-world-permutation
    (castModeRenamer-ext (left-cast-renamer perm))
    (right-cast-renamer perm) renameρν renameγν

rel-world-embedding-lift-leftⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  ∃[ ρ′ν ] ∃[ γ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    RelWorldEmbeddingⁱ (extᵗ τ) σ (extᵗ ψ) φ
      (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ) hσ
      {ρ = ρν} {ρ′ = ρ′ν} {γ = γν} {γ′ = γ′ν}
rel-world-embedding-lift-leftⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ liftγ
    with rel-store-embedding-lift-leftⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      (store-embedding emb) liftρ
       | rel-ctx-rename-lift-leftⁱ (embedding-context emb) liftγ
rel-world-embedding-lift-leftⁱ emb liftρ liftγ
    | ρ′ν , liftρ′ , embρν
    | γ′ν , liftγ′ , renameγν =
  ρ′ν , γ′ν , liftρ′ , liftγ′ ,
  rel-world-embedding
    (RenameLeftInverse-ext (left-embedding-inverse emb))
    (right-embedding-inverse emb)
    (castModeRenamer-ext (left-embedding-cast-renamer emb))
    (right-embedding-cast-renamer emb) embρν renameγν

rel-world-Λ-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {V V′ A B}
    {p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  Value V →
  Value V′ →
  ∃[ ρ′∀ ] ∃[ γ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    RelWorldPermutationⁱ
      (TyPermutation-ext πᴸ) (TyPermutation-ext πᴿ)
      (rename-assm²-⇑ᵢ assm)
      {ρ = ρ∀} {ρ′ = ρ′∀} {γ = γ∀} {γ′ = γ′∀} ×
    (∀ᵢᶜ Ψ ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ′∀ ∣ γ′∀
       ⊢ᴺ renameᵗᵐ (extᵗ (forward πᴸ)) V
         ⊑ renameᵗᵐ (extᵗ (forward πᴿ)) V′
       ⦂ renameᵗ (extᵗ (forward πᴸ)) A
         ⊑ renameᵗ (extᵗ (forward πᴿ)) B
       ∶ ⊑-renameᵗ²ᵢ (rename-assm²-⇑ᵢ assm)
           (TyRenameWf-ext (forward-wf πᴸ))
           (TyRenameWf-ext (forward-wf πᴿ)) p →
     Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
       ⊢ᴺ renameᵗᵐ (forward πᴸ) (Λ V)
         ⊑ renameᵗᵐ (forward πᴿ) (Λ V′)
       ⦂ renameᵗ (forward πᴸ) (`∀ A)
         ⊑ renameᵗ (forward πᴿ) (`∀ B)
       ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ)
           (∀ⁱ p))
rel-world-Λ-permuteᵀ {πᴸ = πᴸ} {πᴿ = πᴿ}
    perm liftρ liftγ vV vV′
    with rel-world-permutation-lift∀ⁱ perm liftρ liftγ
rel-world-Λ-permuteᵀ {πᴸ = πᴸ} {πᴿ = πᴿ}
    perm liftρ liftγ vV vV′
    | ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-perm =
  ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-perm ,
  λ V⊑V′ →
    Λ⊑Λᵀ liftρ′ liftγ′
      (renameᵗᵐ-preserves-Value (extᵗ (forward πᴸ)) vV)
      (renameᵗᵐ-preserves-Value (extᵗ (forward πᴿ)) vV′)
      V⊑V′

rel-world-Λ-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {V V′ A B}
    {p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  Value V →
  Value V′ →
  ∃[ ρ′∀ ] ∃[ γ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    RelWorldEmbeddingⁱ
      (extᵗ τ) (extᵗ σ) (extᵗ ψ) (extᵗ φ)
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
      {ρ = ρ∀} {ρ′ = ρ′∀} {γ = γ∀} {γ′ = γ′∀} ×
    (∀ᵢᶜ Ψ ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ′∀ ∣ γ′∀
       ⊢ᴺ renameᵗᵐ (extᵗ τ) V ⊑ renameᵗᵐ (extᵗ σ) V′
       ⦂ renameᵗ (extᵗ τ) A ⊑ renameᵗ (extᵗ σ) B
       ∶ ⊑-renameᵗ²ᵢ (rename-assm²-⇑ᵢ assm)
           (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) p →
     Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
       ⊢ᴺ renameᵗᵐ τ (Λ V) ⊑ renameᵗᵐ σ (Λ V′)
       ⦂ renameᵗ τ (`∀ A) ⊑ renameᵗ σ (`∀ B)
       ∶ ⊑-renameᵗ²ᵢ assm hτ hσ (∀ⁱ p))
rel-world-Λ-embedᵀ emb liftρ liftγ vV vV′
    with rel-world-embedding-lift∀ⁱ emb liftρ liftγ
rel-world-Λ-embedᵀ {τ = τ} {σ = σ}
    emb liftρ liftγ vV vV′
    | ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-emb =
  ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-emb ,
  λ V⊑V′ →
    Λ⊑Λᵀ liftρ′ liftγ′
      (renameᵗᵐ-preserves-Value (extᵗ τ) vV)
      (renameᵗᵐ-preserves-Value (extᵗ σ) vV′)
      V⊑V′

rel-world-Λ⊑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ A B}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  {{safe : NonVar A}} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (occ : occurs zero A ≡ true) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  Value V →
  ∃[ ρ′ν ] ∃[ γ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    RelWorldEmbeddingⁱ (extᵗ τ) σ (extᵗ ψ) φ
      (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ) hσ
      {ρ = ρν} {ρ′ = ρ′ν} {γ = γν} {γ′ = γ′ν} ×
    (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
       ∣ suc Θᴸ ∣ Θᴿ ∣ ρ′ν ∣ γ′ν
       ⊢ᴺ renameᵗᵐ (extᵗ τ) V ⊑ renameᵗᵐ σ N′
       ⦂ renameᵗ (extᵗ τ) A ⊑ renameᵗ σ B
       ∶ ⊑-renameᵗ²ᵢ (rename-assm²-⇑ᴸᵢ assm)
           (TyRenameWf-ext hτ) hσ p →
     Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
       ⊢ᴺ renameᵗᵐ τ (Λ V) ⊑ renameᵗᵐ σ N′
       ⦂ renameᵗ τ (`∀ A) ⊑ renameᵗ σ B
       ∶ ⊑-renameᵗ²ᵢ assm hτ hσ (ν _ occ p))
rel-world-Λ⊑-embedᵀ {{safe}} emb occ liftρ liftγ vV
    with rel-world-embedding-lift-leftⁱ emb liftρ liftγ
rel-world-Λ⊑-embedᵀ {τ = τ} {A = A}
    {{safe}} emb occ liftρ liftγ vV
    | ρ′ν , γ′ν , liftρ′ , liftγ′ , body-emb =
  ρ′ν , γ′ν , liftρ′ , liftγ′ , body-emb ,
  λ V⊑N′ →
    Λ⊑ᵀ {{renameNonVar (extᵗ τ) safe}}
      (trans (occurs-zero-rename-ext τ A) occ)
      liftρ′ liftγ′
      (renameᵗᵐ-preserves-Value (extᵗ τ) vV)
      V⊑N′

rel-world-Λ⊑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ A B}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  {{safe : NonVar A}} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (occ : occurs zero A ≡ true) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  Value V →
  ∃[ ρ′ν ] ∃[ γ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    RelWorldPermutationⁱ (TyPermutation-ext πᴸ) πᴿ
      (rename-assm²-⇑ᴸᵢ assm)
      {ρ = ρν} {ρ′ = ρ′ν} {γ = γν} {γ′ = γ′ν} ×
    (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
       ∣ suc Θᴸ ∣ Θᴿ ∣ ρ′ν ∣ γ′ν
       ⊢ᴺ renameᵗᵐ (extᵗ (forward πᴸ)) V
         ⊑ renameᵗᵐ (forward πᴿ) N′
       ⦂ renameᵗ (extᵗ (forward πᴸ)) A
         ⊑ renameᵗ (forward πᴿ) B
       ∶ ⊑-renameᵗ²ᵢ (rename-assm²-⇑ᴸᵢ assm)
           (TyRenameWf-ext (forward-wf πᴸ))
           (forward-wf πᴿ) p →
     Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
       ⊢ᴺ renameᵗᵐ (forward πᴸ) (Λ V)
         ⊑ renameᵗᵐ (forward πᴿ) N′
       ⦂ renameᵗ (forward πᴸ) (`∀ A)
         ⊑ renameᵗ (forward πᴿ) B
       ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ)
           (ν _ occ p))
rel-world-Λ⊑-permuteᵀ {πᴸ = πᴸ} {πᴿ = πᴿ} {A = A}
    {{safe}} perm occ liftρ liftγ vV
    with rel-world-permutation-lift-leftⁱ perm liftρ liftγ
rel-world-Λ⊑-permuteᵀ {πᴸ = πᴸ} {πᴿ = πᴿ} {A = A}
    {{safe}} perm occ liftρ liftγ vV
    | ρ′ν , γ′ν , liftρ′ , liftγ′ , body-perm =
  ρ′ν , γ′ν , liftρ′ , liftγ′ , body-perm ,
  λ V⊑N′ →
    Λ⊑ᵀ
      {{renameNonVar (extᵗ (forward πᴸ)) safe}}
      (trans (occurs-zero-rename-ext (forward πᴸ) A) occ)
      liftρ′ liftγ′
      (renameᵗᵐ-preserves-Value (extᵗ (forward πᴸ)) vV)
      V⊑N′

leftStoreⁱ-rel-rename :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ renameStoreᵗ τ (leftStoreⁱ ρ)
leftStoreⁱ-rel-rename rel-store-rename-[] = refl
leftStoreⁱ-rel-rename
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA) (leftStoreⁱ-rel-rename renameρ)
leftStoreⁱ-rel-rename
    (rel-store-rename-left eqα eqA renameρ) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA) (leftStoreⁱ-rel-rename renameρ)
leftStoreⁱ-rel-rename
    (rel-store-rename-right eqβ eqB renameρ) =
  leftStoreⁱ-rel-rename renameρ
leftStoreⁱ-rel-rename
    (rel-store-rename-link eqα eqA eqβ eqB renameρ) =
  leftStoreⁱ-rel-rename renameρ

rightStoreⁱ-rel-rename :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ renameStoreᵗ σ (rightStoreⁱ ρ)
rightStoreⁱ-rel-rename rel-store-rename-[] = refl
rightStoreⁱ-rel-rename
    (rel-store-rename-matched eqα eqA eqβ eqB renameρ) =
  cong₂ _∷_ (cong₂ _,_ eqβ eqB) (rightStoreⁱ-rel-rename renameρ)
rightStoreⁱ-rel-rename
    (rel-store-rename-left eqα eqA renameρ) =
  rightStoreⁱ-rel-rename renameρ
rightStoreⁱ-rel-rename
    (rel-store-rename-right eqβ eqB renameρ) =
  cong₂ _∷_ (cong₂ _,_ eqβ eqB) (rightStoreⁱ-rel-rename renameρ)
rightStoreⁱ-rel-rename
    (rel-store-rename-link eqα eqA eqβ eqB renameρ) =
  rightStoreⁱ-rel-rename renameρ

leftCtxⁱ-rel-rename :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  leftCtxⁱ γ′ ≡ map (renameᵗ τ) (leftCtxⁱ γ)
leftCtxⁱ-rel-rename rel-ctx-rename-[] = refl
leftCtxⁱ-rel-rename (rel-ctx-rename-∷ eqA eqB renameγ) =
  cong₂ _∷_ eqA (leftCtxⁱ-rel-rename renameγ)

rightCtxⁱ-rel-rename :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  rightCtxⁱ γ′ ≡ map (renameᵗ σ) (rightCtxⁱ γ)
rightCtxⁱ-rel-rename rel-ctx-rename-[] = refl
rightCtxⁱ-rel-rename (rel-ctx-rename-∷ eqA eqB renameγ) =
  cong₂ _∷_ eqB (rightCtxⁱ-rel-rename renameγ)

store-eq-inclusion :
  ∀ {Σ Σ′} → Σ′ ≡ Σ → StoreIncl Σ Σ′
store-eq-inclusion eq {x} x∈ = subst (x ∈_) (sym eq) x∈

rel-store-rename-projection-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  (renameρ : RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′) →
  StoreProjectionEmbeddingⁱ τ σ ρ ρ′
rel-store-rename-projection-embeddingⁱ renameρ =
  store-projection-embedding
    (store-eq-inclusion (leftStoreⁱ-rel-rename renameρ))
    (store-eq-inclusion (rightStoreⁱ-rel-rename renameρ))

rel-world-permutation-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RelWorldEmbeddingⁱ
    (forward πᴸ) (forward πᴿ) (backward πᴸ) (backward πᴿ)
    assm (forward-wf πᴸ) (forward-wf πᴿ)
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}
rel-world-permutation-embeddingⁱ {πᴸ = πᴸ} {πᴿ = πᴿ} perm =
  rel-world-embedding
    (backward-forward πᴸ) (backward-forward πᴿ)
    (left-cast-renamer perm) (right-cast-renamer perm)
    (rel-store-rename-embeddingⁱ (store-permutation perm))
    (ctx-permutation perm)

rel-world-source-typing-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M A} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  No• M →
  Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Θᴸ ∣ leftStoreⁱ ρ′ ∣ leftCtxⁱ γ′
    ⊢ renameᵗᵐ (forward πᴸ) M ⦂ renameᵗ (forward πᴸ) A
rel-world-source-typing-permute
    {Θᴸ = Θᴸ} {πᴸ = πᴸ} {ρ = ρ} {ρ′ = ρ′}
    {γ = γ} {γ′ = γ′} {M = M} {A = A} perm noM M⊢ =
  subst
    (λ Γ → Θᴸ ∣ leftStoreⁱ ρ′ ∣ Γ
      ⊢ renameᵗᵐ (forward πᴸ) M ⦂ renameᵗ (forward πᴸ) A)
    (sym (leftCtxⁱ-rel-rename (ctx-permutation perm)))
    (subst
      (λ Σ → Θᴸ ∣ Σ ∣ map (renameᵗ (forward πᴸ))
        (leftCtxⁱ γ) ⊢ renameᵗᵐ (forward πᴸ) M
        ⦂ renameᵗ (forward πᴸ) A)
      (sym (leftStoreⁱ-rel-rename (store-permutation perm)))
      (typing-renameᵀ
        {ρ = forward πᴸ} {ψ = backward πᴸ}
        (forward-wf πᴸ) (backward-forward πᴸ)
        (left-cast-renamer perm) noM M⊢))

rel-world-target-typing-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  No• M →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
  Θᴿ ∣ rightStoreⁱ ρ′ ∣ rightCtxⁱ γ′
    ⊢ renameᵗᵐ (forward πᴿ) M ⦂ renameᵗ (forward πᴿ) B
rel-world-target-typing-permute
    {Θᴿ = Θᴿ} {πᴿ = πᴿ} {ρ = ρ} {ρ′ = ρ′}
    {γ = γ} {γ′ = γ′} {M = M} {B = B} perm noM M⊢ =
  subst
    (λ Γ → Θᴿ ∣ rightStoreⁱ ρ′ ∣ Γ
      ⊢ renameᵗᵐ (forward πᴿ) M ⦂ renameᵗ (forward πᴿ) B)
    (sym (rightCtxⁱ-rel-rename (ctx-permutation perm)))
    (subst
      (λ Σ → Θᴿ ∣ Σ ∣ map (renameᵗ (forward πᴿ))
        (rightCtxⁱ γ) ⊢ renameᵗᵐ (forward πᴿ) M
        ⦂ renameᵗ (forward πᴿ) B)
      (sym (rightStoreⁱ-rel-rename (store-permutation perm)))
      (typing-renameᵀ
        {ρ = forward πᴿ} {ψ = backward πᴿ}
        (forward-wf πᴿ) (backward-forward πᴿ)
        (right-cast-renamer perm) noM M⊢))

rel-world-source-typing-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M A} →
  RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  No• M →
  Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Θᴸ ∣ leftStoreⁱ ρ′ ∣ leftCtxⁱ γ′
    ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A
rel-world-source-typing-embed
    {Θᴸ = Θᴸ} {τ = τ} {ψ = ψ} {hτ = hτ}
    {ρ = ρ} {ρ′ = ρ′}
    {γ = γ} {γ′ = γ′} {M = M} {A = A} emb noM M⊢ =
  subst
    (λ Γ → Θᴸ ∣ leftStoreⁱ ρ′ ∣ Γ
      ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A)
    (sym (leftCtxⁱ-rel-rename (embedding-context emb)))
    (subst
      (λ Σ → Θᴸ ∣ Σ ∣ map (renameᵗ τ) (leftCtxⁱ γ)
        ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A)
      (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))
      (typing-renameᵀ {ρ = τ} {ψ = ψ} hτ
        (left-embedding-inverse emb)
        (left-embedding-cast-renamer emb) noM M⊢))

rel-world-target-typing-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M B} →
  RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  No• M →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
  Θᴿ ∣ rightStoreⁱ ρ′ ∣ rightCtxⁱ γ′
    ⊢ renameᵗᵐ σ M ⦂ renameᵗ σ B
rel-world-target-typing-embed
    {Θᴿ = Θᴿ} {σ = σ} {φ = φ} {hσ = hσ}
    {ρ = ρ} {ρ′ = ρ′}
    {γ = γ} {γ′ = γ′} {M = M} {B = B} emb noM M⊢ =
  subst
    (λ Γ → Θᴿ ∣ rightStoreⁱ ρ′ ∣ Γ
      ⊢ renameᵗᵐ σ M ⦂ renameᵗ σ B)
    (sym (rightCtxⁱ-rel-rename (embedding-context emb)))
    (subst
      (λ Σ → Θᴿ ∣ Σ ∣ map (renameᵗ σ) (rightCtxⁱ γ)
        ⊢ renameᵗᵐ σ M ⦂ renameᵗ σ B)
      (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))
      (typing-renameᵀ {ρ = σ} {ψ = φ} hσ
        (right-embedding-inverse emb)
        (right-embedding-cast-renamer emb) noM M⊢))

rel-world-x-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {x A B p} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  γ ∋ x ⦂ ctx-imp A B p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (` x) ⊑ renameᵗᵐ σ (` x)
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p
rel-world-x-embedᵀ emb x∈
    with rel-ctx-rename-lookupⁱ (embedding-context emb) x∈
rel-world-x-embedᵀ emb x∈ | A′ , B′ , refl , refl , x∈′ =
  x⊑xᵀ x∈′

rel-world-embedding-ctx-∷ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {A B p} →
  RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′}
    {γ = ctx-imp A B p ∷ γ}
    {γ′ = ctx-imp (renameᵗ τ A) (renameᵗ σ B)
      (⊑-renameᵗ²ᵢ assm hτ hσ p) ∷ γ′}
rel-world-embedding-ctx-∷ⁱ emb =
  rel-world-embedding
    (left-embedding-inverse emb) (right-embedding-inverse emb)
    (left-embedding-cast-renamer emb)
    (right-embedding-cast-renamer emb)
    (store-embedding emb)
    (rel-ctx-rename-∷ refl refl (embedding-context emb))

rel-world-ƛ-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {N N′ A A′ B B′ pA pB} →
  RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣
      ctx-imp (renameᵗ τ A) (renameᵗ σ A′)
        (⊑-renameᵗ²ᵢ assm hτ hσ pA) ∷ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ renameᵗᵐ σ N′
    ⦂ renameᵗ τ B ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ pB →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ƛ N) ⊑ renameᵗᵐ σ (ƛ N′)
    ⦂ renameᵗ τ (A ⇒ B) ⊑ renameᵗ σ (A′ ⇒ B′)
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ (pA ↦ pB)
rel-world-ƛ-embedᵀ {τ = τ} {σ = σ} {hτ = hτ} {hσ = hσ}
    emb hA hA′ N⊑N′ =
  ƛ⊑ƛᵀ
    (renameᵗ-preserves-WfTy hA hτ)
    (renameᵗ-preserves-WfTy hA′ hσ) N⊑N′

rel-world-blame-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M A B p} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  No• M →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ blame ⊑ renameᵗᵐ σ M
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p
rel-world-blame-embedᵀ emb noM M⊢ =
  blame⊑ᵀ (rel-world-target-typing-embed emb noM M⊢)

rel-world-blame-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M A B p} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  No• M →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) blame
      ⊑ renameᵗᵐ (forward πᴿ) M
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p
rel-world-blame-permuteᵀ perm noM M⊢ =
  blame⊑ᵀ (rel-world-target-typing-permute perm noM M⊢)

rel-world-allocation-prefix-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′⁺ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B p} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ⁺} {ρ′ = ρ′⁺} {γ = γ} {γ′ = γ′}) →
  StoreImpPrefix ρ₀ ρ⁺ →
  (∀ {ρ₀′} → RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ₀} {ρ′ = ρ₀′} {γ = γ} {γ′ = γ′} →
    Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ₀′ ∣ γ′
      ⊢ᴺ renameᵗᵐ (forward πᴸ) M
        ⊑ renameᵗᵐ (forward πᴿ) M′
      ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B
      ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p) →
  No• M → No• M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′⁺ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p
rel-world-allocation-prefix-permuteᵀ
    perm prefix body-map noM noM′ M⊢ M′⊢
    with rel-store-rename-prefix-invⁱ
      prefix (store-permutation perm)
rel-world-allocation-prefix-permuteᵀ
    perm prefix body-map noM noM′ M⊢ M′⊢
    | ρ₀′ , renameρ₀ , prefix′ =
  allocation-prefixᵀ prefix′ (body-map base-perm)
    (rel-world-source-typing-permute perm noM M⊢)
    (rel-world-target-typing-permute perm noM′ M′⊢)
  where
  base-perm =
    rel-world-permutation
      (left-cast-renamer perm) (right-cast-renamer perm)
      renameρ₀ (ctx-permutation perm)

rel-world-allocation-prefix-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′⁺ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B p} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ⁺} {ρ′ = ρ′⁺} {γ = γ} {γ′ = γ′}) →
  StoreImpPrefix ρ₀ ρ⁺ →
  (∀ {ρ₀′} → RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ₀} {ρ′ = ρ₀′} {γ = γ} {γ′ = γ′} →
    Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ₀′ ∣ γ′
      ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
      ⦂ renameᵗ τ A ⊑ renameᵗ σ B
      ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p) →
  No• M → No• M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′⁺ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p
rel-world-allocation-prefix-embedᵀ
    emb prefix body-map noM noM′ M⊢ M′⊢
    with rel-store-embedding-prefix-invⁱ
      prefix (store-embedding emb)
rel-world-allocation-prefix-embedᵀ
    emb prefix body-map noM noM′ M⊢ M′⊢
    | ρ₀′ , emb₀ , prefix′ =
  allocation-prefixᵀ prefix′ (body-map base-emb)
    (rel-world-source-typing-embed emb noM M⊢)
    (rel-world-target-typing-embed emb noM′ M′⊢)
  where
  base-emb =
    rel-world-embedding
      (left-embedding-inverse emb) (right-embedding-inverse emb)
      (left-embedding-cast-renamer emb)
      (right-embedding-cast-renamer emb)
      emb₀ (embedding-context emb)

data LeftInsertion : Renameᵗ → Set where
  left-insertion-suc : LeftInsertion suc
  left-insertion-ext : ∀ {τ} →
    LeftInsertion τ → LeftInsertion (extᵗ τ)

left-insertion-mode :
  ∀ {τ} → LeftInsertion τ → ModeEnv → ModeEnv
left-insertion-mode left-insertion-suc μ = weakenCastᵈ μ
left-insertion-mode (left-insertion-ext ins) μ zero = μ zero
left-insertion-mode (left-insertion-ext ins) μ (suc X) =
  left-insertion-mode ins (λ Y → μ (suc Y)) X

mode≤-refl : ∀ m → mode≤ m m ≡ true
mode≤-refl id-only = refl
mode≤-refl tag-or-id = refl
mode≤-refl seal-or-id = refl

left-insertion-mode-rename :
  ∀ {τ} (ins : LeftInsertion τ) (μ : ModeEnv) →
  ModeRename τ μ (left-insertion-mode ins μ)
left-insertion-mode-rename left-insertion-suc μ =
  modeRename-suc-weakenCast
left-insertion-mode-rename (left-insertion-ext ins) μ zero =
  mode≤-refl (μ zero)
left-insertion-mode-rename (left-insertion-ext ins) μ (suc X) =
  left-insertion-mode-rename ins (λ Y → μ (suc Y)) X

left-insertion-cast-renamer :
  ∀ {τ} → LeftInsertion τ → CastModeRenamer τ
left-insertion-cast-renamer left-insertion-suc = castModeRenamer-suc
left-insertion-cast-renamer (left-insertion-ext ins) =
  castModeRenamer-ext (left-insertion-cast-renamer ins)

push-modeᵈ : Mode → ModeEnv → ModeEnv
push-modeᵈ id-only = extᵈ
push-modeᵈ tag-or-id = genᵈ
push-modeᵈ seal-or-id = instᵈ

cast-push-mode :
  ∀ {m μ} → CastMode μ → CastMode (push-modeᵈ m μ)
cast-push-mode {m = id-only} mode = cast-ext mode
cast-push-mode {m = tag-or-id} mode = cast-gen mode
cast-push-mode {m = seal-or-id} mode = cast-inst mode

swap-head-targetᵈ :
  ∀ {μ} → Mode → CastMode μ → ModeEnv
swap-head-targetᵈ m cast-tag-or-id =
  genᵈ (push-modeᵈ m tag-or-idᵈ)
swap-head-targetᵈ m (cast-ext {μ = μ} mode) =
  extᵈ (push-modeᵈ m μ)
swap-head-targetᵈ m (cast-gen {μ = μ} mode) =
  genᵈ (push-modeᵈ m μ)
swap-head-targetᵈ m (cast-inst {μ = μ} mode) =
  instᵈ (push-modeᵈ m μ)
swap-head-targetᵈ m (cast-weaken {μ = μ} mode) =
  extᵈ (push-modeᵈ m μ)

swap-head-target-mode :
  ∀ {m μ} (mode : CastMode μ) →
  CastMode (swap-head-targetᵈ m mode)
swap-head-target-mode {m = m} cast-tag-or-id =
  cast-gen (cast-push-mode {m = m} cast-tag-or-id)
swap-head-target-mode {m = m} (cast-ext mode) =
  cast-ext (cast-push-mode {m = m} mode)
swap-head-target-mode {m = m} (cast-gen mode) =
  cast-gen (cast-push-mode {m = m} mode)
swap-head-target-mode {m = m} (cast-inst mode) =
  cast-inst (cast-push-mode {m = m} mode)
swap-head-target-mode {m = m} (cast-weaken mode) =
  cast-ext (cast-push-mode {m = m} mode)

swap-mode-targetᵈ :
  ∀ {μ} → CastMode μ → ModeEnv
swap-mode-targetᵈ cast-tag-or-id = tag-or-idᵈ
swap-mode-targetᵈ (cast-ext mode) =
  swap-head-targetᵈ id-only mode
swap-mode-targetᵈ (cast-gen mode) =
  swap-head-targetᵈ tag-or-id mode
swap-mode-targetᵈ (cast-inst mode) =
  swap-head-targetᵈ seal-or-id mode
swap-mode-targetᵈ (cast-weaken mode) =
  swap-head-targetᵈ id-only mode

swap-mode-target-mode :
  ∀ {μ} (mode : CastMode μ) → CastMode (swap-mode-targetᵈ mode)
swap-mode-target-mode cast-tag-or-id = cast-tag-or-id
swap-mode-target-mode (cast-ext mode) =
  swap-head-target-mode mode
swap-mode-target-mode (cast-gen mode) =
  swap-head-target-mode mode
swap-mode-target-mode (cast-inst mode) =
  swap-head-target-mode mode
swap-mode-target-mode (cast-weaken mode) =
  swap-head-target-mode mode

swap-push-agrees :
  ∀ m n μ X →
  push-modeᵈ n (push-modeᵈ m μ) X ≡
    push-modeᵈ m (push-modeᵈ n μ) (swap01ᵗ X)
swap-push-agrees id-only id-only μ zero = refl
swap-push-agrees id-only id-only μ (suc zero) = refl
swap-push-agrees id-only id-only μ (suc (suc X)) = refl
swap-push-agrees id-only tag-or-id μ zero = refl
swap-push-agrees id-only tag-or-id μ (suc zero) = refl
swap-push-agrees id-only tag-or-id μ (suc (suc X)) = refl
swap-push-agrees id-only seal-or-id μ zero = refl
swap-push-agrees id-only seal-or-id μ (suc zero) = refl
swap-push-agrees id-only seal-or-id μ (suc (suc X)) = refl
swap-push-agrees tag-or-id id-only μ zero = refl
swap-push-agrees tag-or-id id-only μ (suc zero) = refl
swap-push-agrees tag-or-id id-only μ (suc (suc X)) = refl
swap-push-agrees tag-or-id tag-or-id μ zero = refl
swap-push-agrees tag-or-id tag-or-id μ (suc zero) = refl
swap-push-agrees tag-or-id tag-or-id μ (suc (suc X)) = refl
swap-push-agrees tag-or-id seal-or-id μ zero = refl
swap-push-agrees tag-or-id seal-or-id μ (suc zero) = refl
swap-push-agrees tag-or-id seal-or-id μ (suc (suc X)) = refl
swap-push-agrees seal-or-id id-only μ zero = refl
swap-push-agrees seal-or-id id-only μ (suc zero) = refl
swap-push-agrees seal-or-id id-only μ (suc (suc X)) = refl
swap-push-agrees seal-or-id tag-or-id μ zero = refl
swap-push-agrees seal-or-id tag-or-id μ (suc zero) = refl
swap-push-agrees seal-or-id tag-or-id μ (suc (suc X)) = refl
swap-push-agrees seal-or-id seal-or-id μ zero = refl
swap-push-agrees seal-or-id seal-or-id μ (suc zero) = refl
swap-push-agrees seal-or-id seal-or-id μ (suc (suc X)) = refl

swap-head-base-agrees :
  ∀ m X →
  genᵈ (push-modeᵈ m tag-or-idᵈ) X ≡
    push-modeᵈ m tag-or-idᵈ (swap01ᵗ X)
swap-head-base-agrees id-only zero = refl
swap-head-base-agrees id-only (suc zero) = refl
swap-head-base-agrees id-only (suc (suc X)) = refl
swap-head-base-agrees tag-or-id zero = refl
swap-head-base-agrees tag-or-id (suc zero) = refl
swap-head-base-agrees tag-or-id (suc (suc X)) = refl
swap-head-base-agrees seal-or-id zero = refl
swap-head-base-agrees seal-or-id (suc zero) = refl
swap-head-base-agrees seal-or-id (suc (suc X)) = refl

swap-head-weaken-agrees :
  ∀ m μ X →
  extᵈ (push-modeᵈ m μ) X ≡
    push-modeᵈ m (weakenCastᵈ μ) (swap01ᵗ X)
swap-head-weaken-agrees id-only μ zero = refl
swap-head-weaken-agrees id-only μ (suc zero) = refl
swap-head-weaken-agrees id-only μ (suc (suc X)) = refl
swap-head-weaken-agrees tag-or-id μ zero = refl
swap-head-weaken-agrees tag-or-id μ (suc zero) = refl
swap-head-weaken-agrees tag-or-id μ (suc (suc X)) = refl
swap-head-weaken-agrees seal-or-id μ zero = refl
swap-head-weaken-agrees seal-or-id μ (suc zero) = refl
swap-head-weaken-agrees seal-or-id μ (suc (suc X)) = refl

swap-head-target-agrees :
  ∀ {m μ} (mode : CastMode μ) X →
  swap-head-targetᵈ m mode X ≡ push-modeᵈ m μ (swap01ᵗ X)
swap-head-target-agrees {m = m} cast-tag-or-id X =
  swap-head-base-agrees m X
swap-head-target-agrees {m = m} (cast-ext {μ = μ} mode) X =
  swap-push-agrees m id-only μ X
swap-head-target-agrees {m = m} (cast-gen {μ = μ} mode) X =
  swap-push-agrees m tag-or-id μ X
swap-head-target-agrees {m = m} (cast-inst {μ = μ} mode) X =
  swap-push-agrees m seal-or-id μ X
swap-head-target-agrees {m = m} (cast-weaken {μ = μ} mode) X =
  swap-head-weaken-agrees m μ X

swap-mode-target-agrees :
  ∀ {μ} (mode : CastMode μ) X →
  swap-mode-targetᵈ mode X ≡ μ (swap01ᵗ X)
swap-mode-target-agrees cast-tag-or-id X = refl
swap-mode-target-agrees (cast-ext mode) X =
  swap-head-target-agrees mode X
swap-mode-target-agrees (cast-gen mode) X =
  swap-head-target-agrees mode X
swap-mode-target-agrees (cast-inst mode) X =
  swap-head-target-agrees mode X
swap-mode-target-agrees (cast-weaken mode) zero =
  swap-head-target-agrees mode zero
swap-mode-target-agrees (cast-weaken mode) (suc zero) =
  swap-head-target-agrees mode (suc zero)
swap-mode-target-agrees (cast-weaken mode) (suc (suc X)) =
  swap-head-target-agrees mode (suc (suc X))

swap01-involutiveᵐ : ∀ X → swap01ᵗ (swap01ᵗ X) ≡ X
swap01-involutiveᵐ zero = refl
swap01-involutiveᵐ (suc zero) = refl
swap01-involutiveᵐ (suc (suc X)) = refl

swap-mode-target-rename :
  ∀ {μ} (mode : CastMode μ) →
  ModeRename swap01ᵗ μ (swap-mode-targetᵈ mode)
swap-mode-target-rename {μ = μ} mode X =
  subst
    (λ m → mode≤ (μ X) m ≡ true)
    target-eq
    (mode≤-refl (μ X))
  where
  target-eq : μ X ≡ swap-mode-targetᵈ mode (swap01ᵗ X)
  target-eq =
    sym
      (trans
        (swap-mode-target-agrees mode (swap01ᵗ X))
        (cong μ (swap01-involutiveᵐ X)))

swap-mode-seal-source :
  ∀ {μ} (mode : CastMode μ) (α : TyVar) →
  sealModeAllowed (swap-mode-targetᵈ mode α) ≡ true →
  ∃[ b ]
    (sealModeAllowed (μ b) ≡ true × swap01ᵗ b ≡ α)
swap-mode-seal-source {μ = μ} mode α ok =
  swap01ᵗ α , source-ok , swap01-involutiveᵐ α
  where
  source-ok : sealModeAllowed (μ (swap01ᵗ α)) ≡ true
  source-ok =
    subst (λ m → sealModeAllowed m ≡ true)
      (swap-mode-target-agrees mode α) ok

castModeRenamer-swap01 : CastModeRenamer swap01ᵗ
castModeRenamer-swap01 =
  record
    { targetᵈ = swap-mode-targetᵈ
    ; target-mode = swap-mode-target-mode
    ; target-rename = swap-mode-target-rename
    ; target-seal-source = swap-mode-seal-source
    }

castModeRenamer-id : CastModeRenamer (λ X → X)
castModeRenamer-id =
  record
    { targetᵈ = λ {μ} mode → μ
    ; target-mode = λ mode → mode
    ; target-rename = λ {μ} mode X → mode≤-refl (μ X)
    ; target-seal-source = λ mode α ok → α , ok , refl
    }

mode≤-trans :
  ∀ m n p →
  mode≤ m n ≡ true →
  mode≤ n p ≡ true →
  mode≤ m p ≡ true
mode≤-trans id-only id-only id-only mn np = refl
mode≤-trans id-only id-only tag-or-id mn np = refl
mode≤-trans id-only id-only seal-or-id mn np = refl
mode≤-trans id-only tag-or-id id-only mn ()
mode≤-trans id-only tag-or-id tag-or-id mn np = refl
mode≤-trans id-only tag-or-id seal-or-id mn ()
mode≤-trans id-only seal-or-id id-only mn ()
mode≤-trans id-only seal-or-id tag-or-id mn ()
mode≤-trans id-only seal-or-id seal-or-id mn np = refl
mode≤-trans tag-or-id id-only id-only () np
mode≤-trans tag-or-id id-only tag-or-id () np
mode≤-trans tag-or-id id-only seal-or-id () np
mode≤-trans tag-or-id tag-or-id id-only mn ()
mode≤-trans tag-or-id tag-or-id tag-or-id mn np = refl
mode≤-trans tag-or-id tag-or-id seal-or-id mn ()
mode≤-trans tag-or-id seal-or-id id-only () np
mode≤-trans tag-or-id seal-or-id tag-or-id () np
mode≤-trans tag-or-id seal-or-id seal-or-id () np
mode≤-trans seal-or-id id-only id-only () np
mode≤-trans seal-or-id id-only tag-or-id () np
mode≤-trans seal-or-id id-only seal-or-id () np
mode≤-trans seal-or-id tag-or-id id-only () np
mode≤-trans seal-or-id tag-or-id tag-or-id () np
mode≤-trans seal-or-id tag-or-id seal-or-id () np
mode≤-trans seal-or-id seal-or-id id-only mn ()
mode≤-trans seal-or-id seal-or-id tag-or-id mn ()
mode≤-trans seal-or-id seal-or-id seal-or-id mn np = refl

modeRename-compose :
  ∀ {τ σ μ ν ξ} →
  ModeRename τ μ ν →
  ModeRename σ ν ξ →
  ModeRename (λ X → σ (τ X)) μ ξ
modeRename-compose
    {τ = τ} {σ = σ} {μ = μ} {ν = nu} {ξ = ξ} rel₁ rel₂ X =
  mode≤-trans (μ X) (nu (τ X)) (ξ (σ (τ X)))
    (rel₁ X) (rel₂ (τ X))

castModeRenamer-compose :
  ∀ {τ σ} →
  CastModeRenamer τ →
  CastModeRenamer σ →
  CastModeRenamer (λ X → σ (τ X))
castModeRenamer-compose {τ = τ} {σ = σ} η θ =
  record
    { targetᵈ = target₂
    ; target-mode = target-mode₂
    ; target-rename = target-rename₂
    ; target-seal-source = target-seal-source₂
    }
  where
  target₂ : ∀ {μ} → CastMode μ → ModeEnv
  target₂ mode =
    CastModeRenamer.targetᵈ θ (CastModeRenamer.target-mode η mode)

  target-mode₂ :
    ∀ {μ} (mode : CastMode μ) → CastMode (target₂ mode)
  target-mode₂ mode =
    CastModeRenamer.target-mode θ
      (CastModeRenamer.target-mode η mode)

  target-rename₂ :
    ∀ {μ} (mode : CastMode μ) →
    ModeRename (λ X → σ (τ X)) μ (target₂ mode)
  target-rename₂ {μ = μ} mode =
    modeRename-compose {τ = τ} {σ = σ} {μ = μ}
      {ν = CastModeRenamer.targetᵈ η mode}
      {ξ = target₂ mode}
      (CastModeRenamer.target-rename η mode)
      (CastModeRenamer.target-rename θ
        (CastModeRenamer.target-mode η mode))

  target-seal-source₂ :
    ∀ {μ} (mode : CastMode μ) (α : TyVar) →
    sealModeAllowed (target₂ mode α) ≡ true →
    ∃[ a ]
      (sealModeAllowed (μ a) ≡ true × σ (τ a) ≡ α)
  target-seal-source₂ mode α ok =
    let b , ok-b , eq-b = CastModeRenamer.target-seal-source θ
          (CastModeRenamer.target-mode η mode) α ok
        a , ok-a , eq-a =
          CastModeRenamer.target-seal-source η mode b ok-b in
    a , ok-a , trans (cong σ eq-a) eq-b

permuted-modeᵈ :
  ∀ {Δ Θ} → TyPermutation Δ Θ → ModeEnv → ModeEnv
permuted-modeᵈ π μ X = μ (backward π X)

permuted-mode-rename :
  ∀ {Δ Θ} (π : TyPermutation Δ Θ) μ →
  ModeRename (forward π) μ (permuted-modeᵈ π μ)
permuted-mode-rename π μ X =
  subst
    (λ m → mode≤ (μ X) m ≡ true)
    (sym (cong μ (backward-forward π X)))
    (mode≤-refl (μ X))

permuted-mode-seal-source :
  ∀ {Δ Θ} (π : TyPermutation Δ Θ) μ α →
  sealModeAllowed (permuted-modeᵈ π μ α) ≡ true →
  ∃[ b ]
    (sealModeAllowed (μ b) ≡ true × forward π b ≡ α)
permuted-mode-seal-source π μ α ok =
  backward π α , ok , forward-backward π α

embedded-modeᵈ : Renameᵗ → ModeEnv → ModeEnv
embedded-modeᵈ ψ μ X = μ (ψ X)

embedded-mode-rename :
  ∀ {τ ψ} →
  RenameLeftInverse τ ψ →
  ∀ μ → ModeRename τ μ (embedded-modeᵈ ψ μ)
embedded-mode-rename {τ = τ} {ψ = ψ} inv μ X =
  subst
    (λ m → mode≤ (μ X) m ≡ true)
    (sym (cong μ (inv X)))
    (mode≤-refl (μ X))

left-reveal-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  RevealConversion (embedded-modeᵈ ψ μ) Θᴸ (leftStoreⁱ ρ′)
    (τ α) (renameᵗ τ X) (renameᶜ τ c)
    (renameᵗ τ A) (renameᵗ τ B)
left-reveal-rel-embed
    {τ = τ} {ψ = ψ} {hτ = hτ} {μ = μ} emb conv =
  subst (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))
    (rename-reveal-conversion hτ
      (embedded-mode-rename {τ = τ} {ψ = ψ}
        (left-embedding-inverse emb) μ) conv)

right-reveal-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ β X c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ) β X c A B →
  RevealConversion (embedded-modeᵈ φ μ) Θᴿ (rightStoreⁱ ρ′)
    (σ β) (renameᵗ σ X) (renameᶜ σ c)
    (renameᵗ σ A) (renameᵗ σ B)
right-reveal-rel-embed
    {σ = σ} {φ = φ} {hσ = hσ} {μ = μ} emb conv =
  subst (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))
    (rename-reveal-conversion hσ
      (embedded-mode-rename {τ = σ} {ψ = φ}
        (right-embedding-inverse emb) μ) conv)

left-conceal-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  ConcealConversion (embedded-modeᵈ ψ μ) Θᴸ (leftStoreⁱ ρ′)
    (τ α) (renameᵗ τ X) (renameᶜ τ c)
    (renameᵗ τ A) (renameᵗ τ B)
left-conceal-rel-embed
    {τ = τ} {ψ = ψ} {hτ = hτ} {μ = μ} emb conv =
  subst (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))
    (rename-conceal-conversion hτ
      (embedded-mode-rename {τ = τ} {ψ = ψ}
        (left-embedding-inverse emb) μ) conv)

right-conceal-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ β X c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ) β X c A B →
  ConcealConversion (embedded-modeᵈ φ μ) Θᴿ (rightStoreⁱ ρ′)
    (σ β) (renameᵗ σ X) (renameᶜ σ c)
    (renameᵗ σ A) (renameᵗ σ B)
right-conceal-rel-embed
    {σ = σ} {φ = φ} {hσ = hσ} {μ = μ} emb conv =
  subst (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))
    (rename-conceal-conversion hσ
      (embedded-mode-rename {τ = σ} {ψ = φ}
        (right-embedding-inverse emb) μ) conv)

left-reveal-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  RevealConversion (permuted-modeᵈ πᴸ μ) Θᴸ
    (leftStoreⁱ ρ′) (forward πᴸ α) (renameᵗ (forward πᴸ) X)
    (renameᶜ (forward πᴸ) c) (renameᵗ (forward πᴸ) A)
    (renameᵗ (forward πᴸ) B)
left-reveal-rel-permute {πᴸ = πᴸ} perm conv =
  subst (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (leftStoreⁱ-rel-rename (store-permutation perm)))
    (rename-reveal-conversion (forward-wf πᴸ)
      (permuted-mode-rename πᴸ _) conv)

right-reveal-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ) α X c A B →
  RevealConversion (permuted-modeᵈ πᴿ μ) Θᴿ
    (rightStoreⁱ ρ′) (forward πᴿ α) (renameᵗ (forward πᴿ) X)
    (renameᶜ (forward πᴿ) c) (renameᵗ (forward πᴿ) A)
    (renameᵗ (forward πᴿ) B)
right-reveal-rel-permute {πᴿ = πᴿ} perm conv =
  subst (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (rightStoreⁱ-rel-rename (store-permutation perm)))
    (rename-reveal-conversion (forward-wf πᴿ)
      (permuted-mode-rename πᴿ _) conv)

left-conceal-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  ConcealConversion (permuted-modeᵈ πᴸ μ) Θᴸ
    (leftStoreⁱ ρ′) (forward πᴸ α) (renameᵗ (forward πᴸ) X)
    (renameᶜ (forward πᴸ) c) (renameᵗ (forward πᴸ) A)
    (renameᵗ (forward πᴸ) B)
left-conceal-rel-permute {πᴸ = πᴸ} perm conv =
  subst (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (leftStoreⁱ-rel-rename (store-permutation perm)))
    (rename-conceal-conversion (forward-wf πᴸ)
      (permuted-mode-rename πᴸ _) conv)

right-conceal-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ) α X c A B →
  ConcealConversion (permuted-modeᵈ πᴿ μ) Θᴿ
    (rightStoreⁱ ρ′) (forward πᴿ α) (renameᵗ (forward πᴿ) X)
    (renameᶜ (forward πᴿ) c) (renameᵗ (forward πᴿ) A)
    (renameᵗ (forward πᴿ) B)
right-conceal-rel-permute {πᴿ = πᴿ} perm conv =
  subst (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (rightStoreⁱ-rel-rename (store-permutation perm)))
    (rename-conceal-conversion (forward-wf πᴿ)
      (permuted-mode-rename πᴿ _) conv)

swap-mode-target-inst-ext :
  ∀ {μ} (mode : CastMode μ) →
  swap-mode-targetᵈ (cast-inst (cast-ext mode)) ≡
    extᵈ (instᵈ μ)
swap-mode-target-inst-ext mode = refl

swap-mode-target-ext-inst :
  ∀ {μ} (mode : CastMode μ) →
  swap-mode-targetᵈ (cast-ext (cast-inst mode)) ≡
    instᵈ (extᵈ μ)
swap-mode-target-ext-inst mode = refl

swap-mode-target-gen-ext :
  ∀ {μ} (mode : CastMode μ) →
  swap-mode-targetᵈ (cast-gen (cast-ext mode)) ≡
    extᵈ (genᵈ μ)
swap-mode-target-gen-ext mode = refl

swap-mode-target-ext-gen :
  ∀ {μ} (mode : CastMode μ) →
  swap-mode-targetᵈ (cast-ext (cast-gen mode)) ≡
    genᵈ (extᵈ μ)
swap-mode-target-ext-gen mode = refl

no-crossed-up-mode-rename-id :
  ModeRename suc
    (extᵈ (instᵈ tag-or-idᵈ)) id-onlyᵈ → ⊥
no-crossed-up-mode-rename-id rel with rel (suc zero)
no-crossed-up-mode-rename-id rel | ()

no-crossed-up-mode-rename-same :
  ModeRename suc
    (extᵈ (instᵈ tag-or-idᵈ))
    (extᵈ (instᵈ tag-or-idᵈ)) → ⊥
no-crossed-up-mode-rename-same rel with rel (suc zero)
no-crossed-up-mode-rename-same rel | ()

no-crossed-up-mode-rename-opposite :
  ModeRename suc
    (extᵈ (instᵈ tag-or-idᵈ))
    (instᵈ (extᵈ tag-or-idᵈ)) → ⊥
no-crossed-up-mode-rename-opposite rel with rel (suc zero)
no-crossed-up-mode-rename-opposite rel | ()

crossed-left-mode-rename-opposite :
  ModeRename suc
    (instᵈ (extᵈ tag-or-idᵈ))
    (extᵈ (instᵈ tag-or-idᵈ))
crossed-left-mode-rename-opposite zero = refl
crossed-left-mode-rename-opposite (suc zero) = refl
crossed-left-mode-rename-opposite (suc (suc X)) = refl

swap01-after-suc :
  ∀ X → swap01ᵗ (suc X) ≡ extᵗ suc X
swap01-after-suc zero = refl
swap01-after-suc (suc X) = refl

swap01-after-ext-suc :
  ∀ X → swap01ᵗ (extᵗ suc X) ≡ suc X
swap01-after-ext-suc zero = refl
swap01-after-ext-suc (suc X) = refl

TyRenameWf-compose :
  ∀ {Δ Θ Ω τ υ} →
  TyRenameWf Δ Θ τ →
  TyRenameWf Θ Ω υ →
  TyRenameWf Δ Ω (λ X → υ (τ X))
TyRenameWf-compose hτ hυ X<Δ = hυ (hτ X<Δ)

renameLeftInverse-compose :
  ∀ {τ υ ψ ξ} →
  RenameLeftInverse τ ψ →
  RenameLeftInverse υ ξ →
  RenameLeftInverse (λ X → υ (τ X)) (λ X → ψ (ξ X))
renameLeftInverse-compose
    {τ = τ} {ψ = ψ} inv₁ inv₂ X =
  trans (cong ψ (inv₂ (τ X))) (inv₁ X)

rename-assm²-membership-composeᵢ :
  ∀ {Φ Ψ Ω τ σ υ ω} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ) →
  (∀ {a} → a ∈ Ψ → rename-assm²ᵢ υ ω a ∈ Ω) →
  ∀ {a} → a ∈ Φ →
  rename-assm²ᵢ (λ X → υ (τ X)) (λ X → ω (σ X)) a ∈ Ω
rename-assm²-membership-composeᵢ
    {Ω = Ω} {τ = τ} {σ = σ} {υ = υ} {ω = ω} assm₁ assm₂ {a} a∈ =
  subst (_∈ Ω) (rename-assm²-composeᵢ τ σ υ ω a)
    (assm₂ (assm₁ a∈))

store-inclusion-rename-compose :
  ∀ τ υ {Σ₀ Σ₁ Σ₂} →
  StoreIncl (renameStoreᵗ τ Σ₀) Σ₁ →
  StoreIncl (renameStoreᵗ υ Σ₁) Σ₂ →
  StoreIncl (renameStoreᵗ (λ X → υ (τ X)) Σ₀) Σ₂
store-inclusion-rename-compose τ υ {Σ₀ = Σ₀} incl₁ incl₂ {x} x∈ =
  incl₂
    (renameStoreᵗ-incl υ incl₁
      (subst (x ∈_) (sym (renameStoreᵗ-compose τ υ Σ₀)) x∈))

store-projection-embedding-composeⁱ :
  ∀ {Φ Ψ Ω Δᴸ Δᴿ Θᴸ Θᴿ Ξᴸ Ξᴿ τ σ υ ω}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ₂ : StoreImp Ω Ξᴸ Ξᴿ} →
  StoreProjectionEmbeddingⁱ τ σ ρ₀ ρ₁ →
  StoreProjectionEmbeddingⁱ υ ω ρ₁ ρ₂ →
  StoreProjectionEmbeddingⁱ
    (λ X → υ (τ X)) (λ X → ω (σ X)) ρ₀ ρ₂
store-projection-embedding-composeⁱ
    {τ = τ} {σ = σ} {υ = υ} {ω = ω} emb₁ emb₂ =
  store-projection-embedding
    (store-inclusion-rename-compose τ υ
      (left-store-inclusion emb₁) (left-store-inclusion emb₂))
    (store-inclusion-rename-compose σ ω
      (right-store-inclusion emb₁) (right-store-inclusion emb₂))

rel-world-embedding-[]-composeⁱ :
  ∀ {Φ Ψ Ω Δᴸ Δᴿ Θᴸ Θᴿ Ξᴸ Ξᴿ}
    {τ σ ψ φ υ ω ξ ζ}
    {assm₁ : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {assm₂ : ∀ {a} → a ∈ Ψ → rename-assm²ᵢ υ ω a ∈ Ω}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {hυ : TyRenameWf Θᴸ Ξᴸ υ} {hω : TyRenameWf Θᴿ Ξᴿ ω}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ₂ : StoreImp Ω Ξᴸ Ξᴿ} →
  RelWorldEmbeddingⁱ τ σ ψ φ assm₁ hτ hσ
    {ρ = ρ₀} {ρ′ = ρ₁} {γ = []} {γ′ = []} →
  RelWorldEmbeddingⁱ υ ω ξ ζ assm₂ hυ hω
    {ρ = ρ₁} {ρ′ = ρ₂} {γ = []} {γ′ = []} →
  RelWorldEmbeddingⁱ
    (λ X → υ (τ X)) (λ X → ω (σ X))
    (λ X → ψ (ξ X)) (λ X → φ (ζ X))
    (rename-assm²-membership-composeᵢ assm₁ assm₂)
    (TyRenameWf-compose hτ hυ) (TyRenameWf-compose hσ hω)
    {ρ = ρ₀} {ρ′ = ρ₂} {γ = []} {γ′ = []}
rel-world-embedding-[]-composeⁱ
    {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
    {υ = υ} {ω = ω} {ξ = ξ} {ζ = ζ} emb₁ emb₂ =
  rel-world-embedding
    (renameLeftInverse-compose {τ = τ} {υ = υ} {ψ = ψ} {ξ = ξ}
      (left-embedding-inverse emb₁) (left-embedding-inverse emb₂))
    (renameLeftInverse-compose {τ = σ} {υ = ω} {ψ = φ} {ξ = ζ}
      (right-embedding-inverse emb₁) (right-embedding-inverse emb₂))
    (castModeRenamer-compose
      (left-embedding-cast-renamer emb₁)
      (left-embedding-cast-renamer emb₂))
    (castModeRenamer-compose
      (right-embedding-cast-renamer emb₁)
      (right-embedding-cast-renamer emb₂))
    (rel-store-embedding-composeⁱ
      (store-embedding emb₁) (store-embedding emb₂))
    rel-ctx-rename-[]

renameᵗ-swap01-after-suc :
  ∀ A → renameᵗ swap01ᵗ (⇑ᵗ A) ≡ renameᵗ (extᵗ suc) A
renameᵗ-swap01-after-suc A =
  trans (renameᵗ-compose suc swap01ᵗ A)
    (rename-cong swap01-after-suc A)

renameᵗᵐ-swap01-after-suc :
  ∀ M →
  renameᵗᵐ swap01ᵗ (⇑ᵗᵐ M) ≡ renameᵗᵐ (extᵗ suc) M
renameᵗᵐ-swap01-after-suc M =
  trans (renameᵗᵐ-compose suc swap01ᵗ M)
    (renameᵗᵐ-cong swap01-after-suc M)

renameᵗ-swap01-after-ext-suc :
  ∀ A → renameᵗ swap01ᵗ (renameᵗ (extᵗ suc) A) ≡ ⇑ᵗ A
renameᵗ-swap01-after-ext-suc A =
  trans (renameᵗ-compose (extᵗ suc) swap01ᵗ A)
    (rename-cong swap01-after-ext-suc A)

renameᵗᵐ-swap01-after-ext-suc :
  ∀ M →
  renameᵗᵐ swap01ᵗ (renameᵗᵐ (extᵗ suc) M) ≡ ⇑ᵗᵐ M
renameᵗᵐ-swap01-after-ext-suc M =
  trans (renameᵗᵐ-compose (extᵗ suc) swap01ᵗ M)
    (renameᵗᵐ-cong swap01-after-ext-suc M)

renameᵗᵐ-pointed-bullet :
  ∀ τ L →
  renameᵗᵐ (extᵗ τ) ((⇑ᵗᵐ L) •) ≡
    (⇑ᵗᵐ (renameᵗᵐ τ L)) •
renameᵗᵐ-pointed-bullet τ L =
  cong _• (renameᵗᵐ-ext-suc-comm τ L)

⇑ᴿᵢ-membership :
  ∀ {Φ a} →
  a ∈ Φ →
  ⇑ᴿᵢₐ a ∈ ⇑ᴿᵢ Φ
⇑ᴿᵢ-membership (here refl) = here refl
⇑ᴿᵢ-membership (there a∈) = there (⇑ᴿᵢ-membership a∈)

rename-assm²-⇑ᴿ²ᵢ :
  ∀ {Φ Ψ τ σ} →
  (∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ) →
  ∀ {a} → a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ τ (extᵗ σ) a ∈ ⇑ᴿᵢ Ψ
rename-assm²-⇑ᴿ²ᵢ {Φ = []} assm ()
rename-assm²-⇑ᴿ²ᵢ {Φ = (X ˣ⊑★) ∷ Φ} assm (here refl) =
  ⇑ᴿᵢ-membership (assm (here refl))
rename-assm²-⇑ᴿ²ᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} assm (here refl) =
  ⇑ᴿᵢ-membership (assm (here refl))
rename-assm²-⇑ᴿ²ᵢ {Φ = (X ˣ⊑★) ∷ Φ} assm (there a∈) =
  rename-assm²-⇑ᴿ²ᵢ (λ b∈ → assm (there b∈)) a∈
rename-assm²-⇑ᴿ²ᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} assm (there a∈) =
  rename-assm²-⇑ᴿ²ᵢ (λ b∈ → assm (there b∈)) a∈

rename-assm²-⇑ᴿᵢ :
  ∀ {Φ Ψ τ} →
  (∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  ∀ {a} → a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ τ (λ X → X) a ∈ ⇑ᴿᵢ Ψ
rename-assm²-⇑ᴿᵢ {Φ = []} assm ()
rename-assm²-⇑ᴿᵢ {Φ = (X ˣ⊑★) ∷ Φ} assm (here refl) =
  ⇑ᴿᵢ-membership (assm (here refl))
rename-assm²-⇑ᴿᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} assm (here refl) =
  ⇑ᴿᵢ-membership (assm (here refl))
rename-assm²-⇑ᴿᵢ {Φ = (X ˣ⊑★) ∷ Φ} assm (there a∈) =
  rename-assm²-⇑ᴿᵢ (λ b∈ → assm (there b∈)) a∈
rename-assm²-⇑ᴿᵢ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} assm (there a∈) =
  rename-assm²-⇑ᴿᵢ (λ b∈ → assm (there b∈)) a∈

rename-assm²-source-under-right-tailᵢ :
  ∀ {Φ a} →
  a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ suc (λ X → X) a ∈ ⇑ᴿᵢ (⇑ᴸᵢ Φ)
rename-assm²-source-under-right-tailᵢ {Φ = []} ()
rename-assm²-source-under-right-tailᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (here refl) =
  here refl
rename-assm²-source-under-right-tailᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (here refl) =
  here refl
rename-assm²-source-under-right-tailᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (there a∈) =
  there (rename-assm²-source-under-right-tailᵢ a∈)
rename-assm²-source-under-right-tailᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (there a∈) =
  there (rename-assm²-source-under-right-tailᵢ a∈)

rename-assm²-source-under-rightᵢ :
  ∀ {Φ a} →
  a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ suc (λ X → X) a ∈
    ⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
rename-assm²-source-under-rightᵢ a∈ =
  there (rename-assm²-source-under-right-tailᵢ a∈)

⊑-source-under-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ B ⊣ suc Δᴿ
⊑-source-under-rightᵢ =
  ⊑-rename-leftᵢ suc rename-assm²-source-under-rightᵢ
    TyRenameWf-suc

⊑-target-under-leftᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
    ∣ suc Δᴸ ⊢ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
⊑-target-under-leftᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} p =
  subst
    (λ S → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      ∣ suc Δᴸ ⊢ S ⊑ ⇑ᵗ B ⊣ suc Δᴿ)
    (renameᵗ-ext-id A)
    (⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᴸᵢ rename-assm²-target-rightᵢ)
      (TyRenameWf-ext (λ X<Δ → X<Δ))
      TyRenameWf-suc p)

right-under-left-ctx-eq :
  ∀ Φ →
  ⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ≡
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
right-under-left-ctx-eq Φ =
  cong ((zero ˣ⊑★) ∷_) (sym (⇑ᴸᵢ-⇑ᴿᵢ-commute Φ))

⊑ᵖ-target-under-leftᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
    ∣ suc Δᴸ ⊢ A ⊑ᵖ ⇑ᵗ B ⊣ suc Δᴿ
⊑ᵖ-target-under-leftᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} q =
  subst
    (λ S → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      ∣ suc Δᴸ ⊢ S ⊑ᵖ ⇑ᵗ B ⊣ suc Δᴿ)
    (renameᵗ-ext-id A)
    (⊑ᵖ-rename²ᵢ
      (rename-assm²-⇑ᴸᵢ rename-assm²-target-rightᵢ)
      (TyRenameWf-ext (λ X<Δ → X<Δ))
      TyRenameWf-suc q)

⊑-target-under-left-arrowᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    (pA : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (pB : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  ⊑-target-under-leftᵢ (pA ↦ pB) ≡
    ⊑-target-under-leftᵢ pA ↦ ⊑-target-under-leftᵢ pB
⊑-target-under-left-arrowᵢ {A = A} {B = B} pA pB
    rewrite equality-proof-unique
      (renameᵗ-ext-id (A ⇒ B))
      (cong₂ _⇒_ (renameᵗ-ext-id A) (renameᵗ-ext-id B)) =
  transport-arrow-⊑ᵢ
    (renameᵗ-ext-id A) refl (renameᵗ-ext-id B) refl

⊑-target-lift-right-ν-shapeᵢ :
  ∀ {Φ Δᴸ Δᴿ C B}
    {{safe : NonVar C}}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ}
    (occ : occurs zero C ≡ true) →
  ∃[ occ′ ]
    ⊑-target-lift-rightᵢ (ν safe occ p) ≡
      ν {A = C} safe occ′ (⊑-target-under-leftᵢ p)
⊑-target-lift-right-ν-shapeᵢ {C = C} {{safe}} occ
    rewrite nonVar-unique
      (subst NonVar (renameᵗ-ext-id C)
        (renameNonVar (extᵗ (λ X → X)) safe)) safe
      | equality-proof-unique
      (renameᵗ-id (`∀ C)) (cong `∀ (renameᵗ-ext-id C)) =
  _ ,
  transport-ν-⊑ᵢ
    {C₀ = renameᵗ (extᵗ (λ X → X)) C}
    {C₁ = C}
    {{safe₀ = renameNonVar (extᵗ (λ X → X)) safe}}
    {{safe₁ = safe}}
    (renameᵗ-ext-id C)
    (trans (occurs-zero-rename-ext (λ X → X) C) occ)

⊑-target-lift-right-source-nuᵢ :
  ∀ {Φ Δᴸ Δᴿ C B}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ) →
  SourceNuIndex (⊑-target-lift-rightᵢ (ν safe occ p))
⊑-target-lift-right-source-nuᵢ safe occ p
    with ⊑-target-lift-right-ν-shapeᵢ {{safe}} occ
⊑-target-lift-right-source-nuᵢ safe occ p
    | occ′ , shape =
  source-nu-index safe occ′ (⊑-target-under-leftᵢ p) shape

rel-store-rename-lift-rightⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  RelStoreRenameⁱ τ σ assm hτ hσ ρ ρ′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  ∃[ ρ′ᴿ ]
    LiftRightStoreⁱ (⇑ᴿᵢ Ψ) ρ′ ρ′ᴿ ×
    RelStoreRenameⁱ
      τ (extᵗ σ) (rename-assm²-⇑ᴿ²ᵢ assm)
      hτ (TyRenameWf-ext hσ) ρᴿ ρ′ᴿ
rel-store-rename-lift-rightⁱ
    rel-store-rename-[] lift-right-store-[] =
  [] , lift-right-store-[] , rel-store-rename-[]
rel-store-rename-lift-rightⁱ
    (rel-store-rename-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-right-store-∷ {p′ = pᴿ} shapeᴿ liftρ)
    with rel-store-rename-lift-rightⁱ renameρ liftρ
rel-store-rename-lift-rightⁱ
    {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-rename-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-right-store-∷
      {A = A} {B = B} {p′ = pᴿ} shapeᴿ liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-matched α′ A′ (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ)
      (trans shapeᴿ
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftρ′ ,
  rel-store-rename-matched
    eqα eqA (cong suc eqβ) eqBᴿ renameρᴿ
  where
  eqBᴿ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqBᴿ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-rename-lift-rightⁱ
    (rel-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-right-store-left liftρ)
    with rel-store-rename-lift-rightⁱ renameρ liftρ
rel-store-rename-lift-rightⁱ
    (rel-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-right-store-left liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-left α′ A′ hA′ ∷ ρ′ᴿ ,
  lift-right-store-left liftρ′ ,
  rel-store-rename-left eqα eqA renameρᴿ
rel-store-rename-lift-rightⁱ
    (rel-store-rename-right {β′ = β′} {B′ = B′} {hB′ = hB′}
      eqβ eqB renameρ)
    (lift-right-store-right liftρ)
    with rel-store-rename-lift-rightⁱ renameρ liftρ
rel-store-rename-lift-rightⁱ {σ = σ}
    (rel-store-rename-right {β′ = β′} {B′ = B′} {hB′ = hB′}
      eqβ eqB renameρ)
    (lift-right-store-right {B = B} liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-right (suc β′) (⇑ᵗ B′)
      (renameᵗ-preserves-WfTy hB′ TyRenameWf-suc) ∷ ρ′ᴿ ,
  lift-right-store-right liftρ′ ,
  rel-store-rename-right (cong suc eqβ) eqBᴿ renameρᴿ
  where
  eqBᴿ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqBᴿ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-rename-lift-rightⁱ
    (rel-store-rename-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-right-store-link {p′ = pᴿ} shapeᴿ liftρ)
    with rel-store-rename-lift-rightⁱ renameρ liftρ
rel-store-rename-lift-rightⁱ
    {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-rename-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′} {p = p}
      eqα eqA eqβ eqB renameρ)
    (lift-right-store-link
      {A = A} {B = B} {p′ = pᴿ} shapeᴿ liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-link α′ A′ (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-link
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ)
      (trans shapeᴿ
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftρ′ ,
  rel-store-rename-link eqα eqA (cong suc eqβ) eqBᴿ renameρᴿ
  where
  eqBᴿ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqBᴿ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))

rel-store-embedding-lift-rightⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  ∃[ ρ′ᴿ ]
    LiftRightStoreⁱ (⇑ᴿᵢ Ψ) ρ′ ρ′ᴿ ×
    RelStoreEmbeddingⁱ τ (extᵗ σ) ρᴿ ρ′ᴿ
rel-store-embedding-lift-rightⁱ
    rel-store-embedding-[] lift-right-store-[] =
  [] , lift-right-store-[] , rel-store-embedding-[]
rel-store-embedding-lift-rightⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-right-store-∷ {p′ = pᴿ} shapeᴿ liftρ)
    with rel-store-embedding-lift-rightⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-rightⁱ
    {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-right-store-∷
      {A = A} {B = B} {p′ = pᴿ} shapeᴿ liftρ)
    | ρ′ᴿ , liftρ′ , embᴿ =
  store-matched α′ A′ (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ)
      (trans shapeᴿ (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-matched
    eqα eqA (cong suc eqβ) eqBᴿ
    (⊑-rename-at-shapeᵢ
      (rename-assm²-⇑ᴿ²ᵢ assm)
      hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ)
    embᴿ
  where
  eqBᴿ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqBᴿ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-embedding-lift-rightⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-right-store-left liftρ)
    with rel-store-embedding-lift-rightⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-rightⁱ
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-right-store-left liftρ)
    | ρ′ᴿ , liftρ′ , embᴿ =
  store-left α′ A′ hA′ ∷ ρ′ᴿ ,
  lift-right-store-left liftρ′ ,
  rel-store-embedding-left eqα eqA embᴿ
rel-store-embedding-lift-rightⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-right-store-right liftρ)
    with rel-store-embedding-lift-rightⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-rightⁱ {σ = σ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-right-store-right {B = B} liftρ)
    | ρ′ᴿ , liftρ′ , embᴿ =
  store-right (suc β′) (⇑ᵗ B′)
      (renameᵗ-preserves-WfTy hB′ TyRenameWf-suc) ∷ ρ′ᴿ ,
  lift-right-store-right liftρ′ ,
  rel-store-embedding-right (cong suc eqβ) eqBᴿ embᴿ
  where
  eqBᴿ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqBᴿ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-embedding-lift-rightⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-right-store-link {p′ = pᴿ} shapeᴿ liftρ)
    with rel-store-embedding-lift-rightⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-lift-rightⁱ
    {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-right-store-link
      {A = A} {B = B} {p′ = pᴿ} shapeᴿ liftρ)
    | ρ′ᴿ , liftρ′ , embᴿ =
  store-link α′ A′ (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-link
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ)
      (trans shapeᴿ (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-link eqα eqA (cong suc eqβ) eqBᴿ
    (⊑-rename-at-shapeᵢ
      (rename-assm²-⇑ᴿ²ᵢ assm)
      hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ)
    embᴿ
  where
  eqBᴿ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqBᴿ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))

rel-ctx-rename-lift-rightⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ∃[ γ′ᴿ ]
    LiftRightCtxⁱ (⇑ᴿᵢ Ψ) γ′ γ′ᴿ ×
    RelCtxRenameⁱ
      τ (extᵗ σ) (rename-assm²-⇑ᴿ²ᵢ assm)
      hτ (TyRenameWf-ext hσ) γᴿ γ′ᴿ
rel-ctx-rename-lift-rightⁱ rel-ctx-rename-[] lift-right-ctx-[] =
  [] , lift-right-ctx-[] , rel-ctx-rename-[]
rel-ctx-rename-lift-rightⁱ
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-right-ctx-∷ {p′ = pᴿ} shapeᴿ liftγ)
    with rel-ctx-rename-lift-rightⁱ renameγ liftγ
rel-ctx-rename-lift-rightⁱ
    {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-right-ctx-∷
      {A = A} {B = B} {p′ = pᴿ} shapeᴿ liftγ)
    | γ′ᴿ , liftγ′ , renameγᴿ =
  ctx-imp A′ (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ) ∷ γ′ᴿ ,
  lift-right-ctx-∷
    (trans
      (⊑-rename-at-shapeᵢ
        (rename-assm²-⇑ᴿ²ᵢ assm)
        hτ (TyRenameWf-ext hσ) eqA eqBᴿ pᴿ)
      (trans shapeᴿ
        (sym (⊑-rename-at-shapeᵢ assm hτ hσ eqA eqB p))))
    liftγ′ ,
  rel-ctx-rename-∷ eqA eqBᴿ renameγᴿ
  where
  eqBᴿ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqBᴿ = trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))

rel-world-permutation-lift-rightⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ∃[ ρ′ᴿ ] ∃[ γ′ᴿ ]
    LiftRightStoreⁱ (⇑ᴿᵢ Ψ) ρ′ ρ′ᴿ ×
    LiftRightCtxⁱ (⇑ᴿᵢ Ψ) γ′ γ′ᴿ ×
    RelWorldPermutationⁱ πᴸ (TyPermutation-ext πᴿ)
      (rename-assm²-⇑ᴿ²ᵢ assm)
      {ρ = ρᴿ} {ρ′ = ρ′ᴿ} {γ = γᴿ} {γ′ = γ′ᴿ}
rel-world-permutation-lift-rightⁱ perm liftρ liftγ
    with rel-store-rename-lift-rightⁱ
      (store-permutation perm) liftρ
       | rel-ctx-rename-lift-rightⁱ (ctx-permutation perm) liftγ
rel-world-permutation-lift-rightⁱ perm liftρ liftγ
    | ρ′ᴿ , liftρ′ , renameρᴿ
    | γ′ᴿ , liftγ′ , renameγᴿ =
  ρ′ᴿ , γ′ᴿ , liftρ′ , liftγ′ ,
  rel-world-permutation
    (left-cast-renamer perm)
    (castModeRenamer-ext (right-cast-renamer perm))
    renameρᴿ renameγᴿ

rel-world-embedding-lift-rightⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ∃[ ρ′ᴿ ] ∃[ γ′ᴿ ]
    LiftRightStoreⁱ (⇑ᴿᵢ Ψ) ρ′ ρ′ᴿ ×
    LiftRightCtxⁱ (⇑ᴿᵢ Ψ) γ′ γ′ᴿ ×
    RelWorldEmbeddingⁱ τ (extᵗ σ) ψ (extᵗ φ)
      (rename-assm²-⇑ᴿ²ᵢ assm) hτ (TyRenameWf-ext hσ)
      {ρ = ρᴿ} {ρ′ = ρ′ᴿ} {γ = γᴿ} {γ′ = γ′ᴿ}
rel-world-embedding-lift-rightⁱ
    {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ liftγ
    with rel-store-embedding-lift-rightⁱ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      (store-embedding emb) liftρ
       | rel-ctx-rename-lift-rightⁱ (embedding-context emb) liftγ
rel-world-embedding-lift-rightⁱ emb liftρ liftγ
    | ρ′ᴿ , liftρ′ , embρᴿ
    | γ′ᴿ , liftγ′ , renameγᴿ =
  ρ′ᴿ , γ′ᴿ , liftρ′ , liftγ′ ,
  rel-world-embedding
    (left-embedding-inverse emb)
    (RenameLeftInverse-ext (right-embedding-inverse emb))
    (left-embedding-cast-renamer emb)
    (castModeRenamer-ext (right-embedding-cast-renamer emb))
    embρᴿ renameγᴿ

data LeftStoreRenameⁱ
    {Φ Ψ Δᴸ Δᴸ′ Δᴿ}
    (τ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ Δᴸ′ Δᴿ → Set where
  left-store-rename-[] :
    LeftStoreRenameⁱ τ assm hτ [] []

  left-store-rename-matched :
    ∀ {ρ ρ′ α α′ A A′ β B p}
      (eqα : α′ ≡ τ α) (eqA : A′ ≡ renameᵗ τ A) →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftStoreRenameⁱ τ assm hτ
      (store-matched α A β B p ∷ ρ)
      (store-matched α′ A′ β B
        (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ ρ′)

  left-store-rename-left :
    ∀ {ρ ρ′ α α′ A A′ hA hA′}
      (eqα : α′ ≡ τ α) (eqA : A′ ≡ renameᵗ τ A) →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftStoreRenameⁱ τ assm hτ
      (store-left α A hA ∷ ρ)
      (store-left α′ A′ hA′ ∷ ρ′)

  left-store-rename-right :
    ∀ {ρ ρ′ β B hB hB′} →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftStoreRenameⁱ τ assm hτ
      (store-right β B hB ∷ ρ)
      (store-right β B hB′ ∷ ρ′)

  left-store-rename-link :
    ∀ {ρ ρ′ α α′ A A′ β B p}
      (eqα : α′ ≡ τ α) (eqA : A′ ≡ renameᵗ τ A) →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftStoreRenameⁱ τ assm hτ
      (store-link α A β B p ∷ ρ)
      (store-link α′ A′ β B
        (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ ρ′)

data LeftCtxRenameⁱ
    {Φ Ψ Δᴸ Δᴸ′ Δᴿ}
    (τ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ Δᴸ′ Δᴿ → Set where
  left-ctx-rename-[] :
    LeftCtxRenameⁱ τ assm hτ [] []

  left-ctx-rename-∷ :
    ∀ {γ γ′ A A′ B p} (eqA : A′ ≡ renameᵗ τ A) →
    LeftCtxRenameⁱ τ assm hτ γ γ′ →
    LeftCtxRenameⁱ τ assm hτ
      (ctx-imp A B p ∷ γ)
      (ctx-imp A′ B
        (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ γ′)

left-store-rename-prefix-invⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′⁺ : StoreImp Ψ Δᴸ′ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LeftStoreRenameⁱ τ assm hτ ρ⁺ ρ′⁺ →
  ∃[ ρ₀′ ]
    LeftStoreRenameⁱ τ assm hτ ρ₀ ρ₀′ ×
    StoreImpPrefix ρ₀′ ρ′⁺
left-store-rename-prefix-invⁱ prefix-reflⁱ renameρ =
  _ , renameρ , prefix-reflⁱ
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-matched eqα eqA renameρ)
    with left-store-rename-prefix-invⁱ prefix renameρ
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-matched eqα eqA renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-left eqα eqA renameρ)
    with left-store-rename-prefix-invⁱ prefix renameρ
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-left eqα eqA renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-right renameρ)
    with left-store-rename-prefix-invⁱ prefix renameρ
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-right renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-link eqα eqA renameρ)
    with left-store-rename-prefix-invⁱ prefix renameρ
left-store-rename-prefix-invⁱ (prefix-∷ⁱ prefix)
    (left-store-rename-link eqα eqA renameρ)
    | ρ₀′ , renameρ₀ , prefix′ =
  ρ₀′ , renameρ₀ , prefix-∷ⁱ prefix′

leftStoreⁱ-left-rename :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ renameStoreᵗ τ (leftStoreⁱ ρ)
leftStoreⁱ-left-rename left-store-rename-[] = refl
leftStoreⁱ-left-rename
    (left-store-rename-matched eqα eqA renameρ) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA) (leftStoreⁱ-left-rename renameρ)
leftStoreⁱ-left-rename
    (left-store-rename-left eqα eqA renameρ) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA) (leftStoreⁱ-left-rename renameρ)
leftStoreⁱ-left-rename (left-store-rename-right renameρ) =
  leftStoreⁱ-left-rename renameρ
leftStoreⁱ-left-rename (left-store-rename-link eqα eqA renameρ) =
  leftStoreⁱ-left-rename renameρ

rightStoreⁱ-left-rename :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  rightStoreⁱ ρ′ ≡ rightStoreⁱ ρ
rightStoreⁱ-left-rename left-store-rename-[] = refl
rightStoreⁱ-left-rename
    (left-store-rename-matched eqα eqA renameρ) =
  cong (_ ∷_) (rightStoreⁱ-left-rename renameρ)
rightStoreⁱ-left-rename (left-store-rename-left eqα eqA renameρ) =
  rightStoreⁱ-left-rename renameρ
rightStoreⁱ-left-rename (left-store-rename-right renameρ) =
  cong (_ ∷_) (rightStoreⁱ-left-rename renameρ)
rightStoreⁱ-left-rename (left-store-rename-link eqα eqA renameρ) =
  rightStoreⁱ-left-rename renameρ

leftCtxⁱ-left-rename :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ} →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  leftCtxⁱ γ′ ≡ map (renameᵗ τ) (leftCtxⁱ γ)
leftCtxⁱ-left-rename left-ctx-rename-[] = refl
leftCtxⁱ-left-rename (left-ctx-rename-∷ eqA renameγ) =
  cong₂ _∷_ eqA (leftCtxⁱ-left-rename renameγ)

rightCtxⁱ-left-rename :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ} →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  rightCtxⁱ γ′ ≡ rightCtxⁱ γ
rightCtxⁱ-left-rename left-ctx-rename-[] = refl
rightCtxⁱ-left-rename (left-ctx-rename-∷ eqA renameγ) =
  cong (_ ∷_) (rightCtxⁱ-left-rename renameγ)

left-typing-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ ψ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M A} →
  RenameLeftInverse τ ψ →
  CastModeRenamer τ →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  No• M →
  Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Δᴸ′ ∣ leftStoreⁱ ρ′ ∣ leftCtxⁱ γ′
    ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A
left-typing-renameⁱ {Δᴸ′ = Δᴸ′} {τ = τ} {ψ = ψ} {hτ = hτ}
    {ρ′ = ρ′} {γ = γ} {γ′ = γ′} {M = M} {A = A}
    invτ modeτ renameρ renameγ noM M⊢ =
  subst
    (λ Γ → Δᴸ′ ∣ leftStoreⁱ ρ′ ∣ Γ
      ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A)
    (sym (leftCtxⁱ-left-rename renameγ))
    (subst
      (λ Σ → Δᴸ′ ∣ Σ ∣ map (renameᵗ τ) (leftCtxⁱ γ)
        ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A)
      (sym (leftStoreⁱ-left-rename renameρ))
      (typing-renameᵀ {ρ = τ} {ψ = ψ} hτ invτ modeτ noM M⊢))

right-typing-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M B} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
  Δᴿ ∣ rightStoreⁱ ρ′ ∣ rightCtxⁱ γ′ ⊢ M ⦂ B
right-typing-left-renameⁱ {Δᴿ = Δᴿ} {ρ′ = ρ′}
    {γ = γ} {γ′ = γ′} {M = M} {B = B}
    renameρ renameγ M⊢ =
  subst
    (λ Γ → Δᴿ ∣ rightStoreⁱ ρ′ ∣ Γ ⊢ M ⦂ B)
    (sym (rightCtxⁱ-left-rename renameγ))
    (subst
      (λ Σ → Δᴿ ∣ Σ ∣ rightCtxⁱ γ ⊢ M ⦂ B)
      (sym (rightStoreⁱ-left-rename renameρ)) M⊢)

left-seal★-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} {μ} →
  (modeτ : CastModeRenamer τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★
    (CastModeRenamer.targetᵈ modeτ mode) (leftStoreⁱ ρ′)
left-seal★-renameⁱ modeτ renameρ mode seal★ =
  subst (SealModeStore★ _)
    (sym (leftStoreⁱ-left-rename renameρ))
    (castModeRenamer-seal★ modeτ mode seal★)

left-narrowing-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ c A B} →
  (modeτ : CastModeRenamer τ) →
  (mode : CastMode μ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  CastModeRenamer.targetᵈ modeτ mode ∣ Δᴸ′ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊒ renameᵗ τ B
left-narrowing-renameⁱ {hτ = hτ} modeτ mode renameρ c⊒ =
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
    (sym (leftStoreⁱ-left-rename renameρ))
    (narrow-renameᵗ hτ
      (CastModeRenamer.target-rename modeτ mode) c⊒)

left-widening-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ c A B} →
  (modeτ : CastModeRenamer τ) →
  (mode : CastMode μ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastModeRenamer.targetᵈ modeτ mode ∣ Δᴸ′ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊑ renameᵗ τ B
left-widening-renameⁱ {hτ = hτ} modeτ mode renameρ c⊑ =
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
    (sym (leftStoreⁱ-left-rename renameρ))
    (widen-renameᵗ hτ
      (CastModeRenamer.target-rename modeτ mode) c⊑)

seal★-id-only :
  ∀ {Σ} → SealModeStore★ id-onlyᵈ Σ
seal★-id-only α ()

modeRename-gen-tag-or-id :
  ∀ (τ : Renameᵗ) →
  ModeRename τ (genᵈ tag-or-idᵈ) (genᵈ tag-or-idᵈ)
modeRename-gen-tag-or-id τ zero with τ zero
modeRename-gen-tag-or-id τ zero | zero = refl
modeRename-gen-tag-or-id τ zero | suc Y = refl
modeRename-gen-tag-or-id τ (suc X) with τ (suc X)
modeRename-gen-tag-or-id τ (suc X) | zero = refl
modeRename-gen-tag-or-id τ (suc X) | suc Y = refl

left-narrowing-rename-modeⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ ν c A B} →
  ModeRename τ μ ν →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  ν ∣ Δᴸ′ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊒ renameᵗ τ B
left-narrowing-rename-modeⁱ {hτ = hτ} modeτ renameρ c⊒ =
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
    (sym (leftStoreⁱ-left-rename renameρ))
    (narrow-renameᵗ hτ modeτ c⊒)

left-widening-rename-modeⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ ν c A B} →
  ModeRename τ μ ν →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  ν ∣ Δᴸ′ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊑ renameᵗ τ B
left-widening-rename-modeⁱ {hτ = hτ} modeτ renameρ c⊑ =
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
    (sym (leftStoreⁱ-left-rename renameρ))
    (widen-renameᵗ hτ modeτ c⊑)

left-narrowing-rel-permute-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename (forward πᴸ) μ ν →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  ν ∣ Θᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ (forward πᴸ) c
    ∶ renameᵗ (forward πᴸ) A ⊒ renameᵗ (forward πᴸ) B
left-narrowing-rel-permute-mode
    {Θᴸ = Θᴸ} {πᴸ = πᴸ} {ρ′ = ρ′}
    {c = c} {A = A} {B = B} perm modeπ c⊒ =
  subst
    (λ Σ → _ ∣ Θᴸ ∣ Σ
      ⊢ renameᶜ (forward πᴸ) c
      ∶ renameᵗ (forward πᴸ) A ⊒ renameᵗ (forward πᴸ) B)
    (sym (leftStoreⁱ-rel-rename (store-permutation perm)))
    (narrow-renameᵗ (forward-wf πᴸ) modeπ c⊒)

right-narrowing-rel-permute-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename (forward πᴿ) μ ν →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  ν ∣ Θᴿ ∣ rightStoreⁱ ρ′
    ⊢ renameᶜ (forward πᴿ) c
    ∶ renameᵗ (forward πᴿ) A ⊒ renameᵗ (forward πᴿ) B
right-narrowing-rel-permute-mode
    {Θᴿ = Θᴿ} {πᴿ = πᴿ} {ρ′ = ρ′}
    {c = c} {A = A} {B = B} perm modeπ c⊒ =
  subst
    (λ Σ → _ ∣ Θᴿ ∣ Σ
      ⊢ renameᶜ (forward πᴿ) c
      ∶ renameᵗ (forward πᴿ) A ⊒ renameᵗ (forward πᴿ) B)
    (sym (rightStoreⁱ-rel-rename (store-permutation perm)))
    (narrow-renameᵗ (forward-wf πᴿ) modeπ c⊒)

left-widening-rel-permute-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename (forward πᴸ) μ ν →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  ν ∣ Θᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ (forward πᴸ) c
    ∶ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴸ) B
left-widening-rel-permute-mode
    {Θᴸ = Θᴸ} {πᴸ = πᴸ} {ρ′ = ρ′}
    {c = c} {A = A} {B = B} perm modeπ c⊑ =
  subst
    (λ Σ → _ ∣ Θᴸ ∣ Σ
      ⊢ renameᶜ (forward πᴸ) c
      ∶ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴸ) B)
    (sym (leftStoreⁱ-rel-rename (store-permutation perm)))
    (widen-renameᵗ (forward-wf πᴸ) modeπ c⊑)

right-widening-rel-permute-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename (forward πᴿ) μ ν →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  ν ∣ Θᴿ ∣ rightStoreⁱ ρ′
    ⊢ renameᶜ (forward πᴿ) c
    ∶ renameᵗ (forward πᴿ) A ⊑ renameᵗ (forward πᴿ) B
right-widening-rel-permute-mode
    {Θᴿ = Θᴿ} {πᴿ = πᴿ} {ρ′ = ρ′}
    {c = c} {A = A} {B = B} perm modeπ c⊑ =
  subst
    (λ Σ → _ ∣ Θᴿ ∣ Σ
      ⊢ renameᶜ (forward πᴿ) c
      ∶ renameᵗ (forward πᴿ) A ⊑ renameᵗ (forward πᴿ) B)
    (sym (rightStoreⁱ-rel-rename (store-permutation perm)))
    (widen-renameᵗ (forward-wf πᴿ) modeπ c⊑)

left-seal-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★
    (CastModeRenamer.targetᵈ (left-cast-renamer perm) mode)
    (leftStoreⁱ ρ′)
left-seal-rel-permute perm mode seal★ =
  subst (SealModeStore★ _)
    (sym (leftStoreⁱ-rel-rename (store-permutation perm)))
    (castModeRenamer-seal★ (left-cast-renamer perm) mode seal★)

right-seal-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  SealModeStore★
    (CastModeRenamer.targetᵈ (right-cast-renamer perm) mode)
    (rightStoreⁱ ρ′)
right-seal-rel-permute perm mode seal★ =
  subst (SealModeStore★ _)
    (sym (rightStoreⁱ-rel-rename (store-permutation perm)))
    (castModeRenamer-seal★ (right-cast-renamer perm) mode seal★)

left-narrowing-rel-embed-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename τ μ ν →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  ν ∣ Θᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊒ renameᵗ τ B
left-narrowing-rel-embed-mode
    {Θᴸ = Θᴸ} {τ = τ} {hτ = hτ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb modeτ c⊒ =
  subst
    (λ Σ → _ ∣ Θᴸ ∣ Σ
      ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊒ renameᵗ τ B)
    (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))
    (narrow-renameᵗ hτ modeτ c⊒)

right-narrowing-rel-embed-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename σ μ ν →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  ν ∣ Θᴿ ∣ rightStoreⁱ ρ′
    ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊒ renameᵗ σ B
right-narrowing-rel-embed-mode
    {Θᴿ = Θᴿ} {σ = σ} {hσ = hσ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb modeσ c⊒ =
  subst
    (λ Σ → _ ∣ Θᴿ ∣ Σ
      ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊒ renameᵗ σ B)
    (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))
    (narrow-renameᵗ hσ modeσ c⊒)

left-widening-rel-embed-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename τ μ ν →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  ν ∣ Θᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊑ renameᵗ τ B
left-widening-rel-embed-mode
    {Θᴸ = Θᴸ} {τ = τ} {hτ = hτ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb modeτ c⊑ =
  subst
    (λ Σ → _ ∣ Θᴸ ∣ Σ
      ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊑ renameᵗ τ B)
    (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))
    (widen-renameᵗ hτ modeτ c⊑)

right-widening-rel-embed-mode :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ ν c A B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename σ μ ν →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  ν ∣ Θᴿ ∣ rightStoreⁱ ρ′
    ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊑ renameᵗ σ B
right-widening-rel-embed-mode
    {Θᴿ = Θᴿ} {σ = σ} {hσ = hσ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb modeσ c⊑ =
  subst
    (λ Σ → _ ∣ Θᴿ ∣ Σ
      ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊑ renameᵗ σ B)
    (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))
    (widen-renameᵗ hσ modeσ c⊑)

left-seal-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★
    (CastModeRenamer.targetᵈ (left-embedding-cast-renamer emb) mode)
    (leftStoreⁱ ρ′)
left-seal-rel-embed emb mode seal★ =
  subst (SealModeStore★ _)
    (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))
    (castModeRenamer-seal★
      (left-embedding-cast-renamer emb) mode seal★)

right-seal-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  SealModeStore★
    (CastModeRenamer.targetᵈ (right-embedding-cast-renamer emb) mode)
    (rightStoreⁱ ρ′)
right-seal-rel-embed emb mode seal★ =
  subst (SealModeStore★ _)
    (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))
    (castModeRenamer-seal★
      (right-embedding-cast-renamer emb) mode seal★)

rel-world-conv↑⊑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ α X} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  p [ α ↦ X ]ᴸ q →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ B ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-conv↑⊑-embedᵀ emb conv M⊑M′ replace =
  conv↑⊑ᵀ (left-reveal-rel-embed emb conv) M⊑M′
    _ (replace-left-rename²ᵢ _ _ _ replace)

rel-world-conv↓⊑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ α X} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  q [ α ↦ X ]ᴸ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ B ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-conv↓⊑-embedᵀ emb conv M⊑M′ replace =
  conv↓⊑ᵀ (left-conceal-rel-embed emb conv) M⊑M′
    _ (replace-left-rename²ᵢ _ _ _ replace)

rel-world-⊑conv↑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ β X′} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ A′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  p [ β ↦ X′ ]ᴿ q →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-⊑conv↑-embedᵀ emb conv M⊑M′ replace =
  ⊑conv↑ᵀ (right-reveal-rel-embed emb conv) M⊑M′
    _ (replace-right-rename²ᵢ _ _ _ replace)

rel-world-⊑conv↓-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ β X′} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ A′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  q [ β ↦ X′ ]ᴿ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-⊑conv↓-embedᵀ emb conv M⊑M′ replace =
  ⊑conv↓ᵀ (right-conceal-rel-embed emb conv) M⊑M′
    _ (replace-right-rename²ᵢ _ _ _ replace)

rel-world-quotient-widening-pair-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {u u′ D D′ A A′} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  QuotientWideningPair Θᴸ Θᴿ ρ′
    (renameᶜ τ u) (renameᶜ σ u′)
    (renameᵗ τ D) (renameᵗ σ D′)
    (renameᵗ τ A) (renameᵗ σ A′)
rel-world-quotient-widening-pair-embed
    {τ = τ} {σ = σ} emb (quotient-id-widening u⊑ u′⊑) =
  quotient-id-widening
    (left-widening-rel-embed-mode emb (modeRename-id-only τ) u⊑)
    (right-widening-rel-embed-mode emb (modeRename-id-only σ) u′⊑)
rel-world-quotient-widening-pair-embed emb
    (quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) =
  quotient-cast-widening
    (CastModeRenamer.target-mode
      (left-embedding-cast-renamer emb) mode)
    (left-seal-rel-embed emb mode seal★)
    (left-widening-rel-embed-mode emb
      (CastModeRenamer.target-rename
        (left-embedding-cast-renamer emb) mode) u⊑)
    (CastModeRenamer.target-mode
      (right-embedding-cast-renamer emb) mode′)
    (right-seal-rel-embed emb mode′ seal★′)
    (right-widening-rel-embed-mode emb
      (CastModeRenamer.target-rename
        (right-embedding-cast-renamer emb) mode′) u′⊑)

rel-world-close-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {N N′ A A′ D D′ qD u u′ pA s s′} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  CastShape.widening ⊢ᶜ u ⦂ s →
  CastShape.widening ⊢ᶜ u′ ⦂ s′ →
  s ；⌊ pA ⌋≋ᵖ qD ； s′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA s s′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ N ⊑ renameᵗᵐ σ N′
    ⦂ renameᵗ τ D ⊑ᵖ renameᵗ σ D′
    ∶ ⊑ᵖ-rename²ᵢ assm hτ hσ qD →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (N ⟨ u ⟩) ⊑ renameᵗᵐ σ (N′ ⟨ u′ ⟩)
    ⦂ renameᵗ τ A ⊑ renameᵗ σ A′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ pA
rel-world-close-embedᵀ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    emb widening u-shape u′-shape square compatible N⊑N′ =
  closeᵀ N⊑N′
    (rel-world-quotient-widening-pair-embed emb widening) _
    (cast-shape-rename τ u-shape)
    (cast-shape-rename σ u′-shape)
    (quotient-boundary-square-rename²
      {τ = τ} {σ = σ} {assm = assm}
      {hτ = hτ} {hσ = hσ} square)
    (reduction-closed-quotient-compatible-rename²ᵢ
      {assm = assm} hτ hσ compatible)

rel-world-cast⊒⊑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ s} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  CastShape.narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ B ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-cast⊒⊑-embedᵀ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    {p = p} {q = q}
    emb mode seal★ c⊒ c-shape comp M⊑M′ =
  cast⊒⊑ᵀ
    (CastModeRenamer.target-mode
      (left-embedding-cast-renamer emb) mode)
    (left-seal-rel-embed emb mode seal★)
    (left-narrowing-rel-embed-mode emb
      (CastModeRenamer.target-rename
        (left-embedding-cast-renamer emb) mode) c⊒)
    M⊑M′ _
    (cast-shape-rename τ c-shape)
    (imprecision-composition-shape-transport
      refl
      (shape-rename assm hτ hσ p)
      (shape-rename assm hτ hσ q)
      comp)

rel-world-gen⊑ground-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {V W A B H p q c μ} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ gen A c ∶ A ⊒ `∀ B →
  Ground H →
  Value V →
  Value W →
  No• W →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ W ⦂ H →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ V ⊑ renameᵗᵐ σ (W ⟨ H ! ⟩)
    ⦂ renameᵗ τ A ⊑ ★
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (V ⟨ gen A c ⟩) ⊑ renameᵗᵐ σ W
    ⦂ renameᵗ τ (`∀ B) ⊑ renameᵗ σ H
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-gen⊑ground-embedᵀ {τ = τ} {σ = σ}
    emb mode seal★ c⊒ gH vV vW noW W⊢ V⊑Wtag =
  gen⊑groundᵀ
    (CastModeRenamer.target-mode
      (left-embedding-cast-renamer emb) mode)
    (left-seal-rel-embed emb mode seal★)
    (left-narrowing-rel-embed-mode emb
      (CastModeRenamer.target-rename
        (left-embedding-cast-renamer emb) mode) c⊒)
    (renameᵗ-ground σ gH)
    (renameᵗᵐ-preserves-Value τ vV)
    (renameᵗᵐ-preserves-Value σ vW)
    (rel-world-target-typing-embed emb noW W⊢)
    V⊑Wtag _

rel-world-cast⊑⊑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ s} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastShape.widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ B ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-cast⊑⊑-embedᵀ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    {p = p} {q = q}
    emb mode seal★ c⊑ c-shape comp M⊑M′ =
  cast⊑⊑ᵀ
    (CastModeRenamer.target-mode
      (left-embedding-cast-renamer emb) mode)
    (left-seal-rel-embed emb mode seal★)
    (left-widening-rel-embed-mode emb
      (CastModeRenamer.target-rename
        (left-embedding-cast-renamer emb) mode) c⊑)
    M⊑M′ _
    (cast-shape-rename τ c-shape)
    (imprecision-composition-shape-transport
      refl
      (shape-rename assm hτ hσ q)
      (shape-rename assm hτ hσ p)
      comp)

rel-world-⊑cast⊒-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ s} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode′ : CastMode μ′) →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  CastShape.narrowing ⊢ᶜ c′ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ A′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-⊑cast⊒-embedᵀ
    {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    {p = p} {q = q}
    emb mode′ seal★′ c′⊒ c-shape comp M⊑M′ =
  ⊑cast⊒ᵀ
    (CastModeRenamer.target-mode
      (right-embedding-cast-renamer emb) mode′)
    (right-seal-rel-embed emb mode′ seal★′)
    (right-narrowing-rel-embed-mode emb
      (CastModeRenamer.target-rename
        (right-embedding-cast-renamer emb) mode′) c′⊒)
    M⊑M′ _
    (cast-shape-rename σ c-shape)
    (imprecision-composition-shape-transport
      (shape-rename assm hτ hσ q)
      refl
      (shape-rename assm hτ hσ p)
      comp)

rel-world-⊑cast⊑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ s} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode′ : CastMode μ′) →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  CastShape.widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ A ⊑ renameᵗ σ A′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ τ A ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ q
rel-world-⊑cast⊑-embedᵀ
    {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    {p = p} {q = q}
    emb mode′ seal★′ c′⊑ c-shape comp M⊑M′ =
  ⊑cast⊑ᵀ
    (CastModeRenamer.target-mode
      (right-embedding-cast-renamer emb) mode′)
    (right-seal-rel-embed emb mode′ seal★′)
    (right-widening-rel-embed-mode emb
      (CastModeRenamer.target-rename
        (right-embedding-cast-renamer emb) mode′) c′⊑)
    M⊑M′ _
    (cast-shape-rename σ c-shape)
    (imprecision-composition-shape-transport
      (shape-rename assm hτ hσ p)
      refl
      (shape-rename assm hτ hσ q)
      comp)

rel-world-conv↑⊑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ α X} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  p [ α ↦ X ]ᴸ q →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (M ⟨ c ⟩)
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) B ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-conv↑⊑-permuteᵀ perm conv M⊑M′ replace =
  conv↑⊑ᵀ (left-reveal-rel-permute perm conv) M⊑M′ _
    (replace-left-rename²ᵢ _ _ _ replace)

rel-world-conv↓⊑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ α X} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  q [ α ↦ X ]ᴸ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (M ⟨ c ⟩)
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) B ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-conv↓⊑-permuteᵀ perm conv M⊑M′ replace =
  conv↓⊑ᵀ (left-conceal-rel-permute perm conv) M⊑M′ _
    (replace-left-rename²ᵢ _ _ _ replace)

rel-world-⊑conv↑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ β X′} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) A′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  p [ β ↦ X′ ]ᴿ q →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-⊑conv↑-permuteᵀ perm conv M⊑M′ replace =
  ⊑conv↑ᵀ (right-reveal-rel-permute perm conv) M⊑M′ _
    (replace-right-rename²ᵢ _ _ _ replace)

rel-world-⊑conv↓-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ β X′} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) A′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  q [ β ↦ X′ ]ᴿ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-⊑conv↓-permuteᵀ perm conv M⊑M′ replace =
  ⊑conv↓ᵀ (right-conceal-rel-permute perm conv) M⊑M′ _
    (replace-right-rename²ᵢ _ _ _ replace)

rel-world-cast⊒⊑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ s} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  CastShape.narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (M ⟨ c ⟩)
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) B ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-cast⊒⊑-permuteᵀ
    {πᴸ = πᴸ} {πᴿ = πᴿ} {assm = assm}
    {p = p} {q = q}
    perm mode seal★ c⊒ c-shape comp M⊑M′ =
  cast⊒⊑ᵀ
    (CastModeRenamer.target-mode (left-cast-renamer perm) mode)
    (left-seal-rel-permute perm mode seal★)
    (left-narrowing-rel-permute-mode perm
      (CastModeRenamer.target-rename (left-cast-renamer perm) mode) c⊒)
    M⊑M′ _
    (cast-shape-rename (forward πᴸ) c-shape)
    (imprecision-composition-shape-transport
      refl
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) p)
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) q)
      comp)

rel-world-cast⊑⊑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B B′ p q c μ s} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastShape.widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (M ⟨ c ⟩)
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) B ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-cast⊑⊑-permuteᵀ
    {πᴸ = πᴸ} {πᴿ = πᴿ} {assm = assm}
    {p = p} {q = q}
    perm mode seal★ c⊑ c-shape comp M⊑M′ =
  cast⊑⊑ᵀ
    (CastModeRenamer.target-mode (left-cast-renamer perm) mode)
    (left-seal-rel-permute perm mode seal★)
    (left-widening-rel-permute-mode perm
      (CastModeRenamer.target-rename (left-cast-renamer perm) mode) c⊑)
    M⊑M′ _
    (cast-shape-rename (forward πᴸ) c-shape)
    (imprecision-composition-shape-transport
      refl
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) q)
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) p)
      comp)

rel-world-⊑cast⊒-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ s} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode′ : CastMode μ′) →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  CastShape.narrowing ⊢ᶜ c′ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) A′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-⊑cast⊒-permuteᵀ
    {πᴸ = πᴸ} {πᴿ = πᴿ} {assm = assm}
    {p = p} {q = q}
    perm mode′ seal★′ c′⊒ c-shape comp M⊑M′ =
  ⊑cast⊒ᵀ
    (CastModeRenamer.target-mode (right-cast-renamer perm) mode′)
    (right-seal-rel-permute perm mode′ seal★′)
    (right-narrowing-rel-permute-mode perm
      (CastModeRenamer.target-rename (right-cast-renamer perm) mode′)
      c′⊒)
    M⊑M′ _
    (cast-shape-rename (forward πᴿ) c-shape)
    (imprecision-composition-shape-transport
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) q)
      refl
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) p)
      comp)

rel-world-⊑cast⊑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A A′ B′ p q c′ μ′ s} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode′ : CastMode μ′) →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  CastShape.widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) A′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) (M′ ⟨ c′ ⟩)
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-⊑cast⊑-permuteᵀ
    {πᴸ = πᴸ} {πᴿ = πᴿ} {assm = assm}
    {p = p} {q = q}
    perm mode′ seal★′ c′⊑ c-shape comp M⊑M′ =
  ⊑cast⊑ᵀ
    (CastModeRenamer.target-mode (right-cast-renamer perm) mode′)
    (right-seal-rel-permute perm mode′ seal★′)
    (right-widening-rel-permute-mode perm
      (CastModeRenamer.target-rename (right-cast-renamer perm) mode′)
      c′⊑)
    M⊑M′ _
    (cast-shape-rename (forward πᴿ) c-shape)
    (imprecision-composition-shape-transport
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) p)
      refl
      (shape-rename
        assm (forward-wf πᴸ) (forward-wf πᴿ) q)
      comp)

left-reveal-ν-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ A B C s} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion
    (permuted-modeᵈ (TyPermutation-ext πᴸ) μ)
    (suc Θᴸ)
    ((zero , ⇑ᵗ (renameᵗ (forward πᴸ) A)) ∷
      ⟰ᵗ (leftStoreⁱ ρ′))
    zero (⇑ᵗ (renameᵗ (forward πᴸ) A))
    (renameᶜ (extᵗ (forward πᴸ)) s)
    (renameᵗ (extᵗ (forward πᴸ)) C)
    (⇑ᵗ (renameᵗ (forward πᴸ) B))
left-reveal-ν-rel-permute
    {Θᴸ = Θᴸ} {πᴸ = πᴸ} {ρ = ρ} {ρ′ = ρ′}
    {μ = μ} {A = A} {B = B} {C = C} {s = s} perm conv =
  subst
    (λ D → RevealConversion target-mode (suc Θᴸ) target-store
      zero (⇑ᵗ (renameᵗ τ A)) (renameᶜ (extᵗ τ) s)
      (renameᵗ (extᵗ τ) C) D)
    (renameᵗ-ext-suc-comm τ B)
    (subst
      (λ X → RevealConversion target-mode (suc Θᴸ) target-store
        zero X (renameᶜ (extᵗ τ) s)
        (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      (renameᵗ-ext-suc-comm τ A)
      store-normalized)
  where
  τ = forward πᴸ
  target-mode = permuted-modeᵈ (TyPermutation-ext πᴸ) μ
  target-store =
    (zero , ⇑ᵗ (renameᵗ τ A)) ∷ ⟰ᵗ (leftStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-suc-cons-comm τ (leftStoreⁱ ρ) A)
      (cong ((zero , ⇑ᵗ (renameᵗ τ A)) ∷_)
        (cong ⟰ᵗ
          (sym (leftStoreⁱ-rel-rename (store-permutation perm)))))

  renamed =
    rename-reveal-conversion
      (TyRenameWf-ext (forward-wf πᴸ))
      (permuted-mode-rename (TyPermutation-ext πᴸ) μ) conv

  store-normalized =
    subst
      (λ Σ → RevealConversion target-mode (suc Θᴸ) Σ
        zero (renameᵗ (extᵗ τ) (⇑ᵗ A))
        (renameᶜ (extᵗ τ) s) (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      store-eq renamed

right-reveal-ν-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ A B C s} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion
    (permuted-modeᵈ (TyPermutation-ext πᴿ) μ)
    (suc Θᴿ)
    ((zero , ⇑ᵗ (renameᵗ (forward πᴿ) A)) ∷
      ⟰ᵗ (rightStoreⁱ ρ′))
    zero (⇑ᵗ (renameᵗ (forward πᴿ) A))
    (renameᶜ (extᵗ (forward πᴿ)) s)
    (renameᵗ (extᵗ (forward πᴿ)) C)
    (⇑ᵗ (renameᵗ (forward πᴿ) B))
right-reveal-ν-rel-permute
    {Θᴿ = Θᴿ} {πᴿ = πᴿ} {ρ = ρ} {ρ′ = ρ′}
    {μ = μ} {A = A} {B = B} {C = C} {s = s} perm conv =
  subst
    (λ D → RevealConversion target-mode (suc Θᴿ) target-store
      zero (⇑ᵗ (renameᵗ σ A)) (renameᶜ (extᵗ σ) s)
      (renameᵗ (extᵗ σ) C) D)
    (renameᵗ-ext-suc-comm σ B)
    (subst
      (λ X → RevealConversion target-mode (suc Θᴿ) target-store
        zero X (renameᶜ (extᵗ σ) s)
        (renameᵗ (extᵗ σ) C)
        (renameᵗ (extᵗ σ) (⇑ᵗ B)))
      (renameᵗ-ext-suc-comm σ A)
      store-normalized)
  where
  σ = forward πᴿ
  target-mode = permuted-modeᵈ (TyPermutation-ext πᴿ) μ
  target-store =
    (zero , ⇑ᵗ (renameᵗ σ A)) ∷ ⟰ᵗ (rightStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-suc-cons-comm σ (rightStoreⁱ ρ) A)
      (cong ((zero , ⇑ᵗ (renameᵗ σ A)) ∷_)
        (cong ⟰ᵗ
          (sym (rightStoreⁱ-rel-rename (store-permutation perm)))))

  renamed =
    rename-reveal-conversion
      (TyRenameWf-ext (forward-wf πᴿ))
      (permuted-mode-rename (TyPermutation-ext πᴿ) μ) conv

  store-normalized =
    subst
      (λ Σ → RevealConversion target-mode (suc Θᴿ) Σ
        zero (renameᵗ (extᵗ σ) (⇑ᵗ A))
        (renameᶜ (extᵗ σ) s) (renameᵗ (extᵗ σ) C)
        (renameᵗ (extᵗ σ) (⇑ᵗ B)))
      store-eq renamed

left-reveal-ν-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ A B C s} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion (embedded-modeᵈ (extᵗ ψ) μ) (suc Θᴸ)
    ((zero , ⇑ᵗ (renameᵗ τ A)) ∷ ⟰ᵗ (leftStoreⁱ ρ′))
    zero (⇑ᵗ (renameᵗ τ A)) (renameᶜ (extᵗ τ) s)
    (renameᵗ (extᵗ τ) C) (⇑ᵗ (renameᵗ τ B))
left-reveal-ν-rel-embed
    {Θᴸ = Θᴸ} {τ = τ} {ψ = ψ} {hτ = hτ}
    {ρ = ρ} {ρ′ = ρ′} {μ = μ} {A = A} {B = B} {C = C} {s = s}
    emb conv =
  subst
    (λ D → RevealConversion target-mode (suc Θᴸ) target-store
      zero (⇑ᵗ (renameᵗ τ A)) (renameᶜ (extᵗ τ) s)
      (renameᵗ (extᵗ τ) C) D)
    (renameᵗ-ext-suc-comm τ B)
    (subst
      (λ X → RevealConversion target-mode (suc Θᴸ) target-store
        zero X (renameᶜ (extᵗ τ) s)
        (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      (renameᵗ-ext-suc-comm τ A)
      store-normalized)
  where
  target-mode = embedded-modeᵈ (extᵗ ψ) μ
  target-store =
    (zero , ⇑ᵗ (renameᵗ τ A)) ∷ ⟰ᵗ (leftStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-suc-cons-comm τ (leftStoreⁱ ρ) A)
      (cong ((zero , ⇑ᵗ (renameᵗ τ A)) ∷_)
        (cong ⟰ᵗ
          (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))))

  renamed =
    rename-reveal-conversion (TyRenameWf-ext hτ)
      (embedded-mode-rename {τ = extᵗ τ} {ψ = extᵗ ψ}
        (RenameLeftInverse-ext (left-embedding-inverse emb)) μ) conv

  store-normalized =
    subst
      (λ Σ → RevealConversion target-mode (suc Θᴸ) Σ
        zero (renameᵗ (extᵗ τ) (⇑ᵗ A))
        (renameᶜ (extᵗ τ) s) (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      store-eq renamed

right-reveal-ν-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ A B C s} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion (embedded-modeᵈ (extᵗ φ) μ) (suc Θᴿ)
    ((zero , ⇑ᵗ (renameᵗ σ A)) ∷ ⟰ᵗ (rightStoreⁱ ρ′))
    zero (⇑ᵗ (renameᵗ σ A)) (renameᶜ (extᵗ σ) s)
    (renameᵗ (extᵗ σ) C) (⇑ᵗ (renameᵗ σ B))
right-reveal-ν-rel-embed
    {Θᴿ = Θᴿ} {σ = σ} {φ = φ} {hσ = hσ}
    {ρ = ρ} {ρ′ = ρ′} {μ = μ} {A = A} {B = B} {C = C} {s = s}
    emb conv =
  subst
    (λ D → RevealConversion target-mode (suc Θᴿ) target-store
      zero (⇑ᵗ (renameᵗ σ A)) (renameᶜ (extᵗ σ) s)
      (renameᵗ (extᵗ σ) C) D)
    (renameᵗ-ext-suc-comm σ B)
    (subst
      (λ X → RevealConversion target-mode (suc Θᴿ) target-store
        zero X (renameᶜ (extᵗ σ) s)
        (renameᵗ (extᵗ σ) C)
        (renameᵗ (extᵗ σ) (⇑ᵗ B)))
      (renameᵗ-ext-suc-comm σ A)
      store-normalized)
  where
  target-mode = embedded-modeᵈ (extᵗ φ) μ
  target-store =
    (zero , ⇑ᵗ (renameᵗ σ A)) ∷ ⟰ᵗ (rightStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-suc-cons-comm σ (rightStoreⁱ ρ) A)
      (cong ((zero , ⇑ᵗ (renameᵗ σ A)) ∷_)
        (cong ⟰ᵗ
          (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))))

  renamed =
    rename-reveal-conversion (TyRenameWf-ext hσ)
      (embedded-mode-rename {τ = extᵗ σ} {ψ = extᵗ φ}
        (RenameLeftInverse-ext (right-embedding-inverse emb)) μ) conv

  store-normalized =
    subst
      (λ Σ → RevealConversion target-mode (suc Θᴿ) Σ
        zero (renameᵗ (extᵗ σ) (⇑ᵗ A))
        (renameᶜ (extᵗ σ) s) (renameᵗ (extᵗ σ) C)
        (renameᵗ (extᵗ σ) (⇑ᵗ B)))
      store-eq renamed

rel-world-ν⊑ν-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {A A′ B B′ C C′ N N′ s s′ μ μ′}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  (A⇑⊑A′⇑ : ∀ᵢᶜ Φ
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  q
    [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) N
      ⊑ renameᵗᵐ (forward πᴿ) N′
    ⦂ renameᵗ (forward πᴸ) (`∀ C)
      ⊑ renameᵗ (forward πᴿ) (`∀ C′)
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ)
        (∀ⁱ q) →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (ν A N s)
      ⊑ renameᵗᵐ (forward πᴿ) (ν A′ N′ s′)
    ⦂ renameᵗ (forward πᴸ) B
      ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p
rel-world-ν⊑ν-permuteᵀ
    {πᴸ = πᴸ} {πᴿ = πᴿ}
    perm hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ replace
    N⊑N′
    with rel-world-permutation-lift∀ⁱ perm liftρ liftγ
rel-world-ν⊑ν-permuteᵀ
    {Ψ = Ψ} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {πᴸ = πᴸ} {πᴿ = πᴿ} {assm = assm}
    {A = A} {A′ = A′}
    perm hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ replace
    N⊑N′
    | ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-perm =
  ν⊑νᵀ
    (renameᵗ-preserves-WfTy hA (forward-wf πᴸ))
    (renameᵗ-preserves-WfTy hA′ (forward-wf πᴿ))
    (left-reveal-ν-rel-permute perm s↑)
    (right-reveal-ν-rel-permute perm s′↑)
    (⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ)
      A⊑A′)
    shifted-A⊑A′
    liftρ′ liftγ′ N⊑N′
    (replace-paired-target-shape target-shape-eq
      transported-replace)
  where
  τ = forward πᴸ
  σ = forward πᴿ

  renamed-A⇑⊑A′⇑ =
    ⊑-renameᵗ²ᵢ (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext (forward-wf πᴸ))
      (TyRenameWf-ext (forward-wf πᴿ)) A⇑⊑A′⇑

  shifted-A⊑A′ =
    transport-imprecision-endpoints
      (renameᵗ-ext-suc-comm τ A)
      (renameᵗ-ext-suc-comm σ A′)
      renamed-A⇑⊑A′⇑

  renamed-replace =
    replace-paired-rename²ᵢ
      {α = zero} {β = zero}
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext (forward-wf πᴸ))
      (TyRenameWf-ext (forward-wf πᴿ)) replace

  transported-replace =
    replace-paired-transport-endpoints
      refl refl
      (renameᵗ-ext-suc-comm τ _)
      (renameᵗ-ext-suc-comm σ _)
      (renameᵗ-ext-suc-comm τ A)
      (renameᵗ-ext-suc-comm σ A′)
      renamed-replace

  target-shape-eq =
    trans
      (shape-lift∀ᵢ
        (⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) _))
      (trans
        (shape-rename assm (forward-wf πᴸ) (forward-wf πᴿ) _)
        (trans
          (sym (shape-lift∀ᵢ _))
          (trans
            (sym
              (shape-rename
                (rename-assm²-⇑ᵢ assm)
                (TyRenameWf-ext (forward-wf πᴸ))
                (TyRenameWf-ext (forward-wf πᴿ)) _))
            (sym
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ _)
                (renameᵗ-ext-suc-comm σ _) _)))))

rel-world-ν⊑ν-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {A A′ B B′ C C′ N N′ s s′ μ μ′}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  (A⇑⊑A′⇑ : ∀ᵢᶜ Φ
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  q
    [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ renameᵗᵐ σ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ renameᵗ σ (`∀ C′)
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ (∀ⁱ q) →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν A N s) ⊑ renameᵗᵐ σ (ν A′ N′ s′)
    ⦂ renameᵗ τ B ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p
rel-world-ν⊑ν-embedᵀ
    {τ = τ} {σ = σ}
    emb hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ replace
    N⊑N′
    with rel-world-embedding-lift∀ⁱ emb liftρ liftγ
rel-world-ν⊑ν-embedᵀ
    {Ψ = Ψ} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    {A = A} {A′ = A′}
    emb hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ replace
    N⊑N′
    | ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-emb =
  ν⊑νᵀ
    (renameᵗ-preserves-WfTy hA hτ)
    (renameᵗ-preserves-WfTy hA′ hσ)
    (left-reveal-ν-rel-embed emb s↑)
    (right-reveal-ν-rel-embed emb s′↑)
    (⊑-renameᵗ²ᵢ assm hτ hσ A⊑A′)
    shifted-A⊑A′
    liftρ′ liftγ′ N⊑N′
    (replace-paired-target-shape target-shape-eq
      transported-replace)
  where
  renamed-A⇑⊑A′⇑ =
    ⊑-renameᵗ²ᵢ (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) A⇑⊑A′⇑

  shifted-A⊑A′ =
    transport-imprecision-endpoints
      (renameᵗ-ext-suc-comm τ A)
      (renameᵗ-ext-suc-comm σ A′)
      renamed-A⇑⊑A′⇑

  renamed-replace =
    replace-paired-rename²ᵢ
      {α = zero} {β = zero}
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) replace

  transported-replace =
    replace-paired-transport-endpoints
      refl refl
      (renameᵗ-ext-suc-comm τ _)
      (renameᵗ-ext-suc-comm σ _)
      (renameᵗ-ext-suc-comm τ A)
      (renameᵗ-ext-suc-comm σ A′)
      renamed-replace

  target-shape-eq =
    trans
      (shape-lift∀ᵢ (⊑-renameᵗ²ᵢ assm hτ hσ _))
      (trans
        (shape-rename assm hτ hσ _)
        (trans
          (sym (shape-lift∀ᵢ _))
          (trans
            (sym
              (shape-rename
                (rename-assm²-⇑ᵢ assm)
                (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) _))
            (sym
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ _)
                (renameᵗ-ext-suc-comm σ _) _)))))

rel-world-ν⊑-permuteᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {A B B′ C N N′ s μ occ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar C}} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  WfTy Δᴸ A →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) N
      ⊑ renameᵗᵐ (forward πᴿ) N′
    ⦂ renameᵗ (forward πᴸ) (`∀ C)
      ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ)
        (ν safe occ q) →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) (ν A N s)
      ⊑ renameᵗᵐ (forward πᴿ) N′
    ⦂ renameᵗ (forward πᴸ) B
      ⊑ renameᵗ (forward πᴿ) B′
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p
rel-world-ν⊑-permuteᵀ
    {Θᴸ = Θᴸ} {πᴸ = πᴸ} {A = A} {{safe = safe}}
    perm hA h⇑A s↑ liftρ liftγ replace N⊑N′
    with rel-world-permutation-lift-leftⁱ perm liftρ liftγ
rel-world-ν⊑-permuteᵀ
    {Θᴸ = Θᴸ} {πᴸ = πᴸ} {πᴿ = πᴿ} {assm = assm}
    {A = A} {{safe = safe}}
    perm hA h⇑A s↑ liftρ liftγ replace N⊑N′
    | ρ′ν , γ′ν , liftρ′ , liftγ′ , body-perm =
  ν⊑ᵀ {{renameNonVar (extᵗ (forward πᴸ)) safe}}
    (renameᵗ-preserves-WfTy hA (forward-wf πᴸ))
    h⇑A′
    (left-reveal-ν-rel-permute perm s↑)
    liftρ′ liftγ′ N⊑N′
    (replace-left-target-shape target-shape-eq
      transported-replace)
  where
  τ = forward πᴸ
  σ = forward πᴿ

  h⇑A′ : WfTy (suc Θᴸ) (⇑ᵗ (renameᵗ (forward πᴸ) A))
  h⇑A′ =
    subst (WfTy (suc Θᴸ))
      (renameᵗ-ext-suc-comm (forward πᴸ) A)
      (renameᵗ-preserves-WfTy h⇑A
        (TyRenameWf-ext (forward-wf πᴸ)))

  renamed-replace =
    replace-left-rename²ᵢ
      {α = zero}
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext (forward-wf πᴸ))
      (forward-wf πᴿ) replace

  transported-replace =
    replace-left-transport-endpoints
      refl refl
      (renameᵗ-ext-suc-comm τ _)
      (renameᵗ-ext-suc-comm τ A)
      renamed-replace

  target-shape-eq =
    trans
      (shape-source-liftνᵢ
        (⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) _))
      (trans
        (shape-rename assm (forward-wf πᴸ) (forward-wf πᴿ) _)
        (trans
          (sym (shape-source-liftνᵢ _))
          (trans
            (sym
              (shape-rename
                (rename-assm²-⇑ᴸᵢ assm)
                (TyRenameWf-ext (forward-wf πᴸ))
                (forward-wf πᴿ) _))
            (sym
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ _) refl _)))))

rel-world-ν⊑-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {A B B′ C N N′ s μ occ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar C}} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  WfTy Δᴸ A →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ p →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ renameᵗᵐ σ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ (ν safe occ q) →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν A N s) ⊑ renameᵗᵐ σ N′
    ⦂ renameᵗ τ B ⊑ renameᵗ σ B′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p
rel-world-ν⊑-embedᵀ
    {Θᴸ = Θᴸ} {τ = τ} {hτ = hτ} {A = A} {{safe = safe}}
    emb hA h⇑A s↑ liftρ liftγ replace N⊑N′
    with rel-world-embedding-lift-leftⁱ emb liftρ liftγ
rel-world-ν⊑-embedᵀ
    {Θᴸ = Θᴸ} {τ = τ} {σ = σ} {assm = assm}
    {hτ = hτ} {hσ = hσ} {A = A} {{safe = safe}}
    emb hA h⇑A s↑ liftρ liftγ replace N⊑N′
    | ρ′ν , γ′ν , liftρ′ , liftγ′ , body-emb =
  ν⊑ᵀ {{renameNonVar (extᵗ τ) safe}}
    (renameᵗ-preserves-WfTy hA hτ)
    h⇑A′
    (left-reveal-ν-rel-embed emb s↑)
    liftρ′ liftγ′ N⊑N′
    (replace-left-target-shape target-shape-eq
      transported-replace)
  where
  h⇑A′ : WfTy (suc Θᴸ) (⇑ᵗ (renameᵗ τ A))
  h⇑A′ =
    subst (WfTy (suc Θᴸ))
      (renameᵗ-ext-suc-comm τ A)
      (renameᵗ-preserves-WfTy h⇑A (TyRenameWf-ext hτ))

  renamed-replace =
    replace-left-rename²ᵢ
      {α = zero}
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ replace

  transported-replace =
    replace-left-transport-endpoints
      refl refl
      (renameᵗ-ext-suc-comm τ _)
      (renameᵗ-ext-suc-comm τ A)
      renamed-replace

  target-shape-eq =
    trans
      (shape-source-liftνᵢ (⊑-renameᵗ²ᵢ assm hτ hσ _))
      (trans
        (shape-rename assm hτ hσ _)
        (trans
          (sym (shape-source-liftνᵢ _))
          (trans
            (sym
              (shape-rename
                (rename-assm²-⇑ᴸᵢ assm)
                (TyRenameWf-ext hτ) hσ _))
            (sym
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ _) refl _)))))

left-reveal-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ α X c A B} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  RevealConversion (left-insertion-mode ins μ) Δᴸ′
    (leftStoreⁱ ρ′) (τ α) (renameᵗ τ X)
    (renameᶜ τ c) (renameᵗ τ A) (renameᵗ τ B)
left-reveal-renameⁱ {hτ = hτ} ins renameρ conv =
  subst
    (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (leftStoreⁱ-left-rename renameρ))
    (rename-reveal-conversion hτ
      (left-insertion-mode-rename ins _) conv)

left-reveal-ν-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ A B C s} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion
    (left-insertion-mode (left-insertion-ext ins) μ)
    (suc Δᴸ′)
    ((zero , ⇑ᵗ (renameᵗ τ A)) ∷ ⟰ᵗ (leftStoreⁱ ρ′))
    zero (⇑ᵗ (renameᵗ τ A)) (renameᶜ (extᵗ τ) s)
    (renameᵗ (extᵗ τ) C) (⇑ᵗ (renameᵗ τ B))
left-reveal-ν-renameⁱ
    {Δᴸ′ = Δᴸ′} {τ = τ} {hτ = hτ} {ρ = ρ} {ρ′ = ρ′}
    {μ = μ} {A = A} {B = B} {C = C} {s = s}
    ins renameρ conv =
  subst
    (λ D → RevealConversion target-mode (suc Δᴸ′) target-store
      zero (⇑ᵗ (renameᵗ τ A)) (renameᶜ (extᵗ τ) s)
      (renameᵗ (extᵗ τ) C) D)
    (renameᵗ-ext-suc-comm τ B)
    (subst
      (λ X → RevealConversion target-mode (suc Δᴸ′) target-store
        zero X (renameᶜ (extᵗ τ) s) (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      (renameᵗ-ext-suc-comm τ A)
      store-normalized)
  where
  target-mode = left-insertion-mode (left-insertion-ext ins) μ

  target-store =
    (zero , ⇑ᵗ (renameᵗ τ A)) ∷ ⟰ᵗ (leftStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-suc-cons-comm τ (leftStoreⁱ ρ) A)
      (cong ((zero , ⇑ᵗ (renameᵗ τ A)) ∷_)
        (cong ⟰ᵗ (sym (leftStoreⁱ-left-rename renameρ))))

  renamed :
    RevealConversion target-mode (suc Δᴸ′)
      (renameStoreᵗ (extᵗ τ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ)))
      zero (renameᵗ (extᵗ τ) (⇑ᵗ A))
      (renameᶜ (extᵗ τ) s) (renameᵗ (extᵗ τ) C)
      (renameᵗ (extᵗ τ) (⇑ᵗ B))
  renamed =
    rename-reveal-conversion (TyRenameWf-ext hτ)
      (left-insertion-mode-rename (left-insertion-ext ins) μ) conv

  store-normalized :
    RevealConversion target-mode (suc Δᴸ′) target-store
      zero (renameᵗ (extᵗ τ) (⇑ᵗ A))
      (renameᶜ (extᵗ τ) s) (renameᵗ (extᵗ τ) C)
      (renameᵗ (extᵗ τ) (⇑ᵗ B))
  store-normalized =
    subst
      (λ Σ → RevealConversion target-mode (suc Δᴸ′) Σ
        zero (renameᵗ (extᵗ τ) (⇑ᵗ A))
        (renameᶜ (extᵗ τ) s) (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      store-eq renamed

right-reveal-ν-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ A B C s} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ′))
    zero (⇑ᵗ A) s C (⇑ᵗ B)
right-reveal-ν-left-renameⁱ
    {Δᴿ = Δᴿ} {μ = μ} {A = A} {B = B} {C = C} {s = s}
    renameρ conv =
  subst
    (λ Σ → RevealConversion μ (suc Δᴿ) Σ
      zero (⇑ᵗ A) s C (⇑ᵗ B))
    (cong ((zero , ⇑ᵗ A) ∷_)
      (cong ⟰ᵗ (sym (rightStoreⁱ-left-rename renameρ))))
    conv

renameStoreᵗ-ext-★-cons-comm :
  ∀ (τ : Renameᵗ) (Σ : Store) →
  renameStoreᵗ (extᵗ τ) ((zero , ★) ∷ ⟰ᵗ Σ) ≡
    (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ τ Σ)
renameStoreᵗ-ext-★-cons-comm τ Σ =
  cong ((zero , ★) ∷_) (renameStoreᵗ-ext-suc-comm τ Σ)

left-ν★-widening-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ s C B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode (CastModeRenamer.targetᵈ (left-cast-renamer perm) mode) ×
  SealModeStore★
    (instᵈ (CastModeRenamer.targetᵈ
      (left-cast-renamer perm) mode))
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)) ×
  instᵈ (CastModeRenamer.targetᵈ (left-cast-renamer perm) mode)
    ∣ suc Θᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)
    ⊢ renameᶜ (extᵗ (forward πᴸ)) s
    ∶ renameᵗ (extᵗ (forward πᴸ)) C
      ⊑ ⇑ᵗ (renameᵗ (forward πᴸ) B)
left-ν★-widening-rel-permute
    {Θᴸ = Θᴸ} {πᴸ = πᴸ} {ρ = ρ} {ρ′ = ρ′}
    {s = s} {C = C} {B = B} perm mode seal★ s⊑ =
  CastModeRenamer.target-mode η mode ,
  subst SealTarget store-eq renamed-seal ,
  subst
    (λ D → target-full-mode ∣ suc Θᴸ ∣ target-store
      ⊢ renameᶜ (extᵗ τ) s
      ∶ renameᵗ (extᵗ τ) C ⊑ D)
    (renameᵗ-ext-suc-comm τ B)
    (subst
      (λ Σ → target-full-mode ∣ suc Θᴸ ∣ Σ
        ⊢ renameᶜ (extᵗ τ) s
        ∶ renameᵗ (extᵗ τ) C
          ⊑ renameᵗ (extᵗ τ) (⇑ᵗ B))
      store-eq renamed-widening)
  where
  τ = forward πᴸ
  η = left-cast-renamer perm
  extη = castModeRenamer-ext η
  target-full-mode = instᵈ (CastModeRenamer.targetᵈ η mode)
  target-store = (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)
  SealTarget = SealModeStore★ target-full-mode

  store-eq =
    trans
      (renameStoreᵗ-ext-★-cons-comm τ (leftStoreⁱ ρ))
      (cong ((zero , ★) ∷_)
        (cong ⟰ᵗ
          (sym (leftStoreⁱ-rel-rename (store-permutation perm)))))

  renamed-seal =
    castModeRenamer-seal★ extη (cast-inst mode) seal★

  renamed-widening =
    widen-renameᵗ
      (TyRenameWf-ext (forward-wf πᴸ))
      (CastModeRenamer.target-rename extη (cast-inst mode)) s⊑

right-ν★-widening-rel-permute :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ s C B} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode (CastModeRenamer.targetᵈ (right-cast-renamer perm) mode) ×
  SealModeStore★
    (instᵈ (CastModeRenamer.targetᵈ
      (right-cast-renamer perm) mode))
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′)) ×
  instᵈ (CastModeRenamer.targetᵈ (right-cast-renamer perm) mode)
    ∣ suc Θᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′)
    ⊢ renameᶜ (extᵗ (forward πᴿ)) s
    ∶ renameᵗ (extᵗ (forward πᴿ)) C
      ⊑ ⇑ᵗ (renameᵗ (forward πᴿ) B)
right-ν★-widening-rel-permute
    {Θᴿ = Θᴿ} {πᴿ = πᴿ} {ρ = ρ} {ρ′ = ρ′}
    {s = s} {C = C} {B = B} perm mode seal★ s⊑ =
  CastModeRenamer.target-mode η mode ,
  subst SealTarget store-eq renamed-seal ,
  subst
    (λ D → target-full-mode ∣ suc Θᴿ ∣ target-store
      ⊢ renameᶜ (extᵗ σ) s
      ∶ renameᵗ (extᵗ σ) C ⊑ D)
    (renameᵗ-ext-suc-comm σ B)
    (subst
      (λ Σ → target-full-mode ∣ suc Θᴿ ∣ Σ
        ⊢ renameᶜ (extᵗ σ) s
        ∶ renameᵗ (extᵗ σ) C
          ⊑ renameᵗ (extᵗ σ) (⇑ᵗ B))
      store-eq renamed-widening)
  where
  σ = forward πᴿ
  η = right-cast-renamer perm
  extη = castModeRenamer-ext η
  target-full-mode = instᵈ (CastModeRenamer.targetᵈ η mode)
  target-store = (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′)
  SealTarget = SealModeStore★ target-full-mode

  store-eq =
    trans
      (renameStoreᵗ-ext-★-cons-comm σ (rightStoreⁱ ρ))
      (cong ((zero , ★) ∷_)
        (cong ⟰ᵗ
          (sym (rightStoreⁱ-rel-rename (store-permutation perm)))))

  renamed-seal =
    castModeRenamer-seal★ extη (cast-inst mode) seal★

  renamed-widening =
    widen-renameᵗ
      (TyRenameWf-ext (forward-wf πᴿ))
      (CastModeRenamer.target-rename extη (cast-inst mode)) s⊑

left-ν★-widening-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ s C B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode (CastModeRenamer.targetᵈ
    (left-embedding-cast-renamer emb) mode) ×
  SealModeStore★
    (instᵈ (CastModeRenamer.targetᵈ
      (left-embedding-cast-renamer emb) mode))
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)) ×
  instᵈ (CastModeRenamer.targetᵈ
      (left-embedding-cast-renamer emb) mode)
    ∣ suc Θᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)
    ⊢ renameᶜ (extᵗ τ) s
    ∶ renameᵗ (extᵗ τ) C ⊑ ⇑ᵗ (renameᵗ τ B)
left-ν★-widening-rel-embed
    {Θᴸ = Θᴸ} {τ = τ} {hτ = hτ} {ρ = ρ} {ρ′ = ρ′}
    {s = s} {C = C} {B = B} emb mode seal★ s⊑ =
  CastModeRenamer.target-mode η mode ,
  subst SealTarget store-eq renamed-seal ,
  subst
    (λ D → target-full-mode ∣ suc Θᴸ ∣ target-store
      ⊢ renameᶜ (extᵗ τ) s ∶ renameᵗ (extᵗ τ) C ⊑ D)
    (renameᵗ-ext-suc-comm τ B)
    (subst
      (λ Σ → target-full-mode ∣ suc Θᴸ ∣ Σ
        ⊢ renameᶜ (extᵗ τ) s
        ∶ renameᵗ (extᵗ τ) C ⊑ renameᵗ (extᵗ τ) (⇑ᵗ B))
      store-eq renamed-widening)
  where
  η = left-embedding-cast-renamer emb
  extη = castModeRenamer-ext η
  target-full-mode = instᵈ (CastModeRenamer.targetᵈ η mode)
  target-store = (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)
  SealTarget = SealModeStore★ target-full-mode

  store-eq =
    trans
      (renameStoreᵗ-ext-★-cons-comm τ (leftStoreⁱ ρ))
      (cong ((zero , ★) ∷_)
        (cong ⟰ᵗ
          (sym (leftStoreⁱ-rel-embedding (store-embedding emb)))))

  renamed-seal =
    castModeRenamer-seal★ extη (cast-inst mode) seal★

  renamed-widening =
    widen-renameᵗ (TyRenameWf-ext hτ)
      (CastModeRenamer.target-rename extη (cast-inst mode)) s⊑

right-ν★-widening-rel-embed :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ s C B} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode (CastModeRenamer.targetᵈ
    (right-embedding-cast-renamer emb) mode) ×
  SealModeStore★
    (instᵈ (CastModeRenamer.targetᵈ
      (right-embedding-cast-renamer emb) mode))
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′)) ×
  instᵈ (CastModeRenamer.targetᵈ
      (right-embedding-cast-renamer emb) mode)
    ∣ suc Θᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′)
    ⊢ renameᶜ (extᵗ σ) s
    ∶ renameᵗ (extᵗ σ) C ⊑ ⇑ᵗ (renameᵗ σ B)
right-ν★-widening-rel-embed
    {Θᴿ = Θᴿ} {σ = σ} {hσ = hσ} {ρ = ρ} {ρ′ = ρ′}
    {s = s} {C = C} {B = B} emb mode seal★ s⊑ =
  CastModeRenamer.target-mode η mode ,
  subst SealTarget store-eq renamed-seal ,
  subst
    (λ D → target-full-mode ∣ suc Θᴿ ∣ target-store
      ⊢ renameᶜ (extᵗ σ) s ∶ renameᵗ (extᵗ σ) C ⊑ D)
    (renameᵗ-ext-suc-comm σ B)
    (subst
      (λ Σ → target-full-mode ∣ suc Θᴿ ∣ Σ
        ⊢ renameᶜ (extᵗ σ) s
        ∶ renameᵗ (extᵗ σ) C ⊑ renameᵗ (extᵗ σ) (⇑ᵗ B))
      store-eq renamed-widening)
  where
  η = right-embedding-cast-renamer emb
  extη = castModeRenamer-ext η
  target-full-mode = instᵈ (CastModeRenamer.targetᵈ η mode)
  target-store = (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′)
  SealTarget = SealModeStore★ target-full-mode

  store-eq =
    trans
      (renameStoreᵗ-ext-★-cons-comm σ (rightStoreⁱ ρ))
      (cong ((zero , ★) ∷_)
        (cong ⟰ᵗ
          (sym (rightStoreⁱ-rel-embedding (store-embedding emb)))))

  renamed-seal =
    castModeRenamer-seal★ extη (cast-inst mode) seal★

  renamed-widening =
    widen-renameᵗ (TyRenameWf-ext hσ)
      (CastModeRenamer.target-rename extη (cast-inst mode)) s⊑

left-seal★-ν★-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  SealModeStore★
    (instᵈ (CastModeRenamer.targetᵈ
      (left-insertion-cast-renamer ins) mode))
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′))
left-seal★-ν★-renameⁱ {τ = τ} {ρ = ρ} ins renameρ mode seal★ =
  subst (SealModeStore★ _)
    store-eq
    (castModeRenamer-seal★
      (castModeRenamer-ext (left-insertion-cast-renamer ins))
      (cast-inst mode) seal★)
  where
  store-eq =
    trans
      (renameStoreᵗ-ext-★-cons-comm τ (leftStoreⁱ ρ))
      (cong ((zero , ★) ∷_)
        (cong ⟰ᵗ (sym (leftStoreⁱ-left-rename renameρ))))

right-seal★-ν★-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′))
right-seal★-ν★-left-renameⁱ renameρ seal★ =
  subst (SealModeStore★ _)
    (cong ((zero , ★) ∷_)
      (cong ⟰ᵗ (sym (rightStoreⁱ-left-rename renameρ))))
    seal★

left-widening-ν★-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ c C B} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  (mode : CastMode μ) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ c ∶ C ⊑ ⇑ᵗ B →
  instᵈ (CastModeRenamer.targetᵈ
      (left-insertion-cast-renamer ins) mode)
    ∣ suc Δᴸ′ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)
    ⊢ renameᶜ (extᵗ τ) c
    ∶ renameᵗ (extᵗ τ) C ⊑ ⇑ᵗ (renameᵗ τ B)
left-widening-ν★-renameⁱ
    {Δᴸ′ = Δᴸ′} {τ = τ} {hτ = hτ} {ρ = ρ} {ρ′ = ρ′}
    {μ = μ} {c = c} {C = C} {B = B}
    ins renameρ mode c⊑ =
  subst
    (λ D → instᵈ target-mode ∣ suc Δᴸ′ ∣ target-store
      ⊢ renameᶜ (extᵗ τ) c
      ∶ renameᵗ (extᵗ τ) C ⊑ D)
    (renameᵗ-ext-suc-comm τ B)
    store-normalized
  where
  modeτ = left-insertion-cast-renamer ins
  target-mode = CastModeRenamer.targetᵈ modeτ mode
  target-store = (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-★-cons-comm τ (leftStoreⁱ ρ))
      (cong ((zero , ★) ∷_)
        (cong ⟰ᵗ (sym (leftStoreⁱ-left-rename renameρ))))

  renamed :
    instᵈ target-mode ∣ suc Δᴸ′ ∣
      renameStoreᵗ (extᵗ τ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))
      ⊢ renameᶜ (extᵗ τ) c
      ∶ renameᵗ (extᵗ τ) C ⊑ renameᵗ (extᵗ τ) (⇑ᵗ B)
  renamed =
    widen-renameᵗ (TyRenameWf-ext hτ)
      (CastModeRenamer.target-rename
        (castModeRenamer-ext modeτ) (cast-inst mode)) c⊑

  store-normalized :
    instᵈ target-mode ∣ suc Δᴸ′ ∣ target-store
      ⊢ renameᶜ (extᵗ τ) c
      ∶ renameᵗ (extᵗ τ) C ⊑ renameᵗ (extᵗ τ) (⇑ᵗ B)
  store-normalized =
    subst
      (λ Σ → instᵈ target-mode ∣ suc Δᴸ′ ∣ Σ
        ⊢ renameᶜ (extᵗ τ) c
        ∶ renameᵗ (extᵗ τ) C ⊑ renameᵗ (extᵗ τ) (⇑ᵗ B))
      store-eq renamed

right-widening-ν★-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ c C B} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ c ∶ C ⊑ ⇑ᵗ B →
  instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ′)
    ⊢ c ∶ C ⊑ ⇑ᵗ B
right-widening-ν★-left-renameⁱ
    {Δᴿ = Δᴿ} {μ = μ} {c = c} {C = C} {B = B}
    renameρ c⊑ =
  subst
    (λ Σ → instᵈ μ ∣ suc Δᴿ ∣ Σ ⊢ c ∶ C ⊑ ⇑ᵗ B)
    (cong ((zero , ★) ∷_)
      (cong ⟰ᵗ (sym (rightStoreⁱ-left-rename renameρ))))
    c⊑

left-conceal-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ α X c A B} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  ConcealConversion (left-insertion-mode ins μ) Δᴸ′
    (leftStoreⁱ ρ′) (τ α) (renameᵗ τ X)
    (renameᶜ τ c) (renameᵗ τ A) (renameᵗ τ B)
left-conceal-renameⁱ {hτ = hτ} ins renameρ conv =
  subst
    (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (leftStoreⁱ-left-rename renameρ))
    (rename-conceal-conversion hτ
      (left-insertion-mode-rename ins _) conv)

right-reveal-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ β X c A B} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ) β X c A B →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ′) β X c A B
right-reveal-left-renameⁱ renameρ conv =
  subst
    (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (rightStoreⁱ-left-rename renameρ)) conv

right-conceal-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ β X c A B} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ) β X c A B →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ′) β X c A B
right-conceal-left-renameⁱ renameρ conv =
  subst
    (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (rightStoreⁱ-left-rename renameρ)) conv

right-seal★-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  SealModeStore★ μ (rightStoreⁱ ρ′)
right-seal★-left-renameⁱ renameρ seal★ =
  subst (SealModeStore★ _)
    (sym (rightStoreⁱ-left-rename renameρ)) seal★

right-widening-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ c A B} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ′ ⊢ c ∶ A ⊑ B
right-widening-left-renameⁱ renameρ c⊑ =
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
    (sym (rightStoreⁱ-left-rename renameρ)) c⊑

right-narrowing-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {μ c A B} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ′ ⊢ c ∶ A ⊒ B
right-narrowing-left-renameⁱ renameρ c⊒ =
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
    (sym (rightStoreⁱ-left-rename renameρ)) c⊒

right-store-det-left-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  StoreDetWf Δᴿ (rightStoreⁱ ρ) →
  StoreDetWf Δᴿ (rightStoreⁱ ρ′)
right-store-det-left-renameⁱ renameρ wfΣ =
  subst (StoreDetWf _)
    (sym (rightStoreⁱ-left-rename renameρ)) wfΣ

left-store-rename-∀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  ∃[ ρ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    LeftStoreRenameⁱ
      (extᵗ τ) (rename-assm²-∀-leftᵢ assm) (TyRenameWf-ext hτ)
      ρ∀ ρ′∀
left-store-rename-∀ left-store-rename-[] lift-store-[] =
  [] , lift-store-[] , left-store-rename-[]
left-store-rename-∀
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {p = p} eqα eqA renameρ)
    (lift-store-∷ {p′ = p∀} shape∀ liftρ)
    with left-store-rename-∀ renameρ liftρ
left-store-rename-∀ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {β = β} {B = B} {p = p} eqα eqA renameρ)
    (lift-store-∷ {A = A} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-matched (suc α′) (⇑ᵗ A′) (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀) ∷ ρ′∀ ,
  lift-store-∷
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀)
      (trans shape∀
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′ ,
  left-store-rename-matched (cong suc eqα) eqA∀ renameρ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
left-store-rename-∀
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-store-left liftρ)
    with left-store-rename-∀ renameρ liftρ
left-store-rename-∀ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-store-left {A = A} liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-left liftρ′ ,
  left-store-rename-left (cong suc eqα) eqA∀ renameρ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
left-store-rename-∀
    (left-store-rename-right {hB′ = hB′} renameρ)
    (lift-store-right liftρ)
    with left-store-rename-∀ renameρ liftρ
left-store-rename-∀
    (left-store-rename-right {β = β} {B = B} {hB′ = hB′} renameρ)
    (lift-store-right liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-right (suc β) (⇑ᵗ B)
      (renameᵗ-preserves-WfTy hB′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-right liftρ′ ,
  left-store-rename-right renameρ∀
left-store-rename-∀
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {p = p} eqα eqA renameρ)
    (lift-store-link {p′ = p∀} shape∀ liftρ)
    with left-store-rename-∀ renameρ liftρ
left-store-rename-∀ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {β = β} {B = B} {p = p} eqα eqA renameρ)
    (lift-store-link {A = A} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-link (suc α′) (⇑ᵗ A′) (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀) ∷ ρ′∀ ,
  lift-store-link
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀)
      (trans shape∀
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′ ,
  left-store-rename-link (cong suc eqα) eqA∀ renameρ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

left-ctx-rename-∀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  ∃[ γ′∀ ]
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    LeftCtxRenameⁱ
      (extᵗ τ) (rename-assm²-∀-leftᵢ assm) (TyRenameWf-ext hτ)
      γ∀ γ′∀
left-ctx-rename-∀ left-ctx-rename-[] lift-ctx-[] =
  [] , lift-ctx-[] , left-ctx-rename-[]
left-ctx-rename-∀
    (left-ctx-rename-∷ {A′ = A′} {p = p} eqA renameγ)
    (lift-ctx-∷ {p′ = p∀} shape∀ liftγ)
    with left-ctx-rename-∀ renameγ liftγ
left-ctx-rename-∀ {τ = τ} {assm = assm} {hτ = hτ}
    (left-ctx-rename-∷
      {A′ = A′} {B = B} {p = p} eqA renameγ)
    (lift-ctx-∷ {A = A} {p′ = p∀} shape∀ liftγ)
    | γ′∀ , liftγ′ , renameγ∀ =
  ctx-imp (⇑ᵗ A′) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀) ∷ γ′∀ ,
  lift-ctx-∷
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀)
      (trans shape∀
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftγ′ ,
  left-ctx-rename-∷ eqA∀ renameγ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

left-store-rename-ν :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  ∃[ ρ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    LeftStoreRenameⁱ
      (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ)
      ρν ρ′ν
left-store-rename-ν left-store-rename-[] lift-left-store-[] =
  [] , lift-left-store-[] , left-store-rename-[]
left-store-rename-ν
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {p = p} eqα eqA renameρ)
    (lift-left-store-∷ {p′ = pν} shapeν liftρ)
    with left-store-rename-ν renameρ liftρ
left-store-rename-ν {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {β = β} {B = B} {p = p} eqα eqA renameρ)
    (lift-left-store-∷ {A = A} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-matched (suc α′) (⇑ᵗ A′) β B
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν) ∷ ρ′ν ,
  lift-left-store-∷
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν)
      (trans shapeν
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′ ,
  left-store-rename-matched (cong suc eqα) eqAν renameρν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
left-store-rename-ν
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-left-store-left liftρ)
    with left-store-rename-ν renameρ liftρ
left-store-rename-ν {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-left-store-left {A = A} liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′ν ,
  lift-left-store-left liftρ′ ,
  left-store-rename-left (cong suc eqα) eqAν renameρν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
left-store-rename-ν
    (left-store-rename-right {hB′ = hB′} renameρ)
    (lift-left-store-right liftρ)
    with left-store-rename-ν renameρ liftρ
left-store-rename-ν
    (left-store-rename-right {β = β} {B = B} {hB′ = hB′} renameρ)
    (lift-left-store-right liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-right β B hB′ ∷ ρ′ν ,
  lift-left-store-right liftρ′ ,
  left-store-rename-right renameρν
left-store-rename-ν
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {p = p} eqα eqA renameρ)
    (lift-left-store-link {p′ = pν} shapeν liftρ)
    with left-store-rename-ν renameρ liftρ
left-store-rename-ν {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {β = β} {B = B} {p = p} eqα eqA renameρ)
    (lift-left-store-link {A = A} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-link (suc α′) (⇑ᵗ A′) β B
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν) ∷ ρ′ν ,
  lift-left-store-link
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν)
      (trans shapeν
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′ ,
  left-store-rename-link (cong suc eqα) eqAν renameρν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

left-ctx-rename-ν :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  ∃[ γ′ν ]
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    LeftCtxRenameⁱ
      (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ)
      γν γ′ν
left-ctx-rename-ν left-ctx-rename-[] lift-left-ctx-[] =
  [] , lift-left-ctx-[] , left-ctx-rename-[]
left-ctx-rename-ν
    (left-ctx-rename-∷ {A′ = A′} {p = p} eqA renameγ)
    (lift-left-ctx-∷ {p′ = pν} shapeν liftγ)
    with left-ctx-rename-ν renameγ liftγ
left-ctx-rename-ν {τ = τ} {assm = assm} {hτ = hτ}
    (left-ctx-rename-∷
      {A′ = A′} {B = B} {p = p} eqA renameγ)
    (lift-left-ctx-∷ {A = A} {p′ = pν} shapeν liftγ)
    | γ′ν , liftγ′ , renameγν =
  ctx-imp (⇑ᵗ A′) B
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν) ∷ γ′ν ,
  lift-left-ctx-∷
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν)
      (trans shapeν
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftγ′ ,
  left-ctx-rename-∷ eqAν renameγν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν = trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

left-store-rename-ν-inv :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ′ν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
      (suc Δᴸ′) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LeftStoreRenameⁱ
    (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ)
    ρν ρ′ν →
  ∃[ ρ′ ]
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ ×
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν
left-store-rename-ν-inv
    lift-left-store-[] left-store-rename-[] =
  [] , left-store-rename-[] , lift-left-store-[]
left-store-rename-ν-inv
    {ρ = store-matched α A β B p ∷ ρ}
    (lift-left-store-∷ shapeν liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    with left-store-rename-ν-inv liftρ renameρ
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-matched α A β B p ∷ ρ}
    (lift-left-store-∷ shapeν liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ with eqα
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-matched α A β B p ∷ ρ}
    (lift-left-store-∷ shapeν liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl
    with trans eqA (renameᵗ-ext-suc-comm τ A)
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-matched α A β B p ∷ ρ}
    (lift-left-store-∷ shapeν liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl | refl =
  store-matched (τ α) (renameᵗ τ A) β B
      (⊑-rename-leftᵢ τ assm hτ p) ∷ ρ′ ,
  left-store-rename-matched refl refl renameρ′ ,
  lift-left-store-∷
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqA _)
      (trans shapeν (sym (shape-rename-left assm hτ p))))
    liftρ′
left-store-rename-ν-inv
    {ρ = store-left α A hA ∷ ρ}
    (lift-left-store-left liftρ)
    (left-store-rename-left eqα eqA renameρ)
    with left-store-rename-ν-inv liftρ renameρ
left-store-rename-ν-inv {τ = τ} {hτ = hτ}
    {ρ = store-left α A hA ∷ ρ}
    (lift-left-store-left liftρ)
    (left-store-rename-left eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ with eqα
left-store-rename-ν-inv {τ = τ} {hτ = hτ}
    {ρ = store-left α A hA ∷ ρ}
    (lift-left-store-left liftρ)
    (left-store-rename-left eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl
    with trans eqA (renameᵗ-ext-suc-comm τ A)
left-store-rename-ν-inv {τ = τ} {hτ = hτ}
    {ρ = store-left α A hA ∷ ρ}
    (lift-left-store-left liftρ)
    (left-store-rename-left eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl | refl =
  store-left (τ α) (renameᵗ τ A)
      (renameᵗ-preserves-WfTy hA hτ) ∷ ρ′ ,
  left-store-rename-left refl refl renameρ′ ,
  lift-left-store-left liftρ′
left-store-rename-ν-inv
    {ρ = store-right β B hB ∷ ρ}
    (lift-left-store-right liftρ)
    (left-store-rename-right renameρ)
    with left-store-rename-ν-inv liftρ renameρ
left-store-rename-ν-inv
    {ρ = store-right β B hB ∷ ρ}
    (lift-left-store-right liftρ)
    (left-store-rename-right renameρ)
    | ρ′ , renameρ′ , liftρ′ =
  store-right β B hB ∷ ρ′ ,
  left-store-rename-right renameρ′ ,
  lift-left-store-right liftρ′
left-store-rename-ν-inv
    {ρ = store-link α A β B p ∷ ρ}
    (lift-left-store-link shapeν liftρ)
    (left-store-rename-link eqα eqA renameρ)
    with left-store-rename-ν-inv liftρ renameρ
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-link α A β B p ∷ ρ}
    (lift-left-store-link shapeν liftρ)
    (left-store-rename-link eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ with eqα
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-link α A β B p ∷ ρ}
    (lift-left-store-link shapeν liftρ)
    (left-store-rename-link eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl
    with trans eqA (renameᵗ-ext-suc-comm τ A)
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-link α A β B p ∷ ρ}
    (lift-left-store-link shapeν liftρ)
    (left-store-rename-link eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl | refl =
  store-link (τ α) (renameᵗ τ A) β B
      (⊑-rename-leftᵢ τ assm hτ p) ∷ ρ′ ,
  left-store-rename-link refl refl renameρ′ ,
  lift-left-store-link
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqA _)
      (trans shapeν (sym (shape-rename-left assm hτ p))))
    liftρ′

left-ctx-rename-ν-inv :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ′ν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
      (suc Δᴸ′) Δᴿ} →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  LeftCtxRenameⁱ
    (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ)
    γν γ′ν →
  ∃[ γ′ ]
    LeftCtxRenameⁱ τ assm hτ γ γ′ ×
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν
left-ctx-rename-ν-inv lift-left-ctx-[] left-ctx-rename-[] =
  [] , left-ctx-rename-[] , lift-left-ctx-[]
left-ctx-rename-ν-inv
    {γ = ctx-imp A B p ∷ γ}
    (lift-left-ctx-∷ shapeν liftγ)
    (left-ctx-rename-∷ eqA renameγ)
    with left-ctx-rename-ν-inv liftγ renameγ
left-ctx-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {γ = ctx-imp A B p ∷ γ}
    (lift-left-ctx-∷ shapeν liftγ)
    (left-ctx-rename-∷ eqA renameγ)
    | γ′ , renameγ′ , liftγ′
    with trans eqA (renameᵗ-ext-suc-comm τ A)
left-ctx-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {γ = ctx-imp A B p ∷ γ}
    (lift-left-ctx-∷ shapeν liftγ)
    (left-ctx-rename-∷ eqA renameγ)
    | γ′ , renameγ′ , liftγ′ | refl =
  ctx-imp (renameᵗ τ A) B (⊑-rename-leftᵢ τ assm hτ p) ∷ γ′ ,
  left-ctx-rename-∷ refl renameγ′ ,
  lift-left-ctx-∷
    (trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqA _)
      (trans shapeν (sym (shape-rename-left assm hτ p))))
    liftγ′

left-store-rename-suc-liftⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc ρ ρ′ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
left-store-rename-suc-liftⁱ left-store-rename-[] =
  lift-left-store-[]
left-store-rename-suc-liftⁱ
    {ρ = store-matched α A β B p ∷ ρ}
    (left-store-rename-matched eqα eqA renameρ)
    with eqα
left-store-rename-suc-liftⁱ
    {ρ = store-matched α A β B p ∷ ρ}
    (left-store-rename-matched eqα eqA renameρ) | refl
    with eqA
left-store-rename-suc-liftⁱ
    {ρ = store-matched α A β B p ∷ ρ}
    (left-store-rename-matched eqα eqA renameρ) | refl | refl =
  lift-left-store-∷
    (shape-rename-left rename-assm²-source-νᵢ TyRenameWf-suc p)
    (left-store-rename-suc-liftⁱ renameρ)
left-store-rename-suc-liftⁱ
    {ρ = store-left α A hA ∷ ρ}
    (left-store-rename-left eqα eqA renameρ)
    with eqα
left-store-rename-suc-liftⁱ
    {ρ = store-left α A hA ∷ ρ}
    (left-store-rename-left eqα eqA renameρ) | refl
    with eqA
left-store-rename-suc-liftⁱ
    {ρ = store-left α A hA ∷ ρ}
    (left-store-rename-left eqα eqA renameρ) | refl | refl =
  lift-left-store-left (left-store-rename-suc-liftⁱ renameρ)
left-store-rename-suc-liftⁱ
    {ρ = store-right β B hB ∷ ρ}
    (left-store-rename-right renameρ) =
  lift-left-store-right (left-store-rename-suc-liftⁱ renameρ)
left-store-rename-suc-liftⁱ
    {ρ = store-link α A β B p ∷ ρ}
    (left-store-rename-link eqα eqA renameρ)
    with eqα
left-store-rename-suc-liftⁱ
    {ρ = store-link α A β B p ∷ ρ}
    (left-store-rename-link eqα eqA renameρ) | refl
    with eqA
left-store-rename-suc-liftⁱ
    {ρ = store-link α A β B p ∷ ρ}
    (left-store-rename-link eqα eqA renameρ) | refl | refl =
  lift-left-store-link
    (shape-rename-left rename-assm²-source-νᵢ TyRenameWf-suc p)
    (left-store-rename-suc-liftⁱ renameρ)

left-store-rename-⇑ᴿ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  ∃[ ρ′ᴿ ]
    LiftRightStoreⁱ (⇑ᴿᵢ Ψ) ρ′ ρ′ᴿ ×
    LeftStoreRenameⁱ τ (rename-assm²-⇑ᴿᵢ assm) hτ ρᴿ ρ′ᴿ
left-store-rename-⇑ᴿ left-store-rename-[] lift-right-store-[] =
  [] , lift-right-store-[] , left-store-rename-[]
left-store-rename-⇑ᴿ
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {p = p} eqα eqA renameρ)
    (lift-right-store-∷ {p′ = pᴿ} shapeᴿ liftρ)
    with left-store-rename-⇑ᴿ renameρ liftρ
left-store-rename-⇑ᴿ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {β = β} {B = B} {p = p} eqα eqA renameρ)
    (lift-right-store-∷ {p′ = pᴿ} shapeᴿ liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-matched α′ A′ (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-∷
    (trans
      (shape-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ)
      (trans shapeᴿ
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′ ,
  left-store-rename-matched eqα eqA renameρᴿ
left-store-rename-⇑ᴿ
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-right-store-left liftρ)
    with left-store-rename-⇑ᴿ renameρ liftρ
left-store-rename-⇑ᴿ
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    (lift-right-store-left liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-left α′ A′ hA′ ∷ ρ′ᴿ ,
  lift-right-store-left liftρ′ ,
  left-store-rename-left eqα eqA renameρᴿ
left-store-rename-⇑ᴿ
    (left-store-rename-right renameρ)
    (lift-right-store-right liftρ)
    with left-store-rename-⇑ᴿ renameρ liftρ
left-store-rename-⇑ᴿ
    (left-store-rename-right {β = β} {B = B} renameρ)
    (lift-right-store-right {hB′ = hBᴿ} liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-right (suc β) (⇑ᵗ B) hBᴿ ∷ ρ′ᴿ ,
  lift-right-store-right liftρ′ ,
  left-store-rename-right renameρᴿ
left-store-rename-⇑ᴿ
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {p = p} eqα eqA renameρ)
    (lift-right-store-link {p′ = pᴿ} shapeᴿ liftρ)
    with left-store-rename-⇑ᴿ renameρ liftρ
left-store-rename-⇑ᴿ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {β = β} {B = B} {p = p} eqα eqA renameρ)
    (lift-right-store-link {p′ = pᴿ} shapeᴿ liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-link α′ A′ (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-link
    (trans
      (shape-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ)
      (trans shapeᴿ
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′ ,
  left-store-rename-link eqα eqA renameρᴿ

left-ctx-rename-⇑ᴿ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ∃[ γ′ᴿ ]
    LiftRightCtxⁱ (⇑ᴿᵢ Ψ) γ′ γ′ᴿ ×
    LeftCtxRenameⁱ τ (rename-assm²-⇑ᴿᵢ assm) hτ γᴿ γ′ᴿ
left-ctx-rename-⇑ᴿ left-ctx-rename-[] lift-right-ctx-[] =
  [] , lift-right-ctx-[] , left-ctx-rename-[]
left-ctx-rename-⇑ᴿ
    (left-ctx-rename-∷ {A′ = A′} {p = p} eqA renameγ)
    (lift-right-ctx-∷ {p′ = pᴿ} shapeᴿ liftγ)
    with left-ctx-rename-⇑ᴿ renameγ liftγ
left-ctx-rename-⇑ᴿ {τ = τ} {assm = assm} {hτ = hτ}
    (left-ctx-rename-∷
      {A′ = A′} {B = B} {p = p} eqA renameγ)
    (lift-right-ctx-∷ {p′ = pᴿ} shapeᴿ liftγ)
    | γ′ᴿ , liftγ′ , renameγᴿ =
  ctx-imp A′ (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ) ∷ γ′ᴿ ,
  lift-right-ctx-∷
    (trans
      (shape-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ)
      (trans shapeᴿ
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftγ′ ,
  left-ctx-rename-∷ eqA renameγᴿ

left-store-rename-⇑ᴿ-inv :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {ρ′ᴿ : StoreImp (⇑ᴿᵢ Ψ) Δᴸ′ (suc Δᴿ)} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LeftStoreRenameⁱ τ (rename-assm²-⇑ᴿᵢ assm) hτ ρᴿ ρ′ᴿ →
  ∃[ ρ′ ]
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ ×
    LiftRightStoreⁱ (⇑ᴿᵢ Ψ) ρ′ ρ′ᴿ
left-store-rename-⇑ᴿ-inv
    lift-right-store-[] left-store-rename-[] =
  [] , left-store-rename-[] , lift-right-store-[]
left-store-rename-⇑ᴿ-inv
    (lift-right-store-∷ {p = p} shapeᴿ liftρ)
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    with left-store-rename-⇑ᴿ-inv liftρ renameρ
left-store-rename-⇑ᴿ-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    (lift-right-store-∷ {p = p} shapeᴿ liftρ)
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ =
  store-matched α′ A′ _ _
      (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ ρ′ ,
  left-store-rename-matched eqα eqA renameρ′ ,
  lift-right-store-∷
    (trans
      (shape-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ _ _)
      (trans shapeᴿ
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′
left-store-rename-⇑ᴿ-inv
    (lift-right-store-left liftρ)
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    with left-store-rename-⇑ᴿ-inv liftρ renameρ
left-store-rename-⇑ᴿ-inv
    (lift-right-store-left liftρ)
    (left-store-rename-left {α′ = α′} {A′ = A′} {hA′ = hA′}
      eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ =
  store-left α′ A′ hA′ ∷ ρ′ ,
  left-store-rename-left eqα eqA renameρ′ ,
  lift-right-store-left liftρ′
left-store-rename-⇑ᴿ-inv
    (lift-right-store-right {hB = hB} liftρ)
    (left-store-rename-right renameρ)
    with left-store-rename-⇑ᴿ-inv liftρ renameρ
left-store-rename-⇑ᴿ-inv
    (lift-right-store-right {hB = hB} liftρ)
    (left-store-rename-right renameρ)
    | ρ′ , renameρ′ , liftρ′ =
  store-right _ _ hB ∷ ρ′ ,
  left-store-rename-right renameρ′ ,
  lift-right-store-right liftρ′
left-store-rename-⇑ᴿ-inv
    (lift-right-store-link {p = p} shapeᴿ liftρ)
    (left-store-rename-link {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    with left-store-rename-⇑ᴿ-inv liftρ renameρ
left-store-rename-⇑ᴿ-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    (lift-right-store-link {p = p} shapeᴿ liftρ)
    (left-store-rename-link {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ =
  store-link α′ A′ _ _
      (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ ρ′ ,
  left-store-rename-link eqα eqA renameρ′ ,
  lift-right-store-link
    (trans
      (shape-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ _ _)
      (trans shapeᴿ
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftρ′

left-ctx-rename-⇑ᴿ-inv :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γ′ᴿ : CtxImp (⇑ᴿᵢ Ψ) Δᴸ′ (suc Δᴿ)} →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  LeftCtxRenameⁱ τ (rename-assm²-⇑ᴿᵢ assm) hτ γᴿ γ′ᴿ →
  ∃[ γ′ ]
    LeftCtxRenameⁱ τ assm hτ γ γ′ ×
    LiftRightCtxⁱ (⇑ᴿᵢ Ψ) γ′ γ′ᴿ
left-ctx-rename-⇑ᴿ-inv lift-right-ctx-[] left-ctx-rename-[] =
  [] , left-ctx-rename-[] , lift-right-ctx-[]
left-ctx-rename-⇑ᴿ-inv
    (lift-right-ctx-∷ {p = p} shapeᴿ liftγ)
    (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
    with left-ctx-rename-⇑ᴿ-inv liftγ renameγ
left-ctx-rename-⇑ᴿ-inv {τ = τ} {assm = assm} {hτ = hτ}
    (lift-right-ctx-∷ {p = p} shapeᴿ liftγ)
    (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
    | γ′ , renameγ′ , liftγ′ =
  ctx-imp A′ _ (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ γ′ ,
  left-ctx-rename-∷ eqA renameγ′ ,
  lift-right-ctx-∷
    (trans
      (shape-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ _ _)
      (trans shapeᴿ
        (sym (shape-rename-left-atᵢ
          τ assm hτ eqA p))))
    liftγ′

rename-left-storeⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} (τ : Renameᵗ) →
  (∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  TyRenameWf Δᴸ Δᴸ′ τ →
  StoreImp Φ Δᴸ Δᴿ →
  StoreImp Ψ Δᴸ′ Δᴿ
rename-left-storeⁱ τ assm hτ [] = []
rename-left-storeⁱ τ assm hτ
    (store-matched α A β B p ∷ ρ) =
  store-matched (τ α) (renameᵗ τ A) β B
    (⊑-rename-leftᵢ τ assm hτ p) ∷
  rename-left-storeⁱ τ assm hτ ρ
rename-left-storeⁱ τ assm hτ (store-left α A hA ∷ ρ) =
  store-left (τ α) (renameᵗ τ A)
    (renameᵗ-preserves-WfTy hA hτ) ∷
  rename-left-storeⁱ τ assm hτ ρ
rename-left-storeⁱ τ assm hτ (store-right β B hB ∷ ρ) =
  store-right β B hB ∷ rename-left-storeⁱ τ assm hτ ρ
rename-left-storeⁱ τ assm hτ (store-link α A β B p ∷ ρ) =
  store-link (τ α) (renameᵗ τ A) β B
    (⊑-rename-leftᵢ τ assm hτ p) ∷
  rename-left-storeⁱ τ assm hτ ρ

rename-left-store-coherentⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} (τ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ)
    (ρ : StoreImp Φ Δᴸ Δᴿ) →
  LeftStoreRenameⁱ τ assm hτ ρ
    (rename-left-storeⁱ τ assm hτ ρ)
rename-left-store-coherentⁱ τ assm hτ [] =
  left-store-rename-[]
rename-left-store-coherentⁱ τ assm hτ
    (store-matched α A β B p ∷ ρ) =
  left-store-rename-matched refl refl
    (rename-left-store-coherentⁱ τ assm hτ ρ)
rename-left-store-coherentⁱ τ assm hτ
    (store-left α A hA ∷ ρ) =
  left-store-rename-left refl refl
    (rename-left-store-coherentⁱ τ assm hτ ρ)
rename-left-store-coherentⁱ τ assm hτ
    (store-right β B hB ∷ ρ) =
  left-store-rename-right
    (rename-left-store-coherentⁱ τ assm hτ ρ)
rename-left-store-coherentⁱ τ assm hτ
    (store-link α A β B p ∷ ρ) =
  left-store-rename-link refl refl
    (rename-left-store-coherentⁱ τ assm hτ ρ)

rename-left-store-source-liftⁱ :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ
    (rename-left-storeⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc ρ)
rename-left-store-source-liftⁱ [] = lift-left-store-[]
rename-left-store-source-liftⁱ
    (store-matched α A β B p ∷ ρ) =
  lift-left-store-∷
    (shape-rename-left rename-assm²-source-νᵢ TyRenameWf-suc p)
    (rename-left-store-source-liftⁱ ρ)
rename-left-store-source-liftⁱ (store-left α A hA ∷ ρ) =
  lift-left-store-left (rename-left-store-source-liftⁱ ρ)
rename-left-store-source-liftⁱ (store-right β B hB ∷ ρ) =
  lift-left-store-right (rename-left-store-source-liftⁱ ρ)
rename-left-store-source-liftⁱ (store-link α A β B p ∷ ρ) =
  lift-left-store-link
    (shape-rename-left rename-assm²-source-νᵢ TyRenameWf-suc p)
    (rename-left-store-source-liftⁱ ρ)

leftStoreⁱ-rename-left :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    (ρ : StoreImp Φ Δᴸ Δᴿ) →
  leftStoreⁱ
      (rename-left-storeⁱ {Ψ = Ψ} {Δᴸ′ = Δᴸ′} τ assm hτ ρ)
    ≡ renameStoreᵗ τ (leftStoreⁱ ρ)
leftStoreⁱ-rename-left [] = refl
leftStoreⁱ-rename-left (store-matched α A β B p ∷ ρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-rename-left ρ)
leftStoreⁱ-rename-left (store-left α A hA ∷ ρ) =
  cong ((_,_ _ _) ∷_) (leftStoreⁱ-rename-left ρ)
leftStoreⁱ-rename-left (store-right β B hB ∷ ρ) =
  leftStoreⁱ-rename-left ρ
leftStoreⁱ-rename-left (store-link α A β B p ∷ ρ) =
  leftStoreⁱ-rename-left ρ

rightStoreⁱ-rename-left :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    (ρ : StoreImp Φ Δᴸ Δᴿ) →
  rightStoreⁱ
      (rename-left-storeⁱ {Ψ = Ψ} {Δᴸ′ = Δᴸ′} τ assm hτ ρ)
    ≡ rightStoreⁱ ρ
rightStoreⁱ-rename-left [] = refl
rightStoreⁱ-rename-left (store-matched α A β B p ∷ ρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-rename-left ρ)
rightStoreⁱ-rename-left (store-left α A hA ∷ ρ) =
  rightStoreⁱ-rename-left ρ
rightStoreⁱ-rename-left (store-right β B hB ∷ ρ) =
  cong ((_,_ _ _) ∷_) (rightStoreⁱ-rename-left ρ)
rightStoreⁱ-rename-left (store-link α A β B p ∷ ρ) =
  rightStoreⁱ-rename-left ρ

rename-left-ctxⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} (τ : Renameᵗ) →
  (∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  TyRenameWf Δᴸ Δᴸ′ τ →
  CtxImp Φ Δᴸ Δᴿ →
  CtxImp Ψ Δᴸ′ Δᴿ
rename-left-ctxⁱ τ assm hτ [] = []
rename-left-ctxⁱ τ assm hτ (ctx-imp A B p ∷ γ) =
  ctx-imp (renameᵗ τ A) B
    (⊑-rename-leftᵢ τ assm hτ p) ∷
  rename-left-ctxⁱ τ assm hτ γ

rename-left-ctx-coherentⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} (τ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ)
    (γ : CtxImp Φ Δᴸ Δᴿ) →
  LeftCtxRenameⁱ τ assm hτ γ
    (rename-left-ctxⁱ τ assm hτ γ)
rename-left-ctx-coherentⁱ τ assm hτ [] =
  left-ctx-rename-[]
rename-left-ctx-coherentⁱ τ assm hτ (ctx-imp A B p ∷ γ) =
  left-ctx-rename-∷ refl
    (rename-left-ctx-coherentⁱ τ assm hτ γ)

rename-left-ctx-source-liftⁱ :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ
    (rename-left-ctxⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc γ)
rename-left-ctx-source-liftⁱ [] = lift-left-ctx-[]
rename-left-ctx-source-liftⁱ (ctx-imp A B p ∷ γ) =
  lift-left-ctx-∷
    (shape-rename-left rename-assm²-source-νᵢ TyRenameWf-suc p)
    (rename-left-ctx-source-liftⁱ γ)

left-source-rename-worldsⁱ :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ)
    (γ : CtxImp Φ Δᴸ Δᴿ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ
      (rename-left-storeⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc ρ) ×
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ
      (rename-left-ctxⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc γ) ×
  LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc ρ
      (rename-left-storeⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc ρ) ×
  LeftCtxRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc γ
      (rename-left-ctxⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc γ)
left-source-rename-worldsⁱ ρ γ =
  rename-left-store-source-liftⁱ ρ ,
  rename-left-ctx-source-liftⁱ γ ,
  rename-left-store-coherentⁱ
    suc rename-assm²-source-νᵢ TyRenameWf-suc ρ ,
  rename-left-ctx-coherentⁱ
    suc rename-assm²-source-νᵢ TyRenameWf-suc γ

left-ctx-rename-lookupⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {x A B p} →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  γ ∋ x ⦂ ctx-imp A B p →
  ∃[ A′ ] ∃[ eqA ]
    γ′ ∋ x ⦂ ctx-imp A′ B
      (⊑-rename-left-atᵢ τ assm hτ eqA p)
left-ctx-rename-lookupⁱ
    (left-ctx-rename-∷ eqA renameγ) Z =
  _ , eqA , Z
left-ctx-rename-lookupⁱ
    (left-ctx-rename-∷ eqA renameγ) (S x∈) =
  let A′ , eqA′ , x∈′ = left-ctx-rename-lookupⁱ renameγ x∈ in
  A′ , eqA′ , S x∈′

left-rename-xᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {x A B p}
    {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  γ ∋ x ⦂ ctx-imp A B p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (` x) ⊑ ` x
    ⦂ renameᵗ τ A ⊑ B ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-xᵀ renameγ x∈ with left-ctx-rename-lookupⁱ renameγ x∈
left-rename-xᵀ renameγ x∈ | A′ , refl , x∈′ = x⊑xᵀ x∈′

left-rename-blameᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M A B} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ blame ⊑ M
    ⦂ renameᵗ τ A ⊑ B ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-blameᵀ renameρ renameγ M⊢ =
  blame⊑ᵀ (right-typing-left-renameⁱ renameρ renameγ M⊢)

left-rename-ƛᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {N N′ A A′ B B′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣
      ctx-imp (renameᵗ τ A) A′
        (⊑-rename-leftᵢ τ assm hτ pA) ∷ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ B ⊑ B′
    ∶ ⊑-rename-leftᵢ τ assm hτ pB →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ƛ N) ⊑ ƛ N′
    ⦂ renameᵗ τ (A ⇒ B) ⊑ A′ ⇒ B′
    ∶ ⊑-rename-leftᵢ τ assm hτ (pA ↦ pB)
left-rename-ƛᵀ {hτ = hτ} hA hA′ N⊑N′ =
  ƛ⊑ƛᵀ (renameᵗ-preserves-WfTy hA hτ) hA′ N⊑N′

left-rename-·ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {L L′ M M′ A A′ B B′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ L ⊑ L′
    ⦂ renameᵗ τ (A ⇒ B) ⊑ A′ ⇒ B′
    ∶ ⊑-rename-leftᵢ τ assm hτ (pA ↦ pB) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′
    ∶ ⊑-rename-leftᵢ τ assm hτ pA →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (L · M) ⊑ L′ · M′
    ⦂ renameᵗ τ B ⊑ B′
    ∶ ⊑-rename-leftᵢ τ assm hτ pB
left-rename-·ᵀ L⊑L′ M⊑M′ = ·⊑·ᵀ L⊑L′ M⊑M′

left-rename-cast⊒⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A B B′ c μ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (modeτ : CastModeRenamer τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  CastShape.narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-cast⊒⊑ᵀ
    {τ = τ} {assm = assm} {hτ = hτ} {p = p} {q = q}
    modeτ renameρ mode seal★ c⊒ c-shape comp M⊑M′ =
  cast⊒⊑ᵀ (CastModeRenamer.target-mode modeτ mode)
    (left-seal★-renameⁱ modeτ renameρ mode seal★)
    (left-narrowing-renameⁱ modeτ mode renameρ c⊒)
    M⊑M′ _
    (cast-shape-rename τ c-shape)
    (imprecision-composition-shape-transport
      refl
      (shape-rename-left assm hτ p)
      (shape-rename-left assm hτ q)
      comp)

left-rename-cast⊑⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A B B′ c μ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (modeτ : CastModeRenamer τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastShape.widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-cast⊑⊑ᵀ
    {τ = τ} {assm = assm} {hτ = hτ} {p = p} {q = q}
    modeτ renameρ mode seal★ c⊑ c-shape comp M⊑M′ =
  cast⊑⊑ᵀ (CastModeRenamer.target-mode modeτ mode)
    (left-seal★-renameⁱ modeτ renameρ mode seal★)
    (left-widening-renameⁱ modeτ mode renameρ c⊑)
    M⊑M′ _
    (cast-shape-rename τ c-shape)
    (imprecision-composition-shape-transport
      refl
      (shape-rename-left assm hτ q)
      (shape-rename-left assm hτ p)
      comp)

left-rename-⊑cast⊒ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A A′ B′ c′ μ′ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  CastShape.narrowing ⊢ᶜ c′ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑cast⊒ᵀ
    {assm = assm} {hτ = hτ} {p = p} {q = q}
    renameρ mode′ seal★′ c′⊒ c-shape comp M⊑M′ =
  ⊑cast⊒ᵀ mode′
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-narrowing-left-renameⁱ renameρ c′⊒) M⊑M′ _
    c-shape
    (imprecision-composition-shape-transport
      (shape-rename-left assm hτ q)
      refl
      (shape-rename-left assm hτ p)
      comp)

left-rename-⊑cast⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A A′ B′ c′ μ′ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  CastShape.widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑cast⊑ᵀ
    {assm = assm} {hτ = hτ} {p = p} {q = q}
    renameρ mode′ seal★′ c′⊑ c-shape comp M⊑M′ =
  ⊑cast⊑ᵀ mode′
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-widening-left-renameⁱ renameρ c′⊑) M⊑M′ _
    c-shape
    (imprecision-composition-shape-transport
      (shape-rename-left assm hτ p)
      refl
      (shape-rename-left assm hτ q)
      comp)

left-rename-quotient-widening-pairᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {u u′ D D′ A A′} →
  CastModeRenamer τ →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  QuotientWideningPair Δᴸ′ Δᴿ ρ′
    (renameᶜ τ u) u′
    (renameᵗ τ D) D′ (renameᵗ τ A) A′
left-rename-quotient-widening-pairᵀ {τ = τ} modeτ renameρ
    (quotient-id-widening source target) =
  quotient-id-widening
    (left-widening-rename-modeⁱ
      (modeRename-id-only τ) renameρ source)
    (right-widening-left-renameⁱ renameρ target)
left-rename-quotient-widening-pairᵀ modeτ renameρ
    (quotient-cast-widening
      mode seal★ source mode′ seal★′ target) =
  quotient-cast-widening
    (CastModeRenamer.target-mode modeτ mode)
    (left-seal★-renameⁱ modeτ renameρ mode seal★)
    (left-widening-rename-modeⁱ
      (CastModeRenamer.target-rename modeτ mode) renameρ source)
    mode′
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-widening-left-renameⁱ renameρ target)

left-rename-closeᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {N N′ A A′ D D′ u u′ s s′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  CastModeRenamer τ →
  (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  CastShape.widening ⊢ᶜ u ⦂ s →
  CastShape.widening ⊢ᶜ u′ ⦂ s′ →
  s ；⌊ pA ⌋≋ᵖ qD ； s′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA s s′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ qD →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (N ⟨ u ⟩) ⊑ N′ ⟨ u′ ⟩
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ pA
left-rename-closeᵀ
    {τ = τ} {assm = assm} {hτ = hτ}
    modeτ renameρ widening u-shape u′-shape square compatible N⊑N′ =
  closeᵀ N⊑N′
    (left-rename-quotient-widening-pairᵀ modeτ renameρ widening) _
    (cast-shape-rename τ u-shape) u′-shape
    (quotient-boundary-square-rename-left
      {τ = τ} {assm = assm} {hτ = hτ} square)
    (reduction-closed-quotient-compatible-rename-leftᵢ
      {assm = assm} hτ compatible)

left-rename-Λᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {V V′ A B} {p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  Value V →
  Value V′ →
  (∀ {ρ′∀ γ′∀} →
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ →
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ →
    LeftStoreRenameⁱ
      (extᵗ τ) (rename-assm²-∀-leftᵢ assm) (TyRenameWf-ext hτ)
      ρ∀ ρ′∀ →
    LeftCtxRenameⁱ
      (extᵗ τ) (rename-assm²-∀-leftᵢ assm) (TyRenameWf-ext hτ)
      γ∀ γ′∀ →
    ∀ᵢᶜ Ψ ∣ suc Δᴸ′ ∣ suc Δᴿ ∣ ρ′∀ ∣ γ′∀
      ⊢ᴺ renameᵗᵐ (extᵗ τ) V ⊑ V′
      ⦂ renameᵗ (extᵗ τ) A ⊑ B
      ∶ ⊑-rename-leftᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) p) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (Λ V) ⊑ Λ V′
    ⦂ renameᵗ τ (`∀ A) ⊑ `∀ B
    ∶ ⊑-rename-leftᵢ τ assm hτ (∀ⁱ p)
left-rename-Λᵀ renameρ renameγ liftρ liftγ vV vV′ body-map
    with left-store-rename-∀ renameρ liftρ
left-rename-Λᵀ renameρ renameγ liftρ liftγ vV vV′ body-map
    | ρ′∀ , liftρ′ , renameρ∀
    with left-ctx-rename-∀ renameγ liftγ
left-rename-Λᵀ {τ = τ}
    renameρ renameγ liftρ liftγ vV vV′ body-map
    | ρ′∀ , liftρ′ , renameρ∀
    | γ′∀ , liftγ′ , renameγ∀ =
  Λ⊑Λᵀ liftρ′ liftγ′
    (renameᵗᵐ-preserves-Value (extᵗ τ) vV) vV′
    (body-map liftρ′ liftγ′ renameρ∀ renameγ∀)

left-rename-Λ⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ A B}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  {{safe : NonVar A}} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  (occ : occurs zero A ≡ true) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  Value V →
  (∀ {ρ′ν γ′ν} →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν →
    LeftStoreRenameⁱ
      (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ)
      ρν ρ′ν →
    LeftCtxRenameⁱ
      (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ)
      γν γ′ν →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
      ∣ suc Δᴸ′ ∣ Δᴿ ∣ ρ′ν ∣ γ′ν
      ⊢ᴺ renameᵗᵐ (extᵗ τ) V ⊑ N′
      ⦂ renameᵗ (extᵗ τ) A ⊑ B
      ∶ ⊑-rename-leftᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) p) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (Λ V) ⊑ N′
    ⦂ renameᵗ τ (`∀ A) ⊑ B
    ∶ ⊑-rename-leftᵢ τ assm hτ (ν safe occ p)
left-rename-Λ⊑ᵀ {{safe}} renameρ renameγ occ liftρ liftγ vV body-map
    with left-store-rename-ν renameρ liftρ
left-rename-Λ⊑ᵀ {{safe}} renameρ renameγ occ liftρ liftγ vV body-map
    | ρ′ν , liftρ′ , renameρν
    with left-ctx-rename-ν renameγ liftγ
left-rename-Λ⊑ᵀ {τ = τ} {A = A} {{safe}}
    renameρ renameγ occ liftρ liftγ vV body-map
    | ρ′ν , liftρ′ , renameρν
    | γ′ν , liftγ′ , renameγν =
  Λ⊑ᵀ {{renameNonVar (extᵗ τ) safe}}
    (trans (occurs-zero-rename-ext τ A) occ)
    liftρ′ liftγ′ (renameᵗᵐ-preserves-Value (extᵗ τ) vV)
    (body-map liftρ′ liftγ′ renameρν renameγν)

left-rename-νᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {A A′ B B′ C C′ N N′ s s′ μ μ′}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  (A⇑⊑A′⇑ : ∀ᵢᶜ Φ
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  q
    [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ `∀ C′
    ∶ ⊑-rename-leftᵢ τ assm hτ (∀ⁱ q) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν A N s) ⊑ ν A′ N′ s′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-νᵀ
    ins renameρ renameγ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
    liftρ liftγ replace N⊑N′
    with left-store-rename-∀ renameρ liftρ
left-rename-νᵀ
    ins renameρ renameγ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
    liftρ liftγ replace N⊑N′
    | ρ′∀ , liftρ′ , renameρ∀
    with left-ctx-rename-∀ renameγ liftγ
left-rename-νᵀ {τ = τ} {assm = assm} {hτ = hτ} {A = A}
    ins renameρ renameγ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
    liftρ liftγ replace N⊑N′
    | ρ′∀ , liftρ′ , renameρ∀
    | γ′∀ , liftγ′ , renameγ∀ =
  ν⊑νᵀ
    (renameᵗ-preserves-WfTy hA hτ) hA′
    (left-reveal-ν-renameⁱ ins renameρ s↑)
    (right-reveal-ν-left-renameⁱ renameρ s′↑)
    (⊑-rename-leftᵢ τ assm hτ A⊑A′)
    shifted-A⊑A′
    liftρ′ liftγ′ N⊑N′
    (replace-paired-target-shape target-shape-eq
      (replace-paired-evidence-shape evidence-shape-eq
        transported-replace))
  where
  eqA = renameᵗ-ext-suc-comm τ A

  shifted-A⊑A′ =
    ⊑-rename-left-atᵢ
      (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
      (TyRenameWf-ext hτ) (sym eqA) A⇑⊑A′⇑

  renamed-A⊑A′ =
    ⊑-rename-leftᵢ
      (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
      (TyRenameWf-ext hτ) A⇑⊑A′⇑

  renamed-replace =
    replace-paired-rename-leftᵢ
      {α = zero} {β = zero}
      (rename-assm²-∀-leftᵢ assm)
      (TyRenameWf-ext hτ) replace

  transported-replace =
    replace-paired-transport-endpoints
      refl refl (renameᵗ-ext-suc-comm τ _) refl
      eqA refl renamed-replace

  evidence-shape-eq =
    trans
      (shape-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) (sym eqA) A⇑⊑A′⇑)
      (sym
        (trans
          (shape-transport-imprecision-endpoints
            eqA refl renamed-A⊑A′)
          (shape-rename-left
            (rename-assm²-∀-leftᵢ assm)
            (TyRenameWf-ext hτ) A⇑⊑A′⇑)))

  target-shape-eq =
    trans
      (shape-lift∀ᵢ (⊑-rename-leftᵢ τ assm hτ _))
      (trans
        (shape-rename-left assm hτ _)
        (trans
          (sym (shape-lift∀ᵢ _))
          (trans
            (sym
              (shape-rename-left
                (rename-assm²-∀-leftᵢ assm)
                (TyRenameWf-ext hτ) _))
            (sym
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ _) refl _)))))

left-rename-ν⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {A B B′ C N N′ s μ occ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar C}} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  WfTy Δᴸ A →
  WfTy (suc Δᴸ) (⇑ᵗ A) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ B′
    ∶ ⊑-rename-leftᵢ τ assm hτ (ν safe occ q) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν A N s) ⊑ N′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-ν⊑ᵀ
    ins renameρ renameγ hA h⇑A s↑ liftρ liftγ replace N⊑N′
    with left-store-rename-ν renameρ liftρ
left-rename-ν⊑ᵀ
    ins renameρ renameγ hA h⇑A s↑ liftρ liftγ replace N⊑N′
    | ρ′ν , liftρ′ , renameρν
    with left-ctx-rename-ν renameγ liftγ
left-rename-ν⊑ᵀ
    {Δᴸ′ = Δᴸ′} {τ = τ} {assm = assm}
    {hτ = hτ} {A = A} {{safe = safe}}
    ins renameρ renameγ hA h⇑A s↑ liftρ liftγ replace N⊑N′
    | ρ′ν , liftρ′ , renameρν
    | γ′ν , liftγ′ , renameγν =
  ν⊑ᵀ {{renameNonVar (extᵗ τ) safe}}
    (renameᵗ-preserves-WfTy hA hτ) h⇑A′
    (left-reveal-ν-renameⁱ ins renameρ s↑)
    liftρ′ liftγ′ N⊑N′
    (replace-left-target-shape target-shape-eq
      transported-replace)
  where
  h⇑A′ : WfTy (suc Δᴸ′) (⇑ᵗ (renameᵗ τ A))
  h⇑A′ =
    subst (WfTy (suc Δᴸ′))
      (renameᵗ-ext-suc-comm τ A)
      (renameᵗ-preserves-WfTy h⇑A (TyRenameWf-ext hτ))

  renamed-replace =
    replace-left-rename-leftᵢ
      {α = zero}
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) replace

  transported-replace =
    replace-left-transport-endpoints
      refl refl
      (renameᵗ-ext-suc-comm τ _)
      (renameᵗ-ext-suc-comm τ A)
      renamed-replace

  target-shape-eq =
    trans
      (shape-source-liftνᵢ (⊑-rename-leftᵢ τ assm hτ _))
      (trans
        (shape-rename-left assm hτ _)
        (trans
          (sym (shape-source-liftνᵢ _))
          (trans
            (sym
              (shape-rename-left
                (rename-assm²-⇑ᴸᵢ assm)
                (TyRenameWf-ext hτ) _))
            (sym
              (shape-transport-imprecision-endpoints
                (renameᵗ-ext-suc-comm τ _) refl _)))))

leftCtxⁱ-rename-left :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    (γ : CtxImp Φ Δᴸ Δᴿ) →
  leftCtxⁱ
      (rename-left-ctxⁱ {Ψ = Ψ} {Δᴸ′ = Δᴸ′} τ assm hτ γ)
    ≡ map (renameᵗ τ) (leftCtxⁱ γ)
leftCtxⁱ-rename-left [] = refl
leftCtxⁱ-rename-left (ctx-imp A B p ∷ γ) =
  cong (renameᵗ _ A ∷_) (leftCtxⁱ-rename-left γ)

rightCtxⁱ-rename-left :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    (γ : CtxImp Φ Δᴸ Δᴿ) →
  rightCtxⁱ
      (rename-left-ctxⁱ {Ψ = Ψ} {Δᴸ′ = Δᴸ′} τ assm hτ γ)
    ≡ rightCtxⁱ γ
rightCtxⁱ-rename-left [] = refl
rightCtxⁱ-rename-left (ctx-imp A B p ∷ γ) =
  cong (B ∷_) (rightCtxⁱ-rename-left γ)

rename-left-ctx-∋ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ} {γ x A B p} →
  γ ∋ x ⦂ ctx-imp A B p →
  rename-left-ctxⁱ {Φ = Φ} {Ψ = Ψ}
      {Δᴸ = Δᴸ} {Δᴸ′ = Δᴸ′} {Δᴿ = Δᴿ}
      τ assm hτ γ
    ∋ x ⦂ ctx-imp (renameᵗ τ A) B
      (⊑-rename-leftᵢ τ assm hτ p)
rename-left-ctx-∋ Z = Z
rename-left-ctx-∋ (S x∈) = S (rename-left-ctx-∋ x∈)

rename-left-store-matched∈ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ} {ρ α A β B p} →
  store-matched α A β B p ∈ ρ →
  store-matched (τ α) (renameᵗ τ A) β B
      (⊑-rename-leftᵢ τ assm hτ p)
    ∈ rename-left-storeⁱ {Φ = Φ} {Ψ = Ψ}
      {Δᴸ = Δᴸ} {Δᴸ′ = Δᴸ′} {Δᴿ = Δᴿ}
      τ assm hτ ρ
rename-left-store-matched∈ (here refl) = here refl
rename-left-store-matched∈
    {ρ = store-matched α A β B p ∷ ρ} (there p∈) =
  there (rename-left-store-matched∈ p∈)
rename-left-store-matched∈
    {ρ = store-left α A hA ∷ ρ} (there p∈) =
  there (rename-left-store-matched∈ p∈)
rename-left-store-matched∈
    {ρ = store-right β B hB ∷ ρ} (there p∈) =
  there (rename-left-store-matched∈ p∈)
rename-left-store-matched∈
    {ρ = store-link α A β B p ∷ ρ} (there p∈) =
  there (rename-left-store-matched∈ p∈)

rename-left-store-link∈ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ} {ρ α A β B p} →
  store-link α A β B p ∈ ρ →
  store-link (τ α) (renameᵗ τ A) β B
      (⊑-rename-leftᵢ τ assm hτ p)
    ∈ rename-left-storeⁱ {Φ = Φ} {Ψ = Ψ}
      {Δᴸ = Δᴸ} {Δᴸ′ = Δᴸ′} {Δᴿ = Δᴿ}
      τ assm hτ ρ
rename-left-store-link∈ (here refl) = here refl
rename-left-store-link∈
    {ρ = store-matched α A β B p ∷ ρ} (there p∈) =
  there (rename-left-store-link∈ p∈)
rename-left-store-link∈
    {ρ = store-left α A hA ∷ ρ} (there p∈) =
  there (rename-left-store-link∈ p∈)
rename-left-store-link∈
    {ρ = store-right β B hB ∷ ρ} (there p∈) =
  there (rename-left-store-link∈ p∈)
rename-left-store-link∈
    {ρ = store-link α A β B p ∷ ρ} (there p∈) =
  there (rename-left-store-link∈ p∈)

rename-left-correspondence :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ} {τ : Renameᵗ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ} {ρ α A β B p} →
  StoreCorresponds ρ α A β B p →
  StoreCorresponds
    (rename-left-storeⁱ {Φ = Φ} {Ψ = Ψ}
      {Δᴸ = Δᴸ} {Δᴸ′ = Δᴸ′} {Δᴿ = Δᴿ}
      τ assm hτ ρ)
    (τ α) (renameᵗ τ A) β B
    (⊑-rename-leftᵢ τ assm hτ p)
rename-left-correspondence (correspondence-stored p∈) =
  correspondence-stored (rename-left-store-matched∈ p∈)
rename-left-correspondence (correspondence-linked p∈) =
  correspondence-linked (rename-left-store-link∈ p∈)

left-store-rename-matched∈ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {α A β B p} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  store-matched α A β B p ∈ ρ →
  ∃[ α′ ] α′ ≡ τ α × ∃[ A′ ] ∃[ eqA ]
    store-matched α′ A′ β B
      (⊑-rename-left-atᵢ τ assm hτ eqA p) ∈ ρ′
left-store-rename-matched∈ⁱ
    (left-store-rename-matched eqα eqA renameρ) (here refl) =
  _ , eqα , _ , eqA , here refl
left-store-rename-matched∈ⁱ
    (left-store-rename-matched eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′
left-store-rename-matched∈ⁱ
    (left-store-rename-left eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′
left-store-rename-matched∈ⁱ
    (left-store-rename-right renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′
left-store-rename-matched∈ⁱ
    (left-store-rename-link eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′

left-store-rename-link∈ⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {α A β B p} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  store-link α A β B p ∈ ρ →
  ∃[ α′ ] α′ ≡ τ α × ∃[ A′ ] ∃[ eqA ]
    store-link α′ A′ β B
      (⊑-rename-left-atᵢ τ assm hτ eqA p) ∈ ρ′
left-store-rename-link∈ⁱ
    (left-store-rename-matched eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′
left-store-rename-link∈ⁱ
    (left-store-rename-left eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′
left-store-rename-link∈ⁱ
    (left-store-rename-right renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′
left-store-rename-link∈ⁱ
    (left-store-rename-link eqα eqA renameρ) (here refl) =
  _ , eqα , _ , eqA , here refl
left-store-rename-link∈ⁱ
    (left-store-rename-link eqα eqA renameρ) (there p∈) =
  let α′ , eqα′ , A′ , eqA′ , p∈′ =
        left-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα′ , A′ , eqA′ , there p∈′

left-store-rename-correspondenceⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {α A β B p} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  StoreCorresponds ρ α A β B p →
  ∃[ α′ ] α′ ≡ τ α × ∃[ A′ ] ∃[ eqA ]
    StoreCorresponds ρ′ α′ A′ β B
      (⊑-rename-left-atᵢ τ assm hτ eqA p)
left-store-rename-correspondenceⁱ renameρ
    (correspondence-stored p∈) =
  let α′ , eqα , A′ , eqA , p∈′ =
        left-store-rename-matched∈ⁱ renameρ p∈ in
  α′ , eqα , A′ , eqA , correspondence-stored p∈′
left-store-rename-correspondenceⁱ renameρ
    (correspondence-linked p∈) =
  let α′ , eqα , A′ , eqA , p∈′ =
        left-store-rename-link∈ⁱ renameρ p∈ in
  α′ , eqα , A′ , eqA , correspondence-linked p∈′

left-rename-paired-revealᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ c c′ A A′ B B′ α β X X′ pX μ μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  StoreCorresponds ρ α X β X′ pX →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-paired-revealᵀ ins renameρ corr conv conv′ replace M⊑M′
    with left-store-rename-correspondenceⁱ renameρ corr
left-rename-paired-revealᵀ ins renameρ corr conv conv′ replace M⊑M′
    | α′ , refl , A′ , refl , corr′ =
  paired-revealᵀ corr′
    (left-reveal-renameⁱ ins renameρ conv)
    (right-reveal-left-renameⁱ renameρ conv′)
    (replace-paired-rename-leftᵢ _ _ replace)
    M⊑M′

left-rename-paired-concealᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ c c′ A A′ B B′ α β X X′ pX μ μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  StoreCorresponds ρ α X β X′ pX →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-paired-concealᵀ
    ins renameρ corr conv conv′ replace M⊑M′
    with left-store-rename-correspondenceⁱ renameρ corr
left-rename-paired-concealᵀ
    ins renameρ corr conv conv′ replace M⊑M′
    | α′ , refl , A′ , refl , corr′ =
  paired-concealᵀ corr′
    (left-conceal-renameⁱ ins renameρ conv)
    (right-conceal-left-renameⁱ renameρ conv′)
    (replace-paired-rename-leftᵢ _ _ replace)
    M⊑M′

left-rename-paired-wideningᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ c c′ A A′ B B′ μ μ′ s s′ r}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastShape.widening ⊢ᶜ c ⦂ s →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  CastShape.widening ⊢ᶜ c′ ⦂ s′ →
  s ； ⌊ q ⌋ ≋ r →
  ⌊ p ⌋ ； s′ ≋ r →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ p q s s′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-paired-wideningᵀ
    {assm = assm} {hτ = hτ} ins renameρ
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    left-square right-square compat M⊑M′ =
  paired-wideningᵀ
    (CastModeRenamer.target-mode modeτ mode)
    (left-seal★-renameⁱ modeτ renameρ mode seal★)
    (left-widening-renameⁱ modeτ mode renameρ c⊑)
    (cast-shape-rename _ c-shape)
    mode′
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-widening-left-renameⁱ renameρ c′⊑)
    c′-shape
    (imprecision-composition-shape-transport
      refl (shape-rename-left assm hτ _) refl left-square)
    (imprecision-composition-shape-transport
      (shape-rename-left assm hτ _) refl refl right-square)
    (reduction-closed-paired-compatible-rename-leftᵢ
      {assm = assm} hτ compat)
    M⊑M′
  where
  modeτ = left-insertion-cast-renamer ins

left-rename-conv↑⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A B B′ c μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  p [ α ↦ X ]ᴸ q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-conv↑⊑ᵀ ins renameρ conv M⊑M′ replace =
  conv↑⊑ᵀ (left-reveal-renameⁱ ins renameρ conv) M⊑M′ _
    (replace-left-rename-leftᵢ _ _ replace)

left-rename-conv↓⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A B B′ c μ α X}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  q [ α ↦ X ]ᴸ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-conv↓⊑ᵀ ins renameρ conv M⊑M′ replace =
  conv↓⊑ᵀ (left-conceal-renameⁱ ins renameρ conv) M⊑M′ _
    (replace-left-rename-leftᵢ _ _ replace)

left-rename-⊑conv↑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A A′ B′ c′ μ′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  p [ β ↦ X′ ]ᴿ q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑conv↑ᵀ renameρ conv M⊑M′ replace =
  ⊑conv↑ᵀ (right-reveal-left-renameⁱ renameρ conv) M⊑M′ _
    (replace-right-rename-leftᵢ _ _ replace)

left-rename-⊑conv↓ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A A′ B′ c′ μ′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  q [ β ↦ X′ ]ᴿ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑conv↓ᵀ renameρ conv M⊑M′ replace =
  ⊑conv↓ᵀ (right-conceal-left-renameⁱ renameρ conv) M⊑M′ _
    (replace-right-rename-leftᵢ _ _ replace)

right-target-square-α⊑ᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {ρ× : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      (suc Δᴸ) (suc Δᴿ)}
    {L N′ A B′ C}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {{safe : NonVar C}}
    {occ : occurs zero C ≡ true} →
  Value L →
  No• L →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  LiftRightStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴸ ρ× →
  LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴿ ρ× →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρᴿ ∣ []
    ⊢ᴺ L ⊑ ⇑ᵗᵐ N′
    ⦂ `∀ C ⊑ ⇑ᵗ B′ ∶ ν _ occ (⊑-target-under-leftᵢ p) →
  suc Δᴸ ∣
    leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρᴸ) ∣ []
    ⊢ (⇑ᵗᵐ L) • ⦂ C →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
    ∣ suc Δᴸ ∣ suc Δᴿ ∣
    store-left zero (⇑ᵗ A) h⇑A ∷ ρ× ∣ []
    ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ N′
    ⦂ C ⊑ ⇑ᵗ B′ ∶ ⊑-target-under-leftᵢ p
right-target-square-α⊑ᵀ
    vL noL h⇑A rightᴸρ leftᴿρ L⊑N′ L•⊢ =
  α⊑ᵀ vL noL h⇑A leftᴿρ lift-left-ctx-[] L⊑N′
    source-typing target-typing
  where
  source-typing =
    subst
      (λ Σ → _ ∣ (zero , _) ∷ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (leftStoreⁱ-lift-right rightᴸρ)) L•⊢

  target-typing =
    subst
      (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (rightStoreⁱ-lift-left leftᴿρ))
      (nu-term-imprecision-target-typing L⊑N′)

right-target-lift-α⊑ᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴸ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {L N′ A B′ C}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {{safe : NonVar C}}
    {occ : occurs zero C ≡ true} →
  Value L →
  No• L →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᴸ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γᴸ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρᴿ ∣ γᴿ
    ⊢ᴺ L ⊑ ⇑ᵗᵐ N′
    ⦂ `∀ C ⊑ ⇑ᵗ B′ ∶ ν _ occ (⊑-target-under-leftᵢ p) →
  suc Δᴸ ∣
    leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρᴸ) ∣
    leftCtxⁱ γᴸ ⊢ (⇑ᵗᵐ L) • ⦂ C →
  ∃[ ρ× ] ∃[ γ× ]
    LiftRightStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴸ ρ× ×
    LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρᴿ ρ× ×
    LiftRightCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) γᴸ γ× ×
    LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) γᴿ γ× ×
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      ∣ suc Δᴸ ∣ suc Δᴿ ∣
      store-left zero (⇑ᵗ A) h⇑A ∷ ρ× ∣ γ×
      ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ N′
      ⦂ C ⊑ ⇑ᵗ B′ ∶ ⊑-target-under-leftᵢ p
right-target-lift-α⊑ᵀ
    vL noL h⇑A liftᴸρ liftᴸγ liftᴿρ liftᴿγ
    L⊑N′ L•⊢
    with left-right-store-commute-left-lastⁱ liftᴸρ liftᴿρ
right-target-lift-α⊑ᵀ
    vL noL h⇑A liftᴸρ liftᴸγ liftᴿρ liftᴿγ
    L⊑N′ L•⊢
    | ρ× , rightᴸρ , leftᴿρ
    with left-right-ctx-commute-left-lastⁱ liftᴸγ liftᴿγ
right-target-lift-α⊑ᵀ
    vL noL h⇑A liftᴸρ liftᴸγ liftᴿρ liftᴿγ
    L⊑N′ L•⊢
    | ρ× , rightᴸρ , leftᴿρ
    | γ× , rightᴸγ , leftᴿγ =
  ρ× , γ× , rightᴸρ , leftᴿρ , rightᴸγ , leftᴿγ ,
  α⊑ᵀ vL noL h⇑A leftᴿρ leftᴿγ L⊑N′
    source-typing target-typing
  where
  source-typing =
    subst
      (λ Γ → _ ∣
        leftStoreⁱ (store-left zero _ h⇑A ∷ ρ×) ∣ Γ
        ⊢ _ ⦂ _)
      (sym (leftCtxⁱ-lift-right rightᴸγ))
      (subst
        (λ Σ → _ ∣ (zero , _) ∷ Σ ∣ leftCtxⁱ _
          ⊢ _ ⦂ _)
        (sym (leftStoreⁱ-lift-right rightᴸρ)) L•⊢)

  target-typing =
    subst
      (λ Γ → _ ∣ rightStoreⁱ ρ× ∣ Γ ⊢ _ ⦂ _)
      (sym (rightCtxⁱ-lift-left leftᴿγ))
      (subst
        (λ Σ → _ ∣ Σ ∣ rightCtxⁱ _ ⊢ _ ⦂ _)
        (sym (rightStoreⁱ-lift-left leftᴿρ))
        (nu-term-imprecision-target-typing L⊑N′))

left-source-lift-allocation-leftᵀ :
  ∀ {Φ Δᴸ Δᴿ α α′ A A′ B B′ M M′}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρν′ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν′ : CtxImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) Δᴿ}
    {hA : WfTy (suc Δᴸ) A}
    {hA′ : WfTy (suc (suc Δᴸ)) A′}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  No• M →
  LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
    (store-left α A hA ∷ ρν)
    (store-left α′ A′ hA′ ∷ ρν′) →
  LeftCtxRenameⁱ suc rename-assm²-source-νᵢ
    TyRenameWf-suc γν γν′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
    ∣ suc (suc Δᴸ) ∣ Δᴿ ∣ ρν′ ∣ γν′
    ⊢ᴺ ⇑ᵗᵐ M ⊑ M′ ⦂ ⇑ᵗ B ⊑ B′
    ∶ ⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
      TyRenameWf-suc p →
  suc Δᴸ ∣ leftStoreⁱ (store-left α A hA ∷ ρν)
    ∣ leftCtxⁱ γν ⊢ M ⦂ B →
  Δᴿ ∣ rightStoreⁱ (store-left α A hA ∷ ρν)
    ∣ rightCtxⁱ γν ⊢ M′ ⦂ B′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
    ∣ suc (suc Δᴸ) ∣ Δᴿ ∣
    store-left α′ A′ hA′ ∷ ρν′ ∣ γν′
    ⊢ᴺ ⇑ᵗᵐ M ⊑ M′ ⦂ ⇑ᵗ B ⊑ B′
    ∶ ⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
      TyRenameWf-suc p
left-source-lift-allocation-leftᵀ noM
    (left-store-rename-left eqα eqA renameρν)
    renameγν M⊑M′ M⊢ M′⊢ with eqα
left-source-lift-allocation-leftᵀ noM
    (left-store-rename-left eqα eqA renameρν)
    renameγν M⊑M′ M⊢ M′⊢ | refl with eqA
left-source-lift-allocation-leftᵀ
    {α = α} {A = A} {ρν = ρν} {ρν′ = ρν′}
    {hA = hA} {hA′ = hA′} noM
    (left-store-rename-left eqα eqA renameρν)
    renameγν M⊑M′ M⊢ M′⊢ | refl | refl =
  allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ)
    M⊑M′ source-typing target-typing
  where
  full-rename :
    LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
      (store-left α A hA ∷ ρν)
      (store-left (suc α) (⇑ᵗ A) hA′ ∷ ρν′)
  full-rename = left-store-rename-left refl refl renameρν

  source-typing =
    left-typing-renameⁱ {ψ = predᵗ}
      RenameLeftInverse-suc castModeRenamer-suc
      full-rename renameγν noM M⊢

  target-typing =
    right-typing-left-renameⁱ full-rename renameγν M′⊢

left-rename-allocation-prefixᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′⁺ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A B} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  LeftStoreRenameⁱ τ assm hτ ρ⁺ ρ′⁺ →
  (∀ {ρ₀′} → LeftStoreRenameⁱ τ assm hτ ρ₀ ρ₀′ →
    Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ₀′ ∣ γ′
      ⊢ᴺ renameᵗᵐ τ M ⊑ M′
      ⦂ renameᵗ τ A ⊑ B ∶ ⊑-rename-leftᵢ τ assm hτ p) →
  Δᴸ′ ∣ leftStoreⁱ ρ′⁺ ∣ leftCtxⁱ γ′
    ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A →
  Δᴿ ∣ rightStoreⁱ ρ′⁺ ∣ rightCtxⁱ γ′ ⊢ M′ ⦂ B →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′⁺ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ B ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-allocation-prefixᵀ prefix renameρ body-map M⊢ M′⊢
    with left-store-rename-prefix-invⁱ prefix renameρ
left-rename-allocation-prefixᵀ prefix renameρ body-map M⊢ M′⊢
    | ρ₀′ , renameρ₀ , prefix′ =
  allocation-prefixᵀ prefix′ (body-map renameρ₀) M⊢ M′⊢

⊑-lift-under-∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ renameᵗ (extᵗ suc) A ⊑ renameᵗ (extᵗ suc) B
    ⊣ suc (suc Δᴿ)
⊑-lift-under-∀ᵢ =
  ⊑-renameᵗ²ᵢ
    (rename-assm²-⇑ᵢ rename-assm²-∀ᵢ)
    (TyRenameWf-ext TyRenameWf-suc)
    (TyRenameWf-ext TyRenameWf-suc)

⊑-lift-source-nuᵢ :
  ∀ {Φ Δᴸ Δᴿ C B}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ) →
  SourceNuIndex (⊑-lift∀ᵢ (ν safe occ p))
⊑-lift-source-nuᵢ {C = C} safe occ p =
  source-nu-index
    (renameNonVar (extᵗ suc) safe)
    (trans (occurs-zero-rename-ext suc C) occ)
    (⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᴸᵢ rename-assm²-∀ᵢ)
      (TyRenameWf-ext TyRenameWf-suc)
      TyRenameWf-suc
      p)
    refl

⊑-source-lift-source-nuᵢ :
  ∀ {Φ Δᴸ Δᴿ C B}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ) →
  SourceNuIndex (⊑-source-liftνᵢ (ν safe occ p))
⊑-source-lift-source-nuᵢ {C = C} {B = B} safe occ p =
  sourceNuIndex-transport refl (renameᵗ-id B) raw-shape
  where
  raw-shape =
    source-nu-index
      (renameNonVar (extᵗ suc) safe)
      (trans (occurs-zero-rename-ext suc C) occ)
      (⊑-renameᵗ²ᵢ
        {ρ = extᵗ suc}
        {σ = λ X → X}
        (rename-assm²-⇑ᴸᵢ rename-assm²-source-νᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        (λ X<Δ → X<Δ)
        p)
      refl

⊑-target-lift-right-under-∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ (⇑ᴿᵢ Φ) ∣ suc Δᴸ
    ⊢ A ⊑ renameᵗ (extᵗ suc) B ⊣ suc (suc Δᴿ)
⊑-target-lift-right-under-∀ᵢ {A = A} p =
  subst
    (λ T → _ ∣ _ ⊢ T ⊑ renameᵗ (extᵗ suc) _ ⊣ _)
    (renameᵗ-ext-id A)
    (⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᵢ rename-assm²-target-rightᵢ)
      (TyRenameWf-ext (λ X<Δ → X<Δ))
      (TyRenameWf-ext TyRenameWf-suc)
      p)

rename-assm²-paired-under-right-tailᵢ :
  ∀ {Φ a} →
  a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ suc (extᵗ suc) a ∈ ⇑ᴿᵢ (⇑ᵢ Φ)
rename-assm²-paired-under-right-tailᵢ {Φ = []} ()
rename-assm²-paired-under-right-tailᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (here refl) =
  here refl
rename-assm²-paired-under-right-tailᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (there a∈) =
  there (rename-assm²-paired-under-right-tailᵢ a∈)
rename-assm²-paired-under-right-tailᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (here refl) =
  here refl
rename-assm²-paired-under-right-tailᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (there a∈) =
  there (rename-assm²-paired-under-right-tailᵢ a∈)

rename-assm²-paired-under-rightᵢ :
  ∀ {Φ a} →
  a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ suc (extᵗ suc) a ∈ ⇑ᴿᵢ (∀ᵢᶜ Φ)
rename-assm²-paired-under-rightᵢ a∈ =
  there (rename-assm²-paired-under-right-tailᵢ a∈)

⊑-lift-under-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ⇑ᴿᵢ (∀ᵢᶜ Φ) ∣ suc Δᴸ
    ⊢ ⇑ᵗ A ⊑ renameᵗ (extᵗ suc) B
    ⊣ suc (suc Δᴿ)
⊑-lift-under-rightᵢ =
  ⊑-renameᵗ²ᵢ
    rename-assm²-paired-under-rightᵢ
    TyRenameWf-suc
    (TyRenameWf-ext TyRenameWf-suc)

rename-assm²-right-under-rightᵢ :
  ∀ {Φ a} →
  a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ (λ X → X) (extᵗ suc) a ∈ ⇑ᴿᵢ (⇑ᴿᵢ Φ)
rename-assm²-right-under-rightᵢ {Φ = []} ()
rename-assm²-right-under-rightᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (here refl) =
  here refl
rename-assm²-right-under-rightᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (there a∈) =
  there (rename-assm²-right-under-rightᵢ a∈)
rename-assm²-right-under-rightᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (here refl) =
  here refl
rename-assm²-right-under-rightᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (there a∈) =
  there (rename-assm²-right-under-rightᵢ a∈)

⊑-target-lift-under-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ⇑ᴿᵢ (⇑ᴿᵢ Φ) ∣ Δᴸ
    ⊢ A ⊑ renameᵗ (extᵗ suc) B
    ⊣ suc (suc Δᴿ)
⊑-target-lift-under-rightᵢ {A = A} p =
  subst
    (λ T → _ ∣ _ ⊢ T ⊑ renameᵗ (extᵗ suc) _ ⊣ _)
    (renameᵗ-id A)
    (⊑-renameᵗ²ᵢ
      rename-assm²-right-under-rightᵢ
      (λ X<Δ → X<Δ)
      (TyRenameWf-ext TyRenameWf-suc)
      p)

rename-assm²-crossed-under-right-tailᵢ :
  ∀ {Φ a} →
  a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ
    (λ X → suc (suc X))
    (extᵗ (λ X → suc (suc X))) a
    ∈ ⇑ᴿᵢ (⇑ᵢ (⇑ᵢ Φ))
rename-assm²-crossed-under-right-tailᵢ {Φ = []} ()
rename-assm²-crossed-under-right-tailᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (here refl) =
  here refl
rename-assm²-crossed-under-right-tailᵢ
    {Φ = (X ˣ⊑★) ∷ Φ} (there a∈) =
  there (rename-assm²-crossed-under-right-tailᵢ a∈)
rename-assm²-crossed-under-right-tailᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (here refl) =
  here refl
rename-assm²-crossed-under-right-tailᵢ
    {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (there a∈) =
  there (rename-assm²-crossed-under-right-tailᵢ a∈)

rename-assm²-crossed-under-rightᵢ :
  ∀ {Φ a} →
  a ∈ ⇑ᴿᵢ Φ →
  rename-assm²ᵢ
    (λ X → suc (suc X))
    (extᵗ (λ X → suc (suc X))) a
    ∈ ⇑ᴿᵢ (swapRight∀∀ᵢ Φ)
rename-assm²-crossed-under-rightᵢ a∈ =
  there (there (rename-assm²-crossed-under-right-tailᵢ a∈))

renameᵗ-double-lift :
  ∀ A →
  ⇑ᵗ (⇑ᵗ A) ≡ renameᵗ (λ X → suc (suc X)) A
renameᵗ-double-lift A = renameᵗ-compose suc suc A

renameᵗ-double-under-∀ :
  ∀ A →
  renameᵗ (extᵗ suc) (renameᵗ (extᵗ suc) A) ≡
    renameᵗ (extᵗ (λ X → suc (suc X))) A
renameᵗ-double-under-∀ A =
  trans (renameᵗ-compose (extᵗ suc) (extᵗ suc) A)
    (rename-cong (λ { zero → refl ; (suc X) → refl }) A)

⊑-crossed-double-lift-under-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ⇑ᴿᵢ (swapRight∀∀ᵢ Φ) ∣ suc (suc Δᴸ)
    ⊢ ⇑ᵗ (⇑ᵗ A)
      ⊑ renameᵗ (extᵗ suc) (renameᵗ (extᵗ suc) B)
    ⊣ suc (suc (suc Δᴿ))
⊑-crossed-double-lift-under-rightᵢ {A = A} {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢ ⇑ᵗ (⇑ᵗ A) ⊑ T ⊣ _)
    (sym (renameᵗ-double-under-∀ B))
    (subst
      (λ S → _ ∣ _ ⊢ S ⊑
        renameᵗ (extᵗ (λ X → suc (suc X))) B ⊣ _)
      (sym (renameᵗ-double-lift A))
      (⊑-renameᵗ²ᵢ
        rename-assm²-crossed-under-rightᵢ
        (λ X<Δ → s<s (s<s X<Δ))
        (TyRenameWf-ext (λ X<Δ → s<s (s<s X<Δ)))
        p))

⊑-crossed-double-lift-under-∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  ∀ᵢᶜ (swapRight∀∀ᵢ Φ) ∣ suc (suc (suc Δᴸ))
    ⊢ renameᵗ (extᵗ suc) (renameᵗ (extᵗ suc) A)
      ⊑ renameᵗ (extᵗ suc) (renameᵗ (extᵗ suc) B)
    ⊣ suc (suc (suc Δᴿ))
⊑-crossed-double-lift-under-∀ᵢ {A = A} {B = B} p =
  subst
    (λ T → _ ∣ _ ⊢
      renameᵗ (extᵗ suc) (renameᵗ (extᵗ suc) A) ⊑ T ⊣ _)
    (sym (renameᵗ-double-under-∀ B))
    (subst
      (λ S → _ ∣ _ ⊢ S ⊑
        renameᵗ (extᵗ (λ X → suc (suc X))) B ⊣ _)
      (sym (renameᵗ-double-under-∀ A))
      (⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᵢ rename-assm²-crossed-double∀∀ᵢ)
        (TyRenameWf-ext (λ X<Δ → s<s (s<s X<Δ)))
        (TyRenameWf-ext (λ X<Δ → s<s (s<s X<Δ)))
        p))

⊑-crossed-double-lift-source-nuᵢ :
  ∀ {Φ Δᴸ Δᴿ C B}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B ⊣ Δᴿ) →
  SourceNuIndex (⊑-crossed-double-lift∀∀ᵢ (ν safe occ p))
⊑-crossed-double-lift-source-nuᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {C = C} {B = B}
    safe occ p =
  sourceNuIndex-reindex (sym outer-equalities) transported
  where
  double : TyVar → TyVar
  double X = suc (suc X)

  renamed-body =
    ⊑-renameᵗ²ᵢ
      (rename-assm²-⇑ᴸᵢ rename-assm²-crossed-double∀∀ᵢ)
      (TyRenameWf-ext (λ X<Δ → s<s (s<s X<Δ)))
      (λ X<Δ → s<s (s<s X<Δ))
      p

  raw-shape =
    source-nu-index
      (renameNonVar (extᵗ double) safe)
      (trans (occurs-zero-rename-ext double C) occ)
      renamed-body refl

  transported =
    sourceNuIndex-transport
      (sym (renameᵗ-double-under-∀ C))
      (sym (renameᵗ-double-lift B))
      raw-shape

  outer-equalities =
    cong₂
      (λ eqC eqB →
        subst
          (λ T → swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
            ⊢ `∀
                (renameᵗ (extᵗ suc) (renameᵗ (extᵗ suc) C))
              ⊑ T
            ⊣ suc (suc Δᴿ))
          eqB
          (subst
            (λ S → swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
              ⊢ S ⊑ renameᵗ double B ⊣ suc (suc Δᴿ))
            eqC
            (⊑-renameᵗ²ᵢ
              rename-assm²-crossed-double∀∀ᵢ
              (λ X<Δ → s<s (s<s X<Δ))
              (λ X<Δ → s<s (s<s X<Δ))
              (ν safe occ p))))
      (equality-proof-unique
        (sym (renameᵗ-compose suc suc (`∀ C)))
        (cong `∀ (sym (renameᵗ-double-under-∀ C))))
      (equality-proof-unique
        (sym (renameᵗ-compose suc suc B))
        (sym (renameᵗ-double-lift B)))

⊑-crossed-double-lift-arrowᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  ⊑-crossed-double-lift∀∀ᵢ (pA ↦ pB) ≡
    ⊑-crossed-double-lift∀∀ᵢ pA ↦
      ⊑-crossed-double-lift∀∀ᵢ pB
⊑-crossed-double-lift-arrowᵢ
    {A = A} {A′ = A′} {B = B} {B′ = B′} pA pB
    rewrite equality-proof-unique
      (sym (renameᵗ-compose suc suc (A ⇒ B)))
      (cong₂ _⇒_
        (sym (renameᵗ-double-lift A))
        (sym (renameᵗ-double-lift B)))
          | equality-proof-unique
      (sym (renameᵗ-compose suc suc (A′ ⇒ B′)))
      (cong₂ _⇒_
        (sym (renameᵗ-double-lift A′))
        (sym (renameᵗ-double-lift B′))) =
  transport-arrow-⊑ᵢ
    (sym (renameᵗ-double-lift A))
    (sym (renameᵗ-double-lift A′))
    (sym (renameᵗ-double-lift B))
    (sym (renameᵗ-double-lift B′))

⊑-crossed-double-lift-allᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
  ⊑-crossed-double-lift∀∀ᵢ (∀ⁱ p) ≡
    ∀ⁱ (⊑-crossed-double-lift-under-∀ᵢ p)
⊑-crossed-double-lift-allᵢ {A = A} {B = B} p
    rewrite equality-proof-unique
      (sym (renameᵗ-compose suc suc (`∀ A)))
      (cong `∀ (sym (renameᵗ-double-under-∀ A)))
          | equality-proof-unique
      (sym (renameᵗ-compose suc suc (`∀ B)))
      (cong `∀ (sym (renameᵗ-double-under-∀ B))) =
  transport-all-⊑ᵢ
    (sym (renameᵗ-double-under-∀ A))
    (sym (renameᵗ-double-under-∀ B))

weak-one-step-source-blame-right-allocationᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ V′ s s′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  Value V′ →
  No• V′ →
  WfTy (suc Δᴿ) (⇑ᵗ A′) →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ ν A′ V′ s′ ⦂ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepResult ρ
    (ν A blame s) (((⇑ᵗᵐ V′) •) ⟨ s′ ⟩)
    B B′ (bind A′)
weak-one-step-source-blame-right-allocationᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′}
    {V′ = V′} {s′ = s′} {ρ = ρ}
    wfΣ′ vV′ noV′ h⇑A′ target⊢ pB =
  record
    { sourceChanges = keep ∷ []
    ; targetTailChanges = []
    ; sourceResult = blame
    ; targetResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
    ; resultCtx = ⇑ᴿᵢ _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = store-right zero (⇑ᵗ A′) h⇑A′ ∷ ρ′
    ; resultSourceType = _
    ; resultTargetType = ⇑ᵗ B′
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = ⊑-target-lift-rightᵢ
    ; transportAllBody = ⊑-target-lift-right-under-∀ᵢ
    ; transportRightBody = ⊑-target-lift-under-rightᵢ
    ; transportSourceNu = ⊑-target-lift-right-source-nuᵢ
    ; resultType = ⊑-target-lift-rightᵢ pB
    ; sourceCatchup = ↠-step blame-ν ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = leftStoreⁱ-lift-right liftρ
    ; targetStoreResult = target-store-result
    ; relatedResults = blame⊑ᵀ target-result-typing
    }
  where
    ρ′ = proj₁ (lift-right-store-result ρ)
    liftρ = proj₂ (lift-right-store-result ρ)

    target-store-result =
      cong ((zero , ⇑ᵗ A′) ∷_)
        (rightStoreⁱ-lift-right liftρ)

    target-result-typing =
      subst
        (λ Σ → suc Δᴿ ∣ Σ ∣ []
          ⊢ ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩ ⦂ ⇑ᵗ B′)
        (sym target-store-result)
        (preservation wfΣ′ (ok-ν (ok-no noV′)) target⊢
          (ν-step vV′ noV′))

weak-one-step-compose-type :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (first : WeakOneStepResult ρ M M′ A B χ) →
  ∀ {χ′ N′} →
  (second : WeakOneStepResult (resultStore first)
    (sourceResult first) N′
    (resultSourceType first) (resultTargetType first) χ′) →
  ∀ {C D} →
  Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ →
  resultCtx second ∣ resultLeftCtx second
    ⊢ applyTys (sourceChanges first ++ sourceChanges second) C
      ⊑ applyTys
        (targetTailChanges first ++
          χ′ ∷ targetTailChanges second)
        (applyTy χ D)
      ⊣ resultRightCtx second
weak-one-step-compose-type {B = B} {χ = χ} first
    {χ′ = χ′} second {C = C} {D = D} p =
  subst
    (λ T → resultCtx second ∣ resultLeftCtx second
      ⊢ applyTys
          (sourceChanges first ++ sourceChanges second) C
        ⊑ T ⊣ resultRightCtx second)
    (sym (applyTys-++
      (targetTailChanges first)
      (χ′ ∷ targetTailChanges second)
      (applyTy χ D)))
    (subst
      (λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑ applyTys (targetTailChanges second)
            (applyTy χ′
              (applyTys (targetTailChanges first)
                (applyTy χ D)))
          ⊣ resultRightCtx second)
      (sym (applyTys-++
        (sourceChanges first) (sourceChanges second) C))
      (transportType second (transportType first p)))

weak-one-step-compose-type-to-nested≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′)
    {C D}
    (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  HE._≅_ (weak-one-step-compose-type first second p)
    (transportType second (transportType first p))
weak-one-step-compose-type-to-nested≅ {χ = χ} first
    {χ′ = χ′} second {C = C} {D = D} p =
  HE.trans
    (subst-to-≅
      {P = λ T → resultCtx second ∣ resultLeftCtx second
        ⊢ applyTys
            (sourceChanges first ++ sourceChanges second) C
          ⊑ T ⊣ resultRightCtx second}
      target-eq source-transport)
    (subst-to-≅
      {P = λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑ applyTys (targetTailChanges second)
            (applyTy χ′
              (applyTys (targetTailChanges first) (applyTy χ D)))
          ⊣ resultRightCtx second}
      source-eq raw)
  where
  raw = transportType second (transportType first p)
  source-eq = sym (applyTys-++
    (sourceChanges first) (sourceChanges second) C)
  source-transport = subst
    (λ S → resultCtx second ∣ resultLeftCtx second
      ⊢ S ⊑ applyTys (targetTailChanges second)
          (applyTy χ′
            (applyTys (targetTailChanges first) (applyTy χ D)))
        ⊣ resultRightCtx second)
    source-eq raw
  target-eq = sym (applyTys-++
    (targetTailChanges first)
    (χ′ ∷ targetTailChanges second) (applyTy χ D))

weak-one-step-nested-arrow-coherent≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  WeakOneStepTypeCoherence first →
  WeakOneStepTypeCoherence second →
  ∀ {C C′ D D′}
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  HE._≅_
    (transportType second (transportType first (pC ↦ pD)))
    (transportType second (transportType first pC) ↦
      transportType second (transportType first pD))
weak-one-step-nested-arrow-coherent≅
    first second first-coherence second-coherence pC pD =
  HE.trans
    (HE.sym
      (transportType-transportArrowType-to-raw≅
        first second pC pD))
    (HE.trans
      (HE.≡-to-≅
        (cong (transportType second)
          (transportArrowCoherent first-coherence pC pD)))
      (HE.trans
        (HE.sym
          (transportArrowType-to-raw≅ second
            (transportType first pC) (transportType first pD)))
        (HE.≡-to-≅
          (transportArrowCoherent second-coherence
            (transportType first pC) (transportType first pD)))))

weak-one-step-nested-all-coherent≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  WeakOneStepTypeCoherence first →
  WeakOneStepTypeCoherence second →
  ∀ {C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  HE._≅_
    (transportType second (transportType first (∀ⁱ q)))
    (∀ⁱ (transportAllBody second (transportAllBody first q)))
weak-one-step-nested-all-coherent≅
    first second first-coherence second-coherence q =
  HE.trans
    (HE.sym
      (transportType-transportAllType-to-raw≅
        first second q))
    (HE.trans
      (HE.≡-to-≅
        (cong (transportType second)
          (transportAllCoherent first-coherence q)))
      (HE.trans
        (HE.sym
          (transportAllType-to-raw≅ second
            (transportAllBody first q)))
        (HE.≡-to-≅
          (transportAllCoherent second-coherence
            (transportAllBody first q)))))

weak-one-step-nested-source-nu≅ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′)
    {C D}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  let first-shape = transportSourceNu first safe occ q in
  let second-shape = transportSourceNu second
        (sourceNuSafe first-shape)
        (sourceNuOccurs first-shape)
        (sourceNuBody first-shape) in
  HE._≅_
    (transportType second (transportType first (ν safe occ q)))
    (transportSourceNuType second
      (sourceNuSafe first-shape)
      (sourceNuOccurs first-shape)
      (sourceNuBody first-shape))
weak-one-step-nested-source-nu≅ first second safe occ q =
  HE.trans
    (HE.sym
      (transportType-transportSourceNuType-to-raw≅
        first second safe occ q))
    (HE.trans
      (HE.≡-to-≅
        (cong (transportType second)
          (sourceNuIndexEquality first-shape)))
      (HE.sym
        (transportSourceNuType-to-raw≅ second
          (sourceNuSafe first-shape)
          (sourceNuOccurs first-shape)
          (sourceNuBody first-shape))))
  where
  first-shape = transportSourceNu first safe occ q

weak-one-step-compose-all-body :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (first : WeakOneStepResult ρ M M′ A B χ) →
  ∀ {χ′ N′} →
  (second : WeakOneStepResult (resultStore first)
    (sourceResult first) N′
    (resultSourceType first) (resultTargetType first) χ′) →
  ∀ {C D} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
  ∀ᵢᶜ (resultCtx second) ∣ suc (resultLeftCtx second)
    ⊢ applyTysUnderTyBinders
        (sourceChanges first ++ sourceChanges second) C
      ⊑ applyTysUnderTyBinders
          (targetTailChanges first ++
            χ′ ∷ targetTailChanges second)
          (applyTyUnderTyBinder χ D)
      ⊣ suc (resultRightCtx second)
weak-one-step-compose-all-body {χ = χ} first
    {χ′ = χ′} second {C = C} {D = D} p =
  subst
    (λ T → ∀ᵢᶜ (resultCtx second) ∣ suc (resultLeftCtx second)
      ⊢ applyTysUnderTyBinders
          (sourceChanges first ++ sourceChanges second) C
        ⊑ T ⊣ suc (resultRightCtx second))
    (sym (applyTysUnderTyBinders-++
      (targetTailChanges first)
      (χ′ ∷ targetTailChanges second)
      (applyTyUnderTyBinder χ D)))
    (subst
      (λ S → ∀ᵢᶜ (resultCtx second) ∣ suc (resultLeftCtx second)
        ⊢ S ⊑ applyTysUnderTyBinders
            (targetTailChanges second)
            (applyTyUnderTyBinder χ′
              (applyTysUnderTyBinders
                (targetTailChanges first)
                (applyTyUnderTyBinder χ D)))
          ⊣ suc (resultRightCtx second))
      (sym (applyTysUnderTyBinders-++
        (sourceChanges first) (sourceChanges second) C))
      (transportAllBody second (transportAllBody first p)))

weak-one-step-compose-right-body :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (first : WeakOneStepResult ρ M M′ A B χ) →
  ∀ {χ′ N′} →
  (second : WeakOneStepResult (resultStore first)
    (sourceResult first) N′
    (resultSourceType first) (resultTargetType first) χ′) →
  ∀ {C D} →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
  ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
    ⊢ applyTys
        (sourceChanges first ++ sourceChanges second) C
      ⊑ applyTysUnderTyBinders
          (targetTailChanges first ++
            χ′ ∷ targetTailChanges second)
          (applyTyUnderTyBinder χ D)
      ⊣ suc (resultRightCtx second)
weak-one-step-compose-right-body {χ = χ} first
    {χ′ = χ′} second {C = C} {D = D} p =
  subst
    (λ T → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
      ⊢ applyTys
          (sourceChanges first ++ sourceChanges second) C
        ⊑ T ⊣ suc (resultRightCtx second))
    (sym (applyTysUnderTyBinders-++
      (targetTailChanges first)
      (χ′ ∷ targetTailChanges second)
      (applyTyUnderTyBinder χ D)))
    (subst
      (λ S → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
        ⊢ S ⊑ applyTysUnderTyBinders
            (targetTailChanges second)
            (applyTyUnderTyBinder χ′
              (applyTysUnderTyBinders
                (targetTailChanges first)
                (applyTyUnderTyBinder χ D)))
          ⊣ suc (resultRightCtx second))
      (sym (applyTys-++
        (sourceChanges first) (sourceChanges second) C))
      (transportRightBody second (transportRightBody first p)))

weak-one-step-compose-source-nu :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′)
    {C D}
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  SourceNuIndex
    (subst
      (λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑
          applyTys
            (targetTailChanges first ++
              χ′ ∷ targetTailChanges second)
            (applyTy χ D)
        ⊣ resultRightCtx second)
      (applyTys-∀
        (sourceChanges first ++ sourceChanges second) C)
      (weak-one-step-compose-type first second (ν safe occ q)))
weak-one-step-compose-source-nu
    {χ = χ} first {χ′ = χ′} second {C = C} {D = D}
    safe occ q =
  sourceNuIndex-reindex (sym combined-eq) transported-shape
  where
  first-shape = transportSourceNu first safe occ q
  second-shape = transportSourceNu second
    (sourceNuSafe first-shape)
    (sourceNuOccurs first-shape)
    (sourceNuBody first-shape)

  source-eq = applyTysUnderTyBinders-++
    (sourceChanges first) (sourceChanges second) C

  target-eq = applyTys-++
    (targetTailChanges first)
    (χ′ ∷ targetTailChanges second)
    (applyTy χ D)

  transported-shape =
    sourceNuIndex-transport
      (sym source-eq) (sym target-eq) second-shape

  combined-eq =
    HE.≅-to-≡
      (HE.trans
        (subst-to-≅
          {P = λ S → resultCtx second ∣ resultLeftCtx second
            ⊢ S ⊑
              applyTys
                (targetTailChanges first ++
                  χ′ ∷ targetTailChanges second)
                (applyTy χ D)
            ⊣ resultRightCtx second}
          (applyTys-∀
            (sourceChanges first ++ sourceChanges second) C)
          (weak-one-step-compose-type first second (ν safe occ q)))
        (HE.trans
          (weak-one-step-compose-type-to-nested≅
            first second (ν safe occ q))
          (HE.trans
            (weak-one-step-nested-source-nu≅
              first second safe occ q)
            (HE.sym
              (subst²-to-≅
                {P = λ S T → resultCtx second
                  ∣ resultLeftCtx second
                  ⊢ S ⊑ T ⊣ resultRightCtx second}
                (cong `∀ (sym source-eq)) (sym target-eq)
                (transportSourceNuType second
                  (sourceNuSafe first-shape)
                  (sourceNuOccurs first-shape)
                  (sourceNuBody first-shape)))))))

weak-one-step-composeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (first : WeakOneStepResult ρ M M′ A B χ) →
  ∀ {χ′ N′} →
  targetResult first —→[ χ′ ] N′ →
  (second : WeakOneStepResult (resultStore first)
    (sourceResult first) N′
    (resultSourceType first) (resultTargetType first) χ′) →
  WeakOneStepResult ρ M M′ A B χ
weak-one-step-composeᵀ {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    {χ = χ} {ρ = ρ} first {χ′ = χ′} target→ second =
  record
    { sourceChanges = sourceChanges first ++ sourceChanges second
    ; targetTailChanges =
        targetTailChanges first ++ χ′ ∷ targetTailChanges second
    ; sourceResult = sourceResult second
    ; targetResult = targetResult second
    ; resultCtx = resultCtx second
    ; resultLeftCtx = resultLeftCtx second
    ; resultRightCtx = resultRightCtx second
    ; sourceCtxResult =
        trans (sourceCtxResult second)
          (trans
            (cong (applyTyCtxs (sourceChanges second))
              (sourceCtxResult first))
            (sym (applyTyCtxs-++
              (sourceChanges first) (sourceChanges second) Δᴸ)))
    ; targetCtxResult =
        trans (targetCtxResult second)
          (trans
            (cong
              (λ Δ → applyTyCtxs (targetTailChanges second)
                (applyTyCtx χ′ Δ))
              (targetCtxResult first))
            (sym (applyTyCtxs-++
              (targetTailChanges first)
              (χ′ ∷ targetTailChanges second)
              (applyTyCtx χ Δᴿ))))
    ; resultStore = resultStore second
    ; resultSourceType = resultSourceType second
    ; resultTargetType = resultTargetType second
    ; sourceTypeResult =
        trans (sourceTypeResult second)
          (trans
            (cong (applyTys (sourceChanges second))
              (sourceTypeResult first))
            (sym (applyTys-++
              (sourceChanges first) (sourceChanges second) A)))
    ; targetTypeResult =
        trans (targetTypeResult second)
          (trans
            (cong
              (λ C → applyTys (targetTailChanges second)
                (applyTy χ′ C))
              (targetTypeResult first))
            (sym (applyTys-++
              (targetTailChanges first)
              (χ′ ∷ targetTailChanges second)
              (applyTy χ B))))
    ; transportType = weak-one-step-compose-type first second
    ; transportAllBody = weak-one-step-compose-all-body first second
    ; transportRightBody =
        weak-one-step-compose-right-body first second
    ; transportSourceNu =
        weak-one-step-compose-source-nu first second
    ; resultType = resultType second
    ; sourceCatchup =
        ↠-trans (sourceCatchup first) (sourceCatchup second)
    ; targetTail =
        ↠-trans (targetTail first)
          (↠-step target→ (targetTail second))
    ; sourceStoreResult =
        trans (sourceStoreResult second)
          (trans
            (cong (applyStores (sourceChanges second))
              (sourceStoreResult first))
            (sym (applyStores-++
              (sourceChanges first) (sourceChanges second)
              (leftStoreⁱ ρ))))
    ; targetStoreResult =
        trans (targetStoreResult second)
          (trans
            (cong
              (λ Σ → applyStores (targetTailChanges second)
                (applyStore χ′ Σ))
              (targetStoreResult first))
            (sym (applyStores-++
              (targetTailChanges first)
              (χ′ ∷ targetTailChanges second)
              (applyStore χ (rightStoreⁱ ρ)))))
    ; relatedResults = relatedResults second
    }

weak-one-step-compose-transport-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  WeakOneStepTransport first →
  WeakOneStepTransport second →
  ∀ {L L′ C C′ p} →
  No• L →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ C ⊑ C′ ∶ p →
  resultCtx second
    ∣ resultLeftCtx second
    ∣ resultRightCtx second
    ∣ resultStore second ∣ [] ⊢ᴺ
    applyTerms
      (sourceChanges first ++ sourceChanges second) L
    ⊑ applyTerms
        (targetTailChanges first ++ χ′ ∷ targetTailChanges second)
        (applyTerm χ L′)
    ⦂ applyTys (sourceChanges first ++ sourceChanges second) C
      ⊑ applyTys
          (targetTailChanges first ++ χ′ ∷ targetTailChanges second)
          (applyTy χ C′)
    ∶ weak-one-step-compose-type first second p
weak-one-step-compose-transport-bodyᵀ
    {χ = χ} first {χ′ = χ′} second
    first-transport second-transport
    {L = L} {L′ = L′} {C = C} {C′ = C′}
    noL noL′ L⊑L′
    rewrite applyTerms-++
      (sourceChanges first) (sourceChanges second) L
    | applyTerms-++
      (targetTailChanges first)
      (χ′ ∷ targetTailChanges second) (applyTerm χ L′)
    | applyTys-++
      (sourceChanges first) (sourceChanges second) C
    | applyTys-++
      (targetTailChanges first)
      (χ′ ∷ targetTailChanges second) (applyTy χ C′) =
  transportNo•Terms second-transport
    (applyTerms-preserves-No• (sourceChanges first) noL)
    (applyTerms-preserves-No• (targetTailChanges first)
      (applyTerm-preserves-No• χ noL′))
    (transportNo•Terms first-transport noL noL′ L⊑L′)

weak-one-step-compose-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (target→ : targetResult first —→[ χ′ ] N′)
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  WeakOneStepTransport first →
  WeakOneStepTransport second →
  WeakOneStepTransport
    (weak-one-step-composeᵀ first target→ second)
weak-one-step-compose-preserves-transportᵀ
    first target→ second
    first-transport second-transport =
  weak-step-transport
    (weak-one-step-compose-transport-bodyᵀ
      first second first-transport second-transport)

weak-one-step-prepend-left-silentᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (silent : LeftSilentResult
    {M = M} {V′ = V′} {A = A} {B = B} {ρ = ρ}) →
  let first = silentResult silent in
  ∀ {χ N′} →
  (second : WeakOneStepResult (resultStore first)
    (sourceResult first) N′
    (resultSourceType first) (resultTargetType first) χ) →
  WeakOneStepResult ρ M N′ A B χ
weak-one-step-prepend-left-silentᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    (left-silent first (left-silent-invariant refl refl))
    {χ = χ} second =
  record
    { sourceChanges = sourceChanges first ++ sourceChanges second
    ; targetTailChanges = targetTailChanges second
    ; sourceResult = sourceResult second
    ; targetResult = targetResult second
    ; resultCtx = resultCtx second
    ; resultLeftCtx = resultLeftCtx second
    ; resultRightCtx = resultRightCtx second
    ; sourceCtxResult =
        trans (sourceCtxResult second)
          (trans
            (cong (applyTyCtxs (sourceChanges second))
              (sourceCtxResult first))
            (sym (applyTyCtxs-++
              (sourceChanges first) (sourceChanges second) Δᴸ)))
    ; targetCtxResult =
        trans (targetCtxResult second)
          (cong
            (λ Δ → applyTyCtxs (targetTailChanges second)
              (applyTyCtx χ Δ))
            (targetCtxResult first))
    ; resultStore = resultStore second
    ; resultSourceType = resultSourceType second
    ; resultTargetType = resultTargetType second
    ; sourceTypeResult =
        trans (sourceTypeResult second)
          (trans
            (cong (applyTys (sourceChanges second))
              (sourceTypeResult first))
            (sym (applyTys-++
              (sourceChanges first) (sourceChanges second) A)))
    ; targetTypeResult =
        trans (targetTypeResult second)
          (cong
            (λ C → applyTys (targetTailChanges second)
              (applyTy χ C))
            (targetTypeResult first))
    ; transportType = weak-one-step-compose-type first second
    ; transportAllBody = weak-one-step-compose-all-body first second
    ; transportRightBody =
        weak-one-step-compose-right-body first second
    ; transportSourceNu =
        weak-one-step-compose-source-nu first second
    ; resultType = resultType second
    ; sourceCatchup =
        ↠-trans (sourceCatchup first) (sourceCatchup second)
    ; targetTail = targetTail second
    ; sourceStoreResult =
        trans (sourceStoreResult second)
          (trans
            (cong (applyStores (sourceChanges second))
              (sourceStoreResult first))
            (sym (applyStores-++
              (sourceChanges first) (sourceChanges second)
              (leftStoreⁱ ρ))))
    ; targetStoreResult =
        trans (targetStoreResult second)
          (cong
            (λ Σ → applyStores (targetTailChanges second)
              (applyStore χ Σ))
            (targetStoreResult first))
    ; relatedResults = relatedResults second
    }

weak-one-step-prepend-left-silent-transport-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M V′ A B keep)
    {χ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ) →
  targetTailChanges first ≡ [] →
  WeakOneStepTransport first →
  WeakOneStepTransport second →
  ∀ {L L′ C C′ p} →
  No• L →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ C ⊑ C′ ∶ p →
  resultCtx second
    ∣ resultLeftCtx second
    ∣ resultRightCtx second
    ∣ resultStore second ∣ [] ⊢ᴺ
    applyTerms (sourceChanges first ++ sourceChanges second) L
    ⊑ applyTerms
        (targetTailChanges first ++ χ ∷ targetTailChanges second)
        (applyTerm keep L′)
    ⦂ applyTys (sourceChanges first ++ sourceChanges second) C
      ⊑ applyTys
          (targetTailChanges first ++ χ ∷ targetTailChanges second)
          (applyTy keep C′)
    ∶ weak-one-step-compose-type first second p
weak-one-step-prepend-left-silent-transport-bodyᵀ
    first {χ = χ} second refl first-transport second-transport
    {L = L} {L′ = L′} {C = C} noL noL′ L⊑L′
    rewrite applyTerms-++
      (sourceChanges first) (sourceChanges second) L
    | applyTys-++
      (sourceChanges first) (sourceChanges second) C =
  transportNo•Terms second-transport
    (applyTerms-preserves-No• (sourceChanges first) noL)
    noL′
    (transportNo•Terms first-transport noL noL′ L⊑L′)

weak-one-step-prepend-left-silent-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (silent : LeftSilentResult
      {M = M} {V′ = V′} {A = A} {B = B} {ρ = ρ}) →
  let first = silentResult silent in
  ∀ {χ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ) →
  WeakOneStepTransport first →
  WeakOneStepTransport second →
  WeakOneStepTransport
    (weak-one-step-prepend-left-silentᵀ silent second)
weak-one-step-prepend-left-silent-preserves-transportᵀ
    (left-silent first
      (left-silent-invariant refl refl))
    {χ = χ} second first-transport second-transport =
  weak-step-transport
    (weak-one-step-prepend-left-silent-transport-bodyᵀ
      first second refl first-transport second-transport)

weak-one-step-compose-arrow-componentsᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  ∀ {C C′ D D′}
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  subst
    (λ T → resultCtx second ∣ resultLeftCtx second
      ⊢ applyTys
          (sourceChanges first ++ sourceChanges second) C ⇒
        applyTys (sourceChanges first ++ sourceChanges second) D
        ⊑ T
      ⊣ resultRightCtx second)
    (cong₂ _⇒_
      (sym (applyTys-++ (targetTailChanges first)
        (χ′ ∷ targetTailChanges second) (applyTy χ C′)))
      (sym (applyTys-++ (targetTailChanges first)
        (χ′ ∷ targetTailChanges second) (applyTy χ D′))))
    (subst
      (λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑
          applyTys (targetTailChanges second)
            (applyTy χ′
              (applyTys (targetTailChanges first) (applyTy χ C′))) ⇒
          applyTys (targetTailChanges second)
            (applyTy χ′
              (applyTys (targetTailChanges first) (applyTy χ D′)))
        ⊣ resultRightCtx second)
      (cong₂ _⇒_
        (sym (applyTys-++
          (sourceChanges first) (sourceChanges second) C))
        (sym (applyTys-++
          (sourceChanges first) (sourceChanges second) D)))
      (transportType second (transportType first pC) ↦
        transportType second (transportType first pD)))
    ≡
  weak-one-step-compose-type first second pC ↦
    weak-one-step-compose-type first second pD
weak-one-step-compose-arrow-componentsᵀ
    {χ = χ} first {χ′ = χ′} second
    {C = C} {C′ = C′} {D = D} {D′ = D′} pC pD =
  transport-arrow-⊑ᵢ
    (sym (applyTys-++
      (sourceChanges first) (sourceChanges second) C))
    (sym (applyTys-++ (targetTailChanges first)
      (χ′ ∷ targetTailChanges second) (applyTy χ C′)))
    (sym (applyTys-++
      (sourceChanges first) (sourceChanges second) D))
    (sym (applyTys-++ (targetTailChanges first)
      (χ′ ∷ targetTailChanges second) (applyTy χ D′)))

weak-one-step-compose-all-componentsᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  ∀ {C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  subst
    (λ T → resultCtx second ∣ resultLeftCtx second
      ⊢ `∀ (applyTysUnderTyBinders
          (sourceChanges first ++ sourceChanges second) C)
        ⊑ T ⊣ resultRightCtx second)
    (cong `∀
      (sym (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTyUnderTyBinder χ C′))))
    (subst
      (λ S → resultCtx second ∣ resultLeftCtx second
        ⊢ S ⊑
          `∀ (applyTysUnderTyBinders
            (targetTailChanges second)
            (applyTyUnderTyBinder χ′
              (applyTysUnderTyBinders
                (targetTailChanges first)
                (applyTyUnderTyBinder χ C′))))
        ⊣ resultRightCtx second)
      (cong `∀
        (sym (applyTysUnderTyBinders-++
          (sourceChanges first) (sourceChanges second) C)))
      (∀ⁱ (transportAllBody second (transportAllBody first q))))
    ≡
  ∀ⁱ (weak-one-step-compose-all-body first second q)
weak-one-step-compose-all-componentsᵀ
    {χ = χ} first {χ′ = χ′} second
    {C = C} {C′ = C′} q =
  transport-all-⊑ᵢ
    (sym (applyTysUnderTyBinders-++
      (sourceChanges first) (sourceChanges second) C))
    (sym (applyTysUnderTyBinders-++
      (targetTailChanges first)
      (χ′ ∷ targetTailChanges second)
      (applyTyUnderTyBinder χ C′)))

weak-one-step-compose-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B χ)
    {χ′ N′}
    (target→ : targetResult first —→[ χ′ ] N′)
    (second : WeakOneStepResult
      (resultStore first) (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ′) →
  WeakOneStepTypeCoherence first →
  WeakOneStepTypeCoherence second →
  WeakOneStepTypeCoherence
    (weak-one-step-composeᵀ first target→ second)
weak-one-step-compose-preserves-type-coherenceᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {χ = χ}
    first {χ′ = χ′} target→ second
    first-coherence second-coherence =
  weak-step-type-coherence arrow-coherent all-coherent
    shape-coherent
    right-body-shape-coherent
    left-replacement-coherent
    right-replacement-coherent
    paired-replacement-coherent
    all-body-paired-replacement-coherent
    source-nu-body-left-replacement-coherent
    right-body-right-replacement-coherent
  where
  combined = weak-one-step-composeᵀ first target→ second

  arrow-coherent :
    ∀ {C C′ D D′}
      (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
      (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
    transportArrowType combined pC pD ≡
      weak-one-step-compose-type first second pC ↦
      weak-one-step-compose-type first second pD
  arrow-coherent {C = C} {C′ = C′}
      {D = D} {D′ = D′} pC pD =
    HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ combined pC pD)
        (HE.trans
          (weak-one-step-compose-type-to-nested≅
            first second (pC ↦ pD))
          (HE.trans
            (weak-one-step-nested-arrow-coherent≅
              first second first-coherence second-coherence pC pD)
            (HE.trans
              (HE.sym
                (subst²-to-≅
                  {P = λ S T →
                    resultCtx second ∣ resultLeftCtx second
                      ⊢ S ⊑ T ⊣ resultRightCtx second}
                  (cong₂ _⇒_
                    (sym (applyTys-++
                      (sourceChanges first)
                      (sourceChanges second) C))
                    (sym (applyTys-++
                      (sourceChanges first)
                      (sourceChanges second) D)))
                  (cong₂ _⇒_
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (χ′ ∷ targetTailChanges second)
                      (applyTy χ C′)))
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (χ′ ∷ targetTailChanges second)
                      (applyTy χ D′))))
                  (transportType second (transportType first pC) ↦
                    transportType second (transportType first pD))))
              (HE.≡-to-≅
                (weak-one-step-compose-arrow-componentsᵀ
                  first second pC pD))))))

  all-coherent :
    ∀ {C C′}
      (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    transportAllType combined q ≡
      ∀ⁱ (weak-one-step-compose-all-body first second q)
  all-coherent {C = C} {C′ = C′} q =
    HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ combined q)
        (HE.trans
          (weak-one-step-compose-type-to-nested≅
            first second (∀ⁱ q))
          (HE.trans
            (weak-one-step-nested-all-coherent≅
              first second first-coherence second-coherence q)
            (HE.trans
              (HE.sym
                (subst²-to-≅
                  {P = λ S T →
                    resultCtx second ∣ resultLeftCtx second
                      ⊢ S ⊑ T ⊣ resultRightCtx second}
                  (cong `∀
                    (sym (applyTysUnderTyBinders-++
                      (sourceChanges first)
                      (sourceChanges second) C)))
                  (cong `∀
                    (sym (applyTysUnderTyBinders-++
                      (targetTailChanges first)
                      (χ′ ∷ targetTailChanges second)
                      (applyTyUnderTyBinder χ C′))))
                  (∀ⁱ (transportAllBody second
                    (transportAllBody first q)))))
              (HE.≡-to-≅
                (weak-one-step-compose-all-componentsᵀ
                  first second q))))))

  shape-coherent :
    ∀ {C D}
      (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ weak-one-step-compose-type first second p ⌋ ≡ ⌊ p ⌋
  shape-coherent {C = C} {D = D} p =
    trans
      (shape-subst-target target-eq source-transport)
      (trans
        (shape-subst-source source-eq nested)
        (trans
          (transportShapeCoherent second-coherence
            (transportType first p))
          (transportShapeCoherent first-coherence p)))
    where
    nested = transportType second (transportType first p)
    source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) C)
    source-transport =
      subst
        (λ S → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ applyTys (targetTailChanges second)
              (applyTy χ′
                (applyTys (targetTailChanges first) (applyTy χ D)))
          ⊣ resultRightCtx second)
        source-eq nested
    target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ D))

  composed-type-nested-shape :
    ∀ {C D}
      (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ weak-one-step-compose-type first second p ⌋ ≡
      ⌊ transport-imprecision-endpoints
          (sym
            (applyTys-++
              (sourceChanges first) (sourceChanges second) C))
          (sym
            (applyTys-++
              (targetTailChanges first)
              (χ′ ∷ targetTailChanges second)
              (applyTy χ D)))
          (transportType second (transportType first p))
      ⌋
  composed-type-nested-shape {C = C} {D = D} p =
    trans
      (shape-coherent p)
      (trans
        (sym (transportShapeCoherent first-coherence p))
        (trans
          (sym
            (transportShapeCoherent second-coherence
              (transportType first p)))
          (sym
            (shape-transport-imprecision-endpoints
              source-eq target-eq nested))))
    where
    nested = transportType second (transportType first p)
    source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) C)
    target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ D))

  right-body-shape-coherent :
    ∀ {C D}
      (p : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ) →
    ⌊ weak-one-step-compose-right-body first second p ⌋ ≡ ⌊ p ⌋
  right-body-shape-coherent {C = C} {D = D} p =
    trans
      (shape-subst-target target-eq source-transport)
      (trans
        (shape-subst-source source-eq nested)
        (trans
          (transportRightBodyShapeCoherent second-coherence
            (transportRightBody first p))
          (transportRightBodyShapeCoherent first-coherence p)))
    where
    nested = transportRightBody second (transportRightBody first p)
    source-eq = sym
      (applyTys-++ (sourceChanges first) (sourceChanges second) C)
    source-transport =
      subst
        (λ S → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
          ⊢ S ⊑ applyTysUnderTyBinders
              (targetTailChanges second)
              (applyTyUnderTyBinder χ′
                (applyTysUnderTyBinders
                  (targetTailChanges first)
                  (applyTyUnderTyBinder χ D)))
          ⊣ suc (resultRightCtx second))
        source-eq nested
    target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTyUnderTyBinder χ D))

  left-replacement-coherent :
    ∀ {C C′ D α X}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ C′ ⊣ Δᴿ} →
    p [ α ↦ X ]ᴸ q →
    weak-one-step-compose-type first second p
      [ applyTyVars
          (sourceChanges first ++ sourceChanges second) α
      ↦ applyTys
          (sourceChanges first ++ sourceChanges second) X ]ᴸ
    weak-one-step-compose-type first second q
  left-replacement-coherent
      {C = C} {C′ = C′} {D = D} {α = α} {X = X}
      {p = p} {q = q} replacement
    rewrite applyTyVars-++
              (sourceChanges first) (sourceChanges second) α =
    replace-left-target-shape
      (composed-type-nested-shape q)
      (replace-left-source-shape
        (composed-type-nested-shape p)
        endpoints-replacement)
    where
    second-replacement =
      transportLeftReplacementCoherent second-coherence
        (transportLeftReplacementCoherent
          first-coherence replacement)
    input-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) C)
    target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ C′))
    output-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) D)
    inserted-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) X)
    endpoints-replacement =
      replace-left-transport-endpoints
        input-source-eq target-eq output-source-eq
        inserted-source-eq second-replacement

  right-replacement-coherent :
    ∀ {C C′ D′ β X′}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊑ D′ ⊣ Δᴿ} →
    p [ β ↦ X′ ]ᴿ q →
    weak-one-step-compose-type first second p
      [ applyTyVars
          (targetTailChanges first ++
            χ′ ∷ targetTailChanges second)
          (applyTyVar χ β)
      ↦ applyTys
          (targetTailChanges first ++
            χ′ ∷ targetTailChanges second)
          (applyTy χ X′) ]ᴿ
    weak-one-step-compose-type first second q
  right-replacement-coherent
      {C = C} {C′ = C′} {D′ = D′}
      {β = β} {X′ = X′} {p = p} {q = q} replacement
    rewrite applyTyVars-++
              (targetTailChanges first)
              (χ′ ∷ targetTailChanges second)
              (applyTyVar χ β) =
    replace-right-target-shape
      (composed-type-nested-shape q)
      (replace-right-source-shape
        (composed-type-nested-shape p)
        endpoints-replacement)
    where
    second-replacement =
      transportRightReplacementCoherent second-coherence
        (transportRightReplacementCoherent
          first-coherence replacement)
    input-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) C)
    input-target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ C′))
    output-target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ D′))
    inserted-target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ X′))
    endpoints-replacement =
      replace-right-transport-endpoints
        input-source-eq input-target-eq
        output-target-eq inserted-target-eq
        second-replacement

  paired-replacement-coherent :
    ∀ {C C′ D D′ α β X X′}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ} →
    p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
    weak-one-step-compose-type first second p
      [ applyTyVars
          (sourceChanges first ++ sourceChanges second) α
      ↦ applyTys
          (sourceChanges first ++ sourceChanges second) X
      ⊑⟨ weak-one-step-compose-type first second pX ⟩
      applyTys
        (targetTailChanges first ++ χ′ ∷ targetTailChanges second)
        (applyTy χ X′)
      ↤ applyTyVars
          (targetTailChanges first ++
            χ′ ∷ targetTailChanges second)
          (applyTyVar χ β) ]ᴾ
    weak-one-step-compose-type first second q
  paired-replacement-coherent
      {C = C} {C′ = C′} {D = D} {D′ = D′}
      {α = α} {β = β} {X = X} {X′ = X′}
      {pX = pX} {p = p} {q = q} replacement
    rewrite applyTyVars-++ (sourceChanges first)
              (sourceChanges second) α
          | applyTyVars-++
              (targetTailChanges first)
              (χ′ ∷ targetTailChanges second)
              (applyTyVar χ β) =
    replace-paired-target-shape
      (composed-type-nested-shape q)
      (replace-paired-source-shape
        (composed-type-nested-shape p)
        (replace-paired-evidence-shape
          (composed-type-nested-shape pX)
          endpoints-replacement))
    where
    second-replacement =
      transportPairedReplacementCoherent second-coherence
        (transportPairedReplacementCoherent
          first-coherence replacement)
    input-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) C)
    input-target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ C′))
    output-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) D)
    output-target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ D′))
    inserted-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) X)
    inserted-target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ X′))
    endpoints-replacement =
      replace-paired-transport-endpoints
        input-source-eq input-target-eq
        output-source-eq output-target-eq
        inserted-source-eq inserted-target-eq
        second-replacement

  ∀ˢ-injective-compose :
    ∀ {s t} →
    ∀ˢ s ≡ ∀ˢ t →
    s ≡ t
  ∀ˢ-injective-compose refl = refl

  applyTyUnderTyBinder-⇑ᵗ-local :
    ∀ χ₀ A₀ →
    applyTyUnderTyBinder χ₀ (⇑ᵗ A₀) ≡
      ⇑ᵗ (applyTy χ₀ A₀)
  applyTyUnderTyBinder-⇑ᵗ-local keep A₀ = refl
  applyTyUnderTyBinder-⇑ᵗ-local (bind B₀) A₀ =
    renameᵗ-ext-suc-comm suc A₀

  first-all-type-raw-shape :
    ∀ {C C′}
      (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ transportAllType first q ⌋ ≡
      ⌊ transportType first (∀ⁱ q) ⌋
  first-all-type-raw-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (shape-subst-source source-eq raw)
    where
    raw = transportType first (∀ⁱ q)
    source-eq = applyTys-∀ (sourceChanges first) C
    source-transport =
      subst
        (λ S → resultCtx first ∣ resultLeftCtx first
          ⊢ S ⊑ applyTys (targetTailChanges first)
              (applyTy χ (`∀ C′))
          ⊣ resultRightCtx first)
        source-eq raw
    target-eq =
      trans
        (cong (applyTys (targetTailChanges first))
          (applyTy-∀ χ C′))
        (applyTys-∀ (targetTailChanges first)
          (applyTyUnderTyBinder χ C′))

  first-all-body-shape :
    ∀ {C C′}
      (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ transportAllBody first q ⌋ ≡ ⌊ q ⌋
  first-all-body-shape q =
    ∀ˢ-injective-compose
      (trans
        (sym (cong ⌊_⌋ (transportAllCoherent first-coherence q)))
        (trans
          (first-all-type-raw-shape q)
          (transportShapeCoherent first-coherence (∀ⁱ q))))

  second-all-type-raw-shape :
    ∀ {C C′}
      (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (resultCtx first))
        ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
    ⌊ transportAllType second q ⌋ ≡
      ⌊ transportType second (∀ⁱ q) ⌋
  second-all-type-raw-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (shape-subst-source source-eq raw)
    where
    raw = transportType second (∀ⁱ q)
    source-eq = applyTys-∀ (sourceChanges second) C
    source-transport =
      subst
        (λ S → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ applyTys (targetTailChanges second)
              (applyTy χ′ (`∀ C′))
          ⊣ resultRightCtx second)
        source-eq raw
    target-eq =
      trans
        (cong (applyTys (targetTailChanges second))
          (applyTy-∀ χ′ C′))
        (applyTys-∀ (targetTailChanges second)
          (applyTyUnderTyBinder χ′ C′))

  second-all-body-shape :
    ∀ {C C′}
      (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (resultCtx first))
        ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
    ⌊ transportAllBody second q ⌋ ≡ ⌊ q ⌋
  second-all-body-shape q =
    ∀ˢ-injective-compose
      (trans
        (sym (cong ⌊_⌋ (transportAllCoherent second-coherence q)))
        (trans
          (second-all-type-raw-shape q)
          (transportShapeCoherent second-coherence (∀ⁱ q))))

  composed-all-body-shape :
    ∀ {C C′}
      (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ weak-one-step-compose-all-body first second q ⌋ ≡ ⌊ q ⌋
  composed-all-body-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (trans
        (shape-subst-source source-eq nested)
        (trans
          (second-all-body-shape (transportAllBody first q))
          (first-all-body-shape q)))
    where
    nested = transportAllBody second (transportAllBody first q)
    source-eq = sym
      (applyTysUnderTyBinders-++
        (sourceChanges first) (sourceChanges second) C)
    source-transport =
      subst
        (λ S → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (resultCtx second))
          ∣ suc (resultLeftCtx second)
          ⊢ S ⊑ applyTysUnderTyBinders
              (targetTailChanges second)
              (applyTyUnderTyBinder χ′
                (applyTysUnderTyBinders
                  (targetTailChanges first)
                  (applyTyUnderTyBinder χ C′)))
          ⊣ suc (resultRightCtx second))
        source-eq nested
    target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTyUnderTyBinder χ C′))

  all-body-paired-replacement-coherent :
    ∀ {A₀ A′ B B′ C C′}
      {A⇑⊑A′⇑ :
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A₀ ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
    q
      [ zero ↦ ⇑ᵗ A₀
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
    weak-one-step-compose-all-body first second q
      [ zero ↦
          applyTysUnderTyBinders
            (sourceChanges first ++ sourceChanges second)
            (⇑ᵗ A₀)
      ⊑⟨ weak-one-step-compose-all-body
            first second A⇑⊑A′⇑ ⟩
      applyTysUnderTyBinders
        (targetTailChanges first ++ χ′ ∷ targetTailChanges second)
        (applyTyUnderTyBinder χ (⇑ᵗ A′))
      ↤ zero ]ᴾ
    ⊑-lift∀ᵢ (weak-one-step-compose-type first second pB)
  all-body-paired-replacement-coherent
      {A₀ = A₀} {A′ = A′} {B = B} {B′ = B′}
      {C = C} {C′ = C′}
      {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} {q = q}
      replacement =
    replace-paired-target-shape target-shape
      (replace-paired-source-shape source-shape
        (replace-paired-evidence-shape evidence-shape
          endpoints-replacement))
    where
    first-replacement =
      transportAllBodyPairedReplacementCoherent
        first-coherence replacement

    source-shift =
      applyTysUnderTyBinders-⇑ᵗ (sourceChanges first) A₀

    target-head-shift =
      applyTyUnderTyBinder-⇑ᵗ-local χ A′

    target-shift =
      trans
        (cong
          (applyTysUnderTyBinders (targetTailChanges first))
          target-head-shift)
        (applyTysUnderTyBinders-⇑ᵗ
          (targetTailChanges first) (applyTy χ A′))

    normalized-first-replacement =
      replace-paired-transport-endpoints
        refl refl refl refl source-shift target-shift
        first-replacement

    second-replacement =
      transportAllBodyPairedReplacementCoherent
        second-coherence normalized-first-replacement

    input-source-eq = sym
      (applyTysUnderTyBinders-++
        (sourceChanges first) (sourceChanges second) C)

    input-target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTyUnderTyBinder χ C′))

    output-source-eq = cong ⇑ᵗ
      (sym (applyTys-++
        (sourceChanges first) (sourceChanges second) B))

    output-target-eq = cong ⇑ᵗ
      (sym
        (applyTys-++
          (targetTailChanges first)
          (χ′ ∷ targetTailChanges second)
          (applyTy χ B′)))

    inserted-source-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders (sourceChanges second))
            source-shift))
        (sym
          (applyTysUnderTyBinders-++
            (sourceChanges first) (sourceChanges second) (⇑ᵗ A₀)))

    inserted-target-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders
              (χ′ ∷ targetTailChanges second))
            target-shift))
        (sym
          (applyTysUnderTyBinders-++
            (targetTailChanges first)
            (χ′ ∷ targetTailChanges second)
            (applyTyUnderTyBinder χ (⇑ᵗ A′))))

    endpoints-replacement =
      replace-paired-transport-endpoints
        input-source-eq input-target-eq
        output-source-eq output-target-eq
        inserted-source-eq inserted-target-eq
        second-replacement

    raw-input =
      transportAllBody second (transportAllBody first q)

    source-shape =
      trans
        (composed-all-body-shape q)
        (trans
          (sym (first-all-body-shape q))
          (trans
            (sym
              (second-all-body-shape
                (transportAllBody first q)))
            (sym
              (shape-transport-imprecision-endpoints
                input-source-eq input-target-eq raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-lift∀ᵢ nested-output

    target-shape =
      trans
        (shape-lift∀ᵢ
          (weak-one-step-compose-type first second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-lift∀ᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    output-source-eq output-target-eq raw-output))))))

    normalized-inserted =
      transport-imprecision-endpoints source-shift target-shift
        (transportAllBody first A⇑⊑A′⇑)

    second-inserted =
      transportAllBody second normalized-inserted

    evidence-shape =
      trans
        (composed-all-body-shape A⇑⊑A′⇑)
        (trans
          (sym (first-all-body-shape A⇑⊑A′⇑))
          (trans
            (sym
              (shape-transport-imprecision-endpoints
                source-shift target-shift
                (transportAllBody first A⇑⊑A′⇑)))
            (trans
              (sym (second-all-body-shape normalized-inserted))
              (sym
                (shape-transport-imprecision-endpoints
                  inserted-source-eq inserted-target-eq
                  second-inserted)))))

  first-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ sourceNuBody (transportSourceNu first safe occ q) ⌋
      ≡ ⌊ q ⌋
  first-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges first) C)
            (transportType first (ν safe occ q)))
          (transportShapeCoherent first-coherence (ν safe occ q))))
    where
    final-index = transportSourceNu first safe occ q

  second-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (resultCtx first))
        ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ D ⊣ resultRightCtx first) →
    ⌊ sourceNuBody (transportSourceNu second safe occ q) ⌋
      ≡ ⌊ q ⌋
  second-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges second) C)
            (transportType second (ν safe occ q)))
          (transportShapeCoherent second-coherence (ν safe occ q))))
    where
    final-index = transportSourceNu second safe occ q

  composed-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ sourceNuBody
        (weak-one-step-compose-source-nu
          first second safe occ q) ⌋
      ≡ ⌊ q ⌋
  composed-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀
              (sourceChanges first ++ sourceChanges second) C)
            (weak-one-step-compose-type
              first second (ν safe occ q)))
          (shape-coherent (ν safe occ q))))
    where
    final-index =
      weak-one-step-compose-source-nu first second safe occ q

  source-nu-body-left-replacement-coherent :
    ∀ {A₀ B B′ C}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true) →
    q [ zero ↦ ⇑ᵗ A₀ ]ᴸ ⊑-source-liftνᵢ pB →
    sourceNuBody
        (weak-one-step-compose-source-nu
          first second safe occ q)
      [ zero ↦
          applyTysUnderTyBinders
            (sourceChanges first ++ sourceChanges second)
            (⇑ᵗ A₀) ]ᴸ
    ⊑-source-liftνᵢ
      (weak-one-step-compose-type first second pB)
  source-nu-body-left-replacement-coherent
      {A₀ = A₀} {B = B} {B′ = B′} {C = C}
      {pB = pB} {q = q} safe occ replacement =
    replace-left-target-shape target-shape
      (replace-left-source-shape source-shape
        endpoints-replacement)
    where
    first-index = transportSourceNu first safe occ q

    first-replacement =
      transportSourceNuBodyLeftReplacementCoherent
        first-coherence safe occ replacement

    source-shift =
      applyTysUnderTyBinders-⇑ᵗ (sourceChanges first) A₀

    normalized-first-replacement =
      replace-left-transport-endpoints
        refl refl refl source-shift first-replacement

    second-index =
      transportSourceNu second
        (sourceNuSafe first-index)
        (sourceNuOccurs first-index)
        (sourceNuBody first-index)

    second-replacement =
      transportSourceNuBodyLeftReplacementCoherent
        second-coherence
        (sourceNuSafe first-index)
        (sourceNuOccurs first-index)
        normalized-first-replacement

    input-source-eq = sym
      (applyTysUnderTyBinders-++
        (sourceChanges first) (sourceChanges second) C)

    target-eq = sym
      (applyTys-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTy χ B′))

    output-source-eq = cong ⇑ᵗ
      (sym
        (applyTys-++
          (sourceChanges first) (sourceChanges second) B))

    inserted-source-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders (sourceChanges second))
            source-shift))
        (sym
          (applyTysUnderTyBinders-++
            (sourceChanges first) (sourceChanges second) (⇑ᵗ A₀)))

    endpoints-replacement =
      replace-left-transport-endpoints
        input-source-eq target-eq
        output-source-eq inserted-source-eq
        second-replacement

    raw-input = sourceNuBody second-index

    source-shape =
      trans
        (composed-source-nu-body-shape safe occ q)
        (trans
          (sym (first-source-nu-body-shape safe occ q))
          (trans
            (sym
              (second-source-nu-body-shape
                (sourceNuSafe first-index)
                (sourceNuOccurs first-index)
                (sourceNuBody first-index)))
            (sym
              (shape-transport-imprecision-endpoints
                input-source-eq target-eq raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-source-liftνᵢ nested-output

    target-shape =
      trans
        (shape-source-liftνᵢ
          (weak-one-step-compose-type first second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-source-liftνᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    output-source-eq target-eq raw-output))))))

  right-body-right-replacement-coherent :
    ∀ {A₀ B B′ C′}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
    pC [ zero ↦ ⇑ᵗ A₀ ]ᴿ ⊑-target-lift-rightᵢ pB →
    weak-one-step-compose-right-body first second pC
      [ zero ↦
          applyTysUnderTyBinders
            (targetTailChanges first ++
              χ′ ∷ targetTailChanges second)
            (applyTyUnderTyBinder χ (⇑ᵗ A₀)) ]ᴿ
    ⊑-target-lift-rightᵢ
      (weak-one-step-compose-type first second pB)
  right-body-right-replacement-coherent
      {A₀ = A₀} {B = B} {B′ = B′} {C′ = C′}
      {pB = pB} {pC = pC} replacement =
    replace-right-target-shape target-shape
      (replace-right-source-shape source-shape
        endpoints-replacement)
    where
    first-replacement =
      transportRightBodyRightReplacementCoherent
        first-coherence replacement

    target-head-shift =
      applyTyUnderTyBinder-⇑ᵗ-local χ A₀

    target-shift =
      trans
        (cong
          (applyTysUnderTyBinders (targetTailChanges first))
          target-head-shift)
        (applyTysUnderTyBinders-⇑ᵗ
          (targetTailChanges first) (applyTy χ A₀))

    normalized-first-replacement =
      replace-right-transport-endpoints
        refl refl refl target-shift first-replacement

    second-replacement =
      transportRightBodyRightReplacementCoherent
        second-coherence normalized-first-replacement

    input-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) B)

    input-target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ′ ∷ targetTailChanges second)
        (applyTyUnderTyBinder χ C′))

    output-target-eq = cong ⇑ᵗ
      (sym
        (applyTys-++
          (targetTailChanges first)
          (χ′ ∷ targetTailChanges second)
          (applyTy χ B′)))

    inserted-target-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders
              (χ′ ∷ targetTailChanges second))
            target-shift))
        (sym
          (applyTysUnderTyBinders-++
            (targetTailChanges first)
            (χ′ ∷ targetTailChanges second)
            (applyTyUnderTyBinder χ (⇑ᵗ A₀))))

    endpoints-replacement =
      replace-right-transport-endpoints
        input-source-eq input-target-eq
        output-target-eq inserted-target-eq
        second-replacement

    raw-input =
      transportRightBody second (transportRightBody first pC)

    source-shape =
      trans
        (right-body-shape-coherent pC)
        (trans
          (sym
            (transportRightBodyShapeCoherent first-coherence pC))
          (trans
            (sym
              (transportRightBodyShapeCoherent second-coherence
                (transportRightBody first pC)))
            (sym
              (shape-transport-imprecision-endpoints
                input-source-eq input-target-eq raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-target-lift-rightᵢ nested-output

    target-shape =
      trans
        (shape-target-lift-rightᵢ
          (weak-one-step-compose-type first second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-target-lift-rightᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    input-source-eq output-target-eq raw-output))))))


weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (silent : LeftSilentResult
      {M = M} {V′ = V′} {A = A} {B = B} {ρ = ρ}) →
  let first = silentResult silent in
  ∀ {χ N′}
    (second : WeakOneStepResult (resultStore first)
      (sourceResult first) N′
      (resultSourceType first) (resultTargetType first) χ) →
  WeakOneStepTypeCoherence first →
  WeakOneStepTypeCoherence second →
  WeakOneStepTypeCoherence
    (weak-one-step-prepend-left-silentᵀ silent second)
weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    (left-silent first
      (left-silent-invariant refl refl))
    {χ = χ} second first-coherence second-coherence =
  weak-step-type-coherence arrow-coherent all-coherent shape-coherent
    right-body-shape-coherent left-replacement-coherent
    right-replacement-coherent
    paired-replacement-coherent
    all-body-paired-replacement-coherent
    source-nu-body-left-replacement-coherent
    right-body-right-replacement-coherent
  where
  arrow-coherent :
    ∀ {C C′ D D′}
      (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
      (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
    transportArrowType
      (weak-one-step-prepend-left-silentᵀ
        (left-silent first
          (left-silent-invariant refl refl)) second)
      pC pD ≡
    weak-one-step-compose-type first second pC ↦
      weak-one-step-compose-type first second pD
  arrow-coherent {C = C} {C′ = C′} {D = D} {D′ = D′} pC pD =
    HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ combined pC pD)
        (HE.trans
          (weak-one-step-compose-type-to-nested≅
            first second (pC ↦ pD))
          (HE.trans
            (weak-one-step-nested-arrow-coherent≅
              first second first-coherence second-coherence pC pD)
            (HE.trans
              (HE.sym
                (subst²-to-≅
                  {P = λ S T →
                    resultCtx second ∣ resultLeftCtx second
                      ⊢ S ⊑ T ⊣ resultRightCtx second}
                  (cong₂ _⇒_
                    (sym (applyTys-++
                      (sourceChanges first)
                      (sourceChanges second) C))
                    (sym (applyTys-++
                      (sourceChanges first)
                      (sourceChanges second) D)))
                  (cong₂ _⇒_
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (χ ∷ targetTailChanges second)
                      (applyTy keep C′)))
                    (sym (applyTys-++
                      (targetTailChanges first)
                      (χ ∷ targetTailChanges second)
                      (applyTy keep D′))))
                  (transportType second (transportType first pC) ↦
                    transportType second (transportType first pD))))
              (HE.≡-to-≅
                (weak-one-step-compose-arrow-componentsᵀ
                  first second pC pD))))))
    where
    combined =
      weak-one-step-prepend-left-silentᵀ
        (left-silent first (left-silent-invariant refl refl)) second

  all-coherent :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    transportAllType
      (weak-one-step-prepend-left-silentᵀ
        (left-silent first
          (left-silent-invariant refl refl)) second)
      q ≡
    ∀ⁱ (weak-one-step-compose-all-body first second q)
  all-coherent {C = C} {C′ = C′} q =
    HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ combined q)
        (HE.trans
          (weak-one-step-compose-type-to-nested≅
            first second (∀ⁱ q))
          (HE.trans
            (weak-one-step-nested-all-coherent≅
              first second first-coherence second-coherence q)
            (HE.trans
              (HE.sym
                (subst²-to-≅
                  {P = λ S T →
                    resultCtx second ∣ resultLeftCtx second
                      ⊢ S ⊑ T ⊣ resultRightCtx second}
                  (cong `∀
                    (sym (applyTysUnderTyBinders-++
                      (sourceChanges first)
                      (sourceChanges second) C)))
                  (cong `∀
                    (sym (applyTysUnderTyBinders-++
                      (targetTailChanges first)
                      (χ ∷ targetTailChanges second)
                      (applyTyUnderTyBinder keep C′))))
                  (∀ⁱ (transportAllBody second
                    (transportAllBody first q)))))
              (HE.≡-to-≅
                (weak-one-step-compose-all-componentsᵀ
                  first second q))))))
    where
    combined =
      weak-one-step-prepend-left-silentᵀ
        (left-silent first (left-silent-invariant refl refl)) second

  shape-coherent :
    ∀ {C D}
      (p : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ weak-one-step-compose-type first second p ⌋
      ≡ ⌊ p ⌋
  shape-coherent {C = C} {D = D} p =
    trans
      (shape-subst-target target-eq source-transport)
      (trans
        (shape-subst-source source-eq nested)
        (trans
          (transportShapeCoherent second-coherence
            (transportType first p))
          (transportShapeCoherent first-coherence p)))
    where
    nested = transportType second (transportType first p)
    source-eq = sym
      (applyTys-++ (sourceChanges first) (sourceChanges second) C)
    source-transport =
      subst
        (λ S → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ applyTys (targetTailChanges second)
              (applyTy χ
                (applyTys (targetTailChanges first) D))
          ⊣ resultRightCtx second)
        source-eq nested
    target-eq = sym
      (applyTys-++ (targetTailChanges first)
        (χ ∷ targetTailChanges second) D)

  right-body-shape-coherent :
    ∀ {C D}
      (p : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ) →
    ⌊ weak-one-step-compose-right-body first second p ⌋
      ≡ ⌊ p ⌋
  right-body-shape-coherent {C = C} {D = D} p =
    trans
      (shape-subst-target target-eq source-transport)
      (trans
        (shape-subst-source source-eq nested)
        (trans
          (transportRightBodyShapeCoherent second-coherence
            (transportRightBody first p))
          (transportRightBodyShapeCoherent first-coherence p)))
    where
    nested = transportRightBody second (transportRightBody first p)
    source-eq = sym
      (applyTys-++ (sourceChanges first) (sourceChanges second) C)
    source-transport =
      subst
        (λ S → ⇑ᴿᵢ (resultCtx second) ∣ resultLeftCtx second
          ⊢ S ⊑ applyTysUnderTyBinders
              (targetTailChanges second)
              (applyTyUnderTyBinder χ
                (applyTysUnderTyBinders
                  (targetTailChanges first) D))
          ⊣ suc (resultRightCtx second))
        source-eq nested
    target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ ∷ targetTailChanges second) D)

  left-replacement-coherent :
    ∀ {C C′ D α X}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ C′ ⊣ Δᴿ} →
    p [ α ↦ X ]ᴸ q →
    weak-one-step-compose-type first second p
      [ applyTyVars
          (sourceChanges first ++ sourceChanges second) α
      ↦ applyTys
          (sourceChanges first ++ sourceChanges second) X ]ᴸ
    weak-one-step-compose-type first second q
  left-replacement-coherent
      {C = C} {C′ = C′} {D = D} {α = α} {X = X}
      replacement
    rewrite applyTyVars-++ (sourceChanges first)
              (sourceChanges second) α
          | applyTys-++ (sourceChanges first)
              (sourceChanges second) X
          | applyTys-++ (sourceChanges first)
              (sourceChanges second) C
          | applyTys-++ (sourceChanges first)
              (sourceChanges second) C′
          | applyTys-++ (sourceChanges first)
              (sourceChanges second) D =
    transportLeftReplacementCoherent second-coherence
      (transportLeftReplacementCoherent
        first-coherence replacement)

  right-replacement-coherent :
    ∀ {C C′ D′ β X′}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊑ D′ ⊣ Δᴿ} →
    p [ β ↦ X′ ]ᴿ q →
    weak-one-step-compose-type first second p
      [ applyTyVars (targetTailChanges second)
          (applyTyVar χ β)
      ↦ applyTys (targetTailChanges second)
          (applyTy χ X′) ]ᴿ
    weak-one-step-compose-type first second q
  right-replacement-coherent
      {C = C} {C′ = C′} {D′ = D′} replacement
    rewrite applyTys-++ (sourceChanges first)
              (sourceChanges second) C =
    transportRightReplacementCoherent second-coherence
      (transportRightReplacementCoherent
        first-coherence replacement)

  paired-replacement-coherent :
    ∀ {C C′ D D′ α β X X′}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ} →
    p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
    weak-one-step-compose-type first second p
      [ applyTyVars
          (sourceChanges first ++ sourceChanges second) α
      ↦ applyTys
          (sourceChanges first ++ sourceChanges second) X
      ⊑⟨ weak-one-step-compose-type first second pX ⟩
      applyTys (targetTailChanges second) (applyTy χ X′)
      ↤ applyTyVars (targetTailChanges second)
          (applyTyVar χ β) ]ᴾ
    weak-one-step-compose-type first second q
  paired-replacement-coherent
      {C = C} {C′ = C′} {D = D} {D′ = D′}
      {α = α} {X = X} replacement
    rewrite applyTyVars-++ (sourceChanges first)
              (sourceChanges second) α
          | applyTys-++ (sourceChanges first)
              (sourceChanges second) X
          | applyTys-++ (sourceChanges first)
              (sourceChanges second) C
          | applyTys-++ (sourceChanges first)
              (sourceChanges second) D =
    transportPairedReplacementCoherent second-coherence
      (transportPairedReplacementCoherent
        first-coherence replacement)

  ∀ˢ-injective-compose :
    ∀ {s t} →
    ∀ˢ s ≡ ∀ˢ t →
    s ≡ t
  ∀ˢ-injective-compose refl = refl

  first-all-type-raw-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ transportAllType first q ⌋ ≡
      ⌊ transportType first (∀ⁱ q) ⌋
  first-all-type-raw-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (shape-subst-source source-eq raw)
    where
    raw = transportType first (∀ⁱ q)
    source-eq = applyTys-∀ (sourceChanges first) C
    source-transport =
      subst
        (λ S → resultCtx first ∣ resultLeftCtx first
          ⊢ S ⊑ applyTys (targetTailChanges first)
              (applyTy keep (`∀ C′))
          ⊣ resultRightCtx first)
        source-eq raw
    target-eq =
      trans
        (cong (applyTys (targetTailChanges first))
          (applyTy-∀ keep C′))
        (applyTys-∀ (targetTailChanges first)
          (applyTyUnderTyBinder keep C′))

  first-all-body-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ transportAllBody first q ⌋ ≡ ⌊ q ⌋
  first-all-body-shape q =
    ∀ˢ-injective-compose
      (trans
        (sym (cong ⌊_⌋ (transportAllCoherent first-coherence q)))
        (trans
          (first-all-type-raw-shape q)
          (transportShapeCoherent first-coherence (∀ⁱ q))))

  second-all-type-raw-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ (resultCtx first) ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
    ⌊ transportAllType second q ⌋ ≡
      ⌊ transportType second (∀ⁱ q) ⌋
  second-all-type-raw-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (shape-subst-source source-eq raw)
    where
    raw = transportType second (∀ⁱ q)
    source-eq = applyTys-∀ (sourceChanges second) C
    source-transport =
      subst
        (λ S → resultCtx second ∣ resultLeftCtx second
          ⊢ S ⊑ applyTys (targetTailChanges second)
              (applyTy χ (`∀ C′))
          ⊣ resultRightCtx second)
        source-eq raw
    target-eq =
      trans
        (cong (applyTys (targetTailChanges second))
          (applyTy-∀ χ C′))
        (applyTys-∀ (targetTailChanges second)
          (applyTyUnderTyBinder χ C′))

  second-all-body-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ (resultCtx first) ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ C′ ⊣ suc (resultRightCtx first)) →
    ⌊ transportAllBody second q ⌋ ≡ ⌊ q ⌋
  second-all-body-shape q =
    ∀ˢ-injective-compose
      (trans
        (sym (cong ⌊_⌋ (transportAllCoherent second-coherence q)))
        (trans
          (second-all-type-raw-shape q)
          (transportShapeCoherent second-coherence (∀ⁱ q))))

  composed-all-body-shape :
    ∀ {C C′}
      (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    ⌊ weak-one-step-compose-all-body first second q ⌋ ≡ ⌊ q ⌋
  composed-all-body-shape {C = C} {C′ = C′} q =
    trans
      (shape-subst-target target-eq source-transport)
      (trans
        (shape-subst-source source-eq nested)
        (trans
          (second-all-body-shape (transportAllBody first q))
          (first-all-body-shape q)))
    where
    nested = transportAllBody second (transportAllBody first q)
    source-eq = sym
      (applyTysUnderTyBinders-++
        (sourceChanges first) (sourceChanges second) C)
    source-transport =
      subst
        (λ S → ∀ᵢᶜ (resultCtx second) ∣ suc (resultLeftCtx second)
          ⊢ S ⊑ applyTysUnderTyBinders
              (targetTailChanges second)
              (applyTyUnderTyBinder χ
                (applyTysUnderTyBinders
                  (targetTailChanges first)
                  (applyTyUnderTyBinder keep C′)))
          ⊣ suc (resultRightCtx second))
        source-eq nested
    target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ ∷ targetTailChanges second)
        (applyTyUnderTyBinder keep C′))

  all-body-paired-replacement-coherent :
    ∀ {A A′ B B′ C C′}
      {A⇑⊑A′⇑ :
        ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
    q
      [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
    weak-one-step-compose-all-body first second q
      [ zero ↦
          applyTysUnderTyBinders
            (sourceChanges first ++ sourceChanges second)
            (⇑ᵗ A)
      ⊑⟨ weak-one-step-compose-all-body first second A⇑⊑A′⇑ ⟩
      applyTysUnderTyBinders (targetTailChanges second)
        (applyTyUnderTyBinder χ (⇑ᵗ A′))
      ↤ zero ]ᴾ
    ⊑-lift∀ᵢ (weak-one-step-compose-type first second pB)
  all-body-paired-replacement-coherent
      {A = A} {B = B} {C = C} {C′ = C′}
      {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB} {q = q} replacement =
    replace-paired-target-shape target-shape
      (replace-paired-source-shape source-shape
        (replace-paired-evidence-shape evidence-shape
          endpoints-replacement))
    where
    source-shift =
      applyTysUnderTyBinders-⇑ᵗ (sourceChanges first) A

    first-replacement =
      transportAllBodyPairedReplacementCoherent
        first-coherence replacement

    normalized-first-replacement =
      replace-paired-transport-endpoints
        refl refl refl refl source-shift refl first-replacement

    second-replacement =
      transportAllBodyPairedReplacementCoherent
        second-coherence normalized-first-replacement

    input-source-eq = sym
      (applyTysUnderTyBinders-++
        (sourceChanges first) (sourceChanges second) C)

    output-source-eq = cong ⇑ᵗ
      (sym (applyTys-++
        (sourceChanges first) (sourceChanges second) B))

    inserted-source-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders (sourceChanges second))
            source-shift))
        (sym
          (applyTysUnderTyBinders-++
            (sourceChanges first) (sourceChanges second) (⇑ᵗ A)))

    endpoints-replacement =
      replace-paired-transport-endpoints
        input-source-eq refl output-source-eq refl
        inserted-source-eq refl second-replacement

    raw-input =
      transportAllBody second (transportAllBody first q)

    transported-input =
      transport-imprecision-endpoints input-source-eq refl raw-input

    source-shape =
      trans
        (composed-all-body-shape q)
        (trans
          (sym (first-all-body-shape q))
          (trans
            (sym
              (second-all-body-shape
                (transportAllBody first q)))
            (sym
              (shape-transport-imprecision-endpoints
                input-source-eq refl raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-lift∀ᵢ nested-output

    target-shape =
      trans
        (shape-lift∀ᵢ (weak-one-step-compose-type first second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-lift∀ᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    output-source-eq refl raw-output))))))

    normalized-inserted =
      transport-imprecision-endpoints source-shift refl
        (transportAllBody first A⇑⊑A′⇑)

    second-inserted =
      transportAllBody second normalized-inserted

    evidence-shape =
      trans
        (composed-all-body-shape A⇑⊑A′⇑)
        (trans
          (sym (first-all-body-shape A⇑⊑A′⇑))
          (trans
            (sym
              (shape-transport-imprecision-endpoints
                source-shift refl
                (transportAllBody first A⇑⊑A′⇑)))
            (trans
              (sym (second-all-body-shape normalized-inserted))
              (sym
                (shape-transport-imprecision-endpoints
                  inserted-source-eq refl second-inserted)))))

  first-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ sourceNuBody (transportSourceNu first safe occ q) ⌋
      ≡ ⌊ q ⌋
  first-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges first) C)
            (transportType first (ν safe occ q)))
          (transportShapeCoherent first-coherence (ν safe occ q))))
    where
    final-index = transportSourceNu first safe occ q

  second-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (resultCtx first))
        ∣ suc (resultLeftCtx first)
        ⊢ C ⊑ D ⊣ resultRightCtx first) →
    ⌊ sourceNuBody (transportSourceNu second safe occ q) ⌋
      ≡ ⌊ q ⌋
  second-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges second) C)
            (transportType second (ν safe occ q)))
          (transportShapeCoherent second-coherence (ν safe occ q))))
    where
    final-index = transportSourceNu second safe occ q

  composed-source-nu-body-shape :
    ∀ {C D}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true)
      (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
    ⌊ sourceNuBody
        (weak-one-step-compose-source-nu first second safe occ q) ⌋
      ≡ ⌊ q ⌋
  composed-source-nu-body-shape {C = C} safe occ q =
    νˢ-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀
              (sourceChanges first ++ sourceChanges second) C)
            (weak-one-step-compose-type
              first second (ν safe occ q)))
          (shape-coherent (ν safe occ q))))
    where
    final-index =
      weak-one-step-compose-source-nu first second safe occ q

  source-nu-body-left-replacement-coherent :
    ∀ {A B B′ C}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true) →
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
    sourceNuBody
        (weak-one-step-compose-source-nu first second safe occ q)
      [ zero ↦
          applyTysUnderTyBinders
            (sourceChanges first ++ sourceChanges second)
            (⇑ᵗ A) ]ᴸ
    ⊑-source-liftνᵢ
      (weak-one-step-compose-type first second pB)
  source-nu-body-left-replacement-coherent
      {A = A} {B = B} {C = C} {pB = pB} {q = q}
      safe occ replacement =
    replace-left-target-shape target-shape
      (replace-left-source-shape source-shape endpoints-replacement)
    where
    first-index = transportSourceNu first safe occ q

    first-replacement =
      transportSourceNuBodyLeftReplacementCoherent
        first-coherence safe occ replacement

    source-shift =
      applyTysUnderTyBinders-⇑ᵗ (sourceChanges first) A

    normalized-first-replacement =
      replace-left-transport-endpoints
        refl refl refl source-shift first-replacement

    second-index =
      transportSourceNu second
        (sourceNuSafe first-index)
        (sourceNuOccurs first-index)
        (sourceNuBody first-index)

    second-replacement =
      transportSourceNuBodyLeftReplacementCoherent
        second-coherence
        (sourceNuSafe first-index)
        (sourceNuOccurs first-index)
        normalized-first-replacement

    input-source-eq = sym
      (applyTysUnderTyBinders-++
        (sourceChanges first) (sourceChanges second) C)

    output-source-eq = cong ⇑ᵗ
      (sym (applyTys-++
        (sourceChanges first) (sourceChanges second) B))

    inserted-source-eq =
      trans
        (sym
          (cong
            (applyTysUnderTyBinders (sourceChanges second))
            source-shift))
        (sym
          (applyTysUnderTyBinders-++
            (sourceChanges first) (sourceChanges second) (⇑ᵗ A)))

    endpoints-replacement =
      replace-left-transport-endpoints
        input-source-eq refl output-source-eq inserted-source-eq
        second-replacement

    final-index =
      weak-one-step-compose-source-nu first second safe occ q

    raw-input = sourceNuBody second-index

    source-shape =
      trans
        (composed-source-nu-body-shape safe occ q)
        (trans
          (sym (first-source-nu-body-shape safe occ q))
          (trans
            (sym
              (second-source-nu-body-shape
                (sourceNuSafe first-index)
                (sourceNuOccurs first-index)
                (sourceNuBody first-index)))
            (sym
              (shape-transport-imprecision-endpoints
                input-source-eq refl raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-source-liftνᵢ nested-output

    target-shape =
      trans
        (shape-source-liftνᵢ
          (weak-one-step-compose-type first second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-source-liftνᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    output-source-eq refl raw-output))))))

  right-body-right-replacement-coherent :
    ∀ {A B B′ C′}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
    pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
    weak-one-step-compose-right-body first second pC
      [ zero ↦
          applyTysUnderTyBinders (targetTailChanges second)
            (applyTyUnderTyBinder χ (⇑ᵗ A)) ]ᴿ
    ⊑-target-lift-rightᵢ
      (weak-one-step-compose-type first second pB)
  right-body-right-replacement-coherent
      {A = A} {B = B} {B′ = B′} {C′ = C′}
      {pB = pB} {pC = pC} replacement =
    replace-right-target-shape target-shape
      (replace-right-source-shape source-shape endpoints-replacement)
    where
    first-replacement =
      transportRightBodyRightReplacementCoherent
        first-coherence replacement

    second-replacement =
      transportRightBodyRightReplacementCoherent
        second-coherence first-replacement

    input-source-eq = sym
      (applyTys-++
        (sourceChanges first) (sourceChanges second) B)

    input-target-eq = sym
      (applyTysUnderTyBinders-++
        (targetTailChanges first)
        (χ ∷ targetTailChanges second) C′)

    output-target-eq = cong ⇑ᵗ
      (sym
        (applyTys-++
          (targetTailChanges first)
          (χ ∷ targetTailChanges second) B′))

    endpoints-replacement =
      replace-right-transport-endpoints
        input-source-eq input-target-eq output-target-eq refl
        second-replacement

    raw-input =
      transportRightBody second (transportRightBody first pC)

    source-shape =
      trans
        (right-body-shape-coherent pC)
        (trans
          (sym
            (transportRightBodyShapeCoherent first-coherence pC))
          (trans
            (sym
              (transportRightBodyShapeCoherent second-coherence
                (transportRightBody first pC)))
            (sym
              (shape-transport-imprecision-endpoints
                input-source-eq input-target-eq raw-input))))

    nested-output = transportType second (transportType first pB)

    raw-output = ⊑-target-lift-rightᵢ nested-output

    target-shape =
      trans
        (shape-target-lift-rightᵢ
          (weak-one-step-compose-type first second pB))
        (trans
          (shape-coherent pB)
          (trans
            (sym (transportShapeCoherent first-coherence pB))
            (trans
              (sym
                (transportShapeCoherent second-coherence
                  (transportType first pB)))
              (trans
                (sym (shape-target-lift-rightᵢ nested-output))
                (sym
                  (shape-transport-imprecision-endpoints
                    input-source-eq output-target-eq raw-output))))))

weak-one-step-arrow-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ A A′ B B′ pA pB}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  WeakOneStepArrowResult {χ = keep} pA pB
weak-one-step-arrow-relatedᵀ result =
  weak-arrow-result (weak-one-step-relatedᵀ result) result

weak-one-step-arrow-outcome-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ A A′ B B′ pA pB}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB) →
  WeakOneStepArrowOutcome {χ = keep} pA pB
weak-one-step-arrow-outcome-relatedᵀ result =
  arrow-outcome-related
    (weak-one-step-arrow-relatedᵀ result)
    (weak-one-step-related-transportᵀ result)
    (weak-one-step-related-type-coherenceᵀ result)

weak-one-step-arrow-reindexᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ A A′ B B′ χ pA pB}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result :
      WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ) →
  resultCtx result
    ∣ resultLeftCtx result
    ∣ resultRightCtx result
    ∣ resultStore result ∣ []
    ⊢ᴺ sourceResult result ⊑ targetResult result
    ⦂ applyTys (sourceChanges result) A ⇒
        applyTys (sourceChanges result) B
      ⊑ applyTys (targetTailChanges result) (applyTy χ A′) ⇒
        applyTys (targetTailChanges result) (applyTy χ B′)
    ∶ transportType result pA ↦ transportType result pB →
  WeakOneStepArrowResult pA pB
weak-one-step-arrow-reindexᵀ
    {A′ = A′} {B′ = B′} {χ = χ} result related =
  weak-arrow-result reindexed related
  where
  source-eq =
    sym (applyTys-⇒
      (sourceChanges result) _ _)

  target-eq =
    sym
      (trans
        (cong (applyTys (targetTailChanges result))
          (applyTys-⇒ (χ ∷ []) A′ B′))
        (applyTys-⇒ (targetTailChanges result)
          (applyTy χ A′) (applyTy χ B′)))

  reindexed = weak-one-step-reindexᵀ
    result source-eq target-eq related

weak-one-step-arrow-reindex-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ A A′ B B′ χ pA pB}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result :
      WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ)
    (related : resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ sourceResult result ⊑ targetResult result
      ⦂ applyTys (sourceChanges result) A ⇒
          applyTys (sourceChanges result) B
        ⊑ applyTys (targetTailChanges result) (applyTy χ A′) ⇒
          applyTys (targetTailChanges result) (applyTy χ B′)
      ∶ transportType result pA ↦ transportType result pB) →
  WeakOneStepTransport result →
  WeakOneStepTransport
    (weakArrowResult
      (weak-one-step-arrow-reindexᵀ result related))
weak-one-step-arrow-reindex-preserves-transportᵀ
    {A′ = A′} {B′ = B′} {χ = χ}
    result related transport =
  weak-one-step-reindex-preserves-transportᵀ
    result source-eq target-eq related transport
  where
  source-eq =
    sym (applyTys-⇒
      (sourceChanges result) _ _)

  target-eq =
    sym
      (trans
        (cong (applyTys (targetTailChanges result))
          (applyTys-⇒ (χ ∷ []) A′ B′))
        (applyTys-⇒ (targetTailChanges result)
          (applyTy χ A′) (applyTy χ B′)))

left-catchup-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Value M × No• M) ⊎ M ≡ blame →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ B ∶ p →
  LeftCatchupResult {M = M} {V′ = V′} {ρ = ρ}
left-catchup-relatedᵀ final result =
  left-catchup (weak-one-step-relatedᵀ result)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

weak-one-step-source-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ M N′ A B χ χs} →
  M —↠[ χs ] blame →
  WeakOneStepOutcome {Φ} {Δᴸ} {Δᴿ} ρ M N′ A B χ
weak-one-step-source-blameᵀ = outcome-source-blame

ν-blame-tail :
  ∀ {N A c χs} →
  N —↠[ χs ] blame →
  ν A N c —↠[ χs ++ keep ∷ [] ] blame
ν-blame-tail N↠blame =
  ↠-trans (ν-↠ N↠blame)
    (↠-step blame-ν ↠-refl)

·₁-blame-tail :
  ∀ {L M χs} →
  No• M →
  L —↠[ χs ] blame →
  L · M —↠[ χs ++ keep ∷ [] ] blame
·₁-blame-tail noM L↠blame =
  ↠-trans (·₁-↠ noM L↠blame)
    (↠-step (pure-step blame-·₁) ↠-refl)

weak-one-step-·₁-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  (inner : WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ) →
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ sourceResult inner ⊑ targetResult inner
    ⦂ applyTys (sourceChanges inner) A ⇒
        applyTys (sourceChanges inner) B
      ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ∶ transportType inner pA ↦ transportType inner pB →
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ applyTerms (sourceChanges inner) M
      ⊑ applyTerms (targetTailChanges inner) (applyTerm χ M′)
    ⦂ applyTys (sourceChanges inner) A
      ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
    ∶ transportType inner pA →
  WeakOneStepResult ρ
    (L · M) (L₁′ · applyTerm χ M′) B B′ χ
weak-one-step-·₁-frameᵀ
    {M = M} {M′ = M′} {B = B} {B′ = B′} {χ = χ}
    noM noM′ inner L⊑L′ M⊑M′ =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult =
        sourceResult inner · applyTerms (sourceChanges inner) M
    ; targetResult =
        targetResult inner ·
          applyTerms (targetTailChanges inner) (applyTerm χ M′)
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) B
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; transportSourceNu = transportSourceNu inner
    ; resultType = transportType inner _
    ; sourceCatchup = ·₁-↠ noM (sourceCatchup inner)
    ; targetTail =
        ·₁-↠ (applyTerm-preserves-No• χ noM′)
          (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = ·⊑·ᵀ L⊑L′ M⊑M′
    }

weak-one-step-·₁-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  (∀ (inner :
      WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ) →
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) A ⇒
          applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
          applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner pA ↦ transportType inner pB) ×
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ applyTerms (sourceChanges inner) M
        ⊑ applyTerms (targetTailChanges inner) (applyTerm χ M′)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
      ∶ transportType inner pA) ×
    WeakOneStepTransport inner) →
  WeakOneStepOutcome ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ →
  WeakOneStepOutcome ρ
    (L · M) (L₁′ · applyTerm χ M′) B B′ χ
weak-one-step-·₁-frame-outcomeᵀ
    noM noM′ frame
    (outcome-related inner carried-transport carried-coherence)
    with frame inner
weak-one-step-·₁-frame-outcomeᵀ
    noM noM′ frame
    (outcome-related inner carried-transport carried-coherence)
    | L⊑L′ , M⊑M′ , transport =
  outcome-related
    (weak-one-step-·₁-frameᵀ noM noM′ inner L⊑L′ M⊑M′)
    (weak-step-transport (transportNo•Terms transport))
    (weak-step-type-coherence
      (transportArrowCoherent carried-coherence)
      (transportAllCoherent carried-coherence)
      (transportShapeCoherent carried-coherence)
      (transportRightBodyShapeCoherent carried-coherence)
      (transportLeftReplacementCoherent carried-coherence)
      (transportRightReplacementCoherent carried-coherence)
      (transportPairedReplacementCoherent carried-coherence)
      (transportAllBodyPairedReplacementCoherent carried-coherence)
      (transportSourceNuBodyLeftReplacementCoherent carried-coherence)
      (transportRightBodyRightReplacementCoherent carried-coherence))
weak-one-step-·₁-frame-outcomeᵀ
    noM noM′ frame (outcome-source-blame source↠) =
  outcome-source-blame (·₁-blame-tail noM source↠)

weak-one-step-·₁-frame-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  (inner : WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ) →
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ sourceResult inner ⊑ targetResult inner
    ⦂ applyTys (sourceChanges inner) A ⇒
        applyTys (sourceChanges inner) B
      ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ∶ transportType inner pA ↦ transportType inner pB →
  WeakOneStepTransport inner →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  WeakOneStepResult ρ
    (L · M) (L₁′ · applyTerm χ M′) B B′ χ
weak-one-step-·₁-frame-transportᵀ
    noM noM′ inner L⊑L′ transport M⊑M′ =
  weak-one-step-·₁-frameᵀ noM noM′ inner L⊑L′
    (transportNo•Terms transport noM noM′ M⊑M′)

weak-one-step-·₁-frame-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (noM : No• M) (noM′ : No• M′)
    (inner : WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ)
    (L⊑L′ :
      resultCtx inner
        ∣ resultLeftCtx inner
        ∣ resultRightCtx inner
        ∣ resultStore inner ∣ []
        ⊢ᴺ sourceResult inner ⊑ targetResult inner
        ⦂ applyTys (sourceChanges inner) A ⇒
            applyTys (sourceChanges inner) B
          ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
            applyTys (targetTailChanges inner) (applyTy χ B′)
        ∶ transportType inner pA ↦ transportType inner pB)
    (M⊑M′ :
      resultCtx inner
        ∣ resultLeftCtx inner
        ∣ resultRightCtx inner
        ∣ resultStore inner ∣ []
        ⊢ᴺ applyTerms (sourceChanges inner) M
          ⊑ applyTerms (targetTailChanges inner) (applyTerm χ M′)
        ⦂ applyTys (sourceChanges inner) A
          ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
        ∶ transportType inner pA) →
  WeakOneStepTransport inner →
  WeakOneStepTransport
    (weak-one-step-·₁-frameᵀ noM noM′ inner L⊑L′ M⊑M′)
weak-one-step-·₁-frame-preserves-transportᵀ
    noM noM′ inner L⊑L′ M⊑M′ transport =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-·₁-frame-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (noM : No• M) (noM′ : No• M′)
    (inner :
      WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ)
    (L⊑L′ : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) A ⇒
          applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
          applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner pA ↦ transportType inner pB)
    (M⊑M′ : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ applyTerms (sourceChanges inner) M
        ⊑ applyTerms (targetTailChanges inner) (applyTerm χ M′)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
      ∶ transportType inner pA) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepTypeCoherence
    (weak-one-step-·₁-frameᵀ noM noM′ inner L⊑L′ M⊑M′)
weak-one-step-·₁-frame-preserves-type-coherenceᵀ
    noM noM′ inner L⊑L′ M⊑M′ coherence =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)
    (transportShapeCoherent coherence)
    (transportRightBodyShapeCoherent coherence)
    (transportLeftReplacementCoherent coherence)
    (transportRightReplacementCoherent coherence)
    (transportPairedReplacementCoherent coherence)
    (transportAllBodyPairedReplacementCoherent coherence)
    (transportSourceNuBodyLeftReplacementCoherent coherence)
    (transportRightBodyRightReplacementCoherent coherence)

weak-one-step-·₁-frame-transport-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  (∀ (inner :
      WeakOneStepResult ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ) →
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) A ⇒
          applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
          applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner pA ↦ transportType inner pB) ×
    WeakOneStepTransport inner) →
  WeakOneStepOutcome ρ L L₁′ (A ⇒ B) (A′ ⇒ B′) χ →
  WeakOneStepOutcome ρ
    (L · M) (L₁′ · applyTerm χ M′) B B′ χ
weak-one-step-·₁-frame-transport-outcomeᵀ
    noM noM′ M⊑M′ frame
    (outcome-related inner carried-transport carried-coherence)
    with frame inner
weak-one-step-·₁-frame-transport-outcomeᵀ
    noM noM′ M⊑M′ frame
    (outcome-related inner carried-transport carried-coherence)
    | L⊑L′ , transport =
  let
    transported-M =
      transportNo•Terms transport noM noM′ M⊑M′
  in
  outcome-related
    (weak-one-step-·₁-frameᵀ
      noM noM′ inner L⊑L′ transported-M)
    (weak-one-step-·₁-frame-preserves-transportᵀ
      noM noM′ inner L⊑L′ transported-M transport)
    (weak-one-step-·₁-frame-preserves-type-coherenceᵀ
      noM noM′ inner L⊑L′ transported-M carried-coherence)
weak-one-step-·₁-frame-transport-outcomeᵀ
    noM noM′ M⊑M′ frame (outcome-source-blame source↠) =
  outcome-source-blame (·₁-blame-tail noM source↠)

weak-one-step-·₁-frame-arrow-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  WeakOneStepArrowOutcome
    {L = L} {L₁′ = L₁′} {χ = χ} {ρ = ρ} pA pB →
  WeakOneStepOutcome ρ
    (L · M) (L₁′ · applyTerm χ M′) B B′ χ
weak-one-step-·₁-frame-arrow-outcomeᵀ
    noM noM′ M⊑M′
    (arrow-outcome-related arrow transport coherence) =
  let
    inner = weakArrowResult arrow
    L⊑L′ = canonicalArrowResults arrow
    transported-M =
      transportNo•Terms transport noM noM′ M⊑M′
  in
  outcome-related
    (weak-one-step-·₁-frameᵀ
      noM noM′ inner L⊑L′ transported-M)
    (weak-one-step-·₁-frame-preserves-transportᵀ
      noM noM′ inner L⊑L′ transported-M transport)
    (weak-one-step-·₁-frame-preserves-type-coherenceᵀ
      noM noM′ inner L⊑L′ transported-M coherence)
weak-one-step-·₁-frame-arrow-outcomeᵀ
    noM noM′ M⊑M′
    (arrow-outcome-source-blame source↠) =
  outcome-source-blame (·₁-blame-tail noM source↠)

runtime-stepping-function-argument-no• :
  ∀ {L L₁ M χ} →
  RuntimeOK (L · M) →
  L —→[ χ ] L₁ →
  No• M
runtime-stepping-function-argument-no•
    (ok-no (no•-· noL noM)) L→ = noM
runtime-stepping-function-argument-no•
    (ok-·₁ okL noM) L→ = noM
runtime-stepping-function-argument-no•
    (ok-·₂ vL noL okM) L→ =
  ⊥-elim (value-no-step vL L→)

runtime-application-left-view :
  ∀ {L L′ L₁′ M M′ χ} →
  RuntimeOK (L · M) →
  RuntimeOK (L′ · M′) →
  L′ —→[ χ ] L₁′ →
  (No• M × No• M′) ⊎
  (Value L × No• L × RuntimeOK M × No• M′)
runtime-application-left-view
    (ok-no (no•-· noL noM)) okL′M′ L′→ =
  inj₁ (noM , runtime-stepping-function-argument-no• okL′M′ L′→)
runtime-application-left-view
    (ok-·₁ okL noM) okL′M′ L′→ =
  inj₁ (noM , runtime-stepping-function-argument-no• okL′M′ L′→)
runtime-application-left-view
    (ok-·₂ vL noL okM) okL′M′ L′→ =
  inj₂
    (vL , noL , okM ,
      runtime-stepping-function-argument-no• okL′M′ L′→)

weak-one-step-·₁-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  WeakOneStepIndexedOutcome
    {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} (pA ↦ pB) →
  WeakOneStepIndexedOutcome
    {M = L · M} {N′ = L₁′ · applyTerm χ M′}
    {χ = χ} {ρ = ρ} pB
weak-one-step-·₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′ indexed
    with weak-indexed-arrow-outcomeᵀ indexed
weak-one-step-·₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′ indexed
    | arrow-outcome-related arrow transport coherence =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed)
      framed-transport framed-coherence)
  where
  inner = weakArrowResult arrow
  L⊑L′ = canonicalArrowResults arrow
  transported-M =
    transportNo•Terms transport noM noM′ M⊑M′
  framed =
    weak-one-step-·₁-frameᵀ
      noM noM′ inner L⊑L′ transported-M
  framed-transport =
    weak-one-step-·₁-frame-preserves-transportᵀ
      noM noM′ inner L⊑L′ transported-M transport
  framed-coherence =
    weak-one-step-·₁-frame-preserves-type-coherenceᵀ
      noM noM′ inner L⊑L′ transported-M coherence
weak-one-step-·₁-indexed-frame-outcomeᵀ
    noM noM′ M⊑M′ indexed
    | arrow-outcome-source-blame source↠ =
  indexed-outcome-source-blame (·₁-blame-tail noM source↠)

weak-one-step-·₁-runtime-boundaryᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RuntimeOK (L · M) →
  RuntimeOK (L′ · M′) →
  L′ —→[ χ ] L₁′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
  WeakOneStepIndexedOutcome
    {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} (pA ↦ pB) →
  WeakOneStepIndexedOutcome
      {M = L · M} {N′ = L₁′ · applyTerm χ M′}
      {χ = χ} {ρ = ρ} pB
    ⊎
  ∃[ result ]
    WeakOneStepTransport (weakIndexedResult result) ×
    WeakOneStepTypeCoherence (weakIndexedResult result) ×
    sourceChanges (weakIndexedResult result) ≡ [] ×
    sourceResult (weakIndexedResult result) ≡ L ×
    Value L × No• L × RuntimeOK M × No• M′
weak-one-step-·₁-runtime-boundaryᵀ
    okLM okL′M′ L′→ M⊑M′ recursive
    with runtime-application-left-view okLM okL′M′ L′→
weak-one-step-·₁-runtime-boundaryᵀ
    okLM okL′M′ L′→ M⊑M′ recursive
    | inj₁ (noM , noM′) =
  inj₁
    (weak-one-step-·₁-indexed-frame-outcomeᵀ
      noM noM′ M⊑M′ recursive)
weak-one-step-·₁-runtime-boundaryᵀ
    okLM okL′M′ L′→ M⊑M′ recursive
    | inj₂ (vL , noL , okM , noM′)
    with source-value-indexed-outcome-relatedᵀ vL recursive
weak-one-step-·₁-runtime-boundaryᵀ
    okLM okL′M′ L′→ M⊑M′ recursive
    | inj₂ (vL , noL , okM , noM′)
    | result , changes-eq , result-eq =
  inj₂
    (result , weakIndexedTransport result ,
      weakIndexedTypeCoherence result , changes-eq , result-eq ,
      vL , noL , okM , noM′)

·₂-blame-tail :
  ∀ {L M χs} →
  Value L →
  No• L →
  M —↠[ χs ] blame →
  L · M —↠[ χs ++ keep ∷ [] ] blame
·₂-blame-tail {χs = χs} vL noL M↠blame =
  ↠-trans (·₂-↠ vL noL M↠blame)
    (↠-step
      (pure-step
        (blame-·₂ (applyTerms-preserves-Value χs vL)))
      ↠-refl)

weak-one-step-·₂-indexed-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ M M₁′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  No• L →
  Value L′ →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  (inner : WeakOneStepIndexedResult
    {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} pA) →
  (transport : WeakOneStepTransport (weakIndexedResult inner)) →
  (coherence :
    WeakOneStepTypeCoherence (weakIndexedResult inner)) →
  WeakOneStepIndexedResult
    {M = L · M} {N′ = applyTerm χ L′ · M₁′}
    {χ = χ} {ρ = ρ} pB
weak-one-step-·₂-indexed-frameᵀ
    {L = L} {L′ = L′} {B = B} {B′ = B′} {χ = χ}
    vL noL vL′ noL′ L⊑L′ inner transport coherence =
  weak-indexed-result framed related framed-transport framed-coherence
  where
  base = weakIndexedResult inner

  function-related =
    weak-result-transport-arrow-termsᵀ
      base transport coherence noL noL′ L⊑L′

  related = ·⊑·ᵀ function-related (canonicalIndexedResults inner)
  framed-transport = weak-step-transport (transportNo•Terms transport)
  framed-coherence =
    weak-step-type-coherence
      (transportArrowCoherent coherence)
      (transportAllCoherent coherence)
      (transportShapeCoherent coherence)
      (transportRightBodyShapeCoherent coherence)
      (transportLeftReplacementCoherent coherence)
      (transportRightReplacementCoherent coherence)
      (transportPairedReplacementCoherent coherence)
      (transportAllBodyPairedReplacementCoherent coherence)
      (transportSourceNuBodyLeftReplacementCoherent coherence)
      (transportRightBodyRightReplacementCoherent coherence)

  framed :
    WeakOneStepResult _ (L · _) (applyTerm χ L′ · _) B B′ χ
  framed =
    record
      { sourceChanges = sourceChanges base
      ; targetTailChanges = targetTailChanges base
      ; sourceResult =
          applyTerms (sourceChanges base) L · sourceResult base
      ; targetResult =
          applyTerms (targetTailChanges base) (applyTerm χ L′) ·
            targetResult base
      ; resultCtx = resultCtx base
      ; resultLeftCtx = resultLeftCtx base
      ; resultRightCtx = resultRightCtx base
      ; sourceCtxResult = sourceCtxResult base
      ; targetCtxResult = targetCtxResult base
      ; resultStore = resultStore base
      ; resultSourceType = applyTys (sourceChanges base) B
      ; resultTargetType =
          applyTys (targetTailChanges base) (applyTy χ B′)
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = transportType base
      ; transportAllBody = transportAllBody base
      ; transportRightBody = transportRightBody base
      ; transportSourceNu = transportSourceNu base
      ; resultType = transportType base _
      ; sourceCatchup = ·₂-↠ vL noL (sourceCatchup base)
      ; targetTail =
          ·₂-↠
            (applyTerm-preserves-Value χ vL′)
            (applyTerm-preserves-No• χ noL′)
            (targetTail base)
      ; sourceStoreResult = sourceStoreResult base
      ; targetStoreResult = targetStoreResult base
      ; relatedResults = related
      }

weak-one-step-·₂-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ M M₁′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  No• L →
  Value L′ →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} pA →
  WeakOneStepIndexedOutcome
    {M = L · M} {N′ = applyTerm χ L′ · M₁′}
    {χ = χ} {ρ = ρ} pB
weak-one-step-·₂-indexed-frame-outcomeᵀ
    vL noL vL′ noL′ L⊑L′
    (indexed-outcome-related inner) =
  indexed-outcome-related
    (weak-one-step-·₂-indexed-frameᵀ
      vL noL vL′ noL′ L⊑L′ inner
      (weakIndexedTransport inner)
      (weakIndexedTypeCoherence inner))
weak-one-step-·₂-indexed-frame-outcomeᵀ
    vL noL vL′ noL′ L⊑L′
    (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (·₂-blame-tail vL noL source↠)

weak-outcome-map-source :
  ∀ {Φ Δᴸ Δᴿ M M₀ N′ A A₀ B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (frame : WeakOneStepResult ρ M N′ A B χ →
    WeakOneStepResult ρ M₀ N′ A₀ B χ) →
  (∀ (result : WeakOneStepResult ρ M N′ A B χ) →
    WeakOneStepTransport result →
    WeakOneStepTransport (frame result)) →
  (∀ (result : WeakOneStepResult ρ M N′ A B χ) →
    WeakOneStepTypeCoherence result →
    WeakOneStepTypeCoherence (frame result)) →
  (∀ {χs} → M —↠[ χs ] blame →
    ∃[ χs′ ] (M₀ —↠[ χs′ ] blame)) →
  WeakOneStepOutcome ρ M N′ A B χ →
  WeakOneStepOutcome ρ M₀ N′ A₀ B χ
weak-outcome-map-source
    frame transport-frame coherence-frame blame-frame
    (outcome-related result transport coherence) =
  outcome-related
    (frame result)
    (transport-frame result transport)
    (coherence-frame result coherence)
weak-outcome-map-source
    frame transport-frame coherence-frame blame-frame
    (outcome-source-blame source↠)
    with blame-frame source↠
weak-outcome-map-source
    frame transport-frame coherence-frame blame-frame
    (outcome-source-blame source↠) | χs′ , source₀↠ =
  outcome-source-blame source₀↠

weak-outcome-map-target-ν :
  ∀ {Φ Δᴸ Δᴿ M N′ A B C D Aν c χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (frame : WeakOneStepResult ρ M N′ A B χ →
    WeakOneStepResult ρ M (ν Aν N′ c) C D χ) →
  (∀ (result : WeakOneStepResult ρ M N′ A B χ) →
    WeakOneStepTransport result →
    WeakOneStepTransport (frame result)) →
  (∀ (result : WeakOneStepResult ρ M N′ A B χ) →
    WeakOneStepTypeCoherence result →
    WeakOneStepTypeCoherence (frame result)) →
  WeakOneStepOutcome ρ M N′ A B χ →
  WeakOneStepOutcome ρ M (ν Aν N′ c) C D χ
weak-outcome-map-target-ν
    frame transport-frame coherence-frame
    (outcome-related result transport coherence) =
  outcome-related
    (frame result)
    (transport-frame result transport)
    (coherence-frame result coherence)
weak-outcome-map-target-ν
    frame transport-frame coherence-frame
    (outcome-source-blame source↠) =
  outcome-source-blame source↠

weak-all-outcome-map-target-ν :
  ∀ {Φ Δᴸ Δᴿ N M₀ N′ C C′ A B Aν c χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (frame : WeakOneStepAllResult
      {N = N} {N₁′ = N′} {C = C} {C′ = C′}
      {χ = χ} {ρ = ρ} q →
    WeakOneStepResult ρ M₀ (ν Aν N′ c) A B χ) →
  (∀ (result : WeakOneStepAllResult
      {N = N} {N₁′ = N′} {C = C} {C′ = C′}
      {χ = χ} {ρ = ρ} q) →
    WeakOneStepTransport (weakResult result) →
    WeakOneStepTransport (frame result)) →
  (∀ (result : WeakOneStepAllResult
      {N = N} {N₁′ = N′} {C = C} {C′ = C′}
      {χ = χ} {ρ = ρ} q) →
    WeakOneStepTypeCoherence (weakResult result) →
    WeakOneStepTypeCoherence (frame result)) →
  (∀ {χs} → N —↠[ χs ] blame →
    ∃[ χs′ ] (M₀ —↠[ χs′ ] blame)) →
  WeakOneStepAllOutcome
    {N = N} {N₁′ = N′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q →
  WeakOneStepOutcome ρ M₀ (ν Aν N′ c) A B χ
weak-all-outcome-map-target-ν
    frame transport-frame coherence-frame blame-frame
    (all-outcome-related result transport coherence) =
  outcome-related
    (frame result)
    (transport-frame result transport)
    (coherence-frame result coherence)
weak-all-outcome-map-target-ν
    frame transport-frame coherence-frame blame-frame
    (all-outcome-source-blame source↠)
    with blame-frame source↠
weak-all-outcome-map-target-ν
    frame transport-frame coherence-frame blame-frame
    (all-outcome-source-blame source↠) | χs′ , source₀↠ =
  outcome-source-blame source₀↠

weak-one-step-all-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N N′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  WeakOneStepAllResult {χ = keep} q
weak-one-step-all-relatedᵀ result =
  weak-all-result (weak-one-step-relatedᵀ result) result

left-catchup-all-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Value N × No• N) ⊎ N ≡ blame →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q
left-catchup-all-relatedᵀ final result =
  left-all-catchup (weak-one-step-all-relatedᵀ result)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

left-catchup-all-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RuntimeOK V →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult {N = V} {V′ = V′} {ρ = ρ} q
left-catchup-all-valueᵀ okV vV V⊑V′ =
  left-catchup-all-relatedᵀ
    (inj₁ (vV , runtime-value-no• okV vV)) V⊑V′

left-catchup-all-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ blame ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult {N = blame} {V′ = V′} {ρ = ρ} q
left-catchup-all-blameᵀ blame⊑V′ =
  left-catchup-all-relatedᵀ (inj₂ refl) blame⊑V′

left-catchup-indexed-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Value N × No• N) ⊎ N ≡ blame →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ A ⊑ B ∶ p) →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ} p
left-catchup-indexed-relatedᵀ final N⊑V′ =
  left-indexed-catchup
    (weak-one-step-indexed-relatedᵀ N⊑V′)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

left-catchup-indexed-prefix-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ A B p}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (final : (Value N × No• N) ⊎ N ≡ blame) →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ A ⊑ B ∶ p) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ N ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ V′ ⦂ B →
  LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-prefix-relatedᵀ
    prefix final N⊑V′ N⊢ V′⊢ =
  left-catchup-indexed-relatedᵀ final
    (allocation-prefixᵀ prefix N⊑V′ N⊢ V′⊢)

left-catchup-indexed-source-all-prefix-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ C B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RuntimeOK V →
  Value V →
  No• V′ →
  (V⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ C ⊑ B ∶ p) →
  LeftCatchupIndexedResult
    {N = V} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-source-all-prefix-valueᵀ
    prefix okV vV noV′ V⊑V′ =
  left-catchup-indexed-prefix-relatedᵀ
    prefix (inj₁ (vV , noV)) V⊑V′ V⊢ V′⊢
  where
  noV = runtime-value-no• okV vV
  V⊢ = term-weaken ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix) noV
    (nu-term-imprecision-source-typing V⊑V′)
  V′⊢ = term-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) noV′
    (nu-term-imprecision-target-typing V⊑V′)

left-catchup-indexed-all-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Value N × No• N) ⊎ N ≡ blame →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-all-relatedᵀ final N⊑V′ =
  left-indexed-all-catchup
    (weak-one-step-indexed-relatedᵀ N⊑V′)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

left-catchup-indexed-all-prefix-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ C C′ q}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (final : (Value N × No• N) ⊎ N ≡ blame) →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ N ⦂ `∀ C →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ V′ ⦂ `∀ C′ →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ⁺} q
left-catchup-indexed-all-prefix-relatedᵀ
    prefix final N⊑V′ N⊢ V′⊢ =
  left-catchup-indexed-all-relatedᵀ final
    (allocation-prefixᵀ prefix N⊑V′ N⊢ V′⊢)

left-catchup-indexed-all-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RuntimeOK V →
  Value V →
  (V⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = V} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-all-valueᵀ okV vV V⊑V′ =
  left-catchup-indexed-all-relatedᵀ
    (inj₁ (vV , runtime-value-no• okV vV)) V⊑V′

left-catchup-indexed-all-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (blame⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ blame ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = blame} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-all-blameᵀ blame⊑V′ =
  left-catchup-indexed-all-relatedᵀ (inj₂ refl) blame⊑V′

weak-one-step-all-outcome-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N N′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  WeakOneStepAllOutcome {χ = keep} q
weak-one-step-all-outcome-relatedᵀ result =
  all-outcome-related (weak-one-step-all-relatedᵀ result)
    (weak-one-step-related-transportᵀ result)
    (weak-one-step-related-type-coherenceᵀ result)

weak-one-step-matched-ν-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N₁′ s s′ μ μ′ χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace : q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ pB) →
  (all : WeakOneStepAllResult
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q) →
  (coherence : WeakOneStepTypeCoherence (weakResult all)) →
  WeakOneStepResult ρ
    (ν A N s)
    (ν (applyTy χ A′) N₁′ (applyCoercionUnderTyBinder χ s′))
    B B′ χ
weak-one-step-matched-ν-frameᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {s = s} {s′ = s′} {χ = χ}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν-frameᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {s = s} {s′ = s′} {χ = χ}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} s′↑
weak-one-step-matched-ν-frameᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {s = s} {s′ = s′} {χ = χ}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult =
        ν (applyTys (sourceChanges inner) A)
          (sourceResult inner)
          (applyCoercionUnderTyBinders (sourceChanges inner) s)
    ; targetResult =
        ν (applyTys (targetTailChanges inner) (applyTy χ A′))
          (targetResult inner)
          (applyCoercionUnderTyBinders (targetTailChanges inner)
            (applyCoercionUnderTyBinder χ s′))
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) B
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; transportSourceNu = transportSourceNu inner
    ; resultType = transportType inner pB
    ; sourceCatchup = ν-↠ (sourceCatchup inner)
    ; targetTail = ν-↠ (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults =
        ν⊑νᵀ
          (⊑-src-wf (transportType inner pA))
          (⊑-tgt-wf (transportType inner pA))
          source-reveal target-reveal
          (transportType inner pA)
          transported-A⇑⊑A′⇑
          liftρ lift-ctx-[] innerAll
          transported-replace
    }
  where
    source-A-eq =
      applyTysUnderTyBinders-⇑ᵗ (sourceChanges inner) A

    target-A′-eq =
      applyTysUnderTyBinders-⇑ᵗ
        (χ ∷ targetTailChanges inner) A′

    transported-A⇑⊑A′⇑ =
      transport-imprecision-endpoints source-A-eq target-A′-eq
        (transportAllBody inner A⇑⊑A′⇑)

    transported-replace =
      replace-paired-transport-endpoints
        refl refl refl refl source-A-eq target-A′-eq
        (transportAllBodyPairedReplacementCoherent
          coherence replace)

    source-reveal =
      subst
        (λ Δ → RevealConversion μᵣ (suc Δ)
          ((zero , ⇑ᵗ (applyTys (sourceChanges inner) A)) ∷
            ⟰ᵗ (leftStoreⁱ (resultStore inner)))
          zero (⇑ᵗ (applyTys (sourceChanges inner) A))
          (applyCoercionUnderTyBinders (sourceChanges inner) s)
          (applyTysUnderTyBinders (sourceChanges inner) C)
          (⇑ᵗ (applyTys (sourceChanges inner) B)))
        (sym (sourceCtxResult inner))
        (subst
          (λ Σ → RevealConversion μᵣ
            (suc (applyTyCtxs (sourceChanges inner) _))
            ((zero , ⇑ᵗ (applyTys (sourceChanges inner) A)) ∷
              ⟰ᵗ Σ)
            zero (⇑ᵗ (applyTys (sourceChanges inner) A))
            (applyCoercionUnderTyBinders (sourceChanges inner) s)
            (applyTysUnderTyBinders (sourceChanges inner) C)
            (⇑ᵗ (applyTys (sourceChanges inner) B)))
          (sym (sourceStoreResult inner)) source↑)

    target-reveal =
      subst
        (λ Δ → RevealConversion μᵗ (suc Δ)
          ((zero , ⇑ᵗ
              (applyTys (targetTailChanges inner) (applyTy χ A′))) ∷
            ⟰ᵗ (rightStoreⁱ (resultStore inner)))
          zero (⇑ᵗ
            (applyTys (targetTailChanges inner) (applyTy χ A′)))
          (applyCoercionUnderTyBinders (targetTailChanges inner)
            (applyCoercionUnderTyBinder χ s′))
          (applyTysUnderTyBinders (targetTailChanges inner)
            (applyTyUnderTyBinder χ C′))
          (⇑ᵗ
            (applyTys (targetTailChanges inner) (applyTy χ B′))))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → RevealConversion μᵗ
            (suc (applyTyCtxs (targetTailChanges inner)
              (applyTyCtx χ _)))
            ((zero , ⇑ᵗ
                (applyTys (targetTailChanges inner) (applyTy χ A′))) ∷
              ⟰ᵗ Σ)
            zero (⇑ᵗ
              (applyTys (targetTailChanges inner) (applyTy χ A′)))
            (applyCoercionUnderTyBinders (targetTailChanges inner)
              (applyCoercionUnderTyBinder χ s′))
            (applyTysUnderTyBinders (targetTailChanges inner)
              (applyTyUnderTyBinder χ C′))
            (⇑ᵗ
              (applyTys (targetTailChanges inner) (applyTy χ B′))))
          (sym (targetStoreResult inner)) target↑)

weak-one-step-matched-ν-frame-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N₁′ s s′ μ μ′ χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace : q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
  ⊑-lift∀ᵢ pB) →
  (all : WeakOneStepAllResult
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q) →
  (coherence : WeakOneStepTypeCoherence (weakResult all)) →
  WeakOneStepTransport (weakResult all) →
  WeakOneStepTransport
    (weak-one-step-matched-ν-frameᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace all coherence)
weak-one-step-matched-ν-frame-preserves-transportᵀ
    {χ = χ}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence transport
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν-frame-preserves-transportᵀ
    {χ = χ}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence transport
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      { χs = sourceChanges inner } s↑
       | apply-reveal-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} s′↑
weak-one-step-matched-ν-frame-preserves-transportᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence transport
    | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N₁′ s s′ μ μ′ χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace : q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB) →
  (all : WeakOneStepAllResult
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q) →
  (coherence : WeakOneStepTypeCoherence (weakResult all)) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-ν-frameᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace all coherence)
weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
    {χ = χ}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
    {χ = χ}
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} s′↑
weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)
    (transportShapeCoherent coherence)
    (transportRightBodyShapeCoherent coherence)
    (transportLeftReplacementCoherent coherence)
    (transportRightReplacementCoherent coherence)
    (transportPairedReplacementCoherent coherence)
    (transportAllBodyPairedReplacementCoherent coherence)
    (transportSourceNuBodyLeftReplacementCoherent coherence)
    (transportRightBodyRightReplacementCoherent coherence)

left-silent-matched-ν-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace : q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB) →
  (all : WeakOneStepAllResult
    {N = N} {N₁′ = V′} {χ = keep} {ρ = ρ} q) →
  WeakOneStepTypeCoherence (weakResult all) →
  LeftSilentInvariant (weakResult all) →
  LeftSilentResult
    {M = ν A N s} {V′ = ν A′ V′ s′}
    {A = B} {B = B′} {ρ = ρ}
left-silent-matched-ν-frameᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    (left-silent-invariant refl refl)
    with lift-store-result (resultStore inner)
left-silent-matched-ν-frameᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    (left-silent-invariant refl refl)
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = keep ∷ []} s′↑
left-silent-matched-ν-frameᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (weak-all-result inner innerAll) coherence
    (left-silent-invariant refl refl)
    | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
  left-silent
    (weak-one-step-matched-ν-frameᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace
      (weak-all-result inner innerAll) coherence)
    (left-silent-invariant refl refl)

weak-one-step-source-ν-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N N₁′ s μ χ occ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  {{safe : NonVar C}} →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace :
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB) →
  (indexed : WeakOneStepIndexedResult
    {M = N} {N′ = N₁′} {χ = χ} {ρ = ρ} (ν safe occ q)) →
  WeakOneStepResult ρ (ν A N s) N₁′ B B′ χ
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s}
    {χ = χ} {occ = occ} {q = q}
    {{safe = safe}} hA s↑ pB replace indexed
    with transportSourceNu (weakIndexedResult indexed) safe occ q
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    {occ = occ} {q = q} {{safe = safe}}
    hA s↑ pB replace indexed
    | source-nu-index safe′ occ′ q′ shape
    with lift-left-store-result (resultStore (weakIndexedResult indexed))
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    {occ = occ} {q = q} {{safe = safe}}
    hA s↑ pB replace indexed
    | source-nu-index safe′ occ′ q′ shape | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges (weakIndexedResult indexed)} s↑
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    {occ = occ} {q = q} {{safe = safe}}
    hA s↑ pB replace indexed
    | source-nu-index safe′ occ′ q′ shape
    | ρ′ , liftρ | μ′ , source↑ =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult =
        ν (applyTys (sourceChanges inner) A)
          (sourceResult inner)
          (applyCoercionUnderTyBinders (sourceChanges inner) s)
    ; targetResult = targetResult inner
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) B
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; transportSourceNu = transportSourceNu inner
    ; resultType = transportType inner pB
    ; sourceCatchup = ν-↠ (sourceCatchup inner)
    ; targetTail = targetTail inner
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults =
        ν⊑ᵀ {{safe′}} final-wf final-shift-wf source-reveal
          liftρ lift-left-ctx-[] shaped transported-replace
    }
  where
    inner = weakIndexedResult indexed

    normalized =
      nu-term-imprecision-transport-typesᵀ
        (applyTys-∀ (sourceChanges inner) C) refl refl
        (canonicalIndexedResults indexed)

    shaped =
      nu-term-imprecision-transport-typesᵀ
        refl refl shape normalized

    source-A-eq =
      applyTysUnderTyBinders-⇑ᵗ (sourceChanges inner) A

    transported-index =
      transportSourceNu inner safe occ q

    transported-source-shape =
      νˢ-injective
        (cong ⌊_⌋
          (trans (sym shape)
            (sourceNuIndexEquality transported-index)))

    transported-replace =
      replace-left-source-shape transported-source-shape
        (replace-left-transport-endpoints refl refl refl source-A-eq
          (transportSourceNuBodyLeftReplacementCoherent
            (weakIndexedTypeCoherence indexed) safe occ replace))

    final-wf =
      subst
        (λ Δ → WfTy Δ (applyTys (sourceChanges inner) A))
        (sym (sourceCtxResult inner))
        (wfTy-applyTys (sourceChanges inner) hA)

    final-shift-wf =
      renameᵗ-preserves-WfTy final-wf TyRenameWf-suc

    source-reveal =
      subst
        (λ Δ → RevealConversion μ′ (suc Δ)
          ((zero , ⇑ᵗ (applyTys (sourceChanges inner) A)) ∷
            ⟰ᵗ (leftStoreⁱ (resultStore inner)))
          zero (⇑ᵗ (applyTys (sourceChanges inner) A))
          (applyCoercionUnderTyBinders (sourceChanges inner) s)
          (applyTysUnderTyBinders (sourceChanges inner) C)
          (⇑ᵗ (applyTys (sourceChanges inner) B)))
        (sym (sourceCtxResult inner))
        (subst
          (λ Σ → RevealConversion μ′
            (suc (applyTyCtxs (sourceChanges inner) _))
            ((zero , ⇑ᵗ (applyTys (sourceChanges inner) A)) ∷
              ⟰ᵗ Σ)
            zero (⇑ᵗ (applyTys (sourceChanges inner) A))
            (applyCoercionUnderTyBinders (sourceChanges inner) s)
            (applyTysUnderTyBinders (sourceChanges inner) C)
            (⇑ᵗ (applyTys (sourceChanges inner) B)))
          (sym (sourceStoreResult inner)) source↑)

weak-one-step-source-ν-frame-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N N₁′ s μ χ occ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  {{safe : NonVar C}} →
  (hA : WfTy Δᴸ A) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace :
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB) →
  (indexed : WeakOneStepIndexedResult
    {M = N} {N′ = N₁′} {χ = χ} {ρ = ρ} (ν safe occ q)) →
  WeakOneStepTransport (weakIndexedResult indexed) →
  WeakOneStepTransport
    (weak-one-step-source-ν-frameᵀ hA s↑ pB replace indexed)
weak-one-step-source-ν-frame-preserves-transportᵀ
    {occ = occ} {q = q} {{safe = safe}}
    hA s↑ pB replace indexed transport
    with transportSourceNu (weakIndexedResult indexed) safe occ q
weak-one-step-source-ν-frame-preserves-transportᵀ
    hA s↑ pB replace indexed transport
    | source-nu-index safe′ occ′ q′ shape
    with lift-left-store-result (resultStore (weakIndexedResult indexed))
weak-one-step-source-ν-frame-preserves-transportᵀ
    hA s↑ pB replace indexed transport
    | source-nu-index safe′ occ′ q′ shape | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges (weakIndexedResult indexed)} s↑
weak-one-step-source-ν-frame-preserves-transportᵀ
    hA s↑ pB replace indexed transport
    | source-nu-index safe′ occ′ q′ shape
    | ρ′ , liftρ | μ′ , source↑ =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-source-ν-frame-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N N₁′ s μ χ occ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  {{safe : NonVar C}} →
  (hA : WfTy Δᴸ A) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace :
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB) →
  (indexed : WeakOneStepIndexedResult
    {M = N} {N′ = N₁′} {χ = χ} {ρ = ρ} (ν safe occ q)) →
  WeakOneStepTypeCoherence (weakIndexedResult indexed) →
  WeakOneStepTypeCoherence
    (weak-one-step-source-ν-frameᵀ hA s↑ pB replace indexed)
weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
    {occ = occ} {q = q} {{safe = safe}}
    hA s↑ pB replace indexed coherence
    with transportSourceNu (weakIndexedResult indexed) safe occ q
weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
    hA s↑ pB replace indexed coherence
    | source-nu-index safe′ occ′ q′ shape
    with lift-left-store-result (resultStore (weakIndexedResult indexed))
weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
    hA s↑ pB replace indexed coherence
    | source-nu-index safe′ occ′ q′ shape | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges (weakIndexedResult indexed)} s↑
weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
    hA s↑ pB replace indexed coherence
    | source-nu-index safe′ occ′ q′ shape
    | ρ′ , liftρ | μ′ , source↑ =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)
    (transportShapeCoherent coherence)
    (transportRightBodyShapeCoherent coherence)
    (transportLeftReplacementCoherent coherence)
    (transportRightReplacementCoherent coherence)
    (transportPairedReplacementCoherent coherence)
    (transportAllBodyPairedReplacementCoherent coherence)
    (transportSourceNuBodyLeftReplacementCoherent coherence)
    (transportRightBodyRightReplacementCoherent coherence)

weak-one-step-matched-ν-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N₁′ s s′ μ μ′ χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace : q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB) →
  WeakOneStepAllOutcome
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q →
  WeakOneStepOutcome ρ
    (ν A N s)
    (ν (applyTy χ A′) N₁′ (applyCoercionUnderTyBinder χ s′))
    B B′ χ
weak-one-step-matched-ν-frame-outcomeᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (all-outcome-related all transport coherence) =
  outcome-related framed framed-transport framed-coherence
  where
  framed = weak-one-step-matched-ν-frameᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace all coherence
  framed-transport =
    weak-one-step-matched-ν-frame-preserves-transportᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace
      all coherence transport
  framed-coherence =
    weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace all coherence
weak-one-step-matched-ν-frame-outcomeᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace
    (all-outcome-source-blame source↠) =
  outcome-source-blame (ν-blame-tail source↠)

weak-one-step-matched-ν-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N₁′ s s′ μ μ′ χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace : q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB) →
  WeakOneStepIndexedOutcome
    {M = N} {N′ = N₁′} {χ = χ} {ρ = ρ} (∀ⁱ q) →
  WeakOneStepIndexedOutcome
    {M = ν A N s}
    {N′ = ν (applyTy χ A′) N₁′
      (applyCoercionUnderTyBinder χ s′)}
    {χ = χ} {ρ = ρ} pB
weak-one-step-matched-ν-indexed-frame-outcomeᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace indexed
    with weak-indexed-all-outcomeᵀ indexed
weak-one-step-matched-ν-indexed-frame-outcomeᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace indexed
    | all-outcome-related all transport coherence =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed)
      framed-transport framed-coherence)
  where
  framed = weak-one-step-matched-ν-frameᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace all coherence
  framed-transport =
    weak-one-step-matched-ν-frame-preserves-transportᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace
      all coherence transport
  framed-coherence =
    weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace all coherence
weak-one-step-matched-ν-indexed-frame-outcomeᵀ
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace indexed
    | all-outcome-source-blame source↠ =
  indexed-outcome-source-blame (ν-blame-tail source↠)

weak-one-step-source-ν-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N N₁′ s μ χ occ}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  {{safe : NonVar C}} →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (replace :
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB) →
  WeakOneStepIndexedOutcome
    {M = N} {N′ = N₁′} {χ = χ} {ρ = ρ} (ν safe occ q) →
  WeakOneStepIndexedOutcome
    {M = ν A N s} {N′ = N₁′} {χ = χ} {ρ = ρ} pB
weak-one-step-source-ν-indexed-frame-outcomeᵀ
    hA s↑ pB replace
    (indexed-outcome-related indexed) =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed)
      framed-transport framed-coherence)
  where
  framed =
    weak-one-step-source-ν-frameᵀ hA s↑ pB replace indexed
  framed-transport =
    weak-one-step-source-ν-frame-preserves-transportᵀ
      hA s↑ pB replace indexed (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
      hA s↑ pB replace indexed (weakIndexedTypeCoherence indexed)
weak-one-step-source-ν-indexed-frame-outcomeᵀ
    hA s↑ pB replace (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (ν-blame-tail source↠)

swap01ᵢ-agrees-swap01ᵗ : ∀ X → swap01ᵢ X ≡ swap01ᵗ X
swap01ᵢ-agrees-swap01ᵗ zero = refl
swap01ᵢ-agrees-swap01ᵗ (suc zero) = refl
swap01ᵢ-agrees-swap01ᵗ (suc (suc X)) = refl

renameᵗ-swap01ᵢ-agrees-swap01ᵗ :
  ∀ A → renameᵗ swap01ᵢ A ≡ renameᵗ swap01ᵗ A
renameᵗ-swap01ᵢ-agrees-swap01ᵗ A =
  rename-cong swap01ᵢ-agrees-swap01ᵗ A

direct-swap-residualᵖ :
  ∀ {Φ Δᴸ Δᴿ D E T} →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ E ⊣ suc (suc Δᴿ) →
  renameᵗ swap01ᵗ E ≈∀ T →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ D ⊑ᵖ T ⊣ suc (suc Δᴿ)
direct-swap-residualᵖ {E = E} D⊑E Eˢ≈T =
  quotientᵖ ≈∀-refl crossed Eˢ≈T
  where
    crossed =
      subst
        (λ T → swapRight∀∀ᵢ _ ∣ _ ⊢ _ ⊑ T ⊣ _)
        (renameᵗ-swap01ᵢ-agrees-swap01ᵗ E)
        (⊑-swapRight01∀∀ᵢ D⊑E)

reverse-swap-residualᵖ :
  ∀ {Φ Δᴸ Δᴿ S D E} →
  S ≈∀ renameᵗ swap01ᵗ D →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ E ⊣ suc (suc Δᴿ) →
  swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ S ⊑ᵖ E ⊣ suc (suc Δᴿ)
reverse-swap-residualᵖ {D = D} S≈Dˢ D⊑E =
  quotientᵖ S≈Dˢ crossed ≈∀-refl
  where
    crossed =
      subst
        (λ T → swapRight∀∀ᵢ _ ∣ _ ⊢ T ⊑ _ ⊣ _)
        (renameᵗ-swap01ᵢ-agrees-swap01ᵗ D)
        (⊑-swapLeft01∀∀ᵢ D⊑E)

direct-swap-residual-outerᵖ :
  ∀ {Φ Δᴸ Δᴿ D E T} →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ E ⊣ suc (suc Δᴿ) →
  renameᵗ swap01ᵗ E ≈∀ T →
  Φ ∣ Δᴸ ⊢ `∀ (`∀ D) ⊑ᵖ `∀ (`∀ T) ⊣ Δᴿ
direct-swap-residual-outerᵖ D⊑E Eˢ≈T =
  quotientᵖ ≈∀-refl (∀ⁱ (∀ⁱ D⊑E))
    (≈∀-double-swap Eˢ≈T)

reverse-swap-residual-outerᵖ :
  ∀ {Φ Δᴸ Δᴿ S D E} →
  S ≈∀ renameᵗ swap01ᵗ D →
  ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ E ⊣ suc (suc Δᴿ) →
  Φ ∣ Δᴸ ⊢ `∀ (`∀ S) ⊑ᵖ `∀ (`∀ E) ⊣ Δᴿ
reverse-swap-residual-outerᵖ S≈Dˢ D⊑E =
  quotientᵖ (≈∀-double-swap-sym S≈Dˢ)
    (∀ⁱ (∀ⁱ D⊑E)) ≈∀-refl
