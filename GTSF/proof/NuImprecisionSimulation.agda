module proof.NuImprecisionSimulation where

-- File Charter:
--   * Develops universal catch-up and generic `β-∀•` simulation lemmas on
--     top of the stable weak-simulation core.
--   * Factors bare runtime-bullet instantiation from reveal and widening
--     conversions for ordinary `ν` and `ν ★`.
--   * Checks `β-Λ•`, `β-∀•`, `β-gen•`, and `β-inst` boundaries.
--   * Connects crossed stores to two `bind` traces in opposite logical order.
--   * Packages both generic-cast constructor orders at `β-∀•`, for all
--     source/target narrowing and widening combinations.
--   * Depends on `NuImprecisionSimulationCore`; completed synchronized and
--     one-sided allocation cases live in `NuImprecisionAllocationSimulation`.

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
  ; widen-weaken
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
open import NuTermImprecision using
  ( StoreImp
  ; StoreImpEntry
  ; StoreCorresponds
  ; correspondence-stored
  ; correspondence-linked
  ; CtxImp
  ; ctx-imp
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
  ; store-matched
  ; store-left
  ; store-right
  ; store-link
  ; crossedStoreⁱ
  ; crossedStoreⁱ-new-old
  ; crossedStoreⁱ-old-new
  )
open import QuotientedTermImprecision
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
open import proof.CastImprecision using
  ( RightCastCtxCompatible
  ; seal★-ext-shift
  ; seal★-gen-shift
  ; widening⇒⊑ᵢ
  ; ⊑-transʳ-castᵢ
  )
open import proof.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; rename-assm²ᵢ
  ; rename-assm²-composeᵢ
  ; rename-assm²-congᵢ
  ; rename-assm²-∀ᵢ
  ; rename-assm²-crossed-left∀∀ᵢ
  ; rename-assm²-crossed-right∀∀ᵢ
  ; rename-assm²-crossed-double∀∀ᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-source-νᵢ
  ; rename-assm²-swapLeft∀∀ᵢ
  ; rename-assm²-swapRight∀∀ᵢ
  ; rename-assm²-target-rightᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-crossed-body-lift∀∀ᵢ
  ; ⊑-crossed-left-body-lift∀∀ᵢ
  ; ⊑-crossed-double-lift∀∀ᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-open∀ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-ν∀-to-∀νᵢ
  ; ⊑-swapLeft01∀∀ᵢ
  ; ⊑-swapRight01∀∀ᵢ
  ; ⊑-target-lift-rightᵢ
  ; swap01ᵢ
  ; swap01ᵢ-after-suc
  )
open import proof.MediationProperties using (wfTy-applyTys)
open import proof.ForallPermutationProperties using
  ( ≈∀-double-swap
  ; ≈∀-double-swap-sym
  ; ⊑→⊑ᵖ
  )
open import proof.NarrowWidenProperties using
  ( StoreDetWf
  ; allocate-all-narrowing
  ; allocate-all-widening
  ; allocate-gen-narrowing
  ; open-all-narrowing
  ; open-all-widening
  )
open import proof.NuTermProperties using
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
open import proof.NuProgress using
  ( AllView
  ; av-Λ
  ; av-∀
  ; av-gen
  ; canonical-∀
  ; runtime-value-no•
  )
open import proof.NuPreservation using
  ( runtime-ν
  ; runtime-⟨⟩
  ; value-no-step
  )
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-inst
  ; applyCoercions-preserves-Inert
  ; applyCoercionUnderTyBinders
  ; applyTerm-preserves-No•
  ; applyTerm-preserves-Value
  ; applyTerms-++
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyStores-++
  ; applyTy-∀
  ; applyTyUnderTyBinder
  ; applyTyCtxs-++
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
  ; applyTys-++
  ; applyTys-★
  ; applyTys-∀
  ; cast-↠
  ; ·₁-↠
  ; ·₂-↠
  ; ν-↠
  ; ↠-trans
  )
open import proof.LeftChangeNarrowingSeparated using
  (applyTys-⇒)
open import proof.CoercionProperties using
  ( ModeIncl-ext
  ; ModeIncl-gen
  ; ModeIncl-inst
  ; ModeRename
  ; open0-ext-suc-cancelᶜ
  )
open import proof.TypePreservation using
  ( applyNarrow-typing
  ; applyWiden-typing
  ; applyWidenInstUnderTyBinder-typing
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
open import proof.NuWideningTransport using
  (apply-widens-typing)
open import proof.StoreProperties using
  (∈-renameStoreᵗ; renameStoreᵗ-incl)
open import proof.TypeProperties using
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
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  ; renameStoreᵗ-compose
  ; renameStoreᵗ-ext-suc-comm
  )

open import proof.NuImprecisionRelStoreEmbeddingDef
open import proof.NuImprecisionSimulationCore
open import proof.NuImprecisionSourcePolymorphicValueBase using
  ( left-polymorphic-value-shapeᵀ
  ; post-allocation-β-∀•-bare
  ; post-allocation-β-gen•-bare
  ; post-allocation-polymorphic-value-step
  )
open import proof.NuImprecisionWorldEmbeddingNoBullet using
  (rel-world-embed-no•ᵀ; rel-world-embed-no•ᵀᵖ)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-composeⁱ)
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionStoreLift using (lift-right-store-result)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionCatchupComposition

------------------------------------------------------------------------
-- Crossed stores realize two allocations in opposite logical orders
------------------------------------------------------------------------

lift-store-rel-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ Ψ ρ ρ′ →
  RelStoreEmbeddingⁱ suc suc ρ ρ′
lift-store-rel-embeddingⁱ lift-store-[] =
  rel-store-embedding-[]
lift-store-rel-embeddingⁱ (lift-store-∷ liftρ) =
  rel-store-embedding-matched refl refl refl refl
    (lift-store-rel-embeddingⁱ liftρ)
lift-store-rel-embeddingⁱ (lift-store-left liftρ) =
  rel-store-embedding-left refl refl
    (lift-store-rel-embeddingⁱ liftρ)
lift-store-rel-embeddingⁱ (lift-store-right liftρ) =
  rel-store-embedding-right refl refl
    (lift-store-rel-embeddingⁱ liftρ)
lift-store-rel-embeddingⁱ (lift-store-link liftρ) =
  rel-store-embedding-link refl refl refl refl
    (lift-store-rel-embeddingⁱ liftρ)

identity-store-rel-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RelStoreEmbeddingⁱ (λ X → X) (λ X → X) ρ ρ
identity-store-rel-embeddingⁱ {ρ = []} =
  rel-store-embedding-[]
identity-store-rel-embeddingⁱ
    {ρ = store-matched α A β B p ∷ ρ} =
  rel-store-embedding-matched refl (sym (renameᵗ-id A))
    refl (sym (renameᵗ-id B)) identity-store-rel-embeddingⁱ
identity-store-rel-embeddingⁱ
    {ρ = store-left α A hA ∷ ρ} =
  rel-store-embedding-left refl (sym (renameᵗ-id A))
    identity-store-rel-embeddingⁱ
identity-store-rel-embeddingⁱ
    {ρ = store-right β B hB ∷ ρ} =
  rel-store-embedding-right refl (sym (renameᵗ-id B))
    identity-store-rel-embeddingⁱ
identity-store-rel-embeddingⁱ
    {ρ = store-link α A β B p ∷ ρ} =
  rel-store-embedding-link refl (sym (renameᵗ-id A))
    refl (sym (renameᵗ-id B)) identity-store-rel-embeddingⁱ

identity-world-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RelWorldEmbeddingⁱ
    (λ X → X) (λ X → X) (λ X → X) (λ X → X)
    rename-assm²-idᵢ (λ X<Δ → X<Δ) (λ X<Δ → X<Δ)
    {ρ = ρ} {ρ′ = ρ} {γ = []} {γ′ = []}
identity-world-embeddingⁱ =
  rel-world-embedding (λ X → refl) (λ X → refl)
    castModeRenamer-id castModeRenamer-id
    identity-store-rel-embeddingⁱ rel-ctx-rename-[]

paired-left-lift-rel-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρᵃ →
  LiftLeftStoreⁱ Ψ ρ ρᵇ →
  RelStoreEmbeddingⁱ (λ X → X) (λ X → X) ρᵃ ρᵇ
paired-left-lift-rel-embeddingⁱ
    lift-left-store-[] lift-left-store-[] =
  rel-store-embedding-[]
paired-left-lift-rel-embeddingⁱ
    (lift-left-store-∷ liftρᵃ) (lift-left-store-∷ liftρᵇ) =
  rel-store-embedding-matched refl (sym (renameᵗ-id _))
    refl (sym (renameᵗ-id _))
    (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)
paired-left-lift-rel-embeddingⁱ
    (lift-left-store-left liftρᵃ)
    (lift-left-store-left liftρᵇ) =
  rel-store-embedding-left refl (sym (renameᵗ-id _))
    (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)
paired-left-lift-rel-embeddingⁱ
    (lift-left-store-right liftρᵃ)
    (lift-left-store-right liftρᵇ) =
  rel-store-embedding-right refl (sym (renameᵗ-id _))
    (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)
paired-left-lift-rel-embeddingⁱ
    (lift-left-store-link liftρᵃ)
    (lift-left-store-link liftρᵇ) =
  rel-store-embedding-link refl (sym (renameᵗ-id _))
    refl (sym (renameᵗ-id _))
    (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)

paired-left-lift-world-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρᵃ →
  LiftLeftStoreⁱ Ψ ρ ρᵇ →
  RelWorldEmbeddingⁱ
    (λ X → X) (λ X → X) (λ X → X) (λ X → X)
    rename-assm²-idᵢ (λ X<Δ → X<Δ) (λ X<Δ → X<Δ)
    {ρ = ρᵃ} {ρ′ = ρᵇ} {γ = []} {γ′ = []}
paired-left-lift-world-embeddingⁱ liftρᵃ liftρᵇ =
  rel-world-embedding (λ X → refl) (λ X → refl)
    castModeRenamer-id castModeRenamer-id
    (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)
    rel-ctx-rename-[]

paired-left-lift-prefix-world-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ A}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp Ψ (suc Δᴸ) Δᴿ}
    {hA : WfTy (suc Δᴸ) A} →
  LiftLeftStoreⁱ Ψ ρ ρᵃ →
  LiftLeftStoreⁱ Ψ ρ ρᵇ →
  RelWorldEmbeddingⁱ
    (λ X → X) (λ X → X) (λ X → X) (λ X → X)
    rename-assm²-idᵢ (λ X<Δ → X<Δ) (λ X<Δ → X<Δ)
    {ρ = store-left zero A hA ∷ ρᵃ}
    {ρ′ = store-left zero A hA ∷ ρᵇ}
    {γ = []} {γ′ = []}
paired-left-lift-prefix-world-embeddingⁱ liftρᵃ liftρᵇ =
  rel-world-embedding (λ X → refl) (λ X → refl)
    castModeRenamer-id castModeRenamer-id
    (rel-store-embedding-left refl (sym (renameᵗ-id _))
      (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ))
    rel-ctx-rename-[]

lift-right-store-rel-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ Ψ ρ ρ′ →
  RelStoreEmbeddingⁱ (λ X → X) suc ρ ρ′
lift-right-store-rel-embeddingⁱ lift-right-store-[] =
  rel-store-embedding-[]
lift-right-store-rel-embeddingⁱ (lift-right-store-∷ liftρ) =
  rel-store-embedding-matched refl (sym (renameᵗ-id _))
    refl refl (lift-right-store-rel-embeddingⁱ liftρ)
lift-right-store-rel-embeddingⁱ (lift-right-store-left liftρ) =
  rel-store-embedding-left refl (sym (renameᵗ-id _))
    (lift-right-store-rel-embeddingⁱ liftρ)
lift-right-store-rel-embeddingⁱ (lift-right-store-right liftρ) =
  rel-store-embedding-right refl refl
    (lift-right-store-rel-embeddingⁱ liftρ)
lift-right-store-rel-embeddingⁱ (lift-right-store-link liftρ) =
  rel-store-embedding-link refl (sym (renameᵗ-id _))
    refl refl (lift-right-store-rel-embeddingⁱ liftρ)

matched-lift-world-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  RelWorldEmbeddingⁱ suc suc predᵗ predᵗ
    rename-assm²-∀ᵢ TyRenameWf-suc TyRenameWf-suc
    {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
matched-lift-world-embeddingⁱ liftρ =
  rel-world-embedding RenameLeftInverse-suc RenameLeftInverse-suc
    castModeRenamer-suc castModeRenamer-suc
    (lift-store-rel-embeddingⁱ liftρ) rel-ctx-rename-[]

right-lift-world-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  RelWorldEmbeddingⁱ (λ X → X) suc (λ X → X) predᵗ
    rename-assm²-target-rightᵢ (λ X<Δ → X<Δ) TyRenameWf-suc
    {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
right-lift-world-embeddingⁱ liftρ =
  rel-world-embedding (λ X → refl) RenameLeftInverse-suc
    castModeRenamer-id castModeRenamer-suc
    (lift-right-store-rel-embeddingⁱ liftρ) rel-ctx-rename-[]

right-lift-under-left-store-rel-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴿ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      (suc Δᴸ) (suc Δᴿ)} →
  LiftRightStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρ ρᴿ →
  RelStoreEmbeddingⁱ (extᵗ (λ X → X)) suc ρ ρᴿ
right-lift-under-left-store-rel-embeddingⁱ
    lift-right-store-[] =
  rel-store-embedding-[]
right-lift-under-left-store-rel-embeddingⁱ
    (lift-right-store-∷ {A = A} liftρ) =
  rel-store-embedding-matched
    (sym (ext-id-pointwise _)) (sym (renameᵗ-ext-id A))
    refl refl (right-lift-under-left-store-rel-embeddingⁱ liftρ)
right-lift-under-left-store-rel-embeddingⁱ
    (lift-right-store-left {A = A} liftρ) =
  rel-store-embedding-left
    (sym (ext-id-pointwise _)) (sym (renameᵗ-ext-id A))
    (right-lift-under-left-store-rel-embeddingⁱ liftρ)
right-lift-under-left-store-rel-embeddingⁱ
    (lift-right-store-right liftρ) =
  rel-store-embedding-right refl refl
    (right-lift-under-left-store-rel-embeddingⁱ liftρ)
right-lift-under-left-store-rel-embeddingⁱ
    (lift-right-store-link {A = A} liftρ) =
  rel-store-embedding-link
    (sym (ext-id-pointwise _)) (sym (renameᵗ-ext-id A))
    refl refl (right-lift-under-left-store-rel-embeddingⁱ liftρ)

right-lift-under-left-world-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴿ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ))
      (suc Δᴸ) (suc Δᴿ)} →
  LiftRightStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (⇑ᴿᵢ Φ)) ρ ρᴿ →
  RelWorldEmbeddingⁱ
    (extᵗ (λ X → X)) suc (extᵗ (λ X → X)) predᵗ
    (rename-assm²-⇑ᴸᵢ rename-assm²-target-rightᵢ)
    (TyRenameWf-ext (λ X<Δ → X<Δ)) TyRenameWf-suc
    {ρ = ρ} {ρ′ = ρᴿ} {γ = []} {γ′ = []}
right-lift-under-left-world-embeddingⁱ liftρ =
  rel-world-embedding
    (RenameLeftInverse-ext (λ X → refl))
    RenameLeftInverse-suc
    (castModeRenamer-ext castModeRenamer-id)
    castModeRenamer-suc
    (right-lift-under-left-store-rel-embeddingⁱ liftρ)
    rel-ctx-rename-[]

crossed-double-world-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RelWorldEmbeddingⁱ
    (λ X → suc (suc X)) (λ X → suc (suc X))
    (λ X → predᵗ (predᵗ X)) (λ X → predᵗ (predᵗ X))
    rename-assm²-crossed-double∀∀ᵢ
    (λ X<Δ → s<s (s<s X<Δ)) (λ X<Δ → s<s (s<s X<Δ))
    {ρ = ρ₀} {ρ′ = ρ₂} {γ = []} {γ′ = []}
crossed-double-world-embeddingⁱ liftρ₁ liftρ₂ =
  rel-world-embedding
    (renameLeftInverse-compose
      {τ = suc} {υ = suc} {ψ = predᵗ} {ξ = predᵗ}
      RenameLeftInverse-suc RenameLeftInverse-suc)
    (renameLeftInverse-compose
      {τ = suc} {υ = suc} {ψ = predᵗ} {ξ = predᵗ}
      RenameLeftInverse-suc RenameLeftInverse-suc)
    (castModeRenamer-compose
      {τ = suc} {σ = suc} castModeRenamer-suc castModeRenamer-suc)
    (castModeRenamer-compose
      {τ = suc} {σ = suc} castModeRenamer-suc castModeRenamer-suc)
    (rel-store-embedding-composeⁱ
      {τ = suc} {σ = suc} {υ = suc} {ω = suc}
      (lift-store-rel-embeddingⁱ liftρ₁)
      (lift-store-rel-embeddingⁱ liftρ₂))
    rel-ctx-rename-[]

leftStoreⁱ-crossed-two-binds :
  ∀ {Φ Δᴸ Δᴿ Aold Anew Bold Bnew}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))}
    {hAnew : WfTy (suc (suc Δᴸ)) (⇑ᵗ Anew)}
    {hAold : WfTy (suc (suc Δᴸ)) (⇑ᵗ (⇑ᵗ Aold))}
    {hBnew : WfTy (suc (suc Δᴿ)) (⇑ᵗ Bnew)}
    {hBold : WfTy (suc (suc Δᴿ)) (⇑ᵗ (⇑ᵗ Bold))}
    {pnew-old : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
      ⊢ ⇑ᵗ Anew ⊑ ⇑ᵗ (⇑ᵗ Bold) ⊣ suc (suc Δᴿ)}
    {pold-new : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
      ⊢ ⇑ᵗ (⇑ᵗ Aold) ⊑ ⇑ᵗ Bnew ⊣ suc (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  leftStoreⁱ
      (crossedStoreⁱ hAnew hAold hBnew hBold
        pnew-old pold-new ρ₂)
    ≡ applyStores (bind Aold ∷ bind Anew ∷ []) (leftStoreⁱ ρ₀)
leftStoreⁱ-crossed-two-binds liftρ₁ liftρ₂
    rewrite leftStoreⁱ-lift liftρ₂
      | leftStoreⁱ-lift liftρ₁ =
  refl

rightStoreⁱ-crossed-two-binds :
  ∀ {Φ Δᴸ Δᴿ Aold Anew Bold Bnew}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))}
    {hAnew : WfTy (suc (suc Δᴸ)) (⇑ᵗ Anew)}
    {hAold : WfTy (suc (suc Δᴸ)) (⇑ᵗ (⇑ᵗ Aold))}
    {hBnew : WfTy (suc (suc Δᴿ)) (⇑ᵗ Bnew)}
    {hBold : WfTy (suc (suc Δᴿ)) (⇑ᵗ (⇑ᵗ Bold))}
    {pnew-old : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
      ⊢ ⇑ᵗ Anew ⊑ ⇑ᵗ (⇑ᵗ Bold) ⊣ suc (suc Δᴿ)}
    {pold-new : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
      ⊢ ⇑ᵗ (⇑ᵗ Aold) ⊑ ⇑ᵗ Bnew ⊣ suc (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  rightStoreⁱ
      (crossedStoreⁱ hAnew hAold hBnew hBold
        pnew-old pold-new ρ₂)
    ≡ applyStores (bind Bold ∷ bind Bnew ∷ []) (rightStoreⁱ ρ₀)
rightStoreⁱ-crossed-two-binds liftρ₁ liftρ₂
    rewrite rightStoreⁱ-lift liftρ₂
      | rightStoreⁱ-lift liftρ₁ =
  refl

rightStoreⁱ-crossed-body :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  renameStoreᵗ (extᵗ suc) (rightStoreⁱ ρ₁) ≡ rightStoreⁱ ρ₂
rightStoreⁱ-crossed-body {ρ₀ = ρ₀} {ρ₁ = ρ₁} liftρ₁ liftρ₂ =
  trans
    (cong (renameStoreᵗ (extᵗ suc)) (rightStoreⁱ-lift liftρ₁))
    (trans
      (renameStoreᵗ-ext-suc-comm suc (rightStoreⁱ ρ₀))
      (trans
        (cong ⟰ᵗ (sym (rightStoreⁱ-lift liftρ₁)))
        (sym (rightStoreⁱ-lift liftρ₂))))

leftStoreⁱ-crossed-body :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  renameStoreᵗ (extᵗ suc) (leftStoreⁱ ρ₁) ≡ leftStoreⁱ ρ₂
leftStoreⁱ-crossed-body {ρ₀ = ρ₀} {ρ₁ = ρ₁} liftρ₁ liftρ₂ =
  trans
    (cong (renameStoreᵗ (extᵗ suc)) (leftStoreⁱ-lift liftρ₁))
    (trans
      (renameStoreᵗ-ext-suc-comm suc (leftStoreⁱ ρ₀))
      (trans
        (cong ⟰ᵗ (sym (leftStoreⁱ-lift liftρ₁)))
        (sym (leftStoreⁱ-lift liftρ₂))))

crossed-right-store-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  StoreProjectionEmbeddingⁱ suc (extᵗ suc) ρ₁ ρ₂
crossed-right-store-embeddingⁱ liftρ₁ liftρ₂ =
  store-projection-embedding
    (store-eq-inclusion (leftStoreⁱ-lift liftρ₂))
    (store-eq-inclusion
      (sym (rightStoreⁱ-crossed-body liftρ₁ liftρ₂)))

crossed-left-store-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  StoreProjectionEmbeddingⁱ (extᵗ suc) suc ρ₁ ρ₂
crossed-left-store-embeddingⁱ liftρ₁ liftρ₂ =
  store-projection-embedding
    (store-eq-inclusion
      (sym (leftStoreⁱ-crossed-body liftρ₁ liftρ₂)))
    (store-eq-inclusion (rightStoreⁱ-lift liftρ₂))

crossed-right-rel-store-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RelStoreEmbeddingⁱ suc (extᵗ suc) ρ₁ ρ₂
crossed-right-rel-store-embeddingⁱ
    lift-store-[] lift-store-[] =
  rel-store-embedding-[]
crossed-right-rel-store-embeddingⁱ
    (lift-store-∷ {B = B} liftρ₁) (lift-store-∷ liftρ₂) =
  rel-store-embedding-matched refl refl refl
    (sym (renameᵗ-ext-suc-comm suc B))
    (crossed-right-rel-store-embeddingⁱ liftρ₁ liftρ₂)
crossed-right-rel-store-embeddingⁱ
    (lift-store-left liftρ₁) (lift-store-left liftρ₂) =
  rel-store-embedding-left refl refl
    (crossed-right-rel-store-embeddingⁱ liftρ₁ liftρ₂)
crossed-right-rel-store-embeddingⁱ
    (lift-store-right {B = B} liftρ₁)
    (lift-store-right liftρ₂) =
  rel-store-embedding-right refl
    (sym (renameᵗ-ext-suc-comm suc B))
    (crossed-right-rel-store-embeddingⁱ liftρ₁ liftρ₂)
crossed-right-rel-store-embeddingⁱ
    (lift-store-link {B = B} liftρ₁)
    (lift-store-link liftρ₂) =
  rel-store-embedding-link refl refl refl
    (sym (renameᵗ-ext-suc-comm suc B))
    (crossed-right-rel-store-embeddingⁱ liftρ₁ liftρ₂)

crossed-left-rel-store-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RelStoreEmbeddingⁱ (extᵗ suc) suc ρ₁ ρ₂
crossed-left-rel-store-embeddingⁱ
    lift-store-[] lift-store-[] =
  rel-store-embedding-[]
crossed-left-rel-store-embeddingⁱ
    (lift-store-∷ {A = A} liftρ₁) (lift-store-∷ liftρ₂) =
  rel-store-embedding-matched refl
    (sym (renameᵗ-ext-suc-comm suc A)) refl refl
    (crossed-left-rel-store-embeddingⁱ liftρ₁ liftρ₂)
crossed-left-rel-store-embeddingⁱ
    (lift-store-left {A = A} liftρ₁)
    (lift-store-left liftρ₂) =
  rel-store-embedding-left refl
    (sym (renameᵗ-ext-suc-comm suc A))
    (crossed-left-rel-store-embeddingⁱ liftρ₁ liftρ₂)
crossed-left-rel-store-embeddingⁱ
    (lift-store-right liftρ₁) (lift-store-right liftρ₂) =
  rel-store-embedding-right refl refl
    (crossed-left-rel-store-embeddingⁱ liftρ₁ liftρ₂)
crossed-left-rel-store-embeddingⁱ
    (lift-store-link {A = A} liftρ₁)
    (lift-store-link liftρ₂) =
  rel-store-embedding-link refl
    (sym (renameᵗ-ext-suc-comm suc A)) refl refl
    (crossed-left-rel-store-embeddingⁱ liftρ₁ liftρ₂)

crossed-right-world-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RelWorldEmbeddingⁱ suc (extᵗ suc) predᵗ predᵗ
    rename-assm²-crossed-right∀∀ᵢ
    TyRenameWf-suc (TyRenameWf-ext TyRenameWf-suc)
    {ρ = ρ₁} {ρ′ = ρ₂} {γ = []} {γ′ = []}
crossed-right-world-embeddingⁱ liftρ₁ liftρ₂ =
  rel-world-embedding
    RenameLeftInverse-suc RenameLeftInverse-ext-suc-pred
    castModeRenamer-suc (castModeRenamer-ext castModeRenamer-suc)
    (crossed-right-rel-store-embeddingⁱ liftρ₁ liftρ₂)
    rel-ctx-rename-[]

crossed-left-world-embeddingⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RelWorldEmbeddingⁱ (extᵗ suc) suc predᵗ predᵗ
    rename-assm²-crossed-left∀∀ᵢ
    (TyRenameWf-ext TyRenameWf-suc) TyRenameWf-suc
    {ρ = ρ₁} {ρ′ = ρ₂} {γ = []} {γ′ = []}
crossed-left-world-embeddingⁱ liftρ₁ liftρ₂ =
  rel-world-embedding
    RenameLeftInverse-ext-suc-pred RenameLeftInverse-suc
    (castModeRenamer-ext castModeRenamer-suc) castModeRenamer-suc
    (crossed-left-rel-store-embeddingⁱ liftρ₁ liftρ₂)
    rel-ctx-rename-[]

crossed-right-then-permutation-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation (suc (suc Δᴸ)) Θᴸ}
    {πᴿ : TyPermutation (suc (suc Δᴿ)) Θᴿ}
    {assm : ∀ {a} → a ∈ swapRight∀∀ᵢ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))}
    {ρ₃ : StoreImp Ψ Θᴸ Θᴿ} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ₂} {ρ′ = ρ₃} {γ = []} {γ′ = []} →
  RelWorldEmbeddingⁱ
    (λ X → forward πᴸ (suc X))
    (λ X → forward πᴿ (extᵗ suc X))
    (λ X → predᵗ (backward πᴸ X))
    (λ X → predᵗ (backward πᴿ X))
    (rename-assm²-membership-composeᵢ
      rename-assm²-crossed-right∀∀ᵢ assm)
    (TyRenameWf-compose TyRenameWf-suc (forward-wf πᴸ))
    (TyRenameWf-compose
      (TyRenameWf-ext TyRenameWf-suc) (forward-wf πᴿ))
    {ρ = ρ₁} {ρ′ = ρ₃} {γ = []} {γ′ = []}
crossed-right-then-permutation-embeddingⁱ liftρ₁ liftρ₂ perm =
  rel-world-embedding-[]-composeⁱ
    (crossed-right-world-embeddingⁱ liftρ₁ liftρ₂)
    (rel-world-permutation-embeddingⁱ perm)

crossed-left-then-permutation-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation (suc (suc Δᴸ)) Θᴸ}
    {πᴿ : TyPermutation (suc (suc Δᴿ)) Θᴿ}
    {assm : ∀ {a} → a ∈ swapRight∀∀ᵢ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))}
    {ρ₃ : StoreImp Ψ Θᴸ Θᴿ} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ₂} {ρ′ = ρ₃} {γ = []} {γ′ = []} →
  RelWorldEmbeddingⁱ
    (λ X → forward πᴸ (extᵗ suc X))
    (λ X → forward πᴿ (suc X))
    (λ X → predᵗ (backward πᴸ X))
    (λ X → predᵗ (backward πᴿ X))
    (rename-assm²-membership-composeᵢ
      rename-assm²-crossed-left∀∀ᵢ assm)
    (TyRenameWf-compose
      (TyRenameWf-ext TyRenameWf-suc) (forward-wf πᴸ))
    (TyRenameWf-compose TyRenameWf-suc (forward-wf πᴿ))
    {ρ = ρ₁} {ρ′ = ρ₃} {γ = []} {γ′ = []}
crossed-left-then-permutation-embeddingⁱ liftρ₁ liftρ₂ perm =
  rel-world-embedding-[]-composeⁱ
    (crossed-left-world-embeddingⁱ liftρ₁ liftρ₂)
    (rel-world-permutation-embeddingⁱ perm)

identity-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ A B L L′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• L →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ ⊑-rename-idᵢ p
identity-bodyᵀ {A = A} {B = B} {L = L} {L′ = L′}
    noL noL′ L⊑L′ =
  nu-term-imprecision-transport-termsᵀ
    (renameᵗᵐ-id L) (renameᵗᵐ-id L′)
    (nu-term-imprecision-transport-typesᵀ
      (renameᵗ-id A) (renameᵗ-id B) refl
      (rel-world-embed-no•ᵀ
        identity-world-embeddingⁱ L⊑L′ noL noL′))

rel-world-permute-no•ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ A B} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  No• M → No• M′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) A ⊑ renameᵗ (forward πᴿ) B
    ∶ ⊑-renameᵗ²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) p
rel-world-permute-no•ᵀ perm M⊑M′ noM noM′ =
  rel-world-embed-no•ᵀ
    (rel-world-permutation-embeddingⁱ perm) M⊑M′ noM noM′

rel-world-permute-no•ᵀᵖ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    {πᴸ : TyPermutation Δᴸ Θᴸ}
    {πᴿ : TyPermutation Δᴿ Θᴿ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ (forward πᴸ) (forward πᴿ) a ∈ Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ D D′} {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (perm : RelWorldPermutationⁱ πᴸ πᴿ assm
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
  No• M → No• M′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ (forward πᴸ) M
      ⊑ renameᵗᵐ (forward πᴿ) M′
    ⦂ renameᵗ (forward πᴸ) D ⊑ᵖ renameᵗ (forward πᴿ) D′
    ∶ ⊑ᵖ-rename²ᵢ assm (forward-wf πᴸ) (forward-wf πᴿ) q
rel-world-permute-no•ᵀᵖ perm M⊑M′ noM noM′ =
  rel-world-embed-no•ᵀᵖ
    (rel-world-permutation-embeddingⁱ perm) M⊑M′ noM noM′

∀gen-body-mode≤gen :
  ModeIncl
    (genᵈ (extᵈ (genᵈ tag-or-idᵈ)))
    (genᵈ tag-or-idᵈ)
∀gen-body-mode≤gen zero = refl
∀gen-body-mode≤gen (suc zero) = refl
∀gen-body-mode≤gen (suc (suc zero)) = refl
∀gen-body-mode≤gen (suc (suc (suc X))) = refl

gen∀-body-mode≤gen :
  ModeIncl
    (extᵈ (genᵈ (genᵈ tag-or-idᵈ)))
    (genᵈ tag-or-idᵈ)
gen∀-body-mode≤gen zero = refl
gen∀-body-mode≤gen (suc zero) = refl
gen∀-body-mode≤gen (suc (suc zero)) = refl
gen∀-body-mode≤gen (suc (suc (suc X))) = refl

∀gen-narrowing-body :
  ∀ {Δ Σ A D d} →
  genᵈ tag-or-idᵈ ∣ Δ ∣ Σ
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D) →
  genᵈ tag-or-idᵈ ∣ suc (suc Δ) ∣ ⟰ᵗ (⟰ᵗ Σ)
    ⊢ d ∶ ⇑ᵗ A ⊒ D
∀gen-narrowing-body
    (C.cast-all (C.cast-gen hA occ d⊢) ,
      NW.cross (NW.`∀ (NW.gen dⁿ))) =
  narrow-mode-relax ∀gen-body-mode≤gen (d⊢ , dⁿ)

gen∀-narrowing-body :
  ∀ {Δ Σ B D′ d′} →
  genᵈ tag-or-idᵈ ∣ Δ ∣ Σ
    ⊢ gen (`∀ B) (`∀ d′) ∶ `∀ B ⊒ `∀ (`∀ D′) →
  genᵈ tag-or-idᵈ ∣ suc (suc Δ) ∣ ⟰ᵗ (⟰ᵗ Σ)
    ⊢ d′ ∶ renameᵗ (extᵗ suc) B ⊒ D′
gen∀-narrowing-body
    (C.cast-gen hB occ (C.cast-all d′⊢) ,
      NW.gen (NW.cross (NW.`∀ d′ⁿ))) =
  narrow-mode-relax gen∀-body-mode≤gen (d′⊢ , d′ⁿ)

inst∀-widening-body :
  ∀ {Δ Σ D E u} →
  id-onlyᵈ ∣ Δ ∣ Σ
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E →
  extᵈ (instᵈ tag-or-idᵈ) ∣ suc (suc Δ) ∣
    ⟰ᵗ ((zero , ★) ∷ ⟰ᵗ Σ)
    ⊢ u ∶ D ⊑ renameᵗ (extᵗ suc) E
inst∀-widening-body
    (C.cast-inst hE occ (C.cast-all u⊢) ,
      NW.inst (NW.cross (NW.`∀ uʷ))) =
  widen-mode-relax
    (ModeIncl-ext (ModeIncl-inst id-only≤tag-or-idᵈ))
    (u⊢ , uʷ)

∀inst-widening-body :
  ∀ {Δ Σ D′ E′ u′} →
  id-onlyᵈ ∣ Δ ∣ Σ
    ⊢ `∀ (inst E′ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′ →
  instᵈ (extᵈ tag-or-idᵈ) ∣ suc (suc Δ) ∣
    (zero , ★) ∷ ⟰ᵗ (⟰ᵗ Σ)
    ⊢ u′ ∶ D′ ⊑ ⇑ᵗ E′
∀inst-widening-body
    (C.cast-all (C.cast-inst hE′ occ u′⊢) ,
      NW.cross (NW.`∀ (NW.inst u′ʷ))) =
  widen-mode-relax
    (ModeIncl-inst (ModeIncl-ext id-only≤tag-or-idᵈ))
    (u′⊢ , u′ʷ)

leftStoreⁱ-double-lift :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  ⟰ᵗ (⟰ᵗ (leftStoreⁱ ρ₀)) ≡ leftStoreⁱ ρ₂
leftStoreⁱ-double-lift liftρ₁ liftρ₂ =
  trans
    (cong ⟰ᵗ (sym (leftStoreⁱ-lift liftρ₁)))
    (sym (leftStoreⁱ-lift liftρ₂))

rightStoreⁱ-double-lift :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  ⟰ᵗ (⟰ᵗ (rightStoreⁱ ρ₀)) ≡ rightStoreⁱ ρ₂
rightStoreⁱ-double-lift liftρ₁ liftρ₂ =
  trans
    (cong ⟰ᵗ (sym (rightStoreⁱ-lift liftρ₁)))
    (sym (rightStoreⁱ-lift liftρ₂))

crossed-lift-store :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  ∃[ ρ₂ ] LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂
crossed-lift-store lift-store-[] =
  [] , lift-store-[]
crossed-lift-store (lift-store-∷ {p = p} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store (lift-store-∷ {p = p} liftρ)
    | ρ₂ , liftρ₂ =
  _ , lift-store-∷
    {p′ = ⊑-crossed-double-lift∀∀ᵢ p}
    liftρ₂
crossed-lift-store (lift-store-left {hA′ = hA′} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store (lift-store-left {hA′ = hA′} liftρ)
    | ρ₂ , liftρ₂ =
  _ , lift-store-left
    {hA′ = renameᵗ-preserves-WfTy hA′ TyRenameWf-suc}
    liftρ₂
crossed-lift-store (lift-store-right {hB′ = hB′} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store (lift-store-right {hB′ = hB′} liftρ)
    | ρ₂ , liftρ₂ =
  _ , lift-store-right
    {hB′ = renameᵗ-preserves-WfTy hB′ TyRenameWf-suc}
    liftρ₂
crossed-lift-store (lift-store-link {p = p} liftρ)
    with crossed-lift-store liftρ
crossed-lift-store (lift-store-link {p = p} liftρ)
    | ρ₂ , liftρ₂ =
  _ , lift-store-link
    {p′ = ⊑-crossed-double-lift∀∀ᵢ p}
    liftρ₂

∀gen-crossed-narrowing-body :
  ∀ {Φ Δᴸ Δᴿ Aobs A D d}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D) →
  genᵈ tag-or-idᵈ ∣ suc (suc Δᴸ) ∣
    (zero , Aobs) ∷ (suc zero , ★) ∷ leftStoreⁱ ρ₂
    ⊢ d ∶ ⇑ᵗ A ⊒ D
∀gen-crossed-narrowing-body liftρ₁ liftρ₂ d⊒ =
  narrow-weaken ≤-refl (λ x∈ → there (there x∈))
    (subst
      (λ Σ → genᵈ tag-or-idᵈ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (leftStoreⁱ-double-lift liftρ₁ liftρ₂)
      (∀gen-narrowing-body d⊒))

gen∀-crossed-narrowing-body :
  ∀ {Φ Δᴸ Δᴿ Bobs B D′ d′}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ gen (`∀ B) (`∀ d′) ∶ `∀ B ⊒ `∀ (`∀ D′) →
  genᵈ tag-or-idᵈ ∣ suc (suc Δᴿ) ∣
    (zero , ★) ∷ (suc zero , Bobs) ∷ rightStoreⁱ ρ₂
    ⊢ d′ ∶ renameᵗ (extᵗ suc) B ⊒ D′
gen∀-crossed-narrowing-body liftρ₁ liftρ₂ d′⊒ =
  narrow-weaken ≤-refl (λ x∈ → there (there x∈))
    (subst
      (λ Σ → genᵈ tag-or-idᵈ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (rightStoreⁱ-double-lift liftρ₁ liftρ₂)
      (gen∀-narrowing-body d′⊒))

inst∀-crossed-widening-body :
  ∀ {Φ Δᴸ Δᴿ Aobs D E u}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E →
  extᵈ (instᵈ tag-or-idᵈ) ∣ suc (suc Δᴸ) ∣
    (zero , Aobs) ∷ (suc zero , ★) ∷ leftStoreⁱ ρ₂
    ⊢ u ∶ D ⊑ renameᵗ (extᵗ suc) E
inst∀-crossed-widening-body liftρ₁ liftρ₂ u⊑ =
  widen-weaken ≤-refl StoreIncl-drop
    (subst
      (λ Σ → extᵈ (instᵈ tag-or-idᵈ) ∣ _ ∣
        (suc zero , ★) ∷ Σ ⊢ _ ∶ _ ⊑ _)
      (leftStoreⁱ-double-lift liftρ₁ liftρ₂)
      (inst∀-widening-body u⊑))

∀inst-crossed-widening-body :
  ∀ {Φ Δᴸ Δᴿ Bobs D′ E′ u′}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (inst E′ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′ →
  instᵈ (extᵈ tag-or-idᵈ) ∣ suc (suc Δᴿ) ∣
    (zero , ★) ∷ (suc zero , Bobs) ∷ rightStoreⁱ ρ₂
    ⊢ u′ ∶ D′ ⊑ ⇑ᵗ E′
∀inst-crossed-widening-body liftρ₁ liftρ₂ u′⊑ =
  widen-weaken ≤-refl store-incl-insert-second
    (subst
      (λ Σ → instᵈ (extᵈ tag-or-idᵈ) ∣ _ ∣
        (zero , ★) ∷ Σ ⊢ _ ∶ _ ⊑ _)
      (rightStoreⁱ-double-lift liftρ₁ liftρ₂)
      (∀inst-widening-body u′⊑))

gen∀-crossed-source-narrowing-body :
  ∀ {Φ Δᴸ Δᴿ Aobs A D d}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ gen (`∀ A) (`∀ d) ∶ `∀ A ⊒ `∀ (`∀ D) →
  genᵈ tag-or-idᵈ ∣ suc (suc Δᴸ) ∣
    (zero , ★) ∷ (suc zero , Aobs) ∷ leftStoreⁱ ρ₂
    ⊢ d ∶ renameᵗ (extᵗ suc) A ⊒ D
gen∀-crossed-source-narrowing-body liftρ₁ liftρ₂ d⊒ =
  narrow-weaken ≤-refl (λ x∈ → there (there x∈))
    (subst
      (λ Σ → genᵈ tag-or-idᵈ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (leftStoreⁱ-double-lift liftρ₁ liftρ₂)
      (gen∀-narrowing-body d⊒))

∀gen-crossed-target-narrowing-body :
  ∀ {Φ Δᴸ Δᴿ Bobs B D′ d′}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (gen B d′) ∶ `∀ B ⊒ `∀ (`∀ D′) →
  genᵈ tag-or-idᵈ ∣ suc (suc Δᴿ) ∣
    (zero , Bobs) ∷ (suc zero , ★) ∷ rightStoreⁱ ρ₂
    ⊢ d′ ∶ ⇑ᵗ B ⊒ D′
∀gen-crossed-target-narrowing-body liftρ₁ liftρ₂ d′⊒ =
  narrow-weaken ≤-refl (λ x∈ → there (there x∈))
    (subst
      (λ Σ → genᵈ tag-or-idᵈ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (rightStoreⁱ-double-lift liftρ₁ liftρ₂)
      (∀gen-narrowing-body d′⊒))

∀inst-crossed-source-widening-body :
  ∀ {Φ Δᴸ Δᴿ Aobs D E u}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (inst E u) ∶ `∀ (`∀ D) ⊑ `∀ E →
  instᵈ (extᵈ tag-or-idᵈ) ∣ suc (suc Δᴸ) ∣
    (zero , ★) ∷ (suc zero , Aobs) ∷ leftStoreⁱ ρ₂
    ⊢ u ∶ D ⊑ ⇑ᵗ E
∀inst-crossed-source-widening-body liftρ₁ liftρ₂ u⊑ =
  widen-weaken ≤-refl store-incl-insert-second
    (subst
      (λ Σ → instᵈ (extᵈ tag-or-idᵈ) ∣ _ ∣
        (zero , ★) ∷ Σ ⊢ _ ∶ _ ⊑ _)
      (leftStoreⁱ-double-lift liftρ₁ liftρ₂)
      (∀inst-widening-body u⊑))

inst∀-crossed-target-widening-body :
  ∀ {Φ Δᴸ Δᴿ Bobs D′ E′ u′}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (`∀ E′) (`∀ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′ →
  extᵈ (instᵈ tag-or-idᵈ) ∣ suc (suc Δᴿ) ∣
    (zero , Bobs) ∷ (suc zero , ★) ∷ rightStoreⁱ ρ₂
    ⊢ u′ ∶ D′ ⊑ renameᵗ (extᵗ suc) E′
inst∀-crossed-target-widening-body liftρ₁ liftρ₂ u′⊑ =
  widen-weaken ≤-refl StoreIncl-drop
    (subst
      (λ Σ → extᵈ (instᵈ tag-or-idᵈ) ∣ _ ∣
        (suc zero , ★) ∷ Σ ⊢ _ ∶ _ ⊑ _)
      (rightStoreⁱ-double-lift liftρ₁ liftρ₂)
      (inst∀-widening-body u′⊑))

seal★-ext-inst-tag-or-id :
  ∀ {Σ A} →
  SealModeStore★ (extᵈ (instᵈ tag-or-idᵈ))
    ((zero , A) ∷ (suc zero , ★) ∷ Σ)
seal★-ext-inst-tag-or-id zero ()
seal★-ext-inst-tag-or-id (suc zero) refl =
  there (here refl)
seal★-ext-inst-tag-or-id (suc (suc X)) ()

seal★-inst-ext-tag-or-id :
  ∀ {Σ B} →
  SealModeStore★ (instᵈ (extᵈ tag-or-idᵈ))
    ((zero , ★) ∷ (suc zero , B) ∷ Σ)
seal★-inst-ext-tag-or-id zero refl = here refl
seal★-inst-ext-tag-or-id (suc zero) ()
seal★-inst-ext-tag-or-id (suc (suc X)) ()

left-swap-reveal-store :
  ∀ {Φ Δᴸ Δᴿ Aobs}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  renameStoreᵗ (extᵗ suc)
      ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    ≡ (zero , ⇑ᵗ (⇑ᵗ Aobs)) ∷ leftStoreⁱ ρ₂
left-swap-reveal-store {Aobs = Aobs} {ρ₀ = ρ₀} liftρ₁ liftρ₂ =
  cong₂ _∷_
    (cong (λ C → zero , C) (renameᵗ-ext-suc-comm suc Aobs))
    (trans
      (renameStoreᵗ-ext-suc-comm suc (leftStoreⁱ ρ₀))
      (trans
        (cong ⟰ᵗ (sym (leftStoreⁱ-lift liftρ₁)))
        (sym (leftStoreⁱ-lift liftρ₂))))

matched-lift-prefix-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ A B L L′ p}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ ρ⁺ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  StoreImpPrefix ρ₁ ρ⁺ →
  No• L → No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ⁺ ∣ []
    ⊢ᴺ ⇑ᵗᵐ L ⊑ ⇑ᵗᵐ L′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B
      ∶ ⊑-lift∀ᵢ p
matched-lift-prefix-bodyᵀ liftρ prefix noL noL′ L⊑L′ =
  allocation-prefixᵀ prefix body
    (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noL↑ (nu-term-imprecision-source-typing body))
    (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noL′↑ (nu-term-imprecision-target-typing body))
  where
  body = rel-world-embed-no•ᵀ
    (matched-lift-world-embeddingⁱ liftρ) L⊑L′ noL noL′
  noL↑ = renameᵗᵐ-preserves-No• suc noL
  noL′↑ = renameᵗᵐ-preserves-No• suc noL′

right-lift-prefix-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ A B L L′ p}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ₀ ρ₁ →
  StoreImpPrefix ρ₁ ρ⁺ →
  No• L → No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ⁺ ∣ []
    ⊢ᴺ L ⊑ ⇑ᵗᵐ L′ ⦂ A ⊑ ⇑ᵗ B
      ∶ ⊑-target-lift-rightᵢ p
right-lift-prefix-bodyᵀ {A = A} {L = L}
    liftρ prefix noL noL′ L⊑L′ =
  allocation-prefixᵀ prefix body
    (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noL (nu-term-imprecision-source-typing body))
    (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noL′↑ (nu-term-imprecision-target-typing body))
  where
  body =
    nu-term-imprecision-transport-termsᵀ (renameᵗᵐ-id L) refl
      (nu-term-imprecision-transport-typesᵀ
        (renameᵗ-id A) refl refl
        (rel-world-embed-no•ᵀ
          (right-lift-world-embeddingⁱ liftρ) L⊑L′ noL noL′))
  noL′↑ = renameᵗᵐ-preserves-No• suc noL′

right-swap-reveal-store :
  ∀ {Φ Δᴸ Δᴿ Bobs}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  renameStoreᵗ suc
      ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    ≡ (suc zero , ⇑ᵗ (⇑ᵗ Bobs)) ∷ rightStoreⁱ ρ₂
right-swap-reveal-store liftρ₁ liftρ₂ =
  cong₂ _∷_ refl
    (trans
      (cong ⟰ᵗ (sym (rightStoreⁱ-lift liftρ₁)))
      (sym (rightStoreⁱ-lift liftρ₂)))

left-swap-reveal-conversion :
  ∀ {Φ Δᴸ Δᴿ Aobs E F s μ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E F →
  RevealConversion (λ Y → μ (predᵗ Y)) (suc (suc Δᴸ))
    ((zero , ⇑ᵗ (⇑ᵗ Aobs)) ∷
      (suc zero , ★) ∷ leftStoreⁱ ρ₂)
    zero (⇑ᵗ (⇑ᵗ Aobs)) (renameᶜ (extᵗ suc) s)
    (renameᵗ (extᵗ suc) E) (renameᵗ (extᵗ suc) F)
left-swap-reveal-conversion {Δᴸ = Δᴸ} {Aobs = Aobs}
    {E = E} {F = F} {s = s} {μ = μ} {ρ₂ = ρ₂}
    liftρ₁ liftρ₂ s↑ =
  weaken-reveal-conversion store-incl-insert-second
    (subst
      (λ C → RevealConversion (λ Y → μ (predᵗ Y))
        (suc (suc Δᴸ))
        ((zero , ⇑ᵗ (⇑ᵗ Aobs)) ∷ leftStoreⁱ ρ₂)
        zero C (renameᶜ (extᵗ suc) s)
        (renameᵗ (extᵗ suc) E) (renameᵗ (extᵗ suc) F))
      (renameᵗ-ext-suc-comm suc Aobs)
      (subst
        (λ Σ → RevealConversion (λ Y → μ (predᵗ Y))
          (suc (suc Δᴸ)) Σ zero
          (renameᵗ (extᵗ suc) (⇑ᵗ Aobs))
          (renameᶜ (extᵗ suc) s)
          (renameᵗ (extᵗ suc) E) (renameᵗ (extᵗ suc) F))
        (left-swap-reveal-store liftρ₁ liftρ₂)
        (rename-reveal-conversion
          (TyRenameWf-ext TyRenameWf-suc)
          (modeRename-left-inverse
            {ρ = extᵗ suc} {ψ = predᵗ}
            RenameLeftInverse-ext-suc-pred)
          s↑)))

right-swap-reveal-conversion :
  ∀ {Φ Δᴸ Δᴿ Bobs E′ F′ s′ μ′}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ F′ →
  RevealConversion (λ Y → μ′ (predᵗ Y)) (suc (suc Δᴿ))
    ((zero , ★) ∷
      (suc zero , ⇑ᵗ (⇑ᵗ Bobs)) ∷ rightStoreⁱ ρ₂)
    (suc zero) (⇑ᵗ (⇑ᵗ Bobs)) (⇑ᶜ s′)
    (⇑ᵗ E′) (⇑ᵗ F′)
right-swap-reveal-conversion {Δᴿ = Δᴿ} {Bobs = Bobs}
    {E′ = E′} {F′ = F′} {s′ = s′} {μ′ = μ′}
    liftρ₁ liftρ₂ s′↑ =
  weaken-reveal-conversion StoreIncl-drop
    (subst
      (λ Σ → RevealConversion (λ Y → μ′ (predᵗ Y))
        (suc (suc Δᴿ)) Σ (suc zero) (⇑ᵗ (⇑ᵗ Bobs))
        (⇑ᶜ s′) (⇑ᵗ E′) (⇑ᵗ F′))
      (right-swap-reveal-store liftρ₁ liftρ₂)
      (rename-reveal-conversion
        TyRenameWf-suc
        (modeRename-left-inverse
          {ρ = suc} {ψ = predᵗ} RenameLeftInverse-suc)
        s′↑))

right-swap-source-reveal-store :
  ∀ {Φ Δᴸ Δᴿ Aobs}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  renameStoreᵗ suc
      ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    ≡ (suc zero , ⇑ᵗ (⇑ᵗ Aobs)) ∷ leftStoreⁱ ρ₂
right-swap-source-reveal-store liftρ₁ liftρ₂ =
  cong₂ _∷_ refl
    (trans
      (cong ⟰ᵗ (sym (leftStoreⁱ-lift liftρ₁)))
      (sym (leftStoreⁱ-lift liftρ₂)))

left-swap-target-reveal-store :
  ∀ {Φ Δᴸ Δᴿ Bobs}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  renameStoreᵗ (extᵗ suc)
      ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    ≡ (zero , ⇑ᵗ (⇑ᵗ Bobs)) ∷ rightStoreⁱ ρ₂
left-swap-target-reveal-store {Bobs = Bobs} {ρ₀ = ρ₀}
    liftρ₁ liftρ₂ =
  cong₂ _∷_
    (cong (λ C → zero , C) (renameᵗ-ext-suc-comm suc Bobs))
    (trans
      (renameStoreᵗ-ext-suc-comm suc (rightStoreⁱ ρ₀))
      (trans
        (cong ⟰ᵗ (sym (rightStoreⁱ-lift liftρ₁)))
        (sym (rightStoreⁱ-lift liftρ₂))))

right-swap-source-reveal-conversion :
  ∀ {Φ Δᴸ Δᴿ Aobs E F s μ}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E F →
  RevealConversion (λ Y → μ (predᵗ Y)) (suc (suc Δᴸ))
    ((zero , ★) ∷
      (suc zero , ⇑ᵗ (⇑ᵗ Aobs)) ∷ leftStoreⁱ ρ₂)
    (suc zero) (⇑ᵗ (⇑ᵗ Aobs)) (⇑ᶜ s)
    (⇑ᵗ E) (⇑ᵗ F)
right-swap-source-reveal-conversion {Δᴸ = Δᴸ}
    {Aobs = Aobs} {E = E} {F = F} {s = s} {μ = μ}
    liftρ₁ liftρ₂ s↑ =
  weaken-reveal-conversion StoreIncl-drop
    (subst
      (λ Σ → RevealConversion (λ Y → μ (predᵗ Y))
        (suc (suc Δᴸ)) Σ (suc zero) (⇑ᵗ (⇑ᵗ Aobs))
        (⇑ᶜ s) (⇑ᵗ E) (⇑ᵗ F))
      (right-swap-source-reveal-store liftρ₁ liftρ₂)
      (rename-reveal-conversion
        TyRenameWf-suc
        (modeRename-left-inverse
          {ρ = suc} {ψ = predᵗ} RenameLeftInverse-suc)
        s↑))

left-swap-target-reveal-conversion :
  ∀ {Φ Δᴸ Δᴿ Bobs E′ F′ s′ μ′}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ F′ →
  RevealConversion (λ Y → μ′ (predᵗ Y)) (suc (suc Δᴿ))
    ((zero , ⇑ᵗ (⇑ᵗ Bobs)) ∷
      (suc zero , ★) ∷ rightStoreⁱ ρ₂)
    zero (⇑ᵗ (⇑ᵗ Bobs)) (renameᶜ (extᵗ suc) s′)
    (renameᵗ (extᵗ suc) E′) (renameᵗ (extᵗ suc) F′)
left-swap-target-reveal-conversion {Δᴿ = Δᴿ}
    {Bobs = Bobs} {E′ = E′} {F′ = F′} {s′ = s′}
    {μ′ = μ′} {ρ₂ = ρ₂} liftρ₁ liftρ₂ s′↑ =
  weaken-reveal-conversion store-incl-insert-second
    (subst
      (λ C → RevealConversion (λ Y → μ′ (predᵗ Y))
        (suc (suc Δᴿ))
        ((zero , ⇑ᵗ (⇑ᵗ Bobs)) ∷ rightStoreⁱ ρ₂)
        zero C (renameᶜ (extᵗ suc) s′)
        (renameᵗ (extᵗ suc) E′)
        (renameᵗ (extᵗ suc) F′))
      (renameᵗ-ext-suc-comm suc Bobs)
      (subst
        (λ Σ → RevealConversion (λ Y → μ′ (predᵗ Y))
          (suc (suc Δᴿ)) Σ zero
          (renameᵗ (extᵗ suc) (⇑ᵗ Bobs))
          (renameᶜ (extᵗ suc) s′)
          (renameᵗ (extᵗ suc) E′)
          (renameᵗ (extᵗ suc) F′))
        (left-swap-target-reveal-store liftρ₁ liftρ₂)
        (rename-reveal-conversion
          (TyRenameWf-ext TyRenameWf-suc)
          (modeRename-left-inverse
            {ρ = extᵗ suc} {ψ = predᵗ}
            RenameLeftInverse-ext-suc-pred)
          s′↑)))

crossed-double-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ A B L L′ p}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  No• L → No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  swapRight∀∀ᵢ Φ
    ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣ ρ₂ ∣ []
    ⊢ᴺ ⇑ᵗᵐ (⇑ᵗᵐ L) ⊑ ⇑ᵗᵐ (⇑ᵗᵐ L′)
    ⦂ ⇑ᵗ (⇑ᵗ A) ⊑ ⇑ᵗ (⇑ᵗ B)
    ∶ ⊑-crossed-double-lift∀∀ᵢ p
crossed-double-bodyᵀ {A = A} {B = B} {L = L} {L′ = L′}
    liftρ₁ liftρ₂ noL noL′ L⊑L′ =
  nu-term-imprecision-transport-termsᵀ
    (sym (renameᵗᵐ-compose suc suc L))
    (sym (renameᵗᵐ-compose suc suc L′))
    (nu-term-imprecision-transport-typesᵀ
      (sym (renameᵗ-compose suc suc A))
      (sym (renameᵗ-compose suc suc B))
      refl
      (rel-world-embed-no•ᵀ
        (crossed-double-world-embeddingⁱ liftρ₁ liftρ₂)
        L⊑L′ noL noL′))

crossed-double-prefix-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ A B L L′ p}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ ρ⁺ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  StoreImpPrefix ρ₂ ρ⁺ →
  No• L → No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  swapRight∀∀ᵢ Φ
    ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣ ρ⁺ ∣ []
    ⊢ᴺ ⇑ᵗᵐ (⇑ᵗᵐ L) ⊑ ⇑ᵗᵐ (⇑ᵗᵐ L′)
    ⦂ ⇑ᵗ (⇑ᵗ A) ⊑ ⇑ᵗ (⇑ᵗ B)
    ∶ ⊑-crossed-double-lift∀∀ᵢ p
crossed-double-prefix-bodyᵀ liftρ₁ liftρ₂ prefix noL noL′ L⊑L′ =
  allocation-prefixᵀ prefix body
    (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noLL (nu-term-imprecision-source-typing body))
    (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noLL′ (nu-term-imprecision-target-typing body))
  where
  body = crossed-double-bodyᵀ liftρ₁ liftρ₂ noL noL′ L⊑L′
  noLL = renameᵗᵐ-preserves-No• suc
    (renameᵗᵐ-preserves-No• suc noL)
  noLL′ = renameᵗᵐ-preserves-No• suc
    (renameᵗᵐ-preserves-No• suc noL′)

paired-left-lift-prefix-bodyᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ A B C L L′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp Ψ (suc Δᴸ) Δᴿ}
    {hC : WfTy (suc Δᴸ) C} →
  LiftLeftStoreⁱ Ψ ρ ρᵃ →
  LiftLeftStoreⁱ Ψ ρ ρᵇ →
  No• L → No• L′ →
  Ψ ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero C hC ∷ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
  Ψ ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero C hC ∷ ρᵃ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ ⊑-rename-idᵢ p
paired-left-lift-prefix-bodyᵀ
    {A = A} {B = B} {L = L} {L′ = L′}
    liftρᵃ liftρᵇ noL noL′ L⊑L′ =
  nu-term-imprecision-transport-termsᵀ
    (renameᵗᵐ-id L) (renameᵗᵐ-id L′)
    (nu-term-imprecision-transport-typesᵀ
      (renameᵗ-id A) (renameᵗ-id B) refl
      (rel-world-embed-no•ᵀ
        (paired-left-lift-prefix-world-embeddingⁱ liftρᵇ liftρᵃ)
        L⊑L′ noL noL′))

weak-one-step-·₁-value-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ L L₁′
      (A ⇒ B) (A′ ⇒ B′) χ) →
  sourceChanges inner ≡ [] →
  sourceResult inner ≡ L →
  No• M′ →
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ L ⊑ targetResult inner
    ⦂ applyTys (sourceChanges inner) A ⇒
        applyTys (sourceChanges inner) B
      ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ∶ transportType inner pA ↦ transportType inner pB →
  resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ M ⊑
      applyTerms (targetTailChanges inner) (applyTerm χ M′)
    ⦂ applyTys (sourceChanges inner) A
      ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
    ∶ transportType inner pA →
  WeakOneStepResult ρ
    (L · M) (L₁′ · applyTerm χ M′) B B′ χ
weak-one-step-·₁-value-frameᵀ
    {L = L} {M = M} {M′ = M′} {B = B} {B′ = B′} {χ = χ}
    {pB = pB}
    inner refl refl noM′ L⊑L′ M⊑M′ =
  record
    { sourceChanges = []
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult = L · M
    ; targetResult =
        targetResult inner ·
          applyTerms (targetTailChanges inner) (applyTerm χ M′)
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = B
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; resultType = transportType inner pB
    ; sourceCatchup = ↠-refl
    ; targetTail =
        ·₁-↠ (applyTerm-preserves-No• χ noM′)
          (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = ·⊑·ᵀ L⊑L′ M⊑M′
    }

weak-one-step-·₁-value-frame-preserves-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ L L₁′
      (A ⇒ B) (A′ ⇒ B′) χ)
    (changes-eq : sourceChanges inner ≡ [])
    (result-eq : sourceResult inner ≡ L)
    (noM′ : No• M′)
    (L⊑L′ : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ L ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) A ⇒
          applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
          applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner pA ↦ transportType inner pB)
    (M⊑M′ : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ M ⊑
        applyTerms (targetTailChanges inner) (applyTerm χ M′)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
      ∶ transportType inner pA) →
  WeakOneStepTransport inner →
  WeakOneStepTransport
    (weak-one-step-·₁-value-frameᵀ
      inner changes-eq result-eq noM′ L⊑L′ M⊑M′)
weak-one-step-·₁-value-frame-preserves-transportᵀ
    inner refl refl noM′ L⊑L′ M⊑M′ transport =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-·₁-value-frame-preserves-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ A A′ B B′ χ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ L L₁′
      (A ⇒ B) (A′ ⇒ B′) χ)
    (changes-eq : sourceChanges inner ≡ [])
    (result-eq : sourceResult inner ≡ L)
    (noM′ : No• M′)
    (L⊑L′ : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ L ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) A ⇒
          applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′) ⇒
          applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner pA ↦ transportType inner pB)
    (M⊑M′ : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ M ⊑
        applyTerms (targetTailChanges inner) (applyTerm χ M′)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ A′)
      ∶ transportType inner pA) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepTypeCoherence
    (weak-one-step-·₁-value-frameᵀ
      inner changes-eq result-eq noM′ L⊑L′ M⊑M′)
weak-one-step-·₁-value-frame-preserves-type-coherenceᵀ
    inner refl refl noM′ L⊑L′ M⊑M′ coherence =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)

weak-one-step-source-blame-right-allocation-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ V′ s s′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (h⇑A′ : WfTy (suc Δᴿ) (⇑ᵗ A′)) →
  (target⊢ : Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ ν A′ V′ s′ ⦂ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepTransport
    (weak-one-step-source-blame-right-allocationᵀ
      {A = A} {A′ = A′} {B = B} {B′ = B′}
      {V′ = V′} {s = s} {s′ = s′} {ρ = ρ}
      wfΣ′ vV′ noV′ h⇑A′ target⊢ pB)
weak-one-step-source-blame-right-allocation-transportᵀ
    {ρ = ρ} wfΣ′ vV′ noV′ h⇑A′ target⊢ pB =
  weak-step-transport
    (right-lift-prefix-bodyᵀ
      (proj₂ (lift-right-store-result ρ))
      (prefix-∷ⁱ prefix-reflⁱ))

⊑-target-lift-right-arrow-coherentᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′ D D′}
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  ⊑-target-lift-rightᵢ (pC ↦ pD) ≡
    (⊑-target-lift-rightᵢ pC ↦ ⊑-target-lift-rightᵢ pD)
⊑-target-lift-right-arrow-coherentᵢ
    {C = C} {D = D} pC pD =
  transport-arrow-⊑ᵢ
    (renameᵗ-id C) refl (renameᵗ-id D) refl

⊑-target-lift-right-all-coherentᵢ :
  ∀ {Φ Δᴸ Δᴿ C C′}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
  ⊑-target-lift-rightᵢ (∀ⁱ q) ≡
    (∀ⁱ (⊑-target-lift-right-under-∀ᵢ q))
⊑-target-lift-right-all-coherentᵢ {C = C} q
    rewrite equality-proof-unique
      (renameᵗ-id (`∀ C)) (cong `∀ (renameᵗ-ext-id C)) =
  transport-all-⊑ᵢ (renameᵗ-ext-id C) refl

weak-one-step-source-blame-right-allocation-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ V′ s s′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (h⇑A′ : WfTy (suc Δᴿ) (⇑ᵗ A′)) →
  (target⊢ : Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ ν A′ V′ s′ ⦂ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepTypeCoherence
    (weak-one-step-source-blame-right-allocationᵀ
      {A = A} {A′ = A′} {B = B} {B′ = B′}
      {V′ = V′} {s = s} {s′ = s′} {ρ = ρ}
      wfΣ′ vV′ noV′ h⇑A′ target⊢ pB)
weak-one-step-source-blame-right-allocation-type-coherenceᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {V′ = V′} {s = s} {s′ = s′} {ρ = ρ}
    wfΣ′ vV′ noV′ h⇑A′ target⊢ pB =
  weak-step-type-coherence
    (λ pC pD → HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ result pC pD)
        (≡-to-≅
          (⊑-target-lift-right-arrow-coherentᵢ pC pD))))
    (λ q → HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ result q)
        (≡-to-≅ (⊑-target-lift-right-all-coherentᵢ q))))
  where
  result = weak-one-step-source-blame-right-allocationᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {V′ = V′} {s = s} {s′ = s′} {ρ = ρ}
    wfΣ′ vV′ noV′ h⇑A′ target⊢ pB

crossed-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ A B W W′ p}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  No• W →
  No• W′ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ p →
  swapRight∀∀ᵢ Φ
    ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣ ρ₂ ∣ []
    ⊢ᴺ ⇑ᵗᵐ W ⊑ renameᵗᵐ (extᵗ suc) W′
    ⦂ ⇑ᵗ A ⊑ renameᵗ (extᵗ suc) B
    ∶ ⊑-crossed-body-lift∀∀ᵢ p
crossed-bodyᵀ liftρ₁ liftρ₂ noW noW′ W⊑W′ =
  rel-world-embed-no•ᵀ
    (crossed-right-world-embeddingⁱ liftρ₁ liftρ₂)
    W⊑W′ noW noW′

crossed-left-bodyᵀ :
  ∀ {Φ Δᴸ Δᴿ A B W W′ p}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  No• W →
  No• W′ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ p →
  swapRight∀∀ᵢ Φ
    ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣ ρ₂ ∣ []
    ⊢ᴺ renameᵗᵐ (extᵗ suc) W ⊑ ⇑ᵗᵐ W′
    ⦂ renameᵗ (extᵗ suc) A ⊑ ⇑ᵗ B
    ∶ ⊑-crossed-left-body-lift∀∀ᵢ p
crossed-left-bodyᵀ liftρ₁ liftρ₂ noW noW′ W⊑W′ =
  rel-world-embed-no•ᵀ
    (crossed-left-world-embeddingⁱ liftρ₁ liftρ₂)
    W⊑W′ noW noW′

lift-store-matched-∈ :
  ∀ {Φ Ψ Δᴸ Δᴿ ρ ρ′ α β A B p} →
  LiftStoreⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} Ψ ρ ρ′ →
  store-matched α A β B p ∈ ρ →
  ∃[ p′ ]
    store-matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) p′ ∈ ρ′
lift-store-matched-∈ lift-store-[] ()
lift-store-matched-∈ (lift-store-∷ {p′ = p′} liftρ) (here refl) =
  p′ , here refl
lift-store-matched-∈ (lift-store-∷ liftρ) (there x∈)
    with lift-store-matched-∈ liftρ x∈
lift-store-matched-∈ (lift-store-∷ liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈
lift-store-matched-∈ (lift-store-left liftρ) (here ())
lift-store-matched-∈ (lift-store-left liftρ) (there x∈)
    with lift-store-matched-∈ liftρ x∈
lift-store-matched-∈ (lift-store-left liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈
lift-store-matched-∈ (lift-store-right liftρ) (here ())
lift-store-matched-∈ (lift-store-right liftρ) (there x∈)
    with lift-store-matched-∈ liftρ x∈
lift-store-matched-∈ (lift-store-right liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈
lift-store-matched-∈ (lift-store-link liftρ) (here ())
lift-store-matched-∈ (lift-store-link liftρ) (there x∈)
    with lift-store-matched-∈ liftρ x∈
lift-store-matched-∈ (lift-store-link liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈

lift-store-link-∈ :
  ∀ {Φ Ψ Δᴸ Δᴿ ρ ρ′ α β A B p} →
  LiftStoreⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} Ψ ρ ρ′ →
  store-link α A β B p ∈ ρ →
  ∃[ p′ ]
    store-link (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) p′ ∈ ρ′
lift-store-link-∈ lift-store-[] ()
lift-store-link-∈ (lift-store-∷ liftρ) (here ())
lift-store-link-∈ (lift-store-∷ liftρ) (there x∈)
    with lift-store-link-∈ liftρ x∈
lift-store-link-∈ (lift-store-∷ liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈
lift-store-link-∈ (lift-store-left liftρ) (here ())
lift-store-link-∈ (lift-store-left liftρ) (there x∈)
    with lift-store-link-∈ liftρ x∈
lift-store-link-∈ (lift-store-left liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈
lift-store-link-∈ (lift-store-right liftρ) (here ())
lift-store-link-∈ (lift-store-right liftρ) (there x∈)
    with lift-store-link-∈ liftρ x∈
lift-store-link-∈ (lift-store-right liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈
lift-store-link-∈ (lift-store-link {p′ = p′} liftρ) (here refl) =
  p′ , here refl
lift-store-link-∈ (lift-store-link liftρ) (there x∈)
    with lift-store-link-∈ liftρ x∈
lift-store-link-∈ (lift-store-link liftρ) (there x∈)
    | p′ , shifted∈ =
  p′ , there shifted∈

lift-store-corresponds :
  ∀ {Φ Ψ Δᴸ Δᴿ ρ ρ′ α β A B p} →
  LiftStoreⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} Ψ ρ ρ′ →
  StoreCorresponds ρ α A β B p →
  ∃[ p′ ] StoreCorresponds ρ′
    (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) p′
lift-store-corresponds liftρ (correspondence-stored x∈)
    with lift-store-matched-∈ liftρ x∈
lift-store-corresponds liftρ (correspondence-stored x∈)
    | p′ , shifted∈ =
  p′ , correspondence-stored shifted∈
lift-store-corresponds liftρ (correspondence-linked x∈)
    with lift-store-link-∈ liftρ x∈
lift-store-corresponds liftρ (correspondence-linked x∈)
    | p′ , shifted∈ =
  p′ , correspondence-linked shifted∈

weaken-store-corresponds :
  ∀ {Φ Δᴸ Δᴿ ρ α β A B p}
    {entry : StoreImpEntry Φ Δᴸ Δᴿ} →
  StoreCorresponds ρ α A β B p →
  StoreCorresponds (entry ∷ ρ) α A β B p
weaken-store-corresponds (correspondence-stored x∈) =
  correspondence-stored (there x∈)
weaken-store-corresponds (correspondence-linked x∈) =
  correspondence-linked (there x∈)

allocated-left-seal★ :
  ∀ {Φ Δᴸ Δᴿ μ Aν}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★ (extᵈ μ) ((zero , Aν) ∷ leftStoreⁱ ρ′)
allocated-left-seal★ liftρ seal★ zero ()
allocated-left-seal★ {μ = μ} {ρ′ = ρ′} liftρ seal★ (suc α) ok =
  there (shifted-seal★ (suc α) ok)
  where
    shifted-seal★ : SealModeStore★ (extᵈ μ) (leftStoreⁱ ρ′)
    shifted-seal★ =
      subst (SealModeStore★ (extᵈ μ))
        (sym (leftStoreⁱ-lift-left liftρ))
        (seal★-ext-shift seal★)

allocated-left-gen-seal★ :
  ∀ {Φ Δᴸ Δᴿ μ Aν}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★ (genᵈ μ) ((zero , Aν) ∷ leftStoreⁱ ρ′)
allocated-left-gen-seal★ liftρ seal★ zero ()
allocated-left-gen-seal★ {μ = μ} {ρ′ = ρ′}
    liftρ seal★ (suc α) ok =
  there (shifted-seal★ (suc α) ok)
  where
    shifted-seal★ : SealModeStore★ (genᵈ μ) (leftStoreⁱ ρ′)
    shifted-seal★ =
      subst (SealModeStore★ (genᵈ μ))
        (sym (leftStoreⁱ-lift-left liftρ))
        (seal★-gen-shift seal★)

seal★-weakenCast-shift :
  ∀ {μ Σ} →
  SealModeStore★ μ Σ →
  SealModeStore★ (weakenCastᵈ μ) (⟰ᵗ Σ)
seal★-weakenCast-shift seal★ zero ()
seal★-weakenCast-shift seal★ (suc α) ok =
  ∈-renameStoreᵗ suc (seal★ α ok)

lifted-left-weakenCast-seal★ :
  ∀ {Φ Δᴸ Δᴿ μ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★ (weakenCastᵈ μ) (leftStoreⁱ ρ′)
lifted-left-weakenCast-seal★ liftρ seal★ =
  subst (SealModeStore★ _)
    (sym (leftStoreⁱ-lift-left liftρ))
    (seal★-weakenCast-shift seal★)

lifted-left-narrowing :
  ∀ {Φ Δᴸ Δᴿ μ c A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  weakenCastᵈ μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ suc c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
lifted-left-narrowing liftρ c⊒ =
  subst
    (λ Σ → weakenCastᵈ _ ∣ _ ∣ Σ
      ⊢ renameᶜ suc _ ∶ ⇑ᵗ _ ⊒ ⇑ᵗ _)
    (sym (leftStoreⁱ-lift-left liftρ))
    (narrow-renameᵗ TyRenameWf-suc
      modeRename-suc-weakenCast c⊒)

lifted-left-widening :
  ∀ {Φ Δᴸ Δᴿ μ c A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  weakenCastᵈ μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ suc c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
lifted-left-widening liftρ c⊑ =
  subst
    (λ Σ → weakenCastᵈ _ ∣ _ ∣ Σ
      ⊢ renameᶜ suc _ ∶ ⇑ᵗ _ ⊑ ⇑ᵗ _)
    (sym (leftStoreⁱ-lift-left liftρ))
    (widen-renameᵗ TyRenameWf-suc
      modeRename-suc-weakenCast c⊑)

left-source-lift-cast-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ c M M′ A B B′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ′ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ ⇑ᵗᵐ M ⊑ M′ ⦂ ⇑ᵗ A ⊑ B′ ∶ p →
  (q′ : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ B ⊑ B′ ⊣ Δᴿ) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ ⇑ᵗᵐ (M ⟨ c ⟩) ⊑ M′ ⦂ ⇑ᵗ B ⊑ B′ ∶ q′
left-source-lift-cast-narrowingᵀ liftρ mode seal★ c⊒ M⊑M′ q′ =
  cast⊒⊑ᵀ (cast-weaken mode)
    (lifted-left-weakenCast-seal★ liftρ seal★)
    (lifted-left-narrowing liftρ c⊒) M⊑M′ q′

left-source-lift-cast-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ c M M′ A B B′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ′ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ ⇑ᵗᵐ M ⊑ M′ ⦂ ⇑ᵗ A ⊑ B′ ∶ p →
  (q′ : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ B ⊑ B′ ⊣ Δᴿ) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ ⇑ᵗᵐ (M ⟨ c ⟩) ⊑ M′ ⦂ ⇑ᵗ B ⊑ B′ ∶ q′
left-source-lift-cast-wideningᵀ liftρ mode seal★ c⊑ M⊑M′ q′ =
  cast⊑⊑ᵀ (cast-weaken mode)
    (lifted-left-weakenCast-seal★ liftρ seal★)
    (lifted-left-widening liftρ c⊑) M⊑M′ q′

allocated-left-relationᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν M M′ B B′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ′ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  (hAν : WfTy (suc Δᴸ) Aν) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  No• M →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ M ⊑ M′ ⦂ B ⊑ B′ ∶ p →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero Aν hAν ∷ ρ′ ∣ γ′
    ⊢ᴺ M ⊑ M′ ⦂ B ⊑ B′ ∶ p
allocated-left-relationᵀ hAν liftρ noM M⊑M′ =
  allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) M⊑M′
    (term-weaken {Δ′ = _} {Σ′ = _} ≤-refl StoreIncl-drop noM
      (nu-term-imprecision-source-typing M⊑M′))
    (nu-term-imprecision-target-typing M⊑M′)

open-allocated-left-all-reveal :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν c A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ B) →
  RevealConversion (extᵈ μ) (suc Δᴸ)
    ((zero , Aν) ∷ leftStoreⁱ ρ′)
    (suc α) (⇑ᵗ X) c A B
open-allocated-left-all-reveal liftρ (reveal-all c↑) =
  weaken-reveal-conversion StoreIncl-drop
    (subst
      (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
      (sym (leftStoreⁱ-lift-left liftρ)) c↑)

open-allocated-left-all-conceal :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν c A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ B) →
  ConcealConversion (extᵈ μ) (suc Δᴸ)
    ((zero , Aν) ∷ leftStoreⁱ ρ′)
    (suc α) (⇑ᵗ X) c A B
open-allocated-left-all-conceal liftρ (conceal-all c↓) =
  weaken-conceal-conversion StoreIncl-drop
    (subst
      (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
      (sym (leftStoreⁱ-lift-left liftρ)) c↓)

open-allocated-paired-all-conversion :
  ∀ {Φ Δᴸ Δᴿ X X′ pX c c′ A A′ B B′ p q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  PairedConversion Φ Δᴸ Δᴿ ρ
    (`∀ c) (`∀ c′) {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
    (∀ⁱ p) (∀ⁱ q) →
  PairedConversion (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)
    (store-matched zero X zero X′ pX ∷ ρ′)
    c c′ {A} {A′} {B} {B′} p q
open-allocated-paired-all-conversion liftρ
    (paired-reveal x~ (reveal-all c↑) (reveal-all c′↑))
    with lift-store-corresponds liftρ x~
open-allocated-paired-all-conversion liftρ
    (paired-reveal x~ (reveal-all c↑) (reveal-all c′↑))
    | p′ , shifted~ =
  paired-reveal (weaken-store-corresponds shifted~)
    (weaken-reveal-conversion StoreIncl-drop left-reveal)
    (weaken-reveal-conversion StoreIncl-drop right-reveal)
  where
    left-reveal =
      subst
        (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
        (sym (leftStoreⁱ-lift liftρ))
        c↑

    right-reveal =
      subst
        (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
        (sym (rightStoreⁱ-lift liftρ))
        c′↑
open-allocated-paired-all-conversion liftρ
    (paired-conceal x~ (conceal-all c↓) (conceal-all c′↓))
    with lift-store-corresponds liftρ x~
open-allocated-paired-all-conversion liftρ
    (paired-conceal x~ (conceal-all c↓) (conceal-all c′↓))
    | p′ , shifted~ =
  paired-conceal (weaken-store-corresponds shifted~)
    (weaken-conceal-conversion StoreIncl-drop left-conceal)
    (weaken-conceal-conversion StoreIncl-drop right-conceal)
  where
    left-conceal =
      subst
        (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
        (sym (leftStoreⁱ-lift liftρ))
        c↓

    right-conceal =
      subst
        (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
        (sym (rightStoreⁱ-lift liftρ))
        c′↓

------------------------------------------------------------------------
-- First administrative step after allocation
------------------------------------------------------------------------

post-allocation-β-Λ•-bare :
  ∀ {V} →
  Value V →
  (⇑ᵗᵐ (Λ V)) • —→[ keep ] V
post-allocation-β-Λ•-bare {V = V} vV =
  subst
    (λ W → (⇑ᵗᵐ (Λ V)) • —→[ keep ] W)
    (open0-ext-suc-cancelᵐ V)
    (pure-step
      (β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc) vV)))

post-allocation-β-Λ• :
  ∀ {V s} →
  Value V →
  ((⇑ᵗᵐ (Λ V)) •) ⟨ s ⟩ —→[ keep ] V ⟨ s ⟩
post-allocation-β-Λ• vV =
  ξ-⟨⟩ (post-allocation-β-Λ•-bare vV)

post-β-inst :
  ∀ {V B s} →
  Value V →
  V ⟨ inst B s ⟩ —→[ keep ] ν ★ V s
post-β-inst vV = pure-step (β-inst vV)

post-catchup-β-inst :
  ∀ χs {V B s} →
  Value V →
  V ⟨ applyCoercions χs (inst B s) ⟩
    —→[ keep ]
      ν ★ V (applyCoercionUnderTyBinders χs s)
post-catchup-β-inst χs {B = B} {s = s} vV
    rewrite applyCoercions-inst χs B s =
  pure-step (β-inst vV)

post-β-gen• :
  ∀ {V A c} →
  Value V →
  ((V ⟨ gen A c ⟩) •) —→[ keep ] (V ⟨ (c [ zero ]ᶜ) ⟩)
post-β-gen• vV = pure-step (β-gen• vV)

post-allocation-β-gen• :
  ∀ {V A c s} →
  Value V →
  ((⇑ᵗᵐ (V ⟨ gen A c ⟩)) •) ⟨ s ⟩
    —→[ keep ] ((⇑ᵗᵐ V) ⟨ c ⟩) ⟨ s ⟩
post-allocation-β-gen• {V = V} {c = c} {s = s} vV =
  ξ-⟨⟩ (post-allocation-β-gen•-bare vV)

nested-Λ-no• :
  ∀ {W c d} →
  No• (((Λ W) ⟨ c ⟩) ⟨ d ⟩) →
  No• W
nested-Λ-no• (no•-⟨⟩ (no•-⟨⟩ (no•-Λ noW))) = noW

nested-Λ-runtime-no• :
  ∀ {A W c d s} →
  RuntimeOK (ν A (((Λ W) ⟨ c ⟩) ⟨ d ⟩) s) →
  No• W
nested-Λ-runtime-no• okM
    with runtime-⟨⟩ (runtime-⟨⟩ (runtime-ν okM))
nested-Λ-runtime-no• okM | ok-no (no•-Λ noW) = noW

------------------------------------------------------------------------
-- Direct-swap administrative traces
------------------------------------------------------------------------

left-swap-allocation-trace :
  ∀ {Aobs G U W d u s} →
  Value W →
  No• W →
  ν Aobs
      ((Λ W) ⟨ `∀ (gen G d) ⟩ ⟨ inst U (`∀ u) ⟩)
      s
    —↠[
      keep ∷ bind ★ ∷ keep ∷ keep ∷
      bind (⇑ᵗ Aobs) ∷ keep ∷ keep ∷ []
    ]
      (((⇑ᵗᵐ W) ⟨ d ⟩) ⟨ u ⟩)
        ⟨ renameᶜ (extᵗ suc) s ⟩
left-swap-allocation-trace {Aobs = Aobs} {G = G} {U = U}
    {W = W} {d = d} {u = u} {s = s} vW noW =
  ↠-step
    (ξ-ν (post-β-inst ((Λ vW) ⟨ `∀ (gen G d) ⟩)))
    (↠-step
      (ξ-ν
        (ν-step ((Λ vW) ⟨ `∀ (gen G d) ⟩)
          (no•-⟨⟩ (no•-Λ noW))))
      (↠-step
        (ξ-ν
          (ξ-⟨⟩
            (post-allocation-β-∀•-bare (Λ vW))))
        (↠-step
          (ξ-ν
            (ξ-⟨⟩
              (ξ-⟨⟩ (post-allocation-β-Λ•-bare vW))))
          (↠-step
            (ν-step
              (((vW ⟨ gen G d ⟩) ⟨ `∀ u ⟩))
              (no•-⟨⟩ (no•-⟨⟩ noW)))
            (↠-step
              (ξ-⟨⟩
                (post-allocation-β-∀•-bare
                  (vW ⟨ gen G d ⟩)))
              (↠-step
                (ξ-⟨⟩
                  (ξ-⟨⟩
                    (post-allocation-β-gen•-bare vW)))
                ↠-refl))))))

left-swap-allocation-step-tail :
  ∀ {Aobs G U W d u s} →
  Value W →
  No• W →
  (ν Aobs
      ((Λ W) ⟨ `∀ (gen G d) ⟩ ⟨ inst U (`∀ u) ⟩)
      s
    —→[ keep ]
      ν Aobs
        (ν ★ ((Λ W) ⟨ `∀ (gen G d) ⟩) (`∀ u))
        s) ×
  (ν Aobs
      (ν ★ ((Λ W) ⟨ `∀ (gen G d) ⟩) (`∀ u))
      s
    —↠[
      bind ★ ∷ keep ∷ keep ∷ bind (⇑ᵗ Aobs) ∷
      keep ∷ keep ∷ []
    ]
      (((⇑ᵗᵐ W) ⟨ d ⟩) ⟨ u ⟩)
        ⟨ renameᶜ (extᵗ suc) s ⟩)
left-swap-allocation-step-tail {Aobs = Aobs} {G = G} {U = U}
    {W = W} {d = d} {u = u} {s = s} vW noW =
  ξ-ν (post-β-inst ((Λ vW) ⟨ `∀ (gen G d) ⟩)) ,
  ↠-step
    (ξ-ν
      (ν-step ((Λ vW) ⟨ `∀ (gen G d) ⟩)
        (no•-⟨⟩ (no•-Λ noW))))
    (↠-step
      (ξ-ν
        (ξ-⟨⟩
          (post-allocation-β-∀•-bare (Λ vW))))
      (↠-step
        (ξ-ν
          (ξ-⟨⟩
            (ξ-⟨⟩ (post-allocation-β-Λ•-bare vW))))
        (↠-step
          (ν-step
            (((vW ⟨ gen G d ⟩) ⟨ `∀ u ⟩))
            (no•-⟨⟩ (no•-⟨⟩ noW)))
          (↠-step
            (ξ-⟨⟩
              (post-allocation-β-∀•-bare
                (vW ⟨ gen G d ⟩)))
            (↠-step
              (ξ-⟨⟩
                (ξ-⟨⟩
                  (post-allocation-β-gen•-bare vW)))
              ↠-refl)))))

right-swap-allocation-trace :
  ∀ {Bobs G′ U′ W′ d′ u′ s′} →
  Value W′ →
  No• W′ →
  ν Bobs
      ((Λ W′) ⟨ gen G′ (`∀ d′) ⟩
        ⟨ `∀ (inst U′ u′) ⟩)
      s′
    —↠[
      bind Bobs ∷ keep ∷ keep ∷ keep ∷
      bind ★ ∷ keep ∷ keep ∷ []
    ]
      ((renameᵗᵐ (extᵗ suc) W′ ⟨ d′ ⟩) ⟨ u′ ⟩)
        ⟨ ⇑ᶜ s′ ⟩
right-swap-allocation-trace {Bobs = Bobs} {G′ = G′} {U′ = U′}
    {W′ = W′} {d′ = d′} {u′ = u′} {s′ = s′} vW′ noW′ =
  ↠-step
    (ν-step
      (((Λ vW′) ⟨ gen G′ (`∀ d′) ⟩)
        ⟨ `∀ (inst U′ u′) ⟩)
      (no•-⟨⟩ (no•-⟨⟩ (no•-Λ noW′))))
    (↠-step
      (ξ-⟨⟩
        (post-allocation-β-∀•-bare
          ((Λ vW′) ⟨ gen G′ (`∀ d′) ⟩)))
      (↠-step
        (ξ-⟨⟩
          (ξ-⟨⟩
            (post-allocation-β-gen•-bare (Λ vW′))))
        (↠-step
          (ξ-⟨⟩
            (post-β-inst
              ((renameᵗᵐ-preserves-Value suc (Λ vW′))
                ⟨ `∀ d′ ⟩)))
          (↠-step
            (ξ-⟨⟩
              (ν-step
                ((renameᵗᵐ-preserves-Value suc (Λ vW′))
                  ⟨ `∀ d′ ⟩)
                (no•-⟨⟩
                  (renameᵗᵐ-preserves-No• suc (no•-Λ noW′)))))
            (↠-step
              (ξ-⟨⟩
                (ξ-⟨⟩
                  (post-allocation-β-∀•-bare
                    (renameᵗᵐ-preserves-Value suc (Λ vW′)))))
              (↠-step
                (ξ-⟨⟩
                  (ξ-⟨⟩
                    (ξ-⟨⟩
                      (post-allocation-β-Λ•-bare
                        (renameᵗᵐ-preserves-Value
                          (extᵗ suc) vW′)))))
                ↠-refl))))))

right-swap-allocation-step-tail :
  ∀ {Bobs G′ U′ W′ d′ u′ s′} →
  Value W′ →
  No• W′ →
  (ν Bobs
      ((Λ W′) ⟨ gen G′ (`∀ d′) ⟩
        ⟨ `∀ (inst U′ u′) ⟩)
      s′
    —→[ bind Bobs ]
      ((⇑ᵗᵐ
        ((Λ W′) ⟨ gen G′ (`∀ d′) ⟩
          ⟨ `∀ (inst U′ u′) ⟩)) •) ⟨ s′ ⟩) ×
  (((⇑ᵗᵐ
      ((Λ W′) ⟨ gen G′ (`∀ d′) ⟩
        ⟨ `∀ (inst U′ u′) ⟩)) •) ⟨ s′ ⟩
    —↠[
      keep ∷ keep ∷ keep ∷ bind ★ ∷ keep ∷ keep ∷ []
    ]
      ((renameᵗᵐ (extᵗ suc) W′ ⟨ d′ ⟩) ⟨ u′ ⟩)
        ⟨ ⇑ᶜ s′ ⟩)
right-swap-allocation-step-tail {G′ = G′} {U′ = U′}
    {d′ = d′} {u′ = u′} vW′ noW′ =
  ν-step
    (((Λ vW′) ⟨ gen G′ (`∀ d′) ⟩)
      ⟨ `∀ (inst U′ u′) ⟩)
    (no•-⟨⟩ (no•-⟨⟩ (no•-Λ noW′))) ,
  ↠-step
    (ξ-⟨⟩
      (post-allocation-β-∀•-bare
        ((Λ vW′) ⟨ gen G′ (`∀ d′) ⟩)))
    (↠-step
      (ξ-⟨⟩
        (ξ-⟨⟩
          (post-allocation-β-gen•-bare (Λ vW′))))
      (↠-step
        (ξ-⟨⟩
          (post-β-inst
            ((renameᵗᵐ-preserves-Value suc (Λ vW′))
              ⟨ `∀ d′ ⟩)))
        (↠-step
          (ξ-⟨⟩
            (ν-step
              ((renameᵗᵐ-preserves-Value suc (Λ vW′))
                ⟨ `∀ d′ ⟩)
              (no•-⟨⟩
                (renameᵗᵐ-preserves-No• suc (no•-Λ noW′)))))
          (↠-step
            (ξ-⟨⟩
              (ξ-⟨⟩
                (post-allocation-β-∀•-bare
                  (renameᵗᵐ-preserves-Value suc (Λ vW′)))))
            (↠-step
              (ξ-⟨⟩
                (ξ-⟨⟩
                  (ξ-⟨⟩
                    (post-allocation-β-Λ•-bare
                      (renameᵗᵐ-preserves-Value
                        (extᵗ suc) vW′)))))
              ↠-refl)))))

paired-swap-gen-inst-allocationᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B D D′ E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (qD : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ D ⊑ᵖ D′ ⊣ suc (suc Δᴿ)) →
  (pE : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ renameᵗ (extᵗ suc) E ⊑ ⇑ᵗ E′ ⊣ suc (suc Δᴿ)) →
  (pF : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ renameᵗ (extᵗ suc) F ⊑ ⇑ᵗ F′ ⊣ suc (suc Δᴿ)) →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D) →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ gen (`∀ B) (`∀ d′) ∶ `∀ B ⊒ `∀ (`∀ D′) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (inst E′ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E F →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ F′ →
  (ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩ ⟨ inst (`∀ E) (`∀ u) ⟩) s
    —↠[
      keep ∷ bind ★ ∷ keep ∷ keep ∷
      bind (⇑ᵗ Aobs) ∷ keep ∷ keep ∷ []
    ]
      (((⇑ᵗᵐ W) ⟨ d ⟩) ⟨ u ⟩)
        ⟨ renameᶜ (extᵗ suc) s ⟩) ×
  (ν Bobs
      ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
        ⟨ `∀ (inst E′ u′) ⟩) s′
    —→[ bind Bobs ]
      ((⇑ᵗᵐ
        ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
          ⟨ `∀ (inst E′ u′) ⟩)) •) ⟨ s′ ⟩) ×
  (((⇑ᵗᵐ
      ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
        ⟨ `∀ (inst E′ u′) ⟩)) •) ⟨ s′ ⟩
    —↠[
      keep ∷ keep ∷ keep ∷ bind ★ ∷ keep ∷ keep ∷ []
    ]
      ((renameᵗᵐ (extᵗ suc) W′ ⟨ d′ ⟩) ⟨ u′ ⟩)
        ⟨ ⇑ᶜ s′ ⟩) ×
  (swapRight∀∀ᵢ Φ
    ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣
      crossedStoreⁱ
        (⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
        wf★ wf★
        (⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
        (⊑-crossed-double-lift∀∀ᵢ pObs) id★ ρ₂
    ∣ []
    ⊢ᴺ (((⇑ᵗᵐ W) ⟨ d ⟩) ⟨ u ⟩)
        ⟨ renameᶜ (extᵗ suc) s ⟩
      ⊑ ((renameᵗᵐ (extᵗ suc) W′ ⟨ d′ ⟩) ⟨ u′ ⟩)
        ⟨ ⇑ᶜ s′ ⟩
    ⦂ renameᵗ (extᵗ suc) F ⊑ ⇑ᵗ F′ ∶ pF)
paired-swap-gen-inst-allocationᵀ {Aobs = Aobs} {Bobs = Bobs}
    liftρ₁ liftρ₂ vW noW vW′ noW′
    W⊑W′ pObs qD pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑
    s↑ s′↑
    with right-swap-allocation-step-tail vW′ noW′
paired-swap-gen-inst-allocationᵀ {Aobs = Aobs} {Bobs = Bobs}
    liftρ₁ liftρ₂ vW noW vW′ noW′
    W⊑W′ pObs qD pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑
    s↑ s′↑ | right→ , right↠ =
  let
    body⊑body′ = crossed-bodyᵀ liftρ₁ liftρ₂ noW noW′ W⊑W′
    allocated-body =
      allocation-prefixᵀ
        (prefix-∷ⁱ (prefix-∷ⁱ (prefix-∷ⁱ
          (prefix-∷ⁱ (prefix-∷ⁱ
            (prefix-∷ⁱ prefix-reflⁱ))))))
        body⊑body′
        (term-weaken ≤-refl (λ x∈ → there (there x∈))
          (renameᵗᵐ-preserves-No• suc noW)
          (nu-term-imprecision-source-typing body⊑body′))
        (term-weaken ≤-refl (λ x∈ → there (there x∈))
          (renameᵗᵐ-preserves-No• (extᵗ suc) noW′)
          (nu-term-imprecision-target-typing body⊑body′))
    d⊒ =
      ∀gen-crossed-narrowing-body
        {Aobs = ⇑ᵗ (⇑ᵗ Aobs)} liftρ₁ liftρ₂ ∀gen⊒
    d′⊒ =
      gen∀-crossed-narrowing-body
        {Bobs = ⇑ᵗ (⇑ᵗ Bobs)} liftρ₁ liftρ₂ gen∀⊒
    u⊑ =
      inst∀-crossed-widening-body
        {Aobs = ⇑ᵗ (⇑ᵗ Aobs)} liftρ₁ liftρ₂ inst∀⊑
    u′⊑ =
      ∀inst-crossed-widening-body
        {Bobs = ⇑ᵗ (⇑ᵗ Bobs)} liftρ₁ liftρ₂ ∀inst⊑
    exposed-casts =
      up⊑upᵀ
        (gen-down⊑gen-downᵀ d⊒ d′⊒ allocated-body qD)
        (quotient-cast-widening
          (cast-ext (cast-inst cast-tag-or-id))
          seal★-ext-inst-tag-or-id u⊑
          (cast-inst (cast-ext cast-tag-or-id))
          seal★-inst-ext-tag-or-id u′⊑) pE
  in
  left-swap-allocation-trace vW noW ,
  right→ ,
  right↠ ,
  conv⊑convᵀ
    (paired-conversion
      (paired-reveal crossedStoreⁱ-new-old
        (left-swap-reveal-conversion liftρ₁ liftρ₂ s↑)
        (right-swap-reveal-conversion liftρ₁ liftρ₂ s′↑)))
    exposed-casts

paired-reverse-swap-gen-inst-allocationᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B D D′ E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (qD : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ D ⊑ᵖ D′ ⊣ suc (suc Δᴿ)) →
  (pE : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ ⇑ᵗ E ⊑ renameᵗ (extᵗ suc) E′ ⊣ suc (suc Δᴿ)) →
  (pF : swapRight∀∀ᵢ Φ ∣ suc (suc Δᴸ)
    ⊢ ⇑ᵗ F ⊑ renameᵗ (extᵗ suc) F′ ⊣ suc (suc Δᴿ)) →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ gen (`∀ A) (`∀ d) ∶ `∀ A ⊒ `∀ (`∀ D) →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (gen B d′) ∶ `∀ B ⊒ `∀ (`∀ D′) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (inst E u) ∶ `∀ (`∀ D) ⊑ `∀ E →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (`∀ E′) (`∀ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E F →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ F′ →
  (ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s
    —↠[
      bind Aobs ∷ keep ∷ keep ∷ keep ∷
      bind ★ ∷ keep ∷ keep ∷ []
    ]
      ((renameᵗᵐ (extᵗ suc) W ⟨ d ⟩) ⟨ u ⟩)
        ⟨ ⇑ᶜ s ⟩) ×
  (ν Bobs
      ((Λ W′) ⟨ `∀ (gen B d′) ⟩
        ⟨ inst (`∀ E′) (`∀ u′) ⟩) s′
    —→[ keep ]
      ν Bobs
        (ν ★ ((Λ W′) ⟨ `∀ (gen B d′) ⟩) (`∀ u′))
        s′) ×
  (ν Bobs
      (ν ★ ((Λ W′) ⟨ `∀ (gen B d′) ⟩) (`∀ u′))
      s′
    —↠[
      bind ★ ∷ keep ∷ keep ∷ bind (⇑ᵗ Bobs) ∷
      keep ∷ keep ∷ []
    ]
      (((⇑ᵗᵐ W′) ⟨ d′ ⟩) ⟨ u′ ⟩)
        ⟨ renameᶜ (extᵗ suc) s′ ⟩) ×
  (swapRight∀∀ᵢ Φ
    ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣
      crossedStoreⁱ
        wf★ (⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
        (⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs)) wf★
        id★ (⊑-crossed-double-lift∀∀ᵢ pObs) ρ₂
    ∣ []
    ⊢ᴺ ((renameᵗᵐ (extᵗ suc) W ⟨ d ⟩) ⟨ u ⟩)
        ⟨ ⇑ᶜ s ⟩
      ⊑ (((⇑ᵗᵐ W′) ⟨ d′ ⟩) ⟨ u′ ⟩)
        ⟨ renameᶜ (extᵗ suc) s′ ⟩
    ⦂ ⇑ᵗ F ⊑ renameᵗ (extᵗ suc) F′ ∶ pF)
paired-reverse-swap-gen-inst-allocationᵀ
    {Aobs = Aobs} {Bobs = Bobs}
    liftρ₁ liftρ₂ vW noW vW′ noW′
    W⊑W′ pObs qD pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑
    s↑ s′↑
    with left-swap-allocation-step-tail vW′ noW′
paired-reverse-swap-gen-inst-allocationᵀ
    {Aobs = Aobs} {Bobs = Bobs}
    liftρ₁ liftρ₂ vW noW vW′ noW′
    W⊑W′ pObs qD pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑
    s↑ s′↑ | left→ , left↠ =
  let
    pObs× = ⊑-crossed-double-lift∀∀ᵢ pObs
    body⊑body′ = crossed-left-bodyᵀ
      liftρ₁ liftρ₂ noW noW′ W⊑W′
    allocated-body =
      allocation-prefixᵀ
        (prefix-∷ⁱ (prefix-∷ⁱ (prefix-∷ⁱ
          (prefix-∷ⁱ (prefix-∷ⁱ
            (prefix-∷ⁱ prefix-reflⁱ))))))
        body⊑body′
        (term-weaken ≤-refl (λ x∈ → there (there x∈))
          (renameᵗᵐ-preserves-No• (extᵗ suc) noW)
          (nu-term-imprecision-source-typing body⊑body′))
        (term-weaken ≤-refl (λ x∈ → there (there x∈))
          (renameᵗᵐ-preserves-No• suc noW′)
          (nu-term-imprecision-target-typing body⊑body′))
    d⊒ = gen∀-crossed-source-narrowing-body
      {Aobs = ⇑ᵗ (⇑ᵗ Aobs)} liftρ₁ liftρ₂ gen∀⊒
    d′⊒ = ∀gen-crossed-target-narrowing-body
      {Bobs = ⇑ᵗ (⇑ᵗ Bobs)} liftρ₁ liftρ₂ ∀gen⊒
    u⊑ = ∀inst-crossed-source-widening-body
      {Aobs = ⇑ᵗ (⇑ᵗ Aobs)} liftρ₁ liftρ₂ ∀inst⊑
    u′⊑ = inst∀-crossed-target-widening-body
      {Bobs = ⇑ᵗ (⇑ᵗ Bobs)} liftρ₁ liftρ₂ inst∀⊑
    exposed-casts =
      up⊑upᵀ
        (gen-down⊑gen-downᵀ d⊒ d′⊒ allocated-body qD)
        (quotient-cast-widening
          (cast-inst (cast-ext cast-tag-or-id))
          seal★-inst-ext-tag-or-id u⊑
          (cast-ext (cast-inst cast-tag-or-id))
          seal★-ext-inst-tag-or-id u′⊑) pE
  in
  right-swap-allocation-trace vW noW ,
  left→ ,
  left↠ ,
  conv⊑convᵀ
    (paired-conversion
      (paired-reveal crossedStoreⁱ-old-new
        (right-swap-source-reveal-conversion liftρ₁ liftρ₂ s↑)
        (left-swap-target-reveal-conversion liftρ₁ liftρ₂ s′↑)))
    exposed-casts

direct-swap-gen-inst-caseᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B D D′ T E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  Value W →
  RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩
        ⟨ inst (`∀ E) (`∀ u) ⟩) s) →
  Value W′ →
  No•
    ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
      ⟨ `∀ (inst E′ u′) ⟩) →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ D) ⊑ᵖ
      `∀ (`∀ T) ⊣ Δᴿ) →
  renameᵗ swap01ᵗ D′ ≈∀ T →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D) →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ gen (`∀ B) (`∀ d′)
      ∶ `∀ B ⊒ `∀ (`∀ T) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (inst E′ u′)
      ∶ `∀ (`∀ T) ⊑ `∀ E′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′) →
  ∃[ ρ₂ ] ∃[ pF× ]
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ ×
    (ν Aobs
        ((Λ W) ⟨ `∀ (gen A d) ⟩
          ⟨ inst (`∀ E) (`∀ u) ⟩) s
      —↠[
        keep ∷ bind ★ ∷ keep ∷ keep ∷
        bind (⇑ᵗ Aobs) ∷ keep ∷ keep ∷ []
      ]
        (((⇑ᵗᵐ W) ⟨ d ⟩) ⟨ u ⟩)
          ⟨ renameᶜ (extᵗ suc) s ⟩) ×
    (ν Bobs
        ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
          ⟨ `∀ (inst E′ u′) ⟩) s′
      —→[ bind Bobs ]
        ((⇑ᵗᵐ
          ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
            ⟨ `∀ (inst E′ u′) ⟩)) •) ⟨ s′ ⟩) ×
    (((⇑ᵗᵐ
        ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
          ⟨ `∀ (inst E′ u′) ⟩)) •) ⟨ s′ ⟩
      —↠[
        keep ∷ keep ∷ keep ∷ bind ★ ∷ keep ∷ keep ∷ []
      ]
        ((renameᵗᵐ (extᵗ suc) W′ ⟨ d′ ⟩) ⟨ u′ ⟩)
          ⟨ ⇑ᶜ s′ ⟩) ×
    (swapRight∀∀ᵢ Φ
      ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣
        crossedStoreⁱ
          (⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
          wf★ wf★
          (⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
          (⊑-crossed-double-lift∀∀ᵢ pObs) id★ ρ₂
      ∣ []
      ⊢ᴺ (((⇑ᵗᵐ W) ⟨ d ⟩) ⟨ u ⟩)
          ⟨ renameᶜ (extᵗ suc) s ⟩
        ⊑ ((renameᵗᵐ (extᵗ suc) W′ ⟨ d′ ⟩) ⟨ u′ ⟩)
          ⟨ ⇑ᶜ s′ ⟩
      ⦂ renameᵗ (extᵗ suc) (⇑ᵗ F) ⊑ ⇑ᵗ (⇑ᵗ F′) ∶ pF×)
direct-swap-gen-inst-caseᵀ {F = F} liftρ₁
    vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T pE pF
    ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
    with crossed-lift-store liftρ₁
direct-swap-gen-inst-caseᵀ {F = F} liftρ₁
    vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T pE pF
    ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
    | ρ₂ , liftρ₂ =
  let
    noW = nested-Λ-runtime-no• okM
    noW′ = nested-Λ-no• noM′
    qD× = direct-swap-residualᵖ pD D′ˢ≈T
    pE× = ⊑-crossed-left-body-lift∀∀ᵢ pE
    pF× =
      subst
        (λ T → swapRight∀∀ᵢ _ ∣ _
          ⊢ T ⊑ ⇑ᵗ (⇑ᵗ _) ⊣ _)
        (sym (renameᵗ-ext-suc-comm suc F))
        (⊑-crossed-double-lift∀∀ᵢ pF)
  in
  ρ₂ , pF× , liftρ₂ ,
  paired-swap-gen-inst-allocationᵀ
    liftρ₁ liftρ₂ vW noW vW′ noW′ W⊑W′
    pObs qD× pE× pF× ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑

direct-reverse-swap-gen-inst-caseᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B S D D′ E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  Value W →
  RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s) →
  Value W′ →
  No•
    ((Λ W′) ⟨ `∀ (gen B d′) ⟩
      ⟨ inst (`∀ E′) (`∀ u′) ⟩) →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ S) ⊑ᵖ
      `∀ (`∀ D′) ⊣ Δᴿ) →
  S ≈∀ renameᵗ swap01ᵗ D →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ gen (`∀ A) (`∀ d)
      ∶ `∀ A ⊒ `∀ (`∀ S) →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (gen B d′) ∶ `∀ B ⊒ `∀ (`∀ D′) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (inst E u)
      ∶ `∀ (`∀ S) ⊑ `∀ E →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (`∀ E′) (`∀ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′) →
  ∃[ ρ₂ ] ∃[ pF× ]
    LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ ×
    (ν Aobs
        ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
          ⟨ `∀ (inst E u) ⟩) s
      —↠[
        bind Aobs ∷ keep ∷ keep ∷ keep ∷
        bind ★ ∷ keep ∷ keep ∷ []
      ]
        ((renameᵗᵐ (extᵗ suc) W ⟨ d ⟩) ⟨ u ⟩)
          ⟨ ⇑ᶜ s ⟩) ×
    (ν Bobs
        ((Λ W′) ⟨ `∀ (gen B d′) ⟩
          ⟨ inst (`∀ E′) (`∀ u′) ⟩) s′
      —→[ keep ]
        ν Bobs
          (ν ★ ((Λ W′) ⟨ `∀ (gen B d′) ⟩) (`∀ u′))
          s′) ×
    (ν Bobs
        (ν ★ ((Λ W′) ⟨ `∀ (gen B d′) ⟩) (`∀ u′))
        s′
      —↠[
        bind ★ ∷ keep ∷ keep ∷ bind (⇑ᵗ Bobs) ∷
        keep ∷ keep ∷ []
      ]
        (((⇑ᵗᵐ W′) ⟨ d′ ⟩) ⟨ u′ ⟩)
          ⟨ renameᶜ (extᵗ suc) s′ ⟩) ×
    (swapRight∀∀ᵢ Φ
      ∣ suc (suc Δᴸ) ∣ suc (suc Δᴿ) ∣
        crossedStoreⁱ
          wf★ (⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
          (⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs)) wf★
          id★ (⊑-crossed-double-lift∀∀ᵢ pObs) ρ₂
      ∣ []
      ⊢ᴺ ((renameᵗᵐ (extᵗ suc) W ⟨ d ⟩) ⟨ u ⟩)
          ⟨ ⇑ᶜ s ⟩
        ⊑ (((⇑ᵗᵐ W′) ⟨ d′ ⟩) ⟨ u′ ⟩)
          ⟨ renameᶜ (extᵗ suc) s′ ⟩
      ⦂ ⇑ᵗ (⇑ᵗ F) ⊑ renameᵗ (extᵗ suc) (⇑ᵗ F′)
      ∶ pF×)
direct-reverse-swap-gen-inst-caseᵀ {F′ = F′}
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ pE pF
    gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    with crossed-lift-store liftρ₁
direct-reverse-swap-gen-inst-caseᵀ {F′ = F′}
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ pE pF
    gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    | ρ₂ , liftρ₂ =
  let
    noW = nested-Λ-runtime-no• okM
    noW′ = nested-Λ-no• noM′
    qD× = reverse-swap-residualᵖ S≈Dˢ pD
    pE× = ⊑-crossed-body-lift∀∀ᵢ pE
    pF× =
      subst
        (λ T → swapRight∀∀ᵢ _ ∣ _
          ⊢ ⇑ᵗ (⇑ᵗ _) ⊑ T ⊣ _)
        (sym (renameᵗ-ext-suc-comm suc F′))
        (⊑-crossed-double-lift∀∀ᵢ pF)
  in
  ρ₂ , pF× , liftρ₂ ,
  paired-reverse-swap-gen-inst-allocationᵀ
    liftρ₁ liftρ₂ vW noW vW′ noW′ W⊑W′
    pObs qD× pE× pF× gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑

-- Direct quotient clause for recursion on the term-imprecision derivation.
weak-one-step-direct-quotientᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B D D′ T E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  Value W →
  RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩
        ⟨ inst (`∀ E) (`∀ u) ⟩) s) →
  Value W′ →
  No•
    ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
      ⟨ `∀ (inst E′ u′) ⟩) →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ D) ⊑ᵖ
      `∀ (`∀ T) ⊣ Δᴿ) →
  renameᵗ swap01ᵗ D′ ≈∀ T →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D) →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ gen (`∀ B) (`∀ d′)
      ∶ `∀ B ⊒ `∀ (`∀ T) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (inst E′ u′)
      ∶ `∀ (`∀ T) ⊑ `∀ E′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′) →
  WeakOneStepResult ρ₀
    (ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩
        ⟨ inst (`∀ E) (`∀ u) ⟩) s)
    (((⇑ᵗᵐ
      ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
        ⟨ `∀ (inst E′ u′) ⟩)) •) ⟨ s′ ⟩)
    F F′ (bind Bobs)
weak-one-step-direct-quotientᵀ {Aobs = Aobs} {Bobs = Bobs}
    {F = F} {F′ = F′} liftρ₁ vW okM vW′ noM′
    W⊑W′ pObs pD qD D′ˢ≈T pE pF ∀gen⊒ gen∀⊒
    inst∀⊑ ∀inst⊑ s↑ s′↑
    with direct-swap-gen-inst-caseᵀ liftρ₁ vW okM vW′ noM′
      W⊑W′ pObs pD qD D′ˢ≈T pE pF
      ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
weak-one-step-direct-quotientᵀ {Aobs = Aobs} {Bobs = Bobs}
    {F = F} {F′ = F′} liftρ₁ vW okM vW′ noM′
    W⊑W′ pObs pD qD D′ˢ≈T pE pF ∀gen⊒ gen∀⊒
    inst∀⊑ ∀inst⊑ s↑ s′↑
    | ρ₂ , pF× , liftρ₂ , left↠ , _ , right↠ , result =
  record
    { sourceChanges =
        keep ∷ bind ★ ∷ keep ∷ keep ∷
        bind (⇑ᵗ Aobs) ∷ keep ∷ keep ∷ []
    ; targetTailChanges =
        keep ∷ keep ∷ keep ∷ bind ★ ∷ keep ∷ keep ∷ []
    ; sourceResult =
        (((⇑ᵗᵐ _) ⟨ _ ⟩) ⟨ _ ⟩)
          ⟨ renameᶜ (extᵗ suc) _ ⟩
    ; targetResult =
        ((renameᵗᵐ (extᵗ suc) _ ⟨ _ ⟩) ⟨ _ ⟩)
          ⟨ ⇑ᶜ _ ⟩
    ; resultCtx = swapRight∀∀ᵢ _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore =
        crossedStoreⁱ
          (⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
          wf★ wf★
          (⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
          (⊑-crossed-double-lift∀∀ᵢ pObs) id★ ρ₂
    ; resultSourceType = renameᵗ (extᵗ suc) (⇑ᵗ F)
    ; resultTargetType = ⇑ᵗ (⇑ᵗ F′)
    ; sourceTypeResult = renameᵗ-ext-suc-comm suc F
    ; targetTypeResult = refl
    ; transportType = ⊑-crossed-double-lift∀∀ᵢ
    ; transportAllBody = ⊑-crossed-double-lift-under-∀ᵢ
    ; transportRightBody = ⊑-crossed-double-lift-under-rightᵢ
    ; resultType = pF×
    ; sourceCatchup = left↠
    ; targetTail = right↠
    ; sourceStoreResult =
        leftStoreⁱ-crossed-two-binds
          {Aold = ★} {Anew = ⇑ᵗ Aobs}
          {Bold = Bobs} {Bnew = ★}
          {hAnew =
            ⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {hAold = wf★} {hBnew = wf★}
          {hBold =
            ⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {pnew-old = ⊑-crossed-double-lift∀∀ᵢ pObs}
          {pold-new = id★}
          liftρ₁ liftρ₂
    ; targetStoreResult =
        rightStoreⁱ-crossed-two-binds
          {Aold = ★} {Anew = ⇑ᵗ Aobs}
          {Bold = Bobs} {Bnew = ★}
          {hAnew =
            ⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {hAold = wf★} {hBnew = wf★}
          {hBold =
            ⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {pnew-old = ⊑-crossed-double-lift∀∀ᵢ pObs}
          {pold-new = id★}
          liftρ₁ liftρ₂
    ; relatedResults = result
    }

weak-one-step-direct-quotient-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B D D′ T E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (liftρ₁ : LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁) →
  (vW : Value W) →
  (okM : RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩
        ⟨ inst (`∀ E) (`∀ u) ⟩) s)) →
  (vW′ : Value W′) →
  (noM′ : No•
    ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
      ⟨ `∀ (inst E′ u′) ⟩)) →
  (W⊑W′ : ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA) →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ D) ⊑ᵖ `∀ (`∀ T) ⊣ Δᴿ) →
  (D′ˢ≈T : renameᵗ swap01ᵗ D′ ≈∀ T) →
  (pE : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ) →
  (pF : Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ) →
  (∀gen⊒ : genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D)) →
  (gen∀⊒ : genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ gen (`∀ B) (`∀ d′) ∶ `∀ B ⊒ `∀ (`∀ T)) →
  (inst∀⊑ : id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E) →
  (∀inst⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (inst E′ u′) ∶ `∀ (`∀ T) ⊑ `∀ E′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′)) →
  WeakOneStepTransport
    (weak-one-step-direct-quotientᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
      pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑)
weak-one-step-direct-quotient-transportᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
    pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
    with direct-swap-gen-inst-caseᵀ liftρ₁ vW okM vW′ noM′
      W⊑W′ pObs pD qD D′ˢ≈T pE pF
      ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
weak-one-step-direct-quotient-transportᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
    pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
    | ρ₂ , pF× , liftρ₂ , left↞ , step , right↞ , result =
  weak-step-transport
    (crossed-double-prefix-bodyᵀ liftρ₁ liftρ₂
      (prefix-∷ⁱ (prefix-∷ⁱ (prefix-∷ⁱ
        (prefix-∷ⁱ (prefix-∷ⁱ
          (prefix-∷ⁱ prefix-reflⁱ)))))))

weak-one-step-direct-quotient-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B D D′ T E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (liftρ₁ : LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁) →
  (vW : Value W) →
  (okM : RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩
        ⟨ inst (`∀ E) (`∀ u) ⟩) s)) →
  (vW′ : Value W′) →
  (noM′ : No•
    ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
      ⟨ `∀ (inst E′ u′) ⟩)) →
  (W⊑W′ : ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA) →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ D) ⊑ᵖ `∀ (`∀ T) ⊣ Δᴿ) →
  (D′ˢ≈T : renameᵗ swap01ᵗ D′ ≈∀ T) →
  (pE : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ) →
  (pF : Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ) →
  (∀gen⊒ : genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D)) →
  (gen∀⊒ : genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ gen (`∀ B) (`∀ d′) ∶ `∀ B ⊒ `∀ (`∀ T)) →
  (inst∀⊑ : id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E) →
  (∀inst⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (inst E′ u′) ∶ `∀ (`∀ T) ⊑ `∀ E′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′)) →
  WeakOneStepTypeCoherence
    (weak-one-step-direct-quotientᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
      pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑)
weak-one-step-direct-quotient-type-coherenceᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
    pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
    with direct-swap-gen-inst-caseᵀ liftρ₁ vW okM vW′ noM′
      W⊑W′ pObs pD qD D′ˢ≈T pE pF
      ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
weak-one-step-direct-quotient-type-coherenceᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
    pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
    | ρ₂ , pF× , liftρ₂ , left↞ , step , right↞ , result =
  weak-step-type-coherence
    (λ pC pD′ → HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ oneStep pC pD′)
        (≡-to-≅ (⊑-crossed-double-lift-arrowᵢ pC pD′))))
    (λ q → HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ oneStep q)
        (≡-to-≅ (⊑-crossed-double-lift-allᵢ q))))
  where
  oneStep = weak-one-step-direct-quotientᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
    pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑

weak-one-step-reverse-direct-quotientᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B S D D′ E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  Value W →
  RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s) →
  Value W′ →
  No•
    ((Λ W′) ⟨ `∀ (gen B d′) ⟩
      ⟨ inst (`∀ E′) (`∀ u′) ⟩) →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ S) ⊑ᵖ
      `∀ (`∀ D′) ⊣ Δᴿ) →
  S ≈∀ renameᵗ swap01ᵗ D →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ gen (`∀ A) (`∀ d)
      ∶ `∀ A ⊒ `∀ (`∀ S) →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (gen B d′) ∶ `∀ B ⊒ `∀ (`∀ D′) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (inst E u)
      ∶ `∀ (`∀ S) ⊑ `∀ E →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (`∀ E′) (`∀ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′) →
  WeakOneStepResult ρ₀
    (ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s)
    (ν Bobs
      (ν ★ ((Λ W′) ⟨ `∀ (gen B d′) ⟩) (`∀ u′))
      s′)
    F F′ keep
weak-one-step-reverse-direct-quotientᵀ
    {Aobs = Aobs} {Bobs = Bobs} {F = F} {F′ = F′}
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ pE pF
    gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    with direct-reverse-swap-gen-inst-caseᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ pE pF
      gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
weak-one-step-reverse-direct-quotientᵀ
    {Aobs = Aobs} {Bobs = Bobs} {F = F} {F′ = F′}
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ pE pF
    gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    | ρ₂ , pF× , liftρ₂ , right↠ , _ , left↠ , result =
  record
    { sourceChanges =
        bind Aobs ∷ keep ∷ keep ∷ keep ∷
        bind ★ ∷ keep ∷ keep ∷ []
    ; targetTailChanges =
        bind ★ ∷ keep ∷ keep ∷ bind (⇑ᵗ Bobs) ∷
        keep ∷ keep ∷ []
    ; sourceResult =
        ((renameᵗᵐ (extᵗ suc) _ ⟨ _ ⟩) ⟨ _ ⟩)
          ⟨ ⇑ᶜ _ ⟩
    ; targetResult =
        (((⇑ᵗᵐ _) ⟨ _ ⟩) ⟨ _ ⟩)
          ⟨ renameᶜ (extᵗ suc) _ ⟩
    ; resultCtx = swapRight∀∀ᵢ _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore =
        crossedStoreⁱ
          wf★
          (⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
          (⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
          wf★ id★ (⊑-crossed-double-lift∀∀ᵢ pObs) ρ₂
    ; resultSourceType = ⇑ᵗ (⇑ᵗ F)
    ; resultTargetType = renameᵗ (extᵗ suc) (⇑ᵗ F′)
    ; sourceTypeResult = refl
    ; targetTypeResult = renameᵗ-ext-suc-comm suc F′
    ; transportType = ⊑-crossed-double-lift∀∀ᵢ
    ; transportAllBody = ⊑-crossed-double-lift-under-∀ᵢ
    ; transportRightBody = ⊑-crossed-double-lift-under-rightᵢ
    ; resultType = pF×
    ; sourceCatchup = right↠
    ; targetTail = left↠
    ; sourceStoreResult =
        leftStoreⁱ-crossed-two-binds
          {Aold = Aobs} {Anew = ★}
          {Bold = ★} {Bnew = ⇑ᵗ Bobs}
          {hAnew = wf★}
          {hAold =
            ⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {hBnew =
            ⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {hBold = wf★} {pnew-old = id★}
          {pold-new = ⊑-crossed-double-lift∀∀ᵢ pObs}
          liftρ₁ liftρ₂
    ; targetStoreResult =
        rightStoreⁱ-crossed-two-binds
          {Aold = Aobs} {Anew = ★}
          {Bold = ★} {Bnew = ⇑ᵗ Bobs}
          {hAnew = wf★}
          {hAold =
            ⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {hBnew =
            ⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs)}
          {hBold = wf★} {pnew-old = id★}
          {pold-new = ⊑-crossed-double-lift∀∀ᵢ pObs}
          liftρ₁ liftρ₂
    ; relatedResults = result
    }

weak-one-step-reverse-direct-quotient-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B S D D′ E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (liftρ₁ : LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁) →
  (vW : Value W) →
  (okM : RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s)) →
  (vW′ : Value W′) →
  (noM′ : No•
    ((Λ W′) ⟨ `∀ (gen B d′) ⟩
      ⟨ inst (`∀ E′) (`∀ u′) ⟩)) →
  (W⊑W′ : ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA) →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ S) ⊑ᵖ `∀ (`∀ D′) ⊣ Δᴿ) →
  (S≈Dˢ : S ≈∀ renameᵗ swap01ᵗ D) →
  (pE : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ) →
  (pF : Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ) →
  (gen∀⊒ : genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ gen (`∀ A) (`∀ d) ∶ `∀ A ⊒ `∀ (`∀ S)) →
  (∀gen⊒ : genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (gen B d′) ∶ `∀ B ⊒ `∀ (`∀ D′)) →
  (∀inst⊑ : id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (inst E u) ∶ `∀ (`∀ S) ⊑ `∀ E) →
  (inst∀⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (`∀ E′) (`∀ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′)) →
  WeakOneStepTransport
    (weak-one-step-reverse-direct-quotientᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
      pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑)
weak-one-step-reverse-direct-quotient-transportᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
    pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    with direct-reverse-swap-gen-inst-caseᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ pE pF
      gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
weak-one-step-reverse-direct-quotient-transportᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
    pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    | ρ₂ , pF× , liftρ₂ , right↞ , step , left↞ , result =
  weak-step-transport
    (crossed-double-prefix-bodyᵀ liftρ₁ liftρ₂
      (prefix-∷ⁱ (prefix-∷ⁱ (prefix-∷ⁱ
        (prefix-∷ⁱ (prefix-∷ⁱ
          (prefix-∷ⁱ prefix-reflⁱ)))))))

weak-one-step-reverse-direct-quotient-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B S D D′ E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (liftρ₁ : LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁) →
  (vW : Value W) →
  (okM : RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s)) →
  (vW′ : Value W′) →
  (noM′ : No•
    ((Λ W′) ⟨ `∀ (gen B d′) ⟩
      ⟨ inst (`∀ E′) (`∀ u′) ⟩)) →
  (W⊑W′ : ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA) →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ S) ⊑ᵖ `∀ (`∀ D′) ⊣ Δᴿ) →
  (S≈Dˢ : S ≈∀ renameᵗ swap01ᵗ D) →
  (pE : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ) →
  (pF : Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ) →
  (gen∀⊒ : genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ gen (`∀ A) (`∀ d) ∶ `∀ A ⊒ `∀ (`∀ S)) →
  (∀gen⊒ : genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (gen B d′) ∶ `∀ B ⊒ `∀ (`∀ D′)) →
  (∀inst⊑ : id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (inst E u) ∶ `∀ (`∀ S) ⊑ `∀ E) →
  (inst∀⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (`∀ E′) (`∀ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′)) →
  WeakOneStepTypeCoherence
    (weak-one-step-reverse-direct-quotientᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
      pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑)
weak-one-step-reverse-direct-quotient-type-coherenceᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
    pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    with direct-reverse-swap-gen-inst-caseᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ pE pF
      gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
weak-one-step-reverse-direct-quotient-type-coherenceᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
    pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
    | ρ₂ , pF× , liftρ₂ , right↞ , step , left↞ , result =
  weak-step-type-coherence
    (λ pC pD′ → HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ oneStep pC pD′)
        (≡-to-≅ (⊑-crossed-double-lift-arrowᵢ pC pD′))))
    (λ q → HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ oneStep q)
        (≡-to-≅ (⊑-crossed-double-lift-allᵢ q))))
  where
  oneStep = weak-one-step-reverse-direct-quotientᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
    pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑

weak-one-step-direct-quotient-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B D D′ T E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (liftρ₁ : LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁) →
  (vW : Value W) →
  (okM : RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩
        ⟨ inst (`∀ E) (`∀ u) ⟩) s)) →
  (vW′ : Value W′) →
  (noM′ : No•
    ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
      ⟨ `∀ (inst E′ u′) ⟩)) →
  (W⊑W′ : ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA) →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ D) ⊑ᵖ `∀ (`∀ T) ⊣ Δᴿ) →
  (D′ˢ≈T : renameᵗ swap01ᵗ D′ ≈∀ T) →
  (pE : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ) →
  (pF : Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ) →
  (∀gen⊒ : genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (gen A d) ∶ `∀ A ⊒ `∀ (`∀ D)) →
  (gen∀⊒ : genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ gen (`∀ B) (`∀ d′) ∶ `∀ B ⊒ `∀ (`∀ T)) →
  (inst∀⊑ : id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ E) (`∀ u) ∶ `∀ (`∀ D) ⊑ `∀ E) →
  (∀inst⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (inst E′ u′) ∶ `∀ (`∀ T) ⊑ `∀ E′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′)) →
  WeakOneStepIndexedOutcome
    {M = ν Aobs
      ((Λ W) ⟨ `∀ (gen A d) ⟩
        ⟨ inst (`∀ E) (`∀ u) ⟩) s}
    {N′ = ((⇑ᵗᵐ
      ((Λ W′) ⟨ gen (`∀ B) (`∀ d′) ⟩
        ⟨ `∀ (inst E′ u′) ⟩)) •) ⟨ s′ ⟩}
    {A = F} {B = F′} {χ = bind Bobs} {ρ = ρ₀} pF
weak-one-step-direct-quotient-indexed-outcomeᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
    pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑ =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result type-eq)
    (weak-one-step-direct-quotient-transportᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
      pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑)
    (weak-one-step-direct-quotient-type-coherenceᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
      pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑)
  where
  result = weak-one-step-direct-quotientᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD D′ˢ≈T
    pE pF ∀gen⊒ gen∀⊒ inst∀⊑ ∀inst⊑ s↑ s′↑
  type-eq = subst-cancel-sym
    (λ S → resultCtx result ∣ resultLeftCtx result
      ⊢ S ⊑ resultTargetType result ⊣ resultRightCtx result)
    (sourceTypeResult result)
    (transportType result pF)

weak-one-step-reverse-direct-quotient-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ Aobs Bobs A B S D D′ E E′ F F′}
    {W W′ d d′ u u′ s s′ μ μ′ pA}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (liftρ₁ : LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁) →
  (vW : Value W) →
  (okM : RuntimeOK
    (ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s)) →
  (vW′ : Value W′) →
  (noM′ : No•
    ((Λ W′) ⟨ `∀ (gen B d′) ⟩
      ⟨ inst (`∀ E′) (`∀ u′) ⟩)) →
  (W⊑W′ : ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₁ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ pA) →
  (pObs : Φ ∣ Δᴸ ⊢ Aobs ⊑ Bobs ⊣ Δᴿ) →
  (pD : ∀ᵢᶜ (∀ᵢᶜ Φ) ∣ suc (suc Δᴸ)
    ⊢ D ⊑ D′ ⊣ suc (suc Δᴿ)) →
  (qD : Φ ∣ Δᴸ
    ⊢ `∀ (`∀ S) ⊑ᵖ `∀ (`∀ D′) ⊣ Δᴿ) →
  (S≈Dˢ : S ≈∀ renameᵗ swap01ᵗ D) →
  (pE : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ E ⊑ E′ ⊣ suc Δᴿ) →
  (pF : Φ ∣ Δᴸ ⊢ F ⊑ F′ ⊣ Δᴿ) →
  (gen∀⊒ : genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ gen (`∀ A) (`∀ d) ∶ `∀ A ⊒ `∀ (`∀ S)) →
  (∀gen⊒ : genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ `∀ (gen B d′) ∶ `∀ B ⊒ `∀ (`∀ D′)) →
  (∀inst⊑ : id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ `∀ (inst E u) ∶ `∀ (`∀ S) ⊑ `∀ E) →
  (inst∀⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (`∀ E′) (`∀ u′) ∶ `∀ (`∀ D′) ⊑ `∀ E′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ Aobs) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ Aobs) s E (⇑ᵗ F)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ Bobs) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
    zero (⇑ᵗ Bobs) s′ E′ (⇑ᵗ F′)) →
  WeakOneStepIndexedOutcome
    {M = ν Aobs
      ((Λ W) ⟨ gen (`∀ A) (`∀ d) ⟩
        ⟨ `∀ (inst E u) ⟩) s}
    {N′ = ν Bobs
      (ν ★ ((Λ W′) ⟨ `∀ (gen B d′) ⟩) (`∀ u′))
      s′}
    {A = F} {B = F′} {χ = keep} {ρ = ρ₀} pF
weak-one-step-reverse-direct-quotient-indexed-outcomeᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
    pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑ =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result type-eq)
    (weak-one-step-reverse-direct-quotient-transportᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
      pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑)
    (weak-one-step-reverse-direct-quotient-type-coherenceᵀ
      liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
      pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑)
  where
  result = weak-one-step-reverse-direct-quotientᵀ
    liftρ₁ vW okM vW′ noM′ W⊑W′ pObs pD qD S≈Dˢ
    pE pF gen∀⊒ ∀gen⊒ ∀inst⊑ inst∀⊑ s↑ s′↑
  type-eq = subst-cancel-sym
    (λ T → resultCtx result ∣ resultLeftCtx result
      ⊢ resultSourceType result ⊑ T ⊣ resultRightCtx result)
    (targetTypeResult result)
    (transportType result pF)

matched-polymorphic-value-shapeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ A A′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  Value L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ `∀ A ⊑ `∀ A′ ∶ p →
  AllView L × AllView L′
matched-polymorphic-value-shapeᵀ vL vL′ L⊑L′ =
  canonical-∀ vL
    (forget (nu-term-imprecision-source-typing L⊑L′)) ,
  canonical-∀ vL′
    (forget (nu-term-imprecision-target-typing L⊑L′))

right-polymorphic-value-shapeᵀ :
  ∀ {Φ Δᴸ Δᴿ N L′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ L′ ⦂ A ⊑ `∀ B ∶ p →
  AllView L′
right-polymorphic-value-shapeᵀ vL′ N⊑L′ =
  canonical-∀ vL′
    (forget (nu-term-imprecision-target-typing N⊑L′))

matched-polymorphic-value-stepsᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ A A′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  Value L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ `∀ A ⊑ `∀ A′ ∶ p →
  ∃[ N ] ∃[ N′ ]
    (((⇑ᵗᵐ L) • —→[ keep ] N) ×
     ((⇑ᵗᵐ L′) • —→[ keep ] N′))
matched-polymorphic-value-stepsᵀ vL vL′ L⊑L′
    with post-allocation-polymorphic-value-step vL
      (nu-term-imprecision-source-typing L⊑L′)
       | post-allocation-polymorphic-value-step vL′
      (nu-term-imprecision-target-typing L⊑L′)
matched-polymorphic-value-stepsᵀ vL vL′ L⊑L′
    | N , L→N | N′ , L′→N′ =
  N , N′ , L→N , L′→N′

left-polymorphic-value-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ L N′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ N′ ⦂ `∀ A ⊑ B ∶ p →
  ∃[ N ] ((⇑ᵗᵐ L) • —→[ keep ] N)
left-polymorphic-value-stepᵀ vL L⊑N′ =
  post-allocation-polymorphic-value-step vL
    (nu-term-imprecision-source-typing L⊑N′)

right-polymorphic-value-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ N L′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ L′ ⦂ A ⊑ `∀ B ∶ p →
  ∃[ N′ ] ((⇑ᵗᵐ L′) • —→[ keep ] N′)
right-polymorphic-value-stepᵀ vL′ N⊑L′ =
  post-allocation-polymorphic-value-step vL′
    (nu-term-imprecision-target-typing N⊑L′)

matched-post-allocation-β-∀-conversionᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν Aν′ A A′ B B′ V V′ c c′ p q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  (pν : ∀ᵢᶜ Φ
    ∣ suc Δᴸ ⊢ ⇑ᵗ Aν ⊑ ⇑ᵗ Aν′ ⊣ suc Δᴿ) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ A′ ∶ ∀ⁱ p →
  PairedConversion Φ Δᴸ Δᴿ ρ
    (`∀ c) (`∀ c′) {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
    (∀ⁱ p) (∀ⁱ q) →
  ((⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •
    —→[ keep ] ((⇑ᵗᵐ V) •) ⟨ c ⟩) ×
  ((⇑ᵗᵐ (V′ ⟨ `∀ c′ ⟩)) •
    —→[ keep ] ((⇑ᵗᵐ V′) •) ⟨ c′ ⟩) ×
  (∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣
    store-matched zero (⇑ᵗ Aν) zero (⇑ᵗ Aν′) pν ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ V) •) ⟨ c ⟩ ⊑ ((⇑ᵗᵐ V′) •) ⟨ c′ ⟩
    ⦂ B ⊑ B′ ∶ q)
matched-post-allocation-β-∀-conversionᵀ {p = p} vV noV vV′ noV′
    pν liftρ V⊑V′ conversion =
  post-allocation-β-∀•-bare vV ,
  post-allocation-β-∀•-bare vV′ ,
  conv⊑convᵀ
    (paired-conversion
      (open-allocated-paired-all-conversion liftρ conversion))
    (α⊑αᵀ vV noV vV′ noV′ pν liftρ lift-ctx-[] V⊑V′
      left-bullet-typing right-bullet-typing)
  where
    left-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (leftStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-src-wf p) vV noV
          (nu-term-imprecision-source-typing V⊑V′))

    right-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (rightStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-tgt-wf p) vV′ noV′
          (nu-term-imprecision-target-typing V⊑V′))

post-β-∀-reveal :
  ∀ {μ Δ Σ C c A B V} →
  Value V →
  RevealConversion μ (suc Δ) Σ zero C
    (`∀ c) (`∀ A) (`∀ B) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ] (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   RevealConversion μ (suc Δ) Σ zero C
     (c [ zero ]ᶜ) (A [ zero ]ᴿ) (B [ zero ]ᴿ))
post-β-∀-reveal vV (reveal-all c↑) =
  pure-step (β-∀• vV) ,
  open-reveal-conversion z<s c↑

post-β-∀-conceal :
  ∀ {μ Δ Σ C c A B V} →
  Value V →
  ConcealConversion μ (suc Δ) Σ zero C
    (`∀ c) (`∀ A) (`∀ B) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ] (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   ConcealConversion μ (suc Δ) Σ zero C
     (c [ zero ]ᶜ) (A [ zero ]ᴿ) (B [ zero ]ᴿ))
post-β-∀-conceal vV (conceal-all c↓) =
  pure-step (β-∀• vV) ,
  open-conceal-conversion z<s c↓

paired-β-∀-reveal :
  ∀ {Φ Δᴸ Δᴿ X X′ pX μ μ′ c c′ A A′ B B′ V V′}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  (zero⊑zero : (zero ˣ⊑ˣ zero) ∈ Φ) →
  store-matched zero X zero X′ pX ∈ ρ →
  Value V →
  Value V′ →
  RevealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  RevealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  (p : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ A ⊑ A′ ⊣ suc (suc Δᴿ)) →
  (q : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ B ⊑ B′ ⊣ suc (suc Δᴿ)) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ] (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   PairedConversion Φ (suc Δᴸ) (suc Δᴿ) ρ
     (c [ zero ]ᶜ) (c′ [ zero ]ᶜ)
     (⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s p)
     (⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s q))
paired-β-∀-reveal zero⊑zero zero-entry vV vV′
    (reveal-all c↑) (reveal-all c′↑) p q =
  pure-step (β-∀• vV) ,
  pure-step (β-∀• vV′) ,
  paired-reveal (correspondence-stored zero-entry)
    (open-reveal-conversion z<s c↑)
    (open-reveal-conversion z<s c′↑)

paired-β-∀-conceal :
  ∀ {Φ Δᴸ Δᴿ X X′ pX μ μ′ c c′ A A′ B B′ V V′}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  (zero⊑zero : (zero ˣ⊑ˣ zero) ∈ Φ) →
  store-matched zero X zero X′ pX ∈ ρ →
  Value V →
  Value V′ →
  ConcealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  ConcealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  (p : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ A ⊑ A′ ⊣ suc (suc Δᴿ)) →
  (q : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ B ⊑ B′ ⊣ suc (suc Δᴿ)) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ] (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   PairedConversion Φ (suc Δᴸ) (suc Δᴿ) ρ
     (c [ zero ]ᶜ) (c′ [ zero ]ᶜ)
     (⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s p)
     (⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s q))
paired-β-∀-conceal zero⊑zero zero-entry vV vV′
    (conceal-all c↓) (conceal-all c′↓) p q =
  pure-step (β-∀• vV) ,
  pure-step (β-∀• vV′) ,
  paired-conceal (correspondence-stored zero-entry)
    (open-conceal-conversion z<s c↓)
    (open-conceal-conversion z<s c′↓)

paired-β-∀-revealᵀ :
  ∀ {Φ Δᴸ Δᴿ X X′ pX μ μ′ c c′ A A′ B B′ V V′}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)}
    {γ : CtxImp Φ (suc Δᴸ) (suc Δᴿ)} →
  (zero⊑zero : (zero ˣ⊑ˣ zero) ∈ Φ) →
  store-matched zero X zero X′ pX ∈ ρ →
  Value V →
  Value V′ →
  RevealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  RevealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  (p : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ A ⊑ A′ ⊣ suc (suc Δᴿ)) →
  (q : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ B ⊑ B′ ⊣ suc (suc Δᴿ)) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ
    ∶ ⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s p →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩
        ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ
      ∶ ⊑-open∀ᵢ {α = zero} {β = zero}
          zero⊑zero z<s z<s q))
paired-β-∀-revealᵀ zero⊑zero zero-entry vV vV′
    (reveal-all c↑) (reveal-all c′↑) p q V•⊑V′• =
  pure-step (β-∀• vV) ,
  pure-step (β-∀• vV′) ,
  conv⊑convᵀ
    (paired-conversion
      (paired-reveal (correspondence-stored zero-entry)
        (open-reveal-conversion z<s c↑)
        (open-reveal-conversion z<s c′↑)))
    V•⊑V′•

paired-β-∀-concealᵀ :
  ∀ {Φ Δᴸ Δᴿ X X′ pX μ μ′ c c′ A A′ B B′ V V′}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)}
    {γ : CtxImp Φ (suc Δᴸ) (suc Δᴿ)} →
  (zero⊑zero : (zero ˣ⊑ˣ zero) ∈ Φ) →
  store-matched zero X zero X′ pX ∈ ρ →
  Value V →
  Value V′ →
  ConcealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  ConcealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  (p : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ A ⊑ A′ ⊣ suc (suc Δᴿ)) →
  (q : ∀ᵢᶜ Φ ∣ suc (suc Δᴸ) ⊢ B ⊑ B′ ⊣ suc (suc Δᴿ)) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ
    ∶ ⊑-open∀ᵢ {α = zero} {β = zero} zero⊑zero z<s z<s p →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩
        ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ
      ∶ ⊑-open∀ᵢ {α = zero} {β = zero}
          zero⊑zero z<s z<s q))
paired-β-∀-concealᵀ zero⊑zero zero-entry vV vV′
    (conceal-all c↓) (conceal-all c′↓) p q V•⊑V′• =
  pure-step (β-∀• vV) ,
  pure-step (β-∀• vV′) ,
  conv⊑convᵀ
    (paired-conversion
      (paired-conceal (correspondence-stored zero-entry)
        (open-conceal-conversion z<s c↓)
        (open-conceal-conversion z<s c′↓)))
    V•⊑V′•

left-β-∀-revealᵀ :
  ∀ {Φ Δᴸ Δᴿ X μ c A B B′ V N′ p}
    {ρ : StoreImp Φ (suc Δᴸ) Δᴿ}
    {γ : CtxImp Φ (suc Δᴸ) Δᴿ} →
  Value V →
  RevealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ N′ ⦂ A [ zero ]ᴿ ⊑ B′ ∶ p →
  (q : Φ ∣ suc Δᴸ ⊢ B [ zero ]ᴿ ⊑ B′ ⊣ Δᴿ) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   (N′ —↠[ [] ] N′) ×
   (Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩ ⊑ N′
      ⦂ B [ zero ]ᴿ ⊑ B′ ∶ q))
left-β-∀-revealᵀ vV (reveal-all c↑) V•⊑N′ q =
  pure-step (β-∀• vV) ,
  ↠-refl ,
  conv↑⊑ᵀ (open-reveal-conversion z<s c↑) V•⊑N′ q

left-β-∀-concealᵀ :
  ∀ {Φ Δᴸ Δᴿ X μ c A B B′ V N′ p}
    {ρ : StoreImp Φ (suc Δᴸ) Δᴿ}
    {γ : CtxImp Φ (suc Δᴸ) Δᴿ} →
  Value V →
  ConcealConversion μ (suc Δᴸ) (leftStoreⁱ ρ) zero X
    (`∀ c) (`∀ A) (`∀ B) →
  Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ N′ ⦂ A [ zero ]ᴿ ⊑ B′ ∶ p →
  (q : Φ ∣ suc Δᴸ ⊢ B [ zero ]ᴿ ⊑ B′ ⊣ Δᴿ) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   (N′ —↠[ [] ] N′) ×
   (Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩ ⊑ N′
      ⦂ B [ zero ]ᴿ ⊑ B′ ∶ q))
left-β-∀-concealᵀ vV (conceal-all c↓) V•⊑N′ q =
  pure-step (β-∀• vV) ,
  ↠-refl ,
  conv↓⊑ᵀ (open-conceal-conversion z<s c↓) V•⊑N′ q

right-β-∀-revealᵀ :
  ∀ {Φ Δᴸ Δᴿ X′ μ′ c′ A A′ B′ N V′ p}
    {ρ : StoreImp Φ Δᴸ (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ (suc Δᴿ)} →
  Value V′ →
  RevealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ V′ • ⦂ A ⊑ A′ [ zero ]ᴿ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  ((N —↠[ [] ] N) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ N ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ A ⊑ B′ [ zero ]ᴿ ∶ q))
right-β-∀-revealᵀ vV′ (reveal-all c′↑) N⊑V′• q =
  ↠-refl ,
  pure-step (β-∀• vV′) ,
  ⊑conv↑ᵀ (open-reveal-conversion z<s c′↑) N⊑V′• q

right-β-∀-concealᵀ :
  ∀ {Φ Δᴸ Δᴿ X′ μ′ c′ A A′ B′ N V′ p}
    {ρ : StoreImp Φ Δᴸ (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ (suc Δᴿ)} →
  Value V′ →
  ConcealConversion μ′ (suc Δᴿ) (rightStoreⁱ ρ) zero X′
    (`∀ c′) (`∀ A′) (`∀ B′) →
  Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ V′ • ⦂ A ⊑ A′ [ zero ]ᴿ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  ((N —↠[ [] ] N) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ N ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ A ⊑ B′ [ zero ]ᴿ ∶ q))
right-β-∀-concealᵀ vV′ (conceal-all c′↓) N⊑V′• q =
  ↠-refl ,
  pure-step (β-∀• vV′) ,
  ⊑conv↓ᵀ (open-conceal-conversion z<s c′↓) N⊑V′• q

------------------------------------------------------------------------
-- Generic narrowing and widening `β-∀•`
------------------------------------------------------------------------

left-β-∀-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ c A B B′ V N′ p}
    {ρ : StoreImp Φ (suc Δᴸ) Δᴿ}
    {γ : CtxImp Φ (suc Δᴸ) Δᴿ} →
  Value V →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c∀⊒ : μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ B) →
  Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ N′ ⦂ A [ zero ]ᴿ ⊑ B′ ∶ p →
  (q : Φ ∣ suc Δᴸ ⊢ B [ zero ]ᴿ ⊑ B′ ⊣ Δᴿ) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   (N′ —↠[ [] ] N′) ×
   (Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩ ⊑ N′
      ⦂ B [ zero ]ᴿ ⊑ B′ ∶ q))
left-β-∀-narrowingᵀ vV mode seal★ c∀⊒ V•⊑N′ q =
  pure-step (β-∀• vV) ,
  ↠-refl ,
  cast⊒⊑ᵀ mode seal★
    (open-all-narrowing z<s c∀⊒) V•⊑N′ q

left-β-∀-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ c A B B′ V N′ p}
    {ρ : StoreImp Φ (suc Δᴸ) Δᴿ}
    {γ : CtxImp Φ (suc Δᴸ) Δᴿ} →
  Value V →
  CastMode μ →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (c∀⊑ : μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ B) →
  Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V • ⊑ N′ ⦂ A [ zero ]ᴿ ⊑ B′ ∶ p →
  (q : Φ ∣ suc Δᴸ ⊢ B [ zero ]ᴿ ⊑ B′ ⊣ Δᴿ) →
  (((V ⟨ `∀ c ⟩) • —→[ keep ]
      (V •) ⟨ (c [ zero ]ᶜ) ⟩) ×
   (N′ —↠[ [] ] N′) ×
   (Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ (V •) ⟨ (c [ zero ]ᶜ) ⟩ ⊑ N′
      ⦂ B [ zero ]ᴿ ⊑ B′ ∶ q))
left-β-∀-wideningᵀ vV mode seal★ c∀⊑ V•⊑N′ q =
  pure-step (β-∀• vV) ,
  ↠-refl ,
  cast⊑⊑ᵀ mode seal★
    (open-all-widening z<s c∀⊑) V•⊑N′ q

right-β-∀-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ′ c′ A A′ B′ N V′ p}
    {ρ : StoreImp Φ Δᴸ (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ (suc Δᴿ)} →
  Value V′ →
  CastMode μ′ →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (c∀⊒ : μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊒ `∀ B′) →
  Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ V′ • ⦂ A ⊑ A′ [ zero ]ᴿ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  ((N —↠[ [] ] N) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ N ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ A ⊑ B′ [ zero ]ᴿ ∶ q))
right-β-∀-narrowingᵀ vV′ mode′ seal★′ c∀⊒ N⊑V′• q =
  ↠-refl ,
  pure-step (β-∀• vV′) ,
  ⊑cast⊒ᵀ mode′ seal★′
    (open-all-narrowing z<s c∀⊒) N⊑V′• q

right-β-∀-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ′ c′ A A′ B′ N V′ p}
    {ρ : StoreImp Φ Δᴸ (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ (suc Δᴿ)} →
  Value V′ →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf (suc Δᴿ) (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ (suc Δᴿ) Φ) →
  (c∀⊑ : μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊑ `∀ B′) →
  Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ V′ • ⦂ A ⊑ A′ [ zero ]ᴿ ∶ p →
  ((N —↠[ [] ] N) ×
   ((V′ ⟨ `∀ c′ ⟩) • —→[ keep ]
      (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩) ×
   (Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ N ⊑ (V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩
      ⦂ A ⊑ B′ [ zero ]ᴿ
      ∶ ⊑-transʳ-castᵢ okΦ′ p
          (widening⇒⊑ᵢ wfΣ′ seal★′
            (open-all-widening z<s c∀⊑))))
right-β-∀-wideningᵀ {p = p} vV′ mode′ wfΣ′ seal★′ okΦ′
    c∀⊑ N⊑V′• =
  ↠-refl ,
  pure-step (β-∀• vV′) ,
  ⊑cast⊑ᵀ mode′ seal★′ (open-all-widening z<s c∀⊑) N⊑V′•
    (⊑-transʳ-castᵢ okΦ′ p
      (widening⇒⊑ᵢ wfΣ′ seal★′
        (open-all-widening z<s c∀⊑)))

-- Base recursion clauses for generic casts on the target of `β-∀•`.

weak-one-step-right-β-∀-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ′ c′ A A′ B′ N V′ p}
    {ρ : StoreImp Φ Δᴸ (suc Δᴿ)} →
  Value V′ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊒ `∀ B′ →
  Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ • ⦂ A ⊑ A′ [ zero ]ᴿ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ N
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    A (B′ [ zero ]ᴿ) keep
weak-one-step-right-β-∀-narrowingᵀ vV′ mode′ seal★′ c∀⊒
    N⊑V′• q
    with right-β-∀-narrowingᵀ
      vV′ mode′ seal★′ c∀⊒ N⊑V′• q
weak-one-step-right-β-∀-narrowingᵀ vV′ mode′ seal★′ c∀⊒
    N⊑V′• q
    | _ , _ , result =
  record
    { sourceChanges = []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ p → p
    ; transportAllBody = λ p → p
    ; transportRightBody = λ p → p
    ; resultType = q
    ; sourceCatchup = ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }

weak-one-step-right-β-∀-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ′ c′ A A′ B′ N V′ p}
    {ρ : StoreImp Φ Δᴸ (suc Δᴿ)} →
  Value V′ →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf (suc Δᴿ) (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ (suc Δᴿ) Φ) →
  (c∀⊑ : μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊑ `∀ B′) →
  Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ • ⦂ A ⊑ A′ [ zero ]ᴿ ∶ p →
  WeakOneStepResult ρ N
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    A (B′ [ zero ]ᴿ) keep
weak-one-step-right-β-∀-wideningᵀ {p = p} vV′ mode′ wfΣ′
    seal★′ okΦ′ c∀⊑ N⊑V′•
    with right-β-∀-wideningᵀ vV′ mode′ wfΣ′ seal★′ okΦ′
      c∀⊑ N⊑V′•
weak-one-step-right-β-∀-wideningᵀ {p = p} vV′ mode′ wfΣ′
    seal★′ okΦ′ c∀⊑ N⊑V′•
    | _ , _ , result =
  record
    { sourceChanges = []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ p → p
    ; transportAllBody = λ p → p
    ; transportRightBody = λ p → p
    ; resultType =
        ⊑-transʳ-castᵢ okΦ′ p
          (widening⇒⊑ᵢ wfΣ′ seal★′
            (open-all-widening z<s c∀⊑))
    ; sourceCatchup = ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }

weak-one-step-left-β-∀-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ c A B B′ V N′ p}
    {ρ : StoreImp Φ (suc Δᴸ) Δᴿ} →
  Value V →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c∀⊒ : μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ B) →
  Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ N′ ⦂ A [ zero ]ᴿ ⊑ B′ ∶ p →
  (q : Φ ∣ suc Δᴸ ⊢ B [ zero ]ᴿ ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •) N′
    (B [ zero ]ᴿ) B′ keep
weak-one-step-left-β-∀-narrowingᵀ vV mode seal★ c∀⊒
    V•⊑N′ q
    with left-β-∀-narrowingᵀ vV mode seal★ c∀⊒ V•⊑N′ q
weak-one-step-left-β-∀-narrowingᵀ vV mode seal★ c∀⊒
    V•⊑N′ q
    | source→ , _ , result =
  record
    { sourceChanges = keep ∷ []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ p → p
    ; transportAllBody = λ p → p
    ; transportRightBody = λ p → p
    ; resultType = q
    ; sourceCatchup = ↠-step source→ ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }

weak-one-step-left-β-∀-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ c A B B′ V N′ p}
    {ρ : StoreImp Φ (suc Δᴸ) Δᴿ} →
  Value V →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ N′ ⦂ A [ zero ]ᴿ ⊑ B′ ∶ p →
  (q : Φ ∣ suc Δᴸ ⊢ B [ zero ]ᴿ ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •) N′
    (B [ zero ]ᴿ) B′ keep
weak-one-step-left-β-∀-wideningᵀ vV mode seal★ c∀⊑
    V•⊑N′ q
    with left-β-∀-wideningᵀ vV mode seal★ c∀⊑ V•⊑N′ q
weak-one-step-left-β-∀-wideningᵀ vV mode seal★ c∀⊑
    V•⊑N′ q
    | source→ , _ , result =
  record
    { sourceChanges = keep ∷ []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ p → p
    ; transportAllBody = λ p → p
    ; transportRightBody = λ p → p
    ; resultType = q
    ; sourceCatchup = ↠-step source→ ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }

-- Overlapping two-sided generic-cast derivations, with the left cast outer.

weak-one-step-generic-β-∀-left-outer-narrowing-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c∀⊒ : μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ B) →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊒ `∀ B′ →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  (qR : Φ ∣ suc Δᴸ
    ⊢ A [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  (q : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-left-outer-narrowing-narrowingᵀ
    vV vV′ mode seal★ c∀⊒ mode′ seal★′ c′∀⊒
    V•⊑V′• qR q
    with right-β-∀-narrowingᵀ
      vV′ mode′ seal★′ c′∀⊒ V•⊑V′• qR
weak-one-step-generic-β-∀-left-outer-narrowing-narrowingᵀ
    vV vV′ mode seal★ c∀⊒ mode′ seal★′ c′∀⊒
    V•⊑V′• qR q
    | _ , _ , V•⊑V′•c′ =
  weak-one-step-left-β-∀-narrowingᵀ
    vV mode seal★ c∀⊒ V•⊑V′•c′ q

weak-one-step-generic-β-∀-left-outer-narrowing-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c∀⊒ : μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ B) →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf (suc Δᴿ) (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ (suc Δᴿ) Φ) →
  (c′∀⊑ : μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊑ `∀ B′) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  (q : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-left-outer-narrowing-wideningᵀ
    vV vV′ mode seal★ c∀⊒ mode′ wfΣ′ seal★′
    okΦ′ c′∀⊑ V•⊑V′• q
    with right-β-∀-wideningᵀ
      vV′ mode′ wfΣ′ seal★′ okΦ′ c′∀⊑ V•⊑V′•
weak-one-step-generic-β-∀-left-outer-narrowing-wideningᵀ
    vV vV′ mode seal★ c∀⊒ mode′ wfΣ′ seal★′
    okΦ′ c′∀⊑ V•⊑V′• q
    | _ , _ , V•⊑V′•c′ =
  weak-one-step-left-β-∀-narrowingᵀ
    vV mode seal★ c∀⊒ V•⊑V′•c′ q

weak-one-step-generic-β-∀-left-outer-widening-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊒ `∀ B′ →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  Φ ∣ suc Δᴸ
    ⊢ A [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ →
  (q : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-left-outer-widening-narrowingᵀ
    vV vV′ mode seal★ c∀⊑ mode′ seal★′ c′∀⊒
    V•⊑V′• qR q
    with right-β-∀-narrowingᵀ
      vV′ mode′ seal★′ c′∀⊒ V•⊑V′• qR
weak-one-step-generic-β-∀-left-outer-widening-narrowingᵀ
    vV vV′ mode seal★ c∀⊑ mode′ seal★′ c′∀⊒
    V•⊑V′• qR q
    | _ , _ , V•⊑V′•c′ =
  weak-one-step-left-β-∀-wideningᵀ
    vV mode seal★ c∀⊑ V•⊑V′•c′ q

weak-one-step-generic-β-∀-left-outer-widening-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf (suc Δᴿ) (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ (suc Δᴿ) Φ) →
  (c′∀⊑ : μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊑ `∀ B′) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  (q : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-left-outer-widening-wideningᵀ
    vV vV′ mode seal★ c∀⊑ mode′ wfΣ′ seal★′ okΦ′
    c′∀⊑ V•⊑V′• q
    with right-β-∀-wideningᵀ
      vV′ mode′ wfΣ′ seal★′ okΦ′ c′∀⊑ V•⊑V′•
weak-one-step-generic-β-∀-left-outer-widening-wideningᵀ
    vV vV′ mode seal★ c∀⊑ mode′ wfΣ′ seal★′ okΦ′
    c′∀⊑ V•⊑V′• q
    | _ , _ , V•⊑V′•c′ =
  weak-one-step-left-β-∀-wideningᵀ
    vV mode seal★ c∀⊑ V•⊑V′•c′ q

left-catchup-all-keep-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  (Value N × No• N) ⊎ N ≡ blame →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult {N = M} {V′ = V′} {ρ = ρ} q
left-catchup-all-keep-stepᵀ source→ final N⊑V′ =
  let result = weak-one-step-keep-source-catchupᵀ source→ N⊑V′ in
  left-all-catchup (weak-all-result result N⊑V′)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

left-catchup-all-prepend-keepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q →
  LeftCatchupAllResult {N = M} {V′ = V′} {ρ = ρ} q
left-catchup-all-prepend-keepᵀ source→ N⊑V′
    (left-all-catchup second
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)) =
  let
    first = weak-one-step-keep-source-catchupᵀ source→ N⊑V′
    combined = weak-one-step-prepend-left-silentᵀ
      (left-silent first (left-silent-invariant refl refl))
      (weakResult second)
  in
  left-all-catchup
    (weak-all-result combined (canonicalAllResults second))
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

left-catchup-indexed-all-keep-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (source→ : M —→[ keep ] N) →
  (final : (Value N × No• N) ⊎ N ≡ blame) →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = M} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-all-keep-stepᵀ source→ final N⊑V′ =
  left-indexed-all-catchup
    (weak-one-step-index-resultᵀ result refl)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)
    (weak-one-step-keep-source-catchup-transportᵀ
      source→ N⊑V′)
    (weak-one-step-keep-source-catchup-type-coherenceᵀ
      source→ N⊑V′)
  where
  result = weak-one-step-keep-source-catchupᵀ source→ N⊑V′

left-catchup-indexed-all-prepend-keepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (source→ : M —→[ keep ] N) →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q →
  LeftCatchupIndexedAllResult
    {N = M} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-all-prepend-keepᵀ source→ N⊑V′
    (left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      second-transport second-coherence) =
  left-indexed-all-catchup
    (weak-indexed-result combined (canonicalIndexedResults indexed))
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)
    (weak-one-step-prepend-source-keep-transportᵀ
      source→ second second-transport)
    (weak-one-step-prepend-source-keep-type-coherenceᵀ
      source→ second second-coherence)
  where
  second = weakIndexedResult indexed
  combined = weak-one-step-prepend-source-keepᵀ source→ second

left-catchup-indexed-all-prefix-prepend-keepᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ C C′ q}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (source→ : M —→[ keep ] N) →
  (N⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ N ⦂ `∀ C →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ V′ ⦂ `∀ C′ →
  LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ⁺} q →
  LeftCatchupIndexedAllResult
    {N = M} {V′ = V′} {ρ = ρ⁺} q
left-catchup-indexed-all-prefix-prepend-keepᵀ
    prefix source→ N⊑V′ N⊢ V′⊢ catchup =
  left-catchup-indexed-all-prepend-keepᵀ source→
    (allocation-prefixᵀ prefix N⊑V′ N⊢ V′⊢) catchup

------------------------------------------------------------------------
-- Universal cast shapes used by source catch-up
------------------------------------------------------------------------

weak-one-step-source-cast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ M N′ A A′ χ) →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ (sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩)
      ⊑ targetResult inner
    ⦂ applyTys (sourceChanges inner) B
      ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
    ∶ transportType inner q) →
  WeakOneStepResult ρ (M ⟨ c ⟩) N′ B B′ χ
weak-one-step-source-cast-frameᵀ
    {B = B} {B′ = B′} {c = c} {χ = χ} inner result =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult =
        sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩
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
    ; resultType = transportType inner _
    ; sourceCatchup = cast-↠ (sourceCatchup inner)
    ; targetTail = targetTail inner
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = result
    }

weak-one-step-source-cast-frame-silentᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ keep)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ (sourceResult inner ⟨
          applyCoercions (sourceChanges inner) c ⟩)
        ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy keep B′)
      ∶ transportType inner q) →
  LeftSilentInvariant inner →
  LeftSilentInvariant
    (weak-one-step-source-cast-frameᵀ inner result)
weak-one-step-source-cast-frame-silentᵀ
    inner result (left-silent-invariant refl refl) =
  left-silent-invariant refl refl

weak-one-step-source-cast-frame-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ (sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩)
        ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTransport inner →
  WeakOneStepTransport
    (weak-one-step-source-cast-frameᵀ inner result)
weak-one-step-source-cast-frame-transportᵀ
    inner result transport =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-source-cast-frame-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ (sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩)
        ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepTypeCoherence
    (weak-one-step-source-cast-frameᵀ inner result)
weak-one-step-source-cast-frame-coherenceᵀ
    inner result coherence =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)

weak-one-step-target-cast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ M N′ A A′ χ) →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ sourceResult inner ⊑
      (targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion χ c) ⟩)
    ⦂ applyTys (sourceChanges inner) A
      ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
    ∶ transportType inner q) →
  WeakOneStepResult ρ M (N′ ⟨ applyCoercion χ c ⟩) A B′ χ
weak-one-step-target-cast-frameᵀ
    {A = A} {B′ = B′} {c = c} {χ = χ} inner result =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult = sourceResult inner
    ; targetResult =
        targetResult inner ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ c) ⟩
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) A
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; resultType = transportType inner _
    ; sourceCatchup = sourceCatchup inner
    ; targetTail = cast-↠ (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = result
    }

weak-one-step-target-cast-frame-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑
        (targetResult inner ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ c) ⟩)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTransport inner →
  WeakOneStepTransport
    (weak-one-step-target-cast-frameᵀ inner result)
weak-one-step-target-cast-frame-transportᵀ
    inner result transport =
  weak-step-transport (transportNo•Terms transport)

weak-one-step-target-cast-frame-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ sourceResult inner ⊑
        (targetResult inner ⟨
          applyCoercions (targetTailChanges inner)
            (applyCoercion χ c) ⟩)
      ⦂ applyTys (sourceChanges inner) A
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepTypeCoherence
    (weak-one-step-target-cast-frameᵀ inner result)
weak-one-step-target-cast-frame-coherenceᵀ
    inner result coherence =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)

weak-one-step-source-narrow-cast-indexed-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
  WeakOneStepIndexedResult
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-narrow-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊒ indexed
    with apply-narrows-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ c⊒
weak-one-step-source-narrow-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊒ indexed
    | μ′ , mode′ , seal★′ , c′⊒ =
  weak-indexed-result framed (relatedResults framed)
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) _
          ⊒ applyTys (sourceChanges inner) B
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) _
            ⊒ applyTys (sourceChanges inner) B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) _
              ⊒ applyTys (sourceChanges inner) B)
        (sym (sourceStoreResult inner)) c′⊒)

  final-relation =
    cast⊒⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation

weak-one-step-source-widen-cast-indexed-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
  WeakOneStepIndexedResult
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-widen-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊑ indexed
    with apply-widens-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ c⊑
weak-one-step-source-widen-cast-indexed-frameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊑ indexed
    | μ′ , mode′ , seal★′ , c′⊑ =
  weak-indexed-result framed (relatedResults framed)
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) _
          ⊑ applyTys (sourceChanges inner) B
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) _
            ⊑ applyTys (sourceChanges inner) B)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) _
              ⊑ applyTys (sourceChanges inner) B)
        (sym (sourceStoreResult inner)) c′⊑)

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation

narrow-all-to-all-inert :
  ∀ {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ `∀ A ⊒ `∀ B →
  C.Inert c
narrow-all-to-all-inert
    (C.cast-id hA ok , NW.cross ())
narrow-all-to-all-inert
    (C.cast-seq () t⊢ , G NW.？︔ gⁿ)
narrow-all-to-all-inert
    (C.cast-seq s⊢ () , n NW.︔seal α)
narrow-all-to-all-inert
    (C.cast-all c⊢ , NW.cross (NW.`∀ cⁿ)) =
  C.`∀ _
narrow-all-to-all-inert
    (C.cast-inst hB occ c⊢ , NW.cross ())
narrow-all-to-all-inert
    (C.cast-gen hA occ c⊢ , NW.gen cⁿ) =
  C.gen _ _

widen-all-to-all-shape :
  ∀ {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ `∀ A ⊑ `∀ B →
  C.Inert c ⊎ ∃[ s ] c ≡ inst (`∀ B) s
widen-all-to-all-shape
    (C.cast-id hA ok , NW.cross ())
widen-all-to-all-shape
    (C.cast-seq s⊢ () , gʷ NW.︔ G !)
widen-all-to-all-shape
    (C.cast-seq () t⊢ , NW.unseal︔_ α w)
widen-all-to-all-shape
    (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ)) =
  inj₁ (C.`∀ _)
widen-all-to-all-shape
    (C.cast-inst hB occ c⊢ , NW.inst cʷ) =
  inj₂ (_ , refl)
widen-all-to-all-shape
    (C.cast-gen hA occ c⊢ , NW.cross ())

reveal-all-to-all-inert :
  ∀ {μ Δ Σ α X c A B} →
  RevealConversion μ Δ Σ α X c (`∀ A) (`∀ B) →
  C.Inert c
reveal-all-to-all-inert (reveal-all c↑) = C.`∀ _

conceal-all-to-all-inert :
  ∀ {μ Δ Σ α X c A B} →
  ConcealConversion μ Δ Σ α X c (`∀ A) (`∀ B) →
  C.Inert c
conceal-all-to-all-inert (conceal-all c↓) = C.`∀ _

left-catchup-indexed-all-source-cast-blame-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M L V′ A A′ C C′ ρ d}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  (framed : WeakOneStepIndexedResult
    {M = L} {N′ = V′} {χ = keep} {ρ = ρ} (∀ⁱ r)) →
  let inner = weakIndexedResult (catchupIndexedResult catchup)
      first = weakIndexedResult framed
  in
  sourceResult first ≡ sourceResult inner ⟨ d ⟩ →
  LeftSilentInvariant first →
  WeakOneStepTransport first →
  WeakOneStepTypeCoherence first →
  sourceResult inner ≡ blame →
  LeftCatchupIndexedAllResult
    {N = L} {V′ = V′} {ρ = ρ} r
left-catchup-indexed-all-source-cast-blame-frameᵀ
    {r = r}
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    framed refl (left-silent-invariant refl refl)
    first-transport first-coherence refl =
  left-indexed-all-catchup
    (weak-one-step-index-resultᵀ combined type-eq)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₂ refl))
    combined-transport combined-coherence
  where
  first-raw = weakIndexedResult framed

  first = weak-one-step-reindexᵀ
    first-raw refl refl (canonicalIndexedResults framed)

  first-transport′ =
    weak-one-step-reindex-preserves-transportᵀ
      first-raw refl refl (canonicalIndexedResults framed)
      first-transport

  first-coherence′ =
    weak-one-step-reindex-preserves-type-coherenceᵀ
      first-raw refl refl (canonicalIndexedResults framed)
      first-coherence

  target⊢ =
    nu-term-imprecision-target-typing (relatedResults first)

  second-relation :
    resultCtx first
      ∣ resultLeftCtx first
      ∣ resultRightCtx first
      ∣ resultStore first ∣ []
      ⊢ᴺ blame ⊑ targetResult first
      ⦂ resultSourceType first ⊑ resultTargetType first
      ∶ resultType first
  second-relation = blame⊑ᵀ target⊢

  second = weak-one-step-keep-source-catchupᵀ
    {Φ = resultCtx first}
    {Δᴸ = resultLeftCtx first}
    {Δᴿ = resultRightCtx first}
    {A = resultSourceType first}
    {B = resultTargetType first}
    {p = resultType first}
    {ρ = resultStore first}
    (pure-step blame-⟨⟩) second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first (left-silent-invariant refl refl)) second

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second (∀ⁱ r))))

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      first-transport′
      (weak-one-step-keep-source-catchup-transportᵀ
        (pure-step blame-⟨⟩) second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      first-coherence′
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (pure-step blame-⟨⟩) second-relation)

left-catchup-indexed-all-source-inert-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M L V′ A A′ C C′ ρ d}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  C.Inert d →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  (framed : WeakOneStepIndexedResult
    {M = L} {N′ = V′} {χ = keep} {ρ = ρ} (∀ⁱ r)) →
  let inner = weakIndexedResult
        (catchupIndexedResult catchup)
      first = weakIndexedResult framed
  in
  sourceResult first ≡ sourceResult inner ⟨ d ⟩ →
  LeftSilentInvariant first →
  WeakOneStepTransport first →
  WeakOneStepTypeCoherence first →
  LeftCatchupIndexedAllResult
    {N = L} {V′ = V′} {ρ = ρ} r
left-catchup-indexed-all-source-inert-frameᵀ
    inert
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence
    with final
left-catchup-indexed-all-source-inert-frameᵀ
    inert
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence
    | inj₁ (vW , noW) =
  left-indexed-all-catchup framed
    (left-catchup-invariant first-silent
      (inj₁ (vW ⟨ inert ⟩ , no•-⟨⟩ noW)))
    first-transport first-coherence
left-catchup-indexed-all-source-inert-frameᵀ
    {r = r}
    inert
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence
    | inj₂ refl =
  left-catchup-indexed-all-source-cast-blame-frameᵀ
    (left-indexed-catchup indexed
      (left-catchup-invariant inner-silent final)
      inner-transport inner-coherence)
    framed refl first-silent
    first-transport first-coherence refl

left-catchup-indexed-all-source-narrow-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ `∀ A ⊒ `∀ B →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ} r
left-catchup-indexed-all-source-narrow-castᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊒
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    with apply-narrows-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ c⊒
left-catchup-indexed-all-source-narrow-castᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊒
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | μ′ , mode′ , seal★′ , c′⊒ =
  left-catchup-indexed-all-source-inert-frameᵀ
    (applyCoercions-preserves-Inert (sourceChanges inner)
      (narrow-all-to-all-inert c⊒))
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    framed refl
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation (left-silent-invariant refl refl))
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) (`∀ _)
          ⊒ applyTys (sourceChanges inner) (`∀ B)
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) (`∀ _)
            ⊒ applyTys (sourceChanges inner) (`∀ B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) (`∀ _)
              ⊒ applyTys (sourceChanges inner) (`∀ B))
        (sym (sourceStoreResult inner)) c′⊒)

  final-relation =
    cast⊒⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-all-prefix-source-narrow-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ `∀ A ⊒ `∀ B →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} r
left-catchup-indexed-all-prefix-source-narrow-castᵀ
    prefix mode seal★ c⊒ catchup =
  left-catchup-indexed-all-source-narrow-castᵀ mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) c⊒)
    catchup

left-catchup-indexed-all-source-widen-cast-inertᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ `∀ A ⊑ `∀ B →
  C.Inert c →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ} r
left-catchup-indexed-all-source-widen-cast-inertᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊑ inert
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    with apply-widens-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ c⊑
left-catchup-indexed-all-source-widen-cast-inertᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊑ inert
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    | μ′ , mode′ , seal★′ , c′⊑ =
  left-catchup-indexed-all-source-inert-frameᵀ
    (applyCoercions-preserves-Inert (sourceChanges inner) inert)
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    framed refl
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation (silentInvariant invariant))
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) (`∀ _)
          ⊑ applyTys (sourceChanges inner) (`∀ B)
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) (`∀ _)
            ⊑ applyTys (sourceChanges inner) (`∀ B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) (`∀ _)
              ⊑ applyTys (sourceChanges inner) (`∀ B))
        (sym (sourceStoreResult inner)) c′⊑)

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-all-source-widen-cast-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ `∀ A ⊑ `∀ B →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  sourceResult (weakIndexedResult (catchupIndexedResult catchup))
    ≡ blame →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ} r
left-catchup-indexed-all-source-widen-cast-blameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊑
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    eq-blame
    with apply-widens-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ c⊑
left-catchup-indexed-all-source-widen-cast-blameᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} mode seal★ c⊑
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    eq-blame
    | μ′ , mode′ , seal★′ , c′⊑ =
  left-catchup-indexed-all-source-cast-blame-frameᵀ
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    framed refl
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation (silentInvariant invariant))
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
    eq-blame
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) (`∀ _)
          ⊑ applyTys (sourceChanges inner) (`∀ B)
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) (`∀ _)
            ⊑ applyTys (sourceChanges inner) (`∀ B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) (`∀ _)
              ⊑ applyTys (sourceChanges inner) (`∀ B))
        (sym (sourceStoreResult inner)) c′⊑)

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-all-prefix-source-widen-cast-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ `∀ A ⊑ `∀ B →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  sourceResult (weakIndexedResult (catchupIndexedResult catchup))
    ≡ blame →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} r
left-catchup-indexed-all-prefix-source-widen-cast-blameᵀ
    prefix mode seal★ c⊑ catchup eq-blame =
  left-catchup-indexed-all-source-widen-cast-blameᵀ mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) c⊑)
    catchup eq-blame

left-catchup-indexed-all-source-widen-cast-shapeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c⊑ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ c ∶ `∀ A ⊑ `∀ B) →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  LeftCatchupIndexedAllResult
      {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ} r
    ⊎ ∃[ s ] c ≡ inst (`∀ B) s
left-catchup-indexed-all-source-widen-cast-shapeᵀ
    mode seal★ c⊑ catchup
    with widen-all-to-all-shape c⊑
left-catchup-indexed-all-source-widen-cast-shapeᵀ
    mode seal★ c⊑ catchup | inj₁ inert =
  inj₁ (left-catchup-indexed-all-source-widen-cast-inertᵀ
    mode seal★ c⊑ inert catchup)
left-catchup-indexed-all-source-widen-cast-shapeᵀ
    mode seal★ c⊑ catchup | inj₂ shape =
  inj₂ shape

left-catchup-indexed-all-prefix-source-widen-cast-shapeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  (c⊑ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ c ∶ `∀ A ⊑ `∀ B) →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  LeftCatchupIndexedAllResult
      {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} r
    ⊎ ∃[ s ] c ≡ inst (`∀ B) s
left-catchup-indexed-all-prefix-source-widen-cast-shapeᵀ
    prefix mode seal★ c⊑ catchup
    with widen-all-to-all-shape c⊑
left-catchup-indexed-all-prefix-source-widen-cast-shapeᵀ
    prefix mode seal★ c⊑ catchup | inj₁ inert =
  inj₁ (left-catchup-indexed-all-source-widen-cast-inertᵀ
    mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) c⊑)
    inert catchup)
left-catchup-indexed-all-prefix-source-widen-cast-shapeᵀ
    prefix mode seal★ c⊑ catchup | inj₂ shape =
  inj₂ shape

left-silent-indexed-all-source-widen-inst-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ s}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ inst (`∀ B) s ∶ `∀ A ⊑ `∀ B →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  let inner = weakIndexedResult (catchupIndexedResult catchup) in
  Value (sourceResult inner) →
  No• (sourceResult inner) →
  LeftSilentIndexedResult
    {N = M ⟨ inst (`∀ B) s ⟩} {V′ = V′} {ρ = ρ} (∀ⁱ r)
left-silent-indexed-all-source-widen-inst-valueᵀ
    {Δᴸ = Δᴸ} {B = B} {s = s} mode seal★
    (C.cast-inst hB occ s⊢ , NW.inst sʷ)
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    vW noW
    with apply-widens-typing
      { χs = sourceChanges (weakIndexedResult indexed) }
      mode seal★ (C.cast-inst hB occ s⊢ , NW.inst sʷ)
left-silent-indexed-all-source-widen-inst-valueᵀ
    {Δᴸ = Δᴸ} {B = B} {s = s} mode seal★
    (C.cast-inst hB occ s⊢ , NW.inst sʷ)
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    vW noW
    | μ′ , mode′ , seal★′ , c′⊑ =
  left-silent-indexed
    (weak-one-step-index-resultᵀ combined type-eq)
    (left-silent-invariant refl refl)
    (ok-ν (ok-no noW))
    combined-transport combined-coherence
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner)
          (inst (`∀ B) s)
        ∶ applyTys (sourceChanges inner) (`∀ _)
          ⊑ applyTys (sourceChanges inner) (`∀ B)
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner)
            (inst (`∀ B) s)
          ∶ applyTys (sourceChanges inner) (`∀ _)
            ⊑ applyTys (sourceChanges inner) (`∀ B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner)
              (inst (`∀ B) s)
            ∶ applyTys (sourceChanges inner) (`∀ _)
              ⊑ applyTys (sourceChanges inner) (`∀ B))
        (sym (sourceStoreResult inner)) c′⊑)

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent = weak-one-step-source-cast-frame-silentᵀ
    inner final-relation (left-silent-invariant refl refl)

  ν-framed = weak-one-step-source-νcast-frameᵀ
    mode (seal★-inst seal★) (s⊢ , sʷ) (∀ⁱ _) inner

  second-relation :
    resultCtx first
      ∣ resultLeftCtx first
      ∣ resultRightCtx first
      ∣ resultStore first ∣ []
      ⊢ᴺ sourceResult ν-framed ⊑ targetResult first
      ⦂ resultSourceType first ⊑ resultTargetType first
      ∶ resultType first
  second-relation = relatedResults ν-framed

  second = weak-one-step-keep-source-catchupᵀ
    {Φ = resultCtx first}
    {Δᴸ = resultLeftCtx first}
    {Δᴿ = resultRightCtx first}
    {A = resultSourceType first}
    {B = resultTargetType first}
    {p = resultType first}
    {ρ = resultStore first}
    (post-catchup-β-inst (sourceChanges inner) vW)
    second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second (∀ⁱ _))))

  first-transport = weak-one-step-source-cast-frame-transportᵀ
    inner final-relation inner-transport

  first-coherence = weak-one-step-source-cast-frame-coherenceᵀ
    inner final-relation inner-coherence

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-inst (sourceChanges inner) vW)
        second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-inst (sourceChanges inner) vW)
        second-relation)

left-silent-indexed-all-prefix-source-widen-inst-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ s}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ inst (`∀ B) s ∶ `∀ A ⊑ `∀ B →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  let inner = weakIndexedResult (catchupIndexedResult catchup) in
  Value (sourceResult inner) →
  No• (sourceResult inner) →
  LeftSilentIndexedResult
    {N = M ⟨ inst (`∀ B) s ⟩} {V′ = V′} {ρ = ρ⁺} (∀ⁱ r)
left-silent-indexed-all-prefix-source-widen-inst-valueᵀ
    prefix mode seal★ c⊑ catchup vW noW =
  left-silent-indexed-all-source-widen-inst-valueᵀ mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) c⊑)
    catchup vW noW

left-catchup-indexed-all-source-widen-cast-progressᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c⊑ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ c ∶ `∀ A ⊑ `∀ B) →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  LeftCatchupIndexedProgress
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ} (∀ⁱ r)
left-catchup-indexed-all-source-widen-cast-progressᵀ
    mode seal★ c⊑
    (left-indexed-catchup indexed
      (left-catchup-invariant (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    with final
left-catchup-indexed-all-source-widen-cast-progressᵀ
    mode seal★ c⊑
    (left-indexed-catchup indexed
      (left-catchup-invariant (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₁ (vW , noW)
    with widen-all-to-all-shape c⊑
left-catchup-indexed-all-source-widen-cast-progressᵀ
    mode seal★ c⊑
    (left-indexed-catchup indexed
      (left-catchup-invariant (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₁ (vW , noW) | inj₁ inert =
  left-progress-done
    (generalize-left-indexed-all-catchup
      (left-catchup-indexed-all-source-widen-cast-inertᵀ
        mode seal★ c⊑ inert
        (left-indexed-catchup indexed
          (left-catchup-invariant (left-silent-invariant refl refl) final)
          inner-transport inner-coherence)))
left-catchup-indexed-all-source-widen-cast-progressᵀ
    mode seal★ c⊑
    (left-indexed-catchup indexed
      (left-catchup-invariant (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₁ (vW , noW) | inj₂ (s , refl) =
  left-progress-continue
    (left-silent-indexed-all-source-widen-inst-valueᵀ
      mode seal★ c⊑
      (left-indexed-catchup indexed
        (left-catchup-invariant (left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      vW noW)
left-catchup-indexed-all-source-widen-cast-progressᵀ
    mode seal★ c⊑
    (left-indexed-catchup indexed
      (left-catchup-invariant (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₂ eq-blame =
  left-progress-done
    (generalize-left-indexed-all-catchup
      (left-catchup-indexed-all-source-widen-cast-blameᵀ
        mode seal★ c⊑
        (left-indexed-catchup indexed
          (left-catchup-invariant (left-silent-invariant refl refl) final)
          inner-transport inner-coherence)
        eq-blame))

left-catchup-indexed-all-prefix-source-widen-cast-progressᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  (c⊑ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ c ∶ `∀ A ⊑ `∀ B) →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p) →
  LeftCatchupIndexedProgress
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} (∀ⁱ r)
left-catchup-indexed-all-prefix-source-widen-cast-progressᵀ
    prefix mode seal★ c⊑ catchup =
  left-catchup-indexed-all-source-widen-cast-progressᵀ mode
    (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) c⊑)
    catchup

left-catchup-indexed-all-source-reveal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ α X c}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    c (`∀ A) (`∀ B) →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ} r
left-catchup-indexed-all-source-reveal-castᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} c↑
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    with apply-reveal-conversions
      { χs = sourceChanges (weakIndexedResult indexed) } c↑
left-catchup-indexed-all-source-reveal-castᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} c↑
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    | μ′ , α′ , X′ , c′↑ =
  left-catchup-indexed-all-source-inert-frameᵀ
    (applyCoercions-preserves-Inert (sourceChanges inner)
      (reveal-all-to-all-inert c↑))
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    framed refl
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation (silentInvariant invariant))
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  final-conversion :
    RevealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) (`∀ _))
      (applyTys (sourceChanges inner) (`∀ B))
  final-conversion =
    subst
      (λ Δ → RevealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner)) α′ X′
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) (`∀ _))
        (applyTys (sourceChanges inner) (`∀ B)))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ α′ X′
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) (`∀ _))
          (applyTys (sourceChanges inner) (`∀ B)))
        (sym (sourceStoreResult inner)) c′↑)

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-all-prefix-source-reveal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ α X c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X
    c (`∀ A) (`∀ B) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} r
left-catchup-indexed-all-prefix-source-reveal-castᵀ
    prefix c↑ catchup =
  left-catchup-indexed-all-source-reveal-castᵀ
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↑)
    catchup

left-catchup-indexed-all-source-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ α X c}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    c (`∀ A) (`∀ B) →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ} r
left-catchup-indexed-all-source-conceal-castᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} c↓
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    with apply-conceal-conversions
      { χs = sourceChanges (weakIndexedResult indexed) } c↓
left-catchup-indexed-all-source-conceal-castᵀ
    {Δᴸ = Δᴸ} {B = B} {c = c} c↓
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    | μ′ , α′ , X′ , c′↓ =
  left-catchup-indexed-all-source-inert-frameᵀ
    (applyCoercions-preserves-Inert (sourceChanges inner)
      (conceal-all-to-all-inert c↓))
    (left-indexed-catchup indexed invariant
      inner-transport inner-coherence)
    framed refl
      (weak-one-step-source-cast-frame-silentᵀ
        inner final-relation (silentInvariant invariant))
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation inner-transport)
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation inner-coherence)
  where
  inner = weakIndexedResult indexed

  final-conversion :
    ConcealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) (`∀ _))
      (applyTys (sourceChanges inner) (`∀ B))
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner)) α′ X′
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) (`∀ _))
        (applyTys (sourceChanges inner) (`∀ B)))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ α′ X′
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) (`∀ _))
          (applyTys (sourceChanges inner) (`∀ B)))
        (sym (sourceStoreResult inner)) c′↓)

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner _)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)

left-catchup-indexed-all-prefix-source-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B μ α X c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ `∀ A′ ⊣ Δᴿ}
    {r : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X
    c (`∀ A) (`∀ B) →
  LeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  LeftCatchupIndexedAllResult
    {N = M ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} r
left-catchup-indexed-all-prefix-source-conceal-castᵀ
    prefix c↓ catchup =
  left-catchup-indexed-all-source-conceal-castᵀ
    (weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) c↓)
    catchup

left-catchup-all-post-allocation-β-Λ•ᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  No• V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult
    {N = (⇑ᵗᵐ (Λ V)) •} {V′ = V′} {ρ = ρ} q
left-catchup-all-post-allocation-β-Λ•ᵀ vV noV V⊑V′ =
  left-catchup-all-keep-stepᵀ
    (post-allocation-β-Λ•-bare vV) (inj₁ (vV , noV)) V⊑V′

left-catchup-indexed-all-post-allocation-β-Λ•ᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  No• V →
  (V⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (Λ V)) •} {V′ = V′} {ρ = ρ} q
left-catchup-indexed-all-post-allocation-β-Λ•ᵀ
    vV noV V⊑V′ =
  left-catchup-indexed-all-keep-stepᵀ
    (post-allocation-β-Λ•-bare vV) (inj₁ (vV , noV)) V⊑V′

left-catchup-indexed-all-prefix-post-allocation-β-Λ•ᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ C C′ q}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  (vV : Value V) →
  (noV : No• V) →
  (noV′ : No• V′) →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (V⊑V′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (Λ V)) •} {V′ = V′} {ρ = ρ⁺} q
left-catchup-indexed-all-prefix-post-allocation-β-Λ•ᵀ
    vV noV noV′ prefix V⊑V′ =
  left-catchup-indexed-all-prefix-prepend-keepᵀ
    prefix (post-allocation-β-Λ•-bare vV) V⊑V′
    V⊢ V′⊢
    (left-catchup-indexed-all-prefix-relatedᵀ
      prefix (inj₁ (vV , noV)) V⊑V′ V⊢ V′⊢)
  where
  V⊢ = term-weaken ≤-refl
    (leftStoreⁱ-prefix-inclusion prefix) noV
    (nu-term-imprecision-source-typing V⊑V′)
  V′⊢ = term-weaken ≤-refl
    (rightStoreⁱ-prefix-inclusion prefix) noV′
    (nu-term-imprecision-target-typing V⊑V′)

left-catchup-all-α-Λᵀ :
  ∀ {Φ Δᴸ Δᴿ A W V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  Value W →
  No• W →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵃ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵇ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupAllResult
    {N = (⇑ᵗᵐ (Λ W)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρᵃ} q
left-catchup-all-α-Λᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {W = W} {V′ = V′}
    {C = C} {C′ = C′} {q = q} {ρ = ρ} {ρᵃ = ρᵃ} {ρᵇ = ρᵇ}
    vW noW h⇑A liftρᵃ liftρᵇ W⊑V′ =
  left-all-catchup
    (weak-all-result result allocated-body)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₁ (vW , noW)))
  where
    allocated-body =
      allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) W⊑V′
        (term-weaken {Δ = suc _} {Δ′ = suc _}
          {Σ = leftStoreⁱ ρᵇ}
          {Σ′ = (zero , ⇑ᵗ A) ∷ leftStoreⁱ ρᵇ}
          {Γ = []} ≤-refl StoreIncl-drop noW
          (nu-term-imprecision-source-typing W⊑V′))
        (nu-term-imprecision-target-typing W⊑V′)

    result =
      record
        { sourceChanges = keep ∷ []
        ; targetTailChanges = []
        ; sourceResult = W
        ; targetResult = V′
        ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ _
        ; resultLeftCtx = _
        ; resultRightCtx = _
        ; sourceCtxResult = refl
        ; targetCtxResult = refl
        ; resultStore = store-left zero (⇑ᵗ A) h⇑A ∷ ρᵇ
        ; resultSourceType = `∀ _
        ; resultTargetType = `∀ _
        ; sourceTypeResult = refl
        ; targetTypeResult = refl
        ; transportType = λ p → p
        ; transportAllBody = λ p → p
        ; transportRightBody = λ p → p
        ; resultType = ∀ⁱ q
        ; sourceCatchup =
            ↠-step (post-allocation-β-Λ•-bare vW) ↠-refl
        ; targetTail = ↠-refl
        ; sourceStoreResult =
            cong ((zero , ⇑ᵗ A) ∷_)
              (trans (leftStoreⁱ-lift-left liftρᵇ)
                (sym (leftStoreⁱ-lift-left liftρᵃ)))
        ; targetStoreResult =
            trans (rightStoreⁱ-lift-left liftρᵇ)
              (sym (rightStoreⁱ-lift-left liftρᵃ))
        ; relatedResults = allocated-body
        }

left-catchup-indexed-all-α-Λᵀ :
  ∀ {Φ Δᴸ Δᴿ A W V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  Value W →
  No• W →
  No• V′ →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  (liftρᵃ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵃ) →
  (liftρᵇ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵇ) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (Λ W)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρᵃ} q
left-catchup-indexed-all-α-Λᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {W = W} {V′ = V′}
    {C = C} {C′ = C′} {q = q} {ρ = ρ} {ρᵃ = ρᵃ} {ρᵇ = ρᵇ}
    vW noW noV′ h⇑A liftρᵃ liftρᵇ W⊑V′ =
  left-indexed-all-catchup
    (weak-one-step-index-resultᵀ result refl)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₁ (vW , noW)))
    (weak-step-transport
      (paired-left-lift-prefix-bodyᵀ
        liftρᵃ liftρᵃ))
    (weak-step-type-coherence
      ⊑-rename-id-arrowᵢ ⊑-rename-id-allᵢ)
  where
  allocated-body =
    allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) W⊑V′
      (term-weaken {Δ = suc Δᴸ} {Δ′ = suc Δᴸ}
        {Σ = leftStoreⁱ ρᵇ}
        {Σ′ = (zero , ⇑ᵗ A) ∷ leftStoreⁱ ρᵇ}
        {Γ = []} ≤-refl StoreIncl-drop noW
        (nu-term-imprecision-source-typing W⊑V′))
      (nu-term-imprecision-target-typing W⊑V′)

  canonical-body =
    paired-left-lift-prefix-bodyᵀ
      liftρᵃ liftρᵇ noW noV′ allocated-body

  result =
    record
      { sourceChanges = keep ∷ []
      ; targetTailChanges = []
      ; sourceResult = W
      ; targetResult = V′
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ _
      ; resultLeftCtx = _
      ; resultRightCtx = _
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = store-left zero (⇑ᵗ A) h⇑A ∷ _
      ; resultSourceType = `∀ _
      ; resultTargetType = `∀ _
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-rename-idᵢ
      ; transportAllBody = ⊑-rename-id-all-bodyᵢ
      ; transportRightBody = ⊑-rename-idᵢ
      ; resultType = ⊑-rename-idᵢ (∀ⁱ q)
      ; sourceCatchup =
          ↠-step (post-allocation-β-Λ•-bare vW) ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult = refl
      ; targetStoreResult = refl
      ; relatedResults = canonical-body
      }

left-catchup-indexed-prefix-α-Λᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν W V′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {ρ⁺ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  Value W →
  No• W →
  No• V′ →
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρᵃ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵃ) →
  (liftρᵇ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵇ) →
  (prefix : StoreImpPrefix
    (store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρᵃ) ρ⁺) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ B ∶ p →
  LeftCatchupIndexedResult
    {N = (⇑ᵗᵐ (Λ W)) •} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-prefix-α-Λᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Aν = Aν} {W = W} {V′ = V′}
    {A = A} {B = B} {p = p} {ρᵃ = ρᵃ} {ρᵇ = ρᵇ} {ρ⁺ = ρ⁺}
    vW noW noV′ h⇑Aν liftρᵃ liftρᵇ prefix W⊑V′ =
  left-indexed-catchup
    (weak-one-step-index-resultᵀ result refl)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₁ (vW , noW)))
    (weak-step-transport identity-bodyᵀ)
    (weak-step-type-coherence
      ⊑-rename-id-arrowᵢ ⊑-rename-id-allᵢ)
  where
  allocated-body =
    allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) W⊑V′
      (term-weaken {Δ = suc Δᴸ} {Δ′ = suc Δᴸ}
        {Σ = leftStoreⁱ ρᵇ}
        {Σ′ = (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρᵇ}
        {Γ = []} ≤-refl StoreIncl-drop noW
        (nu-term-imprecision-source-typing W⊑V′))
      (nu-term-imprecision-target-typing W⊑V′)

  canonical-body =
    paired-left-lift-prefix-bodyᵀ
      liftρᵃ liftρᵇ noW noV′ allocated-body

  prefixed-body =
    allocation-prefixᵀ prefix canonical-body
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        noW (nu-term-imprecision-source-typing canonical-body))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        noV′ (nu-term-imprecision-target-typing canonical-body))

  result =
    record
      { sourceChanges = keep ∷ []
      ; targetTailChanges = []
      ; sourceResult = W
      ; targetResult = V′
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
      ; resultLeftCtx = suc Δᴸ
      ; resultRightCtx = _
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = ρ⁺
      ; resultSourceType = A
      ; resultTargetType = B
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-rename-idᵢ
      ; transportAllBody = ⊑-rename-id-all-bodyᵢ
      ; transportRightBody = ⊑-rename-idᵢ
      ; resultType = ⊑-rename-idᵢ p
      ; sourceCatchup =
          ↠-step (post-allocation-β-Λ•-bare vW) ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult = refl
      ; targetStoreResult = refl
      ; relatedResults = prefixed-body
      }

left-catchup-indexed-all-prefix-α-Λᵀ :
  ∀ {Φ Δᴸ Δᴿ A W V′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {ρ⁺ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  Value W →
  No• W →
  No• V′ →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  (liftρᵃ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵃ) →
  (liftρᵇ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵇ) →
  (prefix : StoreImpPrefix
    (store-left zero (⇑ᵗ A) h⇑A ∷ ρᵃ) ρ⁺) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (Λ W)) •} {V′ = V′} {ρ = ρ⁺} q
left-catchup-indexed-all-prefix-α-Λᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {A = A} {W = W} {V′ = V′}
    {q = q} {ρᵃ = ρᵃ} {ρᵇ = ρᵇ} {ρ⁺ = ρ⁺}
    vW noW noV′ h⇑A liftρᵃ liftρᵇ prefix W⊑V′ =
  left-indexed-all-catchup
    (weak-one-step-index-resultᵀ result refl)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₁ (vW , noW)))
    (weak-step-transport identity-bodyᵀ)
    (weak-step-type-coherence
      ⊑-rename-id-arrowᵢ ⊑-rename-id-allᵢ)
  where
  allocated-body =
    allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) W⊑V′
      (term-weaken {Δ = suc Δᴸ} {Δ′ = suc Δᴸ}
        {Σ = leftStoreⁱ ρᵇ}
        {Σ′ = (zero , ⇑ᵗ A) ∷ leftStoreⁱ ρᵇ}
        {Γ = []} ≤-refl StoreIncl-drop noW
        (nu-term-imprecision-source-typing W⊑V′))
      (nu-term-imprecision-target-typing W⊑V′)

  canonical-body =
    paired-left-lift-prefix-bodyᵀ
      liftρᵃ liftρᵇ noW noV′ allocated-body

  prefixed-body =
    allocation-prefixᵀ prefix canonical-body
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        noW (nu-term-imprecision-source-typing canonical-body))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        noV′ (nu-term-imprecision-target-typing canonical-body))

  result =
    record
      { sourceChanges = keep ∷ []
      ; targetTailChanges = []
      ; sourceResult = W
      ; targetResult = V′
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ _
      ; resultLeftCtx = _
      ; resultRightCtx = _
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = ρ⁺
      ; resultSourceType = `∀ _
      ; resultTargetType = `∀ _
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-rename-idᵢ
      ; transportAllBody = ⊑-rename-id-all-bodyᵢ
      ; transportRightBody = ⊑-rename-idᵢ
      ; resultType = ⊑-rename-idᵢ (∀ⁱ q)
      ; sourceCatchup =
          ↠-step (post-allocation-β-Λ•-bare vW) ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult = refl
      ; targetStoreResult = refl
      ; relatedResults = prefixed-body
      }

left-allocated-bulletᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν A B′ V V′ occ r}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ B′ ∶ ν occ r →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero (⇑ᵗ Aν) hAν ∷ ρ′ ∣ []
    ⊢ᴺ (⇑ᵗᵐ V) • ⊑ V′ ⦂ A ⊑ B′ ∶ r
left-allocated-bulletᵀ
    {Aν = Aν} {V = V} {V′ = V′} {r = r}
    vV noV hAν liftρ V⊑V′ =
  α⊑ᵀ vV noV hAν liftρ lift-left-ctx-[] V⊑V′
    left-bullet-typing right-typing
  where
    left-bullet-typing =
      subst
        (λ Σ → _ ∣ (zero , ⇑ᵗ Aν) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ V) • ⦂ _)
        (sym (leftStoreⁱ-lift-left liftρ))
        (⊢• refl refl (⊑-src-wf r) vV noV
          (nu-term-imprecision-source-typing V⊑V′))

    right-typing =
      subst
        (λ Σ → _ ∣ Σ ∣ [] ⊢ V′ ⦂ _)
        (sym (rightStoreⁱ-lift-left liftρ))
        (nu-term-imprecision-target-typing V⊑V′)

left-catchup-all-α-∀-revealᵀ :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ (`∀ C)) →
  (catchup : LeftCatchupAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q) →
  LeftCatchupAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-all-α-∀-revealᵀ
    {Aν = Aν} {V = V} {V′ = V′} {r = r} {q = q} {ρ′ = ρ′}
    vV noV hAν liftρ V⊑V′ c↑ catchup =
  left-catchup-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
    bullet-relation =
      left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

    post-relation =
      conv↑⊑ᵀ (open-allocated-left-all-reveal liftρ c↑)
        bullet-relation (∀ⁱ q)

left-catchup-all-α-∀-concealᵀ :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ (`∀ C)) →
  (catchup : LeftCatchupAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q) →
  LeftCatchupAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-all-α-∀-concealᵀ
    {Aν = Aν} {V = V} {V′ = V′} {q = q} {ρ′ = ρ′}
    vV noV hAν liftρ V⊑V′ c↓ catchup =
  left-catchup-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
    bullet-relation =
      left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

    post-relation =
      conv↓⊑ᵀ (open-allocated-left-all-conceal liftρ c↓)
        bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-∀-revealᵀ :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ (`∀ C)) →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-revealᵀ
    {V = V} {q = q}
    vV noV hAν liftρ V⊑V′ c↑ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  post-relation =
    conv↑⊑ᵀ (open-allocated-left-all-reveal liftρ c↑)
      bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-∀-concealᵀ :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ (`∀ C)) →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-concealᵀ
    {V = V} {q = q}
    vV noV hAν liftρ V⊑V′ c↓ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  post-relation =
    conv↓⊑ᵀ (open-allocated-left-all-conceal liftρ c↓)
      bullet-relation (∀ⁱ q)

left-catchup-all-α-∀-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ (`∀ C) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  (catchup : LeftCatchupAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q) →
  LeftCatchupAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-all-α-∀-narrowingᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {V′ = V′} {q = q} {ρ = ρ} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ c∀⊒ V⊑V′ catchup =
  left-catchup-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
    bullet-relation =
      left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

    body-narrowing :
      extᵈ μ ∣ suc Δᴸ ∣
        (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
        ⊢ c ∶ A ⊒ `∀ C
    body-narrowing =
      subst
        (λ Σ → extᵈ μ ∣ suc Δᴸ ∣ Σ
          ⊢ c ∶ A ⊒ `∀ C)
        (cong ((zero , ⇑ᵗ Aν) ∷_)
          (sym (leftStoreⁱ-lift-left liftρ)))
        (allocate-all-narrowing c∀⊒)

    post-relation =
      cast⊒⊑ᵀ (cast-ext mode)
        (allocated-left-seal★ liftρ seal★)
        body-narrowing bullet-relation (∀ⁱ q)

left-catchup-all-α-∀-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ (`∀ C) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  (catchup : LeftCatchupAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q) →
  LeftCatchupAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-all-α-∀-wideningᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {V′ = V′} {q = q} {ρ = ρ} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ c∀⊑ V⊑V′ catchup =
  left-catchup-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
    bullet-relation =
      left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

    body-widening :
      extᵈ μ ∣ suc Δᴸ ∣
        (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
        ⊢ c ∶ A ⊑ `∀ C
    body-widening =
      subst
        (λ Σ → extᵈ μ ∣ suc Δᴸ ∣ Σ
          ⊢ c ∶ A ⊑ `∀ C)
        (cong ((zero , ⇑ᵗ Aν) ∷_)
          (sym (leftStoreⁱ-lift-left liftρ)))
        (allocate-all-widening c∀⊑)

    post-relation =
      cast⊑⊑ᵀ (cast-ext mode)
        (allocated-left-seal★ liftρ seal★)
        body-widening bullet-relation (∀ⁱ q)

left-catchup-all-α-gen-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ p q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ gen A c ∶ A ⊒ `∀ (`∀ C) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ []
    ⊢ᴺ ⇑ᵗᵐ V ⊑ V′ ⦂ ⇑ᵗ A ⊑ `∀ C′ ∶ p →
  (catchup : LeftCatchupAllResult
    {N = (⇑ᵗᵐ V) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q) →
  LeftCatchupAllResult
    {N = (⇑ᵗᵐ (V ⟨ gen A c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-all-α-gen-narrowingᵀ
    {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {q = q} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ cgen⊒ shifted-body catchup =
  left-catchup-all-prepend-keepᵀ
    (post-allocation-β-gen•-bare vV) post-relation catchup
  where
    body-narrowing :
      genᵈ μ ∣ suc Δᴸ ∣
        (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
        ⊢ c ∶ ⇑ᵗ A ⊒ `∀ C
    body-narrowing =
      subst
        (λ Σ → genᵈ μ ∣ suc Δᴸ ∣ Σ
          ⊢ c ∶ ⇑ᵗ A ⊒ `∀ C)
        (cong ((zero , ⇑ᵗ Aν) ∷_)
          (sym (leftStoreⁱ-lift-left liftρ)))
        (allocate-gen-narrowing cgen⊒)

    body-relation =
      allocated-left-relationᵀ hAν liftρ
        (renameᵗᵐ-preserves-No• suc noV) shifted-body

    post-relation =
      cast⊒⊑ᵀ (cast-gen mode)
        (allocated-left-gen-seal★ liftρ seal★)
        body-narrowing body-relation (∀ⁱ q)

left-catchup-indexed-all-α-∀-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ (`∀ C) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-narrowingᵀ
    {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {q = q} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ c∀⊒ V⊑V′ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  body-narrowing :
    extᵈ μ ∣ suc Δᴸ ∣
      (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
      ⊢ c ∶ A ⊒ `∀ C
  body-narrowing =
    subst
      (λ Σ → extᵈ μ ∣ suc Δᴸ ∣ Σ
        ⊢ c ∶ A ⊒ `∀ C)
      (cong ((zero , ⇑ᵗ Aν) ∷_)
        (sym (leftStoreⁱ-lift-left liftρ)))
      (allocate-all-narrowing c∀⊒)

  post-relation =
    cast⊒⊑ᵀ (cast-ext mode)
      (allocated-left-seal★ liftρ seal★)
      body-narrowing bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-∀-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ occ r q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ (`∀ C) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν occ r →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-wideningᵀ
    {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {q = q} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ c∀⊑ V⊑V′ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  body-widening :
    extᵈ μ ∣ suc Δᴸ ∣
      (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
      ⊢ c ∶ A ⊑ `∀ C
  body-widening =
    subst
      (λ Σ → extᵈ μ ∣ suc Δᴸ ∣ Σ
        ⊢ c ∶ A ⊑ `∀ C)
      (cong ((zero , ⇑ᵗ Aν) ∷_)
        (sym (leftStoreⁱ-lift-left liftρ)))
      (allocate-all-widening c∀⊑)

  post-relation =
    cast⊑⊑ᵀ (cast-ext mode)
      (allocated-left-seal★ liftρ seal★)
      body-widening bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-gen-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ p q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ gen A c ∶ A ⊒ `∀ (`∀ C) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ []
    ⊢ᴺ ⇑ᵗᵐ V ⊑ V′ ⦂ ⇑ᵗ A ⊑ `∀ C′ ∶ p →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ V) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ gen A c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-gen-narrowingᵀ
    {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {q = q} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ cgen⊒ shifted-body catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-gen•-bare vV) post-relation catchup
  where
  body-narrowing :
    genᵈ μ ∣ suc Δᴸ ∣
      (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
      ⊢ c ∶ ⇑ᵗ A ⊒ `∀ C
  body-narrowing =
    subst
      (λ Σ → genᵈ μ ∣ suc Δᴸ ∣ Σ
        ⊢ c ∶ ⇑ᵗ A ⊒ `∀ C)
      (cong ((zero , ⇑ᵗ Aν) ∷_)
        (sym (leftStoreⁱ-lift-left liftρ)))
      (allocate-gen-narrowing cgen⊒)

  body-relation =
    allocated-left-relationᵀ hAν liftρ
      (renameᵗᵐ-preserves-No• suc noV) shifted-body

  post-relation =
    cast⊒⊑ᵀ (cast-gen mode)
      (allocated-left-gen-seal★ liftρ seal★)
      body-narrowing body-relation (∀ⁱ q)

shifted-var-not-wf-at-zero :
  WfTy zero (＇ (suc zero)) → ⊥
shifted-var-not-wf-at-zero (wfVar ())

fresh-shifted-var-store-not-det :
  StoreDetWf (suc (suc zero))
    ((zero , ＇ (suc zero)) ∷ []) → ⊥
fresh-shifted-var-store-not-det wfΣ =
  shifted-var-not-wf-at-zero
    (StoreDetWf.wfOlder wfΣ (here refl))

-- The same generic overlap with the right cast outermost.

weak-one-step-generic-β-∀-right-outer-narrowing-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c∀⊒ : μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ B) →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊒ `∀ B′ →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  (qL : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  (q : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-right-outer-narrowing-narrowingᵀ
    vV vV′ mode seal★ c∀⊒ mode′ seal★′ c′∀⊒
    V•⊑V′• qL q
    with left-β-∀-narrowingᵀ
      vV mode seal★ c∀⊒ V•⊑V′• qL
weak-one-step-generic-β-∀-right-outer-narrowing-narrowingᵀ
    vV vV′ mode seal★ c∀⊒ mode′ seal★′ c′∀⊒
    V•⊑V′• qL q
    | source→ , _ , V•c⊑V′•
    with right-β-∀-narrowingᵀ
      vV′ mode′ seal★′ c′∀⊒ V•c⊑V′• q
weak-one-step-generic-β-∀-right-outer-narrowing-narrowingᵀ
    vV vV′ mode seal★ c∀⊒ mode′ seal★′ c′∀⊒
    V•⊑V′• qL q
    | source→ , _ , V•c⊑V′•
    | _ , _ , result =
  weak-one-step-keep-source-catchupᵀ source→ result

weak-one-step-generic-β-∀-right-outer-narrowing-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (c∀⊒ : μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ B) →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf (suc Δᴿ) (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ (suc Δᴿ) Φ) →
  (c′∀⊑ : μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊑ `∀ B′) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  (qL : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-right-outer-narrowing-wideningᵀ
    vV vV′ mode seal★ c∀⊒ mode′ wfΣ′ seal★′
    okΦ′ c′∀⊑ V•⊑V′• qL
    with left-β-∀-narrowingᵀ
      vV mode seal★ c∀⊒ V•⊑V′• qL
weak-one-step-generic-β-∀-right-outer-narrowing-wideningᵀ
    vV vV′ mode seal★ c∀⊒ mode′ wfΣ′ seal★′
    okΦ′ c′∀⊑ V•⊑V′• qL
    | source→ , _ , V•c⊑V′•
    with right-β-∀-wideningᵀ
      vV′ mode′ wfΣ′ seal★′ okΦ′ c′∀⊑ V•c⊑V′•
weak-one-step-generic-β-∀-right-outer-narrowing-wideningᵀ
    vV vV′ mode seal★ c∀⊒ mode′ wfΣ′ seal★′
    okΦ′ c′∀⊑ V•⊑V′• qL
    | source→ , _ , V•c⊑V′•
    | _ , _ , result =
  weak-one-step-keep-source-catchupᵀ source→ result

weak-one-step-generic-β-∀-right-outer-widening-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊒ `∀ B′ →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ⊣ suc Δᴿ →
  (q : Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ B′ [ zero ]ᴿ ⊣ suc Δᴿ) →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-right-outer-widening-narrowingᵀ
    vV vV′ mode seal★ c∀⊑ mode′ seal★′ c′∀⊒
    V•⊑V′• qL q
    with left-β-∀-wideningᵀ
      vV mode seal★ c∀⊑ V•⊑V′• qL
weak-one-step-generic-β-∀-right-outer-widening-narrowingᵀ
    vV vV′ mode seal★ c∀⊑ mode′ seal★′ c′∀⊒
    V•⊑V′• qL q
    | source→ , _ , V•c⊑V′•
    with right-β-∀-narrowingᵀ
      vV′ mode′ seal★′ c′∀⊒ V•c⊑V′• q
weak-one-step-generic-β-∀-right-outer-widening-narrowingᵀ
    vV vV′ mode seal★ c∀⊑ mode′ seal★′ c′∀⊒
    V•⊑V′• qL q
    | source→ , _ , V•c⊑V′•
    | _ , _ , result =
  weak-one-step-keep-source-catchupᵀ source→ result

weak-one-step-generic-β-∀-right-outer-widening-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ μ′ c c′ A A′ B B′ V V′ p}
    {ρ : StoreImp Φ (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ suc Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  CastMode μ′ →
  (wfΣ′ : StoreDetWf (suc Δᴿ) (rightStoreⁱ ρ)) →
  (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ)) →
  (okΦ′ : RightCastCtxCompatible μ′ (suc Δᴿ) Φ) →
  (c′∀⊑ : μ′ ∣ suc Δᴿ ∣ rightStoreⁱ ρ
    ⊢ `∀ c′ ∶ `∀ A′ ⊑ `∀ B′) →
  Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V • ⊑ V′ •
    ⦂ A [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ∶ p →
  Φ ∣ suc Δᴸ
    ⊢ B [ zero ]ᴿ ⊑ A′ [ zero ]ᴿ ⊣ suc Δᴿ →
  WeakOneStepResult ρ
    ((V ⟨ `∀ c ⟩) •)
    ((V′ •) ⟨ (c′ [ zero ]ᶜ) ⟩)
    (B [ zero ]ᴿ) (B′ [ zero ]ᴿ) keep
weak-one-step-generic-β-∀-right-outer-widening-wideningᵀ
    vV vV′ mode seal★ c∀⊑ mode′ wfΣ′ seal★′ okΦ′
    c′∀⊑ V•⊑V′• qL
    with left-β-∀-wideningᵀ
      vV mode seal★ c∀⊑ V•⊑V′• qL
weak-one-step-generic-β-∀-right-outer-widening-wideningᵀ
    vV vV′ mode seal★ c∀⊑ mode′ wfΣ′ seal★′ okΦ′
    c′∀⊑ V•⊑V′• qL
    | source→ , _ , V•c⊑V′•
    with right-β-∀-wideningᵀ
      vV′ mode′ wfΣ′ seal★′ okΦ′ c′∀⊑ V•c⊑V′•
weak-one-step-generic-β-∀-right-outer-widening-wideningᵀ
    vV vV′ mode seal★ c∀⊑ mode′ wfΣ′ seal★′ okΦ′
    c′∀⊑ V•⊑V′• qL
    | source→ , _ , V•c⊑V′•
    | _ , _ , result =
  weak-one-step-keep-source-catchupᵀ source→ result
