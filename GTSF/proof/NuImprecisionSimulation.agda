module proof.NuImprecisionSimulation where

-- File Charter:
--   * Establishes allocation and forall-administrative simulation lemmas for
--     quotiented Nu-term imprecision.
--   * Factors bare runtime-bullet instantiation from reveal and widening
--     conversions for ordinary `ν` and `ν ★`.
--   * Checks `β-Λ•`, `β-∀•`, `β-gen•`, and `β-inst` boundaries.
--   * Connects crossed stores to two `bind` traces in opposite logical order.
--   * Defines the general weak one-step result over transformed stores,
--     contexts, and endpoint types.
--   * Packages both orientations of the adjacent-`∀` swap as
--     constructor-level weak-simulation cases with generated crossed stores
--     and explicit target administrative tails.
--   * Packages both generic-cast constructor orders at `β-∀•`, for all
--     source/target narrowing and widening combinations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import Coercions using
  ( ModeIncl
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
  ; applyStore
  ; applyStores
  ; applyCoercionUnderTyBinder
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; bind
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
  ; no•-Λ
  ; no•-⟨⟩
  ; ok-no
  ; ok-ν
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
  ; _⟨_⟩
  )
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
open import Store using (StoreIncl; StoreIncl-drop)
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
  ; rename-assm²-∀ᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-source-νᵢ
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
  )
open import proof.ReductionProperties using
  ( applyCoercionUnderTyBinders
  ; applyStores-++
  ; applyTy-∀
  ; applyTyUnderTyBinder
  ; applyTyCtxs-++
  ; applyTysUnderTyBinders
  ; applyTysUnderTyBinders-++
  ; applyTys-++
  ; applyTys-★
  ; applyTys-∀
  ; ν-↠
  ; ↠-trans
  )
open import proof.CoercionProperties using
  ( ModeIncl-ext
  ; ModeIncl-gen
  ; ModeIncl-inst
  ; ModeRename
  ; open0-ext-suc-cancelᶜ
  )
open import proof.TypePreservation using
  ( applyWidenInstUnderTyBinder-typing
  ; CastModeRenamer
  ; castModeRenamer-ext
  ; castModeRenamer-seal★
  ; castModeRenamer-suc
  ; modeRename-suc-weakenCast
  ; preservation
  ; term-weaken
  ; typing-renameᵀ
  )
open import proof.StoreProperties using (∈-renameStoreᵗ)
open import proof.TypeProperties using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; RenameLeftInverse-ext-suc-pred
  ; RenameLeftInverse-suc
  ; TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; predᵗ
  ; occurs-zero-rename-ext
  ; rename-cong
  ; renameᵗ-compose
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
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

------------------------------------------------------------------------
-- General weak one-step simulation result
------------------------------------------------------------------------

record WeakOneStepResult
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (M N′ : Term)
    (A B : Ty)
    (χ : StoreChange) : Set₁ where
  constructor weak-step-result
  field
    sourceChanges : StoreChanges
    targetTailChanges : StoreChanges
    sourceResult : Term
    targetResult : Term
    resultCtx : ImpCtx
    resultLeftCtx : TyCtx
    resultRightCtx : TyCtx
    sourceCtxResult :
      resultLeftCtx ≡ applyTyCtxs sourceChanges Δᴸ
    targetCtxResult :
      resultRightCtx
        ≡ applyTyCtxs targetTailChanges (applyTyCtx χ Δᴿ)
    resultStore :
      StoreImp resultCtx resultLeftCtx resultRightCtx
    resultSourceType : Ty
    resultTargetType : Ty
    sourceTypeResult :
      resultSourceType ≡ applyTys sourceChanges A
    targetTypeResult :
      resultTargetType ≡ applyTys targetTailChanges (applyTy χ B)
    transportType :
      ∀ {C D} →
      Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ →
      resultCtx ∣ resultLeftCtx
        ⊢ applyTys sourceChanges C
          ⊑ applyTys targetTailChanges (applyTy χ D)
        ⊣ resultRightCtx
    transportAllBody :
      ∀ {C D} →
      ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
      ∀ᵢᶜ resultCtx ∣ suc resultLeftCtx
        ⊢ applyTysUnderTyBinders sourceChanges C
          ⊑ applyTysUnderTyBinders targetTailChanges
              (applyTyUnderTyBinder χ D)
        ⊣ suc resultRightCtx
    transportRightBody :
      ∀ {C D} →
      ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
      ⇑ᴿᵢ resultCtx ∣ resultLeftCtx
        ⊢ applyTys sourceChanges C
          ⊑ applyTysUnderTyBinders targetTailChanges
              (applyTyUnderTyBinder χ D)
        ⊣ suc resultRightCtx
    resultType :
      resultCtx ∣ resultLeftCtx
        ⊢ resultSourceType ⊑ resultTargetType
        ⊣ resultRightCtx
    sourceCatchup : M —↠[ sourceChanges ] sourceResult
    targetTail : N′ —↠[ targetTailChanges ] targetResult
    sourceStoreResult :
      leftStoreⁱ resultStore
        ≡ applyStores sourceChanges (leftStoreⁱ ρ)
    targetStoreResult :
      rightStoreⁱ resultStore
        ≡ applyStores targetTailChanges
            (applyStore χ (rightStoreⁱ ρ))
    relatedResults :
      resultCtx
        ∣ resultLeftCtx
        ∣ resultRightCtx
        ∣ resultStore ∣ []
        ⊢ᴺ sourceResult ⊑ targetResult
        ⦂ resultSourceType ⊑ resultTargetType
        ∶ resultType

open WeakOneStepResult

data WeakOneStepOutcome
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (M N′ : Term)
    (A B : Ty)
    (χ : StoreChange) : Set₁ where
  outcome-related :
    WeakOneStepResult ρ M N′ A B χ →
    WeakOneStepOutcome ρ M N′ A B χ

  outcome-source-blame : ∀ {χs} →
    M —↠[ χs ] blame →
    WeakOneStepOutcome ρ M N′ A B χ

record WeakOneStepAllResult
    {Φ Δᴸ Δᴿ N N₁′ C C′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) : Set₁ where
  constructor weak-all-result
  field
    weakResult : WeakOneStepResult ρ N N₁′ (`∀ C) (`∀ C′) χ
    canonicalAllResults :
      resultCtx weakResult
        ∣ resultLeftCtx weakResult
        ∣ resultRightCtx weakResult
        ∣ resultStore weakResult ∣ []
        ⊢ᴺ sourceResult weakResult ⊑ targetResult weakResult
        ⦂ `∀
            (applyTysUnderTyBinders (sourceChanges weakResult) C)
          ⊑ `∀
              (applyTysUnderTyBinders (targetTailChanges weakResult)
                (applyTyUnderTyBinder χ C′))
        ∶ ∀ⁱ (transportAllBody weakResult q)

open WeakOneStepAllResult

data WeakOneStepAllOutcome
    {Φ Δᴸ Δᴿ N N₁′ C C′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) : Set₁ where
  all-outcome-related :
    WeakOneStepAllResult {N = N} {N₁′ = N₁′} {χ = χ} {ρ = ρ} q →
    WeakOneStepAllOutcome q

  all-outcome-source-blame : ∀ {χs} →
    N —↠[ χs ] blame →
    WeakOneStepAllOutcome q

record LeftSilentInvariant
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M V′ A B keep) : Set₁ where
  constructor left-silent-invariant
  field
    targetTailIsEmpty : targetTailChanges result ≡ []
    targetIsUnchanged : targetResult result ≡ V′

open LeftSilentInvariant

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

record LeftCatchupInvariant
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M V′ A B keep) : Set₁ where
  constructor left-catchup-invariant
  field
    silentInvariant : LeftSilentInvariant result
    sourceIsValueOrBlame :
      (Value (sourceResult result) × No• (sourceResult result)) ⊎
      sourceResult result ≡ blame

open LeftCatchupInvariant

record LeftSilentResult
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} : Set₁ where
  constructor left-silent
  field
    silentResult : WeakOneStepResult ρ M V′ A B keep
    resultIsLeftSilent : LeftSilentInvariant silentResult

open LeftSilentResult

record LeftCatchupResult
    {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} : Set₁ where
  constructor left-catchup
  field
    catchupResult : WeakOneStepResult ρ M V′ A B keep
    catchupInvariant : LeftCatchupInvariant catchupResult

open LeftCatchupResult

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

record LeftCatchupAllResult
    {Φ Δᴸ Δᴿ N V′ C C′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) : Set₁ where
  constructor left-all-catchup
  field
    catchupAllResult :
      WeakOneStepAllResult
        {N = N} {N₁′ = V′} {χ = keep} {ρ = ρ} q
    catchupAllInvariant :
      LeftCatchupInvariant (weakResult catchupAllResult)

open LeftCatchupAllResult

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

lift-store-result :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρ′ ] LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′
lift-store-result [] = [] , lift-store-[]
lift-store-result (store-matched α A β B p ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-matched α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ′ ,
  lift-store-∷ liftρ
lift-store-result (store-left α A hA ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-left α A hA ∷ ρ)
    | ρ′ , liftρ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ′ ,
  lift-store-left liftρ
lift-store-result (store-right β B hB ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-right β B hB ∷ ρ)
    | ρ′ , liftρ =
  store-right (suc β) (⇑ᵗ B)
    (renameᵗ-preserves-WfTy hB TyRenameWf-suc) ∷ ρ′ ,
  lift-store-right liftρ
lift-store-result (store-link α A β B p ∷ ρ)
    with lift-store-result ρ
lift-store-result (store-link α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-link (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ′ ,
  lift-store-link liftρ

lift-left-store-result :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρ′ ] LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
lift-left-store-result [] = [] , lift-left-store-[]
lift-left-store-result (store-matched α A β B p ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-matched α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-matched (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ′ ,
  lift-left-store-∷ liftρ
lift-left-store-result (store-left α A hA ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-left α A hA ∷ ρ)
    | ρ′ , liftρ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ′ ,
  lift-left-store-left liftρ
lift-left-store-result (store-right β B hB ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-right β B hB ∷ ρ)
    | ρ′ , liftρ =
  store-right β B hB ∷ ρ′ ,
  lift-left-store-right liftρ
lift-left-store-result (store-link α A β B p ∷ ρ)
    with lift-left-store-result ρ
lift-left-store-result (store-link α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-link (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ′ ,
  lift-left-store-link liftρ

lift-right-store-result :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρ′ ] LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′
lift-right-store-result [] = [] , lift-right-store-[]
lift-right-store-result (store-matched α A β B p ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-matched α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-matched α A (suc β) (⇑ᵗ B)
    (⊑-target-lift-rightᵢ p) ∷ ρ′ ,
  lift-right-store-∷ liftρ
lift-right-store-result (store-left α A hA ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-left α A hA ∷ ρ)
    | ρ′ , liftρ =
  store-left α A hA ∷ ρ′ ,
  lift-right-store-left liftρ
lift-right-store-result (store-right β B hB ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-right β B hB ∷ ρ)
    | ρ′ , liftρ =
  store-right (suc β) (⇑ᵗ B)
    (renameᵗ-preserves-WfTy hB TyRenameWf-suc) ∷ ρ′ ,
  lift-right-store-right liftρ
lift-right-store-result (store-link α A β B p ∷ ρ)
    with lift-right-store-result ρ
lift-right-store-result (store-link α A β B p ∷ ρ)
    | ρ′ , liftρ =
  store-link α A (suc β) (⇑ᵗ B)
    (⊑-target-lift-rightᵢ p) ∷ ρ′ ,
  lift-right-store-link liftρ

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
    (lift-left-store-∷ {p′ = pᴸ} liftᴸ)
    (lift-right-store-∷ liftᴿ)
    with left-right-store-commuteⁱ liftᴸ liftᴿ
left-right-store-commuteⁱ
    (lift-left-store-∷ {p′ = pᴸ} liftᴸ)
    (lift-right-store-∷ liftᴿ)
    | ρ× , rightᴸ , leftᴿ =
  store-matched _ _ _ _ (⊑-target-lift-rightᵢ pᴸ) ∷ ρ× ,
  lift-right-store-∷ rightᴸ ,
  lift-left-store-∷ leftᴿ
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
    (lift-left-store-link {p′ = pᴸ} liftᴸ)
    (lift-right-store-link liftᴿ)
    with left-right-store-commuteⁱ liftᴸ liftᴿ
left-right-store-commuteⁱ
    (lift-left-store-link {p′ = pᴸ} liftᴸ)
    (lift-right-store-link liftᴿ)
    | ρ× , rightᴸ , leftᴿ =
  store-link _ _ _ _ (⊑-target-lift-rightᵢ pᴸ) ∷ ρ× ,
  lift-right-store-link rightᴸ ,
  lift-left-store-link leftᴿ

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
    (lift-left-ctx-∷ {p′ = pᴸ} liftᴸ)
    (lift-right-ctx-∷ liftᴿ)
    with left-right-ctx-commuteⁱ liftᴸ liftᴿ
left-right-ctx-commuteⁱ
    (lift-left-ctx-∷ {p′ = pᴸ} liftᴸ)
    (lift-right-ctx-∷ liftᴿ)
    | γ× , rightᴸ , leftᴿ =
  ctx-imp _ _ (⊑-target-lift-rightᵢ pᴸ) ∷ γ× ,
  lift-right-ctx-∷ rightᴸ ,
  lift-left-ctx-∷ leftᴿ

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

rename-assm²-target-ext-idᵢ :
  ∀ {τ a} →
  rename-assm²ᵢ τ (extᵗ (λ X → X)) a
    ≡ rename-assm²ᵢ τ (λ X → X) a
rename-assm²-target-ext-idᵢ {a = X ˣ⊑★} = refl
rename-assm²-target-ext-idᵢ {a = X ˣ⊑ˣ zero} = refl
rename-assm²-target-ext-idᵢ {a = X ˣ⊑ˣ suc Y} = refl

rename-assm²-∀-leftᵢ :
  ∀ {Φ Ψ τ} →
  (∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  ∀ {a} → a ∈ ∀ᵢᶜ Φ →
  rename-assm²ᵢ (extᵗ τ) (λ X → X) a ∈ ∀ᵢᶜ Ψ
rename-assm²-∀-leftᵢ {Ψ = Ψ} assm {a = a} a∈ =
  subst
    (_∈ ∀ᵢᶜ Ψ)
    rename-assm²-target-ext-idᵢ
    (rename-assm²-⇑ᵢ assm a∈)

⊑-rename-leftᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ A B} (τ : Renameᵗ) →
  (∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  TyRenameWf Δᴸ Δᴸ′ τ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ′ ⊢ renameᵗ τ A ⊑ B ⊣ Δᴿ
⊑-rename-leftᵢ τ assm hτ id★ = id★
⊑-rename-leftᵢ τ assm hτ (idˣ a∈ X<Δ Y<Δ) =
  idˣ (assm a∈) (hτ X<Δ) Y<Δ
⊑-rename-leftᵢ τ assm hτ idι = idι
⊑-rename-leftᵢ τ assm hτ (p ↦ q) =
  ⊑-rename-leftᵢ τ assm hτ p ↦
  ⊑-rename-leftᵢ τ assm hτ q
⊑-rename-leftᵢ τ assm hτ (∀ⁱ p) =
  ∀ⁱ (⊑-rename-leftᵢ
    (extᵗ τ) (rename-assm²-∀-leftᵢ assm) (TyRenameWf-ext hτ) p)
⊑-rename-leftᵢ τ assm hτ (tag ι) = tag ι
⊑-rename-leftᵢ τ assm hτ (tag p ⇛ q) =
  tag (⊑-rename-leftᵢ τ assm hτ p) ⇛
  ⊑-rename-leftᵢ τ assm hτ q
⊑-rename-leftᵢ τ assm hτ (tagˣ a∈ X<Δ) =
  tagˣ (assm a∈) (hτ X<Δ)
⊑-rename-leftᵢ {Φ = Φ} τ assm hτ (ν {A = A} occ p) =
  ν (trans (occurs-zero-rename-ext τ A) occ)
    (⊑-rename-leftᵢ
      (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ) p)

⊑-rename-left-atᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ A A′ B} (τ : Renameᵗ) →
  (assm : ∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
  A′ ≡ renameᵗ τ A →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ′ ⊢ A′ ⊑ B ⊣ Δᴿ
⊑-rename-left-atᵢ τ assm hτ eqA p =
  subst (λ T → _ ∣ _ ⊢ T ⊑ _ ⊣ _) (sym eqA)
    (⊑-rename-leftᵢ τ assm hτ p)

swap01-ext²-commute :
  ∀ (τ : Renameᵗ) X →
  swap01ᵗ (extᵗ (extᵗ τ) X) ≡
    extᵗ (extᵗ τ) (swap01ᵗ X)
swap01-ext²-commute τ zero = refl
swap01-ext²-commute τ (suc zero) = refl
swap01-ext²-commute τ (suc (suc X)) = refl

renameᵗ-swap01-ext²-commute :
  ∀ (τ : Renameᵗ) A →
  renameᵗ swap01ᵗ (renameᵗ (extᵗ (extᵗ τ)) A) ≡
    renameᵗ (extᵗ (extᵗ τ)) (renameᵗ swap01ᵗ A)
renameᵗ-swap01-ext²-commute τ A =
  trans
    (renameᵗ-compose (extᵗ (extᵗ τ)) swap01ᵗ A)
    (trans
      (rename-cong (swap01-ext²-commute τ) A)
      (sym (renameᵗ-compose swap01ᵗ (extᵗ (extᵗ τ)) A)))

≈∀-renameᵗ :
  ∀ {τ A B} → A ≈∀ B → renameᵗ τ A ≈∀ renameᵗ τ B
≈∀-renameᵗ ≈∀-refl = ≈∀-refl
≈∀-renameᵗ (≈∀-sym A≈B) = ≈∀-sym (≈∀-renameᵗ A≈B)
≈∀-renameᵗ (≈∀-trans A≈B B≈C) =
  ≈∀-trans (≈∀-renameᵗ A≈B) (≈∀-renameᵗ B≈C)
≈∀-renameᵗ (≈∀-⇒ A≈A′ B≈B′) =
  ≈∀-⇒ (≈∀-renameᵗ A≈A′) (≈∀-renameᵗ B≈B′)
≈∀-renameᵗ (≈∀-∀ A≈B) = ≈∀-∀ (≈∀-renameᵗ A≈B)
≈∀-renameᵗ {τ = τ} (≈∀-swap {A = A}) =
  subst
    (λ T → `∀ (`∀ (renameᵗ (extᵗ (extᵗ τ)) A)) ≈∀
      `∀ (`∀ T))
    (renameᵗ-swap01-ext²-commute τ A)
    ≈∀-swap

⊑ᵖ-rename-leftᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ A B} (τ : Renameᵗ) →
  (∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  TyRenameWf Δᴸ Δᴸ′ τ →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ′ ⊢ renameᵗ τ A ⊑ᵖ B ⊣ Δᴿ
⊑ᵖ-rename-leftᵢ τ assm hτ (quotientᵖ A≈C C⊑D D≈B) =
  quotientᵖ (≈∀-renameᵗ A≈C)
    (⊑-rename-leftᵢ τ assm hτ C⊑D) D≈B

⇑ᴿᵢ-membership :
  ∀ {Φ a} →
  a ∈ Φ →
  ⇑ᴿᵢₐ a ∈ ⇑ᴿᵢ Φ
⇑ᴿᵢ-membership (here refl) = here refl
⇑ᴿᵢ-membership (there a∈) = there (⇑ᴿᵢ-membership a∈)

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

modeRename-id-only :
  ∀ (τ : Renameᵗ) → ModeRename τ id-onlyᵈ id-onlyᵈ
modeRename-id-only τ X = refl

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
      eqα eqA renameρ)
    (lift-store-∷ {p′ = p∀} liftρ)
    with left-store-rename-∀ renameρ liftρ
left-store-rename-∀ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {β = β} {B = B} eqα eqA renameρ)
    (lift-store-∷ {A = A} {p′ = p∀} liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-matched (suc α′) (⇑ᵗ A′) (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀) ∷ ρ′∀ ,
  lift-store-∷ liftρ′ ,
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
      eqα eqA renameρ)
    (lift-store-link {p′ = p∀} liftρ)
    with left-store-rename-∀ renameρ liftρ
left-store-rename-∀ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {β = β} {B = B} eqα eqA renameρ)
    (lift-store-link {A = A} {p′ = p∀} liftρ)
    | ρ′∀ , liftρ′ , renameρ∀ =
  store-link (suc α′) (⇑ᵗ A′) (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀) ∷ ρ′∀ ,
  lift-store-link liftρ′ ,
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
    (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
    (lift-ctx-∷ {p′ = p∀} liftγ)
    with left-ctx-rename-∀ renameγ liftγ
left-ctx-rename-∀ {τ = τ} {assm = assm} {hτ = hτ}
    (left-ctx-rename-∷ {A′ = A′} {B = B} eqA renameγ)
    (lift-ctx-∷ {A = A} {p′ = p∀} liftγ)
    | γ′∀ , liftγ′ , renameγ∀ =
  ctx-imp (⇑ᵗ A′) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
        (TyRenameWf-ext hτ) eqA∀ p∀) ∷ γ′∀ ,
  lift-ctx-∷ liftγ′ ,
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
      eqα eqA renameρ)
    (lift-left-store-∷ {p′ = pν} liftρ)
    with left-store-rename-ν renameρ liftρ
left-store-rename-ν {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {β = β} {B = B} eqα eqA renameρ)
    (lift-left-store-∷ {A = A} {p′ = pν} liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-matched (suc α′) (⇑ᵗ A′) β B
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν) ∷ ρ′ν ,
  lift-left-store-∷ liftρ′ ,
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
      eqα eqA renameρ)
    (lift-left-store-link {p′ = pν} liftρ)
    with left-store-rename-ν renameρ liftρ
left-store-rename-ν {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {β = β} {B = B} eqα eqA renameρ)
    (lift-left-store-link {A = A} {p′ = pν} liftρ)
    | ρ′ν , liftρ′ , renameρν =
  store-link (suc α′) (⇑ᵗ A′) β B
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν) ∷ ρ′ν ,
  lift-left-store-link liftρ′ ,
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
    (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
    (lift-left-ctx-∷ {p′ = pν} liftγ)
    with left-ctx-rename-ν renameγ liftγ
left-ctx-rename-ν {τ = τ} {assm = assm} {hτ = hτ}
    (left-ctx-rename-∷ {A′ = A′} {B = B} eqA renameγ)
    (lift-left-ctx-∷ {A = A} {p′ = pν} liftγ)
    | γ′ν , liftγ′ , renameγν =
  ctx-imp (⇑ᵗ A′) B
      (⊑-rename-left-atᵢ
        (extᵗ τ) (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) eqAν pν) ∷ γ′ν ,
  lift-left-ctx-∷ liftγ′ ,
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
    (lift-left-store-∷ liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    with left-store-rename-ν-inv liftρ renameρ
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-matched α A β B p ∷ ρ}
    (lift-left-store-∷ liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ with eqα
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-matched α A β B p ∷ ρ}
    (lift-left-store-∷ liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl
    with trans eqA (renameᵗ-ext-suc-comm τ A)
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-matched α A β B p ∷ ρ}
    (lift-left-store-∷ liftρ)
    (left-store-rename-matched eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl | refl =
  store-matched (τ α) (renameᵗ τ A) β B
      (⊑-rename-leftᵢ τ assm hτ p) ∷ ρ′ ,
  left-store-rename-matched refl refl renameρ′ ,
  lift-left-store-∷ liftρ′
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
    (lift-left-store-link liftρ)
    (left-store-rename-link eqα eqA renameρ)
    with left-store-rename-ν-inv liftρ renameρ
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-link α A β B p ∷ ρ}
    (lift-left-store-link liftρ)
    (left-store-rename-link eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ with eqα
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-link α A β B p ∷ ρ}
    (lift-left-store-link liftρ)
    (left-store-rename-link eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl
    with trans eqA (renameᵗ-ext-suc-comm τ A)
left-store-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρ = store-link α A β B p ∷ ρ}
    (lift-left-store-link liftρ)
    (left-store-rename-link eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ | refl | refl =
  store-link (τ α) (renameᵗ τ A) β B
      (⊑-rename-leftᵢ τ assm hτ p) ∷ ρ′ ,
  left-store-rename-link refl refl renameρ′ ,
  lift-left-store-link liftρ′

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
    (lift-left-ctx-∷ liftγ)
    (left-ctx-rename-∷ eqA renameγ)
    with left-ctx-rename-ν-inv liftγ renameγ
left-ctx-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {γ = ctx-imp A B p ∷ γ}
    (lift-left-ctx-∷ liftγ)
    (left-ctx-rename-∷ eqA renameγ)
    | γ′ , renameγ′ , liftγ′
    with trans eqA (renameᵗ-ext-suc-comm τ A)
left-ctx-rename-ν-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    {γ = ctx-imp A B p ∷ γ}
    (lift-left-ctx-∷ liftγ)
    (left-ctx-rename-∷ eqA renameγ)
    | γ′ , renameγ′ , liftγ′ | refl =
  ctx-imp (renameᵗ τ A) B (⊑-rename-leftᵢ τ assm hτ p) ∷ γ′ ,
  left-ctx-rename-∷ refl renameγ′ ,
  lift-left-ctx-∷ liftγ′

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
  lift-left-store-∷ (left-store-rename-suc-liftⁱ renameρ)
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
  lift-left-store-link (left-store-rename-suc-liftⁱ renameρ)

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
      eqα eqA renameρ)
    (lift-right-store-∷ {p′ = pᴿ} liftρ)
    with left-store-rename-⇑ᴿ renameρ liftρ
left-store-rename-⇑ᴿ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      {β = β} {B = B} eqα eqA renameρ)
    (lift-right-store-∷ {p′ = pᴿ} liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-matched α′ A′ (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-∷ liftρ′ ,
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
      eqα eqA renameρ)
    (lift-right-store-link {p′ = pᴿ} liftρ)
    with left-store-rename-⇑ᴿ renameρ liftρ
left-store-rename-⇑ᴿ {τ = τ} {assm = assm} {hτ = hτ}
    (left-store-rename-link {α′ = α′} {A′ = A′}
      {β = β} {B = B} eqα eqA renameρ)
    (lift-right-store-link {p′ = pᴿ} liftρ)
    | ρ′ᴿ , liftρ′ , renameρᴿ =
  store-link α′ A′ (suc β) (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ) ∷ ρ′ᴿ ,
  lift-right-store-link liftρ′ ,
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
    (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
    (lift-right-ctx-∷ {p′ = pᴿ} liftγ)
    with left-ctx-rename-⇑ᴿ renameγ liftγ
left-ctx-rename-⇑ᴿ {τ = τ} {assm = assm} {hτ = hτ}
    (left-ctx-rename-∷ {A′ = A′} {B = B} eqA renameγ)
    (lift-right-ctx-∷ {p′ = pᴿ} liftγ)
    | γ′ᴿ , liftγ′ , renameγᴿ =
  ctx-imp A′ (⇑ᵗ B)
      (⊑-rename-left-atᵢ
        τ (rename-assm²-⇑ᴿᵢ assm) hτ eqA pᴿ) ∷ γ′ᴿ ,
  lift-right-ctx-∷ liftγ′ ,
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
    (lift-right-store-∷ {p = p} liftρ)
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    with left-store-rename-⇑ᴿ-inv liftρ renameρ
left-store-rename-⇑ᴿ-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    (lift-right-store-∷ {p = p} liftρ)
    (left-store-rename-matched {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ =
  store-matched α′ A′ _ _
      (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ ρ′ ,
  left-store-rename-matched eqα eqA renameρ′ ,
  lift-right-store-∷ liftρ′
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
    (lift-right-store-link {p = p} liftρ)
    (left-store-rename-link {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    with left-store-rename-⇑ᴿ-inv liftρ renameρ
left-store-rename-⇑ᴿ-inv
    {τ = τ} {assm = assm} {hτ = hτ}
    (lift-right-store-link {p = p} liftρ)
    (left-store-rename-link {α′ = α′} {A′ = A′}
      eqα eqA renameρ)
    | ρ′ , renameρ′ , liftρ′ =
  store-link α′ A′ _ _
      (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ ρ′ ,
  left-store-rename-link eqα eqA renameρ′ ,
  lift-right-store-link liftρ′

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
    (lift-right-ctx-∷ {p = p} liftγ)
    (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
    with left-ctx-rename-⇑ᴿ-inv liftγ renameγ
left-ctx-rename-⇑ᴿ-inv {τ = τ} {assm = assm} {hτ = hτ}
    (lift-right-ctx-∷ {p = p} liftγ)
    (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
    | γ′ , renameγ′ , liftγ′ =
  ctx-imp A′ _ (⊑-rename-left-atᵢ τ assm hτ eqA p) ∷ γ′ ,
  left-ctx-rename-∷ eqA renameγ′ ,
  lift-right-ctx-∷ liftγ′

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
  lift-left-store-∷ (rename-left-store-source-liftⁱ ρ)
rename-left-store-source-liftⁱ (store-left α A hA ∷ ρ) =
  lift-left-store-left (rename-left-store-source-liftⁱ ρ)
rename-left-store-source-liftⁱ (store-right β B hB ∷ ρ) =
  lift-left-store-right (rename-left-store-source-liftⁱ ρ)
rename-left-store-source-liftⁱ (store-link α A β B p ∷ ρ) =
  lift-left-store-link (rename-left-store-source-liftⁱ ρ)

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
  lift-left-ctx-∷ (rename-left-ctx-source-liftⁱ γ)

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
    {M M′ A B B′ c μ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (modeτ : CastModeRenamer τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-cast⊒⊑ᵀ modeτ renameρ mode seal★ c⊒ M⊑M′ =
  cast⊒⊑ᵀ (CastModeRenamer.target-mode modeτ mode)
    (left-seal★-renameⁱ modeτ renameρ mode seal★)
    (left-narrowing-renameⁱ modeτ mode renameρ c⊒)
    M⊑M′ _

left-rename-cast⊑⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A B B′ c μ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (modeτ : CastModeRenamer τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-cast⊑⊑ᵀ modeτ renameρ mode seal★ c⊑ M⊑M′ =
  cast⊑⊑ᵀ (CastModeRenamer.target-mode modeτ mode)
    (left-seal★-renameⁱ modeτ renameρ mode seal★)
    (left-widening-renameⁱ modeτ mode renameρ c⊑)
    M⊑M′ _

left-rename-⊑cast⊒ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A A′ B′ c′ μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑cast⊒ᵀ renameρ mode′ seal★′ c′⊒ M⊑M′ =
  ⊑cast⊒ᵀ mode′
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-narrowing-left-renameⁱ renameρ c′⊒) M⊑M′ _

left-rename-⊑cast⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A A′ B′ c′ μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑cast⊑ᵀ renameρ mode′ seal★′ c′⊑ M⊑M′ =
  ⊑cast⊑ᵀ mode′
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-widening-left-renameⁱ renameρ c′⊑) M⊑M′ _

left-rename-⊑cast⊑idᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ A A′ B′ c′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  StoreDetWf Δᴿ (rightStoreⁱ ρ) →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑cast⊑idᵀ renameρ wfΣ′ seal★′ c′⊑ M⊑M′ =
  ⊑cast⊑idᵀ
    (right-store-det-left-renameⁱ renameρ wfΣ′)
    (right-seal★-left-renameⁱ {μ = id-onlyᵈ} renameρ seal★′)
    (right-widening-left-renameⁱ renameρ c′⊑) M⊑M′ _

left-rename-up⊑upᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {N N′ A A′ D D′ u u′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ ⊑ A′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ qD →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (N ⟨ u ⟩) ⊑ N′ ⟨ u′ ⟩
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ pA
left-rename-up⊑upᵀ {τ = τ} renameρ u⊑ u′⊑ N⊑N′ =
  up⊑upᵀ N⊑N′
    (left-widening-rename-modeⁱ (modeRename-id-only τ) renameρ u⊑)
    (right-widening-left-renameⁱ renameρ u′⊑) _

left-rename-crossed-up⊑upᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {N N′ A A′ D D′ u u′ μ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {qD′ : Ψ ∣ Δᴸ′ ⊢ renameᵗ τ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
  SealModeStore★
    (instᵈ (extᵈ tag-or-idᵈ)) (rightStoreⁱ ρ) →
  instᵈ (extᵈ tag-or-idᵈ) ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ u′ ∶ D′ ⊑ A′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ qD′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (N ⟨ u ⟩) ⊑ N′ ⟨ u′ ⟩
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ pA
left-rename-crossed-up⊑upᵀ ins renameρ mode seal★ u⊑
    seal★′ u′⊑ N⊑N′ =
  crossed-up⊑upᵀ N⊑N′ target-mode target-seal target-u⊑
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-widening-left-renameⁱ renameρ u′⊑) _
  where
  modeτ = left-insertion-cast-renamer ins
  target-mode = CastModeRenamer.target-mode modeτ mode
  target-seal = left-seal★-renameⁱ modeτ renameρ mode seal★
  target-u⊑ = left-widening-renameⁱ modeτ mode renameρ u⊑

left-rename-crossed-left-up⊑upᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {N N′ A A′ D D′ u u′ μ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {qD′ : Ψ ∣ Δᴸ′ ⊢ renameᵗ τ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
  SealModeStore★
    (extᵈ (instᵈ tag-or-idᵈ)) (rightStoreⁱ ρ) →
  extᵈ (instᵈ tag-or-idᵈ) ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ u′ ∶ D′ ⊑ A′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ qD′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (N ⟨ u ⟩) ⊑ N′ ⟨ u′ ⟩
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ pA
left-rename-crossed-left-up⊑upᵀ ins renameρ mode seal★ u⊑
    seal★′ u′⊑ N⊑N′ =
  crossed-left-up⊑upᵀ N⊑N′ target-mode target-seal target-u⊑
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-widening-left-renameⁱ renameρ u′⊑) _
  where
  modeτ = left-insertion-cast-renamer ins
  target-mode = CastModeRenamer.target-mode modeτ mode
  target-seal = left-seal★-renameⁱ modeτ renameρ mode seal★
  target-u⊑ = left-widening-renameⁱ modeτ mode renameρ u⊑

left-rename-down⊑downᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ C C′ D D′ d d′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ C ⊒ D →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ C′ ⊒ D′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ C ⊑ C′ ∶ ⊑-rename-leftᵢ τ assm hτ pC →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ (M ⟨ d ⟩) ⊑ M′ ⟨ d′ ⟩
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ qD
left-rename-down⊑downᵀ {τ = τ} renameρ d⊒ d′⊒ M⊑M′ =
  down⊑downᵀ
    (left-narrowing-rename-modeⁱ (modeRename-id-only τ) renameρ d⊒)
    (right-narrowing-left-renameⁱ renameρ d′⊒) M⊑M′ _

left-rename-gen-down⊑gen-downᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ C C′ D D′ d d′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ C ⊒ D →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ d′ ∶ C′ ⊒ D′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ C ⊑ C′ ∶ ⊑-rename-leftᵢ τ assm hτ pC →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ (M ⟨ d ⟩) ⊑ M′ ⟨ d′ ⟩
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ qD
left-rename-gen-down⊑gen-downᵀ {τ = τ} renameρ d⊒ d′⊒ M⊑M′ =
  gen-down⊑gen-downᵀ
    (left-narrowing-rename-modeⁱ
      (modeRename-gen-tag-or-id τ) renameρ d⊒)
    (right-narrowing-left-renameⁱ renameρ d′⊒) M⊑M′ _

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
    ∶ ⊑-rename-leftᵢ τ assm hτ (ν occ p)
left-rename-Λ⊑ᵀ renameρ renameγ occ liftρ liftγ vV body-map
    with left-store-rename-ν renameρ liftρ
left-rename-Λ⊑ᵀ renameρ renameγ occ liftρ liftγ vV body-map
    | ρ′ν , liftρ′ , renameρν
    with left-ctx-rename-ν renameγ liftγ
left-rename-Λ⊑ᵀ {τ = τ} {A = A}
    renameρ renameγ occ liftρ liftγ vV body-map
    | ρ′ν , liftρ′ , renameρν
    | γ′ν , liftγ′ , renameγν =
  Λ⊑ᵀ (trans (occurs-zero-rename-ext τ A) occ)
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
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ `∀ C′
    ∶ ⊑-rename-leftᵢ τ assm hτ (∀ⁱ q) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν A N s) ⊑ ν A′ N′ s′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-νᵀ
    ins renameρ renameγ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
    liftρ liftγ N⊑N′
    with left-store-rename-∀ renameρ liftρ
left-rename-νᵀ
    ins renameρ renameγ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
    liftρ liftγ N⊑N′
    | ρ′∀ , liftρ′ , renameρ∀
    with left-ctx-rename-∀ renameγ liftγ
left-rename-νᵀ {τ = τ} {assm = assm} {hτ = hτ} {A = A}
    ins renameρ renameγ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
    liftρ liftγ N⊑N′
    | ρ′∀ , liftρ′ , renameρ∀
    | γ′∀ , liftγ′ , renameγ∀ =
  ν⊑νᵀ
    (renameᵗ-preserves-WfTy hA hτ) hA′
    (left-reveal-ν-renameⁱ ins renameρ s↑)
    (right-reveal-ν-left-renameⁱ renameρ s′↑)
    (⊑-rename-leftᵢ τ assm hτ A⊑A′)
    (⊑-rename-left-atᵢ
      (extᵗ τ) (rename-assm²-∀-leftᵢ assm)
      (TyRenameWf-ext hτ)
      (sym (renameᵗ-ext-suc-comm τ A)) A⇑⊑A′⇑)
    liftρ′ liftγ′ N⊑N′

left-rename-ν⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {A B B′ C N N′ s μ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
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
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ B′
    ∶ ⊑-rename-leftᵢ τ assm hτ q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν A N s) ⊑ N′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-ν⊑ᵀ
    ins renameρ renameγ hA h⇑A s↑ liftρ liftγ N⊑N′
    with left-store-rename-ν renameρ liftρ
left-rename-ν⊑ᵀ
    ins renameρ renameγ hA h⇑A s↑ liftρ liftγ N⊑N′
    | ρ′ν , liftρ′ , renameρν
    with left-ctx-rename-ν renameγ liftγ
left-rename-ν⊑ᵀ {Δᴸ′ = Δᴸ′} {τ = τ} {hτ = hτ} {A = A}
    ins renameρ renameγ hA h⇑A s↑ liftρ liftγ N⊑N′
    | ρ′ν , liftρ′ , renameρν
    | γ′ν , liftγ′ , renameγν =
  ν⊑ᵀ (renameᵗ-preserves-WfTy hA hτ) h⇑A′
    (left-reveal-ν-renameⁱ ins renameρ s↑)
    liftρ′ liftγ′ N⊑N′
  where
  h⇑A′ : WfTy (suc Δᴸ′) (⇑ᵗ (renameᵗ τ A))
  h⇑A′ =
    subst (WfTy (suc Δᴸ′))
      (renameᵗ-ext-suc-comm τ A)
      (renameᵗ-preserves-WfTy h⇑A (TyRenameWf-ext hτ))

left-rename-⊑νᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {A B B′ C′ N N′ s μ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  WfTy Δᴿ A →
  WfTy (suc Δᴿ) (⇑ᵗ A) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ B ⊑ `∀ C′
    ∶ ⊑-rename-leftᵢ τ assm hτ q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ ν A N′ s
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-⊑νᵀ
    renameρ renameγ hA h⇑A s↑ liftρ liftγ B⊑C′ N⊑N′
    with left-store-rename-⇑ᴿ renameρ liftρ
left-rename-⊑νᵀ
    renameρ renameγ hA h⇑A s↑ liftρ liftγ B⊑C′ N⊑N′
    | ρ′ᴿ , liftρ′ , renameρᴿ
    with left-ctx-rename-⇑ᴿ renameγ liftγ
left-rename-⊑νᵀ {τ = τ} {assm = assm} {hτ = hτ}
    renameρ renameγ hA h⇑A s↑ liftρ liftγ B⊑C′ N⊑N′
    | ρ′ᴿ , liftρ′ , renameρᴿ
    | γ′ᴿ , liftγ′ , renameγᴿ =
  ⊑νᵀ hA h⇑A
    (right-reveal-ν-left-renameⁱ renameρ s↑)
    liftρ′ liftγ′
    (⊑-rename-leftᵢ τ (rename-assm²-⇑ᴿᵢ assm) hτ B⊑C′)
    N⊑N′

left-rename-νcastᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {B B′ C C′ N N′ s s′ μ μ′}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  (mode′ : CastMode μ′) →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ `∀ C′
    ∶ ⊑-rename-leftᵢ τ assm hτ (∀ⁱ q) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν ★ N s) ⊑ ν ★ N′ s′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-νcastᵀ
    ins renameρ renameγ mode seal★ mode′ seal★′ s⊑ s′⊑
    liftρ liftγ N⊑N′
    with left-store-rename-∀ renameρ liftρ
left-rename-νcastᵀ
    ins renameρ renameγ mode seal★ mode′ seal★′ s⊑ s′⊑
    liftρ liftγ N⊑N′
    | ρ′∀ , liftρ′ , renameρ∀
    with left-ctx-rename-∀ renameγ liftγ
left-rename-νcastᵀ
    ins renameρ renameγ mode seal★ mode′ seal★′ s⊑ s′⊑
    liftρ liftγ N⊑N′
    | ρ′∀ , liftρ′ , renameρ∀
    | γ′∀ , liftγ′ , renameγ∀ =
  νcast⊑νcastᵀ
    (CastModeRenamer.target-mode
      (left-insertion-cast-renamer ins) mode)
    (left-seal★-ν★-renameⁱ ins renameρ mode seal★)
    mode′ (right-seal★-ν★-left-renameⁱ renameρ seal★′)
    (left-widening-ν★-renameⁱ ins renameρ mode s⊑)
    (right-widening-ν★-left-renameⁱ renameρ s′⊑)
    liftρ′ liftγ′ N⊑N′

left-rename-νcast⊑ᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {B B′ C N N′ s μ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ (`∀ C) ⊑ B′
    ∶ ⊑-rename-leftᵢ τ assm hτ q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (ν ★ N s) ⊑ N′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-νcast⊑ᵀ
    ins renameρ renameγ mode seal★ s⊑ liftρ liftγ N⊑N′
    with left-store-rename-ν renameρ liftρ
left-rename-νcast⊑ᵀ
    ins renameρ renameγ mode seal★ s⊑ liftρ liftγ N⊑N′
    | ρ′ν , liftρ′ , renameρν
    with left-ctx-rename-ν renameγ liftγ
left-rename-νcast⊑ᵀ
    ins renameρ renameγ mode seal★ s⊑ liftρ liftγ N⊑N′
    | ρ′ν , liftρ′ , renameρν
    | γ′ν , liftγ′ , renameγν =
  νcast⊑ᵀ
    (CastModeRenamer.target-mode
      (left-insertion-cast-renamer ins) mode)
    (left-seal★-ν★-renameⁱ ins renameρ mode seal★)
    (left-widening-ν★-renameⁱ ins renameρ mode s⊑)
    liftρ′ liftγ′ N⊑N′

left-rename-⊑νcastᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {B B′ C′ N N′ s μ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  LeftCtxRenameⁱ τ assm hτ γ γ′ →
  (mode : CastMode μ) →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ N′
    ⦂ renameᵗ τ B ⊑ `∀ C′
    ∶ ⊑-rename-leftᵢ τ assm hτ q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ N ⊑ ν ★ N′ s
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ p
left-rename-⊑νcastᵀ
    renameρ renameγ mode seal★ s⊑ liftρ liftγ B⊑C′ N⊑N′
    with left-store-rename-⇑ᴿ renameρ liftρ
left-rename-⊑νcastᵀ
    renameρ renameγ mode seal★ s⊑ liftρ liftγ B⊑C′ N⊑N′
    | ρ′ᴿ , liftρ′ , renameρᴿ
    with left-ctx-rename-⇑ᴿ renameγ liftγ
left-rename-⊑νcastᵀ {τ = τ} {assm = assm} {hτ = hτ}
    renameρ renameγ mode seal★ s⊑ liftρ liftγ B⊑C′ N⊑N′
    | ρ′ᴿ , liftρ′ , renameρᴿ
    | γ′ᴿ , liftγ′ , renameγᴿ =
  ⊑νcastᵀ mode
    (right-seal★-ν★-left-renameⁱ renameρ seal★)
    (right-widening-ν★-left-renameⁱ renameρ s⊑)
    liftρ′ liftγ′
    (⊑-rename-leftᵢ τ (rename-assm²-⇑ᴿᵢ assm) hτ B⊑C′)
    N⊑N′

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

left-paired-conversion-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {c c′ A A′ B B′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  PairedConversion Φ Δᴸ Δᴿ ρ c c′ p q →
  PairedConversion Ψ Δᴸ′ Δᴿ ρ′
    (renameᶜ τ c) c′
    (⊑-rename-leftᵢ τ assm hτ p)
    (⊑-rename-leftᵢ τ assm hτ q)
left-paired-conversion-renameⁱ ins renameρ
    (paired-reveal corr conv conv′)
    with left-store-rename-correspondenceⁱ renameρ corr
left-paired-conversion-renameⁱ ins renameρ
    (paired-reveal corr conv conv′)
    | α′ , refl , A′ , refl , corr′ =
  paired-reveal corr′
    (left-reveal-renameⁱ ins renameρ conv)
    (right-reveal-left-renameⁱ renameρ conv′)
left-paired-conversion-renameⁱ ins renameρ
    (paired-conceal corr conv conv′)
    with left-store-rename-correspondenceⁱ renameρ corr
left-paired-conversion-renameⁱ ins renameρ
    (paired-conceal corr conv conv′)
    | α′ , refl , A′ , refl , corr′ =
  paired-conceal corr′
    (left-conceal-renameⁱ ins renameρ conv)
    (right-conceal-left-renameⁱ renameρ conv′)

left-paired-cast-renameⁱ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {c c′ A A′ B B′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  PairedCast Ψ Δᴸ′ Δᴿ ρ′
    (renameᶜ τ c) c′
    (⊑-rename-leftᵢ τ assm hτ p)
    (⊑-rename-leftᵢ τ assm hτ q)
left-paired-cast-renameⁱ ins renameρ
    (paired-conversion conv) =
  paired-conversion (left-paired-conversion-renameⁱ ins renameρ conv)
left-paired-cast-renameⁱ ins renameρ
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑) =
  paired-widening
    (CastModeRenamer.target-mode modeτ mode)
    (left-seal★-renameⁱ modeτ renameρ mode seal★)
    (left-widening-renameⁱ modeτ mode renameρ c⊑)
    mode′
    (right-seal★-left-renameⁱ renameρ seal★′)
    (right-widening-left-renameⁱ renameρ c′⊑)
  where
  modeτ = left-insertion-cast-renamer ins

left-rename-conv⊑convᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ c c′ A A′ B B′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (ins : LeftInsertion τ) →
  LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ A ⊑ A′ ∶ ⊑-rename-leftᵢ τ assm hτ p →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-conv⊑convᵀ ins renameρ cast M⊑M′ =
  conv⊑convᵀ (left-paired-cast-renameⁱ ins renameρ cast) M⊑M′

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
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-conv↑⊑ᵀ ins renameρ conv M⊑M′ =
  conv↑⊑ᵀ (left-reveal-renameⁱ ins renameρ conv) M⊑M′ _

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
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ (M ⟨ c ⟩) ⊑ M′
    ⦂ renameᵗ τ B ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-conv↓⊑ᵀ ins renameρ conv M⊑M′ =
  conv↓⊑ᵀ (left-conceal-renameⁱ ins renameρ conv) M⊑M′ _

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
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑conv↑ᵀ renameρ conv M⊑M′ =
  ⊑conv↑ᵀ (right-reveal-left-renameⁱ renameρ conv) M⊑M′ _

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
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′ ⟨ c′ ⟩
    ⦂ renameᵗ τ A ⊑ B′ ∶ ⊑-rename-leftᵢ τ assm hτ q
left-rename-⊑conv↓ᵀ renameρ conv M⊑M′ =
  ⊑conv↓ᵀ (right-conceal-left-renameⁱ renameρ conv) M⊑M′ _

lift-ctx-result :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γ′ ] LiftCtxⁱ (∀ᵢᶜ Φ) γ γ′
lift-ctx-result [] = [] , lift-ctx-[]
lift-ctx-result (ctx-imp A B p ∷ γ) with lift-ctx-result γ
lift-ctx-result (ctx-imp A B p ∷ γ) | γ′ , liftγ =
  ctx-imp (⇑ᵗ A) (⇑ᵗ B) (⊑-lift∀ᵢ p) ∷ γ′ ,
  lift-ctx-∷ liftγ

lift-left-ctx-result :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γ′ ] LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
lift-left-ctx-result [] = [] , lift-left-ctx-[]
lift-left-ctx-result (ctx-imp A B p ∷ γ)
    with lift-left-ctx-result γ
lift-left-ctx-result (ctx-imp A B p ∷ γ) | γ′ , liftγ =
  ctx-imp (⇑ᵗ A) B (⊑-source-liftνᵢ p) ∷ γ′ ,
  lift-left-ctx-∷ liftγ

left-forall-store-square :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρν ] ∃[ ρ∀ ] ∃[ ρν∀ ] ∃[ ρ∀ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν ×
    LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ ×
    LiftStoreⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρν ρν∀ ×
    LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (∀ᵢᶜ Φ)) ρ∀ ρ∀ν ×
    leftStoreⁱ ρν∀ ≡ leftStoreⁱ ρ∀ν ×
    rightStoreⁱ ρν∀ ≡ rightStoreⁱ ρ∀ν
left-forall-store-square ρ with lift-left-store-result ρ
left-forall-store-square ρ | ρν , liftν
    with lift-store-result ρ
left-forall-store-square ρ | ρν , liftν | ρ∀ , lift∀
    with lift-store-result ρν
left-forall-store-square ρ | ρν , liftν | ρ∀ , lift∀
    | ρν∀ , liftν∀ with lift-left-store-result ρ∀
left-forall-store-square ρ | ρν , liftν | ρ∀ , lift∀
    | ρν∀ , liftν∀ | ρ∀ν , lift∀ν =
  ρν , ρ∀ , ρν∀ , ρ∀ν ,
  liftν , lift∀ , liftν∀ , lift∀ν ,
  trans
    (leftStoreⁱ-lift liftν∀)
    (trans
      (cong ⟰ᵗ (leftStoreⁱ-lift-left liftν))
      (sym
        (trans
          (leftStoreⁱ-lift-left lift∀ν)
          (cong ⟰ᵗ (leftStoreⁱ-lift lift∀))))) ,
  trans
    (rightStoreⁱ-lift liftν∀)
    (trans
      (cong ⟰ᵗ (rightStoreⁱ-lift-left liftν))
      (sym
        (trans
          (rightStoreⁱ-lift-left lift∀ν)
          (rightStoreⁱ-lift lift∀))))

left-forall-ctx-square :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γν ] ∃[ γ∀ ] ∃[ γν∀ ] ∃[ γ∀ν ]
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν ×
    LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ ×
    LiftCtxⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γν γν∀ ×
    LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (∀ᵢᶜ Φ)) γ∀ γ∀ν ×
    leftCtxⁱ γν∀ ≡ leftCtxⁱ γ∀ν ×
    rightCtxⁱ γν∀ ≡ rightCtxⁱ γ∀ν
left-forall-ctx-square γ with lift-left-ctx-result γ
left-forall-ctx-square γ | γν , liftν with lift-ctx-result γ
left-forall-ctx-square γ | γν , liftν | γ∀ , lift∀
    with lift-ctx-result γν
left-forall-ctx-square γ | γν , liftν | γ∀ , lift∀
    | γν∀ , liftν∀ with lift-left-ctx-result γ∀
left-forall-ctx-square γ | γν , liftν | γ∀ , lift∀
    | γν∀ , liftν∀ | γ∀ν , lift∀ν =
  γν , γ∀ , γν∀ , γ∀ν ,
  liftν , lift∀ , liftν∀ , lift∀ν ,
  trans
    (leftCtxⁱ-lift liftν∀)
    (trans
      (cong ⤊ᵗ (leftCtxⁱ-lift-left liftν))
      (sym
        (trans
          (leftCtxⁱ-lift-left lift∀ν)
          (cong ⤊ᵗ (leftCtxⁱ-lift lift∀))))) ,
  trans
    (rightCtxⁱ-lift liftν∀)
    (trans
      (cong ⤊ᵗ (rightCtxⁱ-lift-left liftν))
      (sym
        (trans
          (rightCtxⁱ-lift-left lift∀ν)
          (rightCtxⁱ-lift lift∀))))

left-source-lift-Λᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρν∀ : StoreImp (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) (suc Δᴿ)}
    {γν∀ : CtxImp (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) (suc Δᴿ)}
    {V V′ A B q} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  LiftStoreⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρν ρν∀ →
  LiftCtxⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γν γν∀ →
  Value V →
  Value V′ →
  ∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc (suc Δᴸ) ∣ suc Δᴿ ∣ ρν∀ ∣ γν∀
    ⊢ᴺ renameᵗᵐ (extᵗ suc) V ⊑ V′
    ⦂ renameᵗ (extᵗ suc) A ⊑ B ∶ q →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρν ∣ γν
    ⊢ᴺ ⇑ᵗᵐ (Λ V) ⊑ Λ V′
    ⦂ ⇑ᵗ (`∀ A) ⊑ `∀ B ∶ ∀ⁱ q
left-source-lift-Λᵀ
    liftνρ liftνγ liftν∀ρ liftν∀γ vV vV′ V⊑V′ =
  Λ⊑Λᵀ liftν∀ρ liftν∀γ
    (renameᵗᵐ-preserves-Value (extᵗ suc) vV) vV′ V⊑V′

left-source-lift-⊑αᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴸ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {N L′ A B C′ q} →
  Value L′ →
  No• L′ →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᴸ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γᴸ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ γᴸ
    ⊢ᴺ ⇑ᵗᵐ N ⊑ L′
    ⦂ ⇑ᵗ B ⊑ `∀ C′ ∶ ⊑-source-liftνᵢ q →
  (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  suc Δᴿ ∣
    rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ) ∣
    rightCtxⁱ γᴿ ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  ∃[ ρ× ] ∃[ γ× ]
    LiftRightStoreⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρᴸ ρ× ×
    LiftLeftStoreⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρᴿ ρ× ×
    LiftRightCtxⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γᴸ γ× ×
    LiftLeftCtxⁱ
      (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γᴿ γ× ×
    (⇑ᴿᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      ∣ suc Δᴸ ∣ suc Δᴿ ∣
      store-right zero (⇑ᵗ A) h⇑A ∷ ρ× ∣ γ×
      ⊢ᴺ ⇑ᵗᵐ N ⊑ (⇑ᵗᵐ L′) •
      ⦂ ⇑ᵗ B ⊑ C′ ∶ ⊑-source-under-rightᵢ r
left-source-lift-⊑αᵀ
    vL′ noL′ h⇑A liftᴸρ liftᴸγ liftᴿρ liftᴿγ
    N⊑L′ r L′•⊢
    with left-right-store-commuteⁱ liftᴸρ liftᴿρ
left-source-lift-⊑αᵀ
    vL′ noL′ h⇑A liftᴸρ liftᴸγ liftᴿρ liftᴿγ
    N⊑L′ r L′•⊢
    | ρ× , rightᴸρ , leftᴿρ
    with left-right-ctx-commuteⁱ liftᴸγ liftᴿγ
left-source-lift-⊑αᵀ
    vL′ noL′ h⇑A liftᴸρ liftᴸγ liftᴿρ liftᴿγ
    N⊑L′ r L′•⊢
    | ρ× , rightᴸρ , leftᴿρ
    | γ× , rightᴸγ , leftᴿγ =
  ρ× , γ× , rightᴸρ , leftᴿρ , rightᴸγ , leftᴿγ ,
  ⊑αᵀ vL′ noL′ h⇑A rightᴸρ rightᴸγ N⊑L′
    (⊑-source-under-rightᵢ r) source-typing target-typing
  where
  source-typing =
    subst
      (λ Γ → _ ∣ leftStoreⁱ ρ× ∣ Γ ⊢ _ ⦂ _)
      (sym (leftCtxⁱ-lift-right rightᴸγ))
      (subst
        (λ Σ → _ ∣ Σ ∣ leftCtxⁱ _ ⊢ _ ⦂ _)
        (sym (leftStoreⁱ-lift-right rightᴸρ))
        (nu-term-imprecision-source-typing N⊑L′))

  target-typing =
    subst
      (λ Γ → _ ∣
        rightStoreⁱ (store-right zero _ h⇑A ∷ ρ×) ∣ Γ
        ⊢ _ ⦂ _)
      (sym (rightCtxⁱ-lift-left leftᴿγ))
      (subst
        (λ Σ → _ ∣ (zero , _) ∷ Σ ∣ rightCtxⁱ _
          ⊢ _ ⦂ _)
        (sym (rightStoreⁱ-lift-left leftᴿρ)) L′•⊢)

left-rename-⊑αᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {ρ′ᴿ : StoreImp (⇑ᴿᵢ Ψ) Δᴸ′ (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γ′ᴿ : CtxImp (⇑ᴿᵢ Ψ) Δᴸ′ (suc Δᴿ)}
    {N L′ A B C′}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ}
    {h⇑A h⇑A′ : WfTy (suc Δᴿ) (⇑ᵗ A)} →
  LeftStoreRenameⁱ τ (rename-assm²-⇑ᴿᵢ assm) hτ
    (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    (store-right zero (⇑ᵗ A) h⇑A′ ∷ ρ′ᴿ) →
  LeftCtxRenameⁱ τ (rename-assm²-⇑ᴿᵢ assm) hτ γᴿ γ′ᴿ →
  Value L′ →
  No• L′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  (∀ {ρ′ γ′} →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftCtxRenameⁱ τ assm hτ γ γ′ →
    Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ renameᵗᵐ τ N ⊑ L′
      ⦂ renameᵗ τ B ⊑ `∀ C′
      ∶ ⊑-rename-leftᵢ τ assm hτ q) →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    ∣ rightCtxⁱ γᴿ ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  (⇑ᴿᵢ Ψ) ∣ Δᴸ′ ∣ suc Δᴿ ∣
    store-right zero (⇑ᵗ A) h⇑A′ ∷ ρ′ᴿ ∣ γ′ᴿ
    ⊢ᴺ renameᵗᵐ τ N ⊑ (⇑ᵗᵐ L′) •
    ⦂ renameᵗ τ B ⊑ C′
    ∶ ⊑-rename-leftᵢ τ (rename-assm²-⇑ᴿᵢ assm) hτ r
left-rename-⊑αᵀ
    {Ψ = Ψ} {Δᴸ′ = Δᴸ′} {Δᴿ = Δᴿ}
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρᴿ = ρᴿ} {ρ′ᴿ = ρ′ᴿ} {γᴿ = γᴿ} {γ′ᴿ = γ′ᴿ}
    {N = N} {L′ = L′} {A = A} {B = B} {C′ = C′}
    {q = q} {r = r} {h⇑A = h⇑A} {h⇑A′ = h⇑A′}
    (left-store-rename-right renameρᴿ) renameγᴿ vL′ noL′
    liftρ liftγ body-map L′•⊢
    with left-store-rename-⇑ᴿ-inv liftρ renameρᴿ
left-rename-⊑αᵀ
    (left-store-rename-right renameρᴿ) renameγᴿ vL′ noL′
    liftρ liftγ body-map L′•⊢
    | ρ′ , renameρ′ , liftρ′
    with left-ctx-rename-⇑ᴿ-inv liftγ renameγᴿ
left-rename-⊑αᵀ
    {Ψ = Ψ} {Δᴸ′ = Δᴸ′} {Δᴿ = Δᴿ}
    {τ = τ} {assm = assm} {hτ = hτ}
    {ρᴿ = ρᴿ} {ρ′ᴿ = ρ′ᴿ} {γᴿ = γᴿ} {γ′ᴿ = γ′ᴿ}
    {N = N} {L′ = L′} {A = A} {B = B} {C′ = C′}
    {q = q} {r = r} {h⇑A = h⇑A} {h⇑A′ = h⇑A′}
    (left-store-rename-right renameρᴿ) renameγᴿ vL′ noL′
    liftρ liftγ body-map L′•⊢
    | ρ′ , renameρ′ , liftρ′
    | γ′ , renameγ′ , liftγ′ =
  ⊑αᵀ vL′ noL′ h⇑A′ liftρ′ liftγ′ N⊑L′
    (⊑-rename-leftᵢ τ (rename-assm²-⇑ᴿᵢ assm) hτ r)
    source-typing target-typing
  where
  N⊑L′ :
    Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ renameᵗᵐ τ N ⊑ L′
      ⦂ renameᵗ τ B ⊑ `∀ C′
      ∶ ⊑-rename-leftᵢ τ assm hτ q
  N⊑L′ = body-map renameρ′ renameγ′

  source-typing :
    Δᴸ′ ∣ leftStoreⁱ ρ′ᴿ ∣ leftCtxⁱ γ′ᴿ
      ⊢ renameᵗᵐ τ N ⦂ renameᵗ τ B
  source-typing =
    subst
      (λ Γ → Δᴸ′ ∣ leftStoreⁱ ρ′ᴿ ∣ Γ
        ⊢ renameᵗᵐ τ N ⦂ renameᵗ τ B)
      (sym (leftCtxⁱ-lift-right liftγ′))
      (subst
        (λ Σ → Δᴸ′ ∣ Σ ∣ leftCtxⁱ γ′
          ⊢ renameᵗᵐ τ N ⦂ renameᵗ τ B)
        (sym (leftStoreⁱ-lift-right liftρ′))
        (nu-term-imprecision-source-typing N⊑L′))

  target-typing :
    suc Δᴿ
      ∣ rightStoreⁱ
          (store-right zero (⇑ᵗ A) h⇑A′ ∷ ρ′ᴿ)
      ∣ rightCtxⁱ γ′ᴿ ⊢ (⇑ᵗᵐ L′) • ⦂ C′
  target-typing =
    subst
      (λ Γ → suc Δᴿ
        ∣ rightStoreⁱ
            (store-right zero (⇑ᵗ A) h⇑A′ ∷ ρ′ᴿ)
        ∣ Γ ⊢ (⇑ᵗᵐ L′) • ⦂ C′)
      (sym (rightCtxⁱ-left-rename renameγᴿ))
      (subst
        (λ Σ → suc Δᴿ ∣ Σ ∣ rightCtxⁱ γᴿ
          ⊢ (⇑ᵗᵐ L′) • ⦂ C′)
        (sym
          (rightStoreⁱ-left-rename
            (left-store-rename-right
              {hB = h⇑A} {hB′ = h⇑A′} renameρᴿ)))
        L′•⊢)

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
  allocation-leftᵀ _ (left-store-rename-suc-liftⁱ renameρν)
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

renameᵗ-ext-id : ∀ A → renameᵗ (extᵗ (λ X → X)) A ≡ A
renameᵗ-ext-id A =
  trans (rename-cong (λ { zero → refl ; (suc X) → refl }) A)
    (renameᵗ-id A)

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

rename-assm²-crossed-doubleᵢ :
  ∀ {Φ a} →
  a ∈ Φ →
  rename-assm²ᵢ (λ X → suc (suc X)) (λ X → suc (suc X)) a
    ∈ swapRight∀∀ᵢ Φ
rename-assm²-crossed-doubleᵢ {a = X ˣ⊑★} a∈ =
  rename-assm²-swapRight∀∀ᵢ
    (rename-assm²-∀ᵢ (rename-assm²-∀ᵢ a∈))
rename-assm²-crossed-doubleᵢ {a = X ˣ⊑ˣ Y} a∈ =
  rename-assm²-swapRight∀∀ᵢ
    (rename-assm²-∀ᵢ (rename-assm²-∀ᵢ a∈))

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
        (rename-assm²-⇑ᵢ rename-assm²-crossed-doubleᵢ)
        (TyRenameWf-ext (λ X<Δ → s<s (s<s X<Δ)))
        (TyRenameWf-ext (λ X<Δ → s<s (s<s X<Δ)))
        p))

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
    wfΣ′ vV′ noV′ h⇑A′ target⊢ pB
    with lift-right-store-result ρ
weak-one-step-source-blame-right-allocationᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′}
    {V′ = V′} {s′ = s′} {ρ = ρ}
    wfΣ′ vV′ noV′ h⇑A′ target⊢ pB
    | ρ′ , liftρ =
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
    ; resultType = ⊑-target-lift-rightᵢ pB
    ; sourceCatchup = ↠-step blame-ν ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = leftStoreⁱ-lift-right liftρ
    ; targetStoreResult = target-store-result
    ; relatedResults = blame⊑ᵀ target-result-typing
    }
  where
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

weak-one-step-prepend-left-silentᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (silent : LeftSilentResult {M = M} {V′ = V′} {ρ = ρ}) →
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

weak-one-step-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ N ⦂ A ⊑ B ∶ p →
  WeakOneStepResult ρ M N A B keep
weak-one-step-relatedᵀ result =
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
    ; resultType = _
    ; sourceCatchup = ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }

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

weak-outcome-map-source :
  ∀ {Φ Δᴸ Δᴿ M M₀ N′ A A₀ B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (WeakOneStepResult ρ M N′ A B χ →
    WeakOneStepResult ρ M₀ N′ A₀ B χ) →
  (∀ {χs} → M —↠[ χs ] blame →
    ∃[ χs′ ] (M₀ —↠[ χs′ ] blame)) →
  WeakOneStepOutcome ρ M N′ A B χ →
  WeakOneStepOutcome ρ M₀ N′ A₀ B χ
weak-outcome-map-source frame blame-frame (outcome-related result) =
  outcome-related (frame result)
weak-outcome-map-source frame blame-frame
    (outcome-source-blame source↠)
    with blame-frame source↠
weak-outcome-map-source frame blame-frame
    (outcome-source-blame source↠) | χs′ , source₀↠ =
  outcome-source-blame source₀↠

weak-outcome-map-target-ν :
  ∀ {Φ Δᴸ Δᴿ M N′ A B C D Aν c χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (WeakOneStepResult ρ M N′ A B χ →
    WeakOneStepResult ρ M (ν Aν N′ c) C D χ) →
  WeakOneStepOutcome ρ M N′ A B χ →
  WeakOneStepOutcome ρ M (ν Aν N′ c) C D χ
weak-outcome-map-target-ν frame (outcome-related result) =
  outcome-related (frame result)
weak-outcome-map-target-ν frame (outcome-source-blame source↠) =
  outcome-source-blame source↠

weak-all-outcome-map-target-ν :
  ∀ {Φ Δᴸ Δᴿ N M₀ N′ C C′ A B Aν c χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (WeakOneStepAllResult
      {N = N} {N₁′ = N′} {C = C} {C′ = C′}
      {χ = χ} {ρ = ρ} q →
    WeakOneStepResult ρ M₀ (ν Aν N′ c) A B χ) →
  (∀ {χs} → N —↠[ χs ] blame →
    ∃[ χs′ ] (M₀ —↠[ χs′ ] blame)) →
  WeakOneStepAllOutcome
    {N = N} {N₁′ = N′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q →
  WeakOneStepOutcome ρ M₀ (ν Aν N′ c) A B χ
weak-all-outcome-map-target-ν frame blame-frame
    (all-outcome-related result) =
  outcome-related (frame result)
weak-all-outcome-map-target-ν frame blame-frame
    (all-outcome-source-blame source↠)
    with blame-frame source↠
weak-all-outcome-map-target-ν frame blame-frame
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

weak-one-step-all-outcome-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ N N′ C C′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  WeakOneStepAllOutcome {χ = keep} q
weak-one-step-all-outcome-relatedᵀ result =
  all-outcome-related (weak-one-step-all-relatedᵀ result)

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
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepAllResult
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q →
  WeakOneStepResult ρ
    (ν A N s)
    (ν (applyTy χ A′) N₁′ (applyCoercionUnderTyBinder χ s′))
    B B′ χ
weak-one-step-matched-ν-frameᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {s = s} {s′ = s′} {χ = χ}
    s↑ s′↑ pA pB (weak-all-result inner innerAll)
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν-frameᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {s = s} {s′ = s′} {χ = χ}
    s↑ s′↑ pA pB (weak-all-result inner innerAll)
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} s′↑
weak-one-step-matched-ν-frameᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {s = s} {s′ = s′} {χ = χ}
    s↑ s′↑ pA pB (weak-all-result inner innerAll)
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
          (⊑-lift∀ᵢ (transportType inner pA))
          liftρ lift-ctx-[] innerAll
    }
  where
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
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (all : WeakOneStepAllResult
    {N = N} {N₁′ = V′} {χ = keep} {ρ = ρ} q) →
  LeftSilentInvariant (weakResult all) →
  LeftSilentResult
    {M = ν A N s} {V′ = ν A′ V′ s′}
    {A = B} {B = B′} {ρ = ρ}
left-silent-matched-ν-frameᵀ
    s↑ s′↑ pA pB (weak-all-result inner innerAll)
    (left-silent-invariant refl refl)
    with lift-store-result (resultStore inner)
left-silent-matched-ν-frameᵀ
    s↑ s′↑ pA pB (weak-all-result inner innerAll)
    (left-silent-invariant refl refl)
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = keep ∷ []} s′↑
left-silent-matched-ν-frameᵀ
    s↑ s′↑ pA pB (weak-all-result inner innerAll)
    (left-silent-invariant refl refl)
    | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
  left-silent
    (weak-one-step-matched-ν-frameᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll))
    (left-silent-invariant refl refl)

weak-one-step-matched-νcast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N N₁′ s s′ μ μ′ χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepAllResult
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q →
  WeakOneStepResult ρ
    (ν ★ N s)
    (ν ★ N₁′ (applyCoercionUnderTyBinder χ s′))
    B B′ χ
weak-one-step-matched-νcast-frameᵀ
    {B = B} {B′ = B′} {C = C} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {s′ = s′} {χ = χ}
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (weak-all-result inner innerAll)
    with lift-store-result (resultStore inner)
weak-one-step-matched-νcast-frameᵀ
    {B = B} {B′ = B′} {C = C} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {s′ = s′} {χ = χ}
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (weak-all-result inner innerAll)
    | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ s⊑
       | apply-widen-inst-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} mode′ seal★′ s′⊑
weak-one-step-matched-νcast-frameᵀ
    {B = B} {B′ = B′} {C = C} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {s′ = s′} {χ = χ}
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (weak-all-result inner innerAll)
    | ρ′ , liftρ
    | μᵣ , modeᵣ , sealᵣ , source⊑
    | μᵗ , modeᵗ , sealᵗ , target⊑ =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult =
        ν ★ (sourceResult inner)
          (applyCoercionUnderTyBinders (sourceChanges inner) s)
    ; targetResult =
        ν ★ (targetResult inner)
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
    ; resultType = transportType inner pB
    ; sourceCatchup =
        subst
          (λ T → ν ★ N s —↠[ sourceChanges inner ]
            ν T (sourceResult inner)
              (applyCoercionUnderTyBinders (sourceChanges inner) s))
          (applyTys-★ (sourceChanges inner))
          (ν-↠ (sourceCatchup inner))
    ; targetTail =
        subst
          (λ T → ν ★ N₁′ (applyCoercionUnderTyBinder χ s′)
            —↠[ targetTailChanges inner ]
            ν T (targetResult inner)
              (applyCoercionUnderTyBinders (targetTailChanges inner)
                (applyCoercionUnderTyBinder χ s′)))
          (applyTys-★ (targetTailChanges inner))
          (ν-↠ (targetTail inner))
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults =
        νcast⊑νcastᵀ modeᵣ source-seal modeᵗ target-seal
          source-widen target-widen
          liftρ lift-ctx-[] innerAll
    }
  where
    source-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ μᵣ)
          ((zero , ★) ∷ ⟰ᵗ Σ))
        (sym (sourceStoreResult inner)) sealᵣ

    source-widen =
      subst
        (λ Δ → instᵈ μᵣ ∣ suc Δ
          ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore inner))
          ⊢ applyCoercionUnderTyBinders (sourceChanges inner) s
            ∶ applyTysUnderTyBinders (sourceChanges inner) C
              ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
        (sym (sourceCtxResult inner))
        (subst
          (λ Σ → instᵈ μᵣ
            ∣ suc (applyTyCtxs (sourceChanges inner) _)
            ∣ (zero , ★) ∷ ⟰ᵗ Σ
            ⊢ applyCoercionUnderTyBinders (sourceChanges inner) s
              ∶ applyTysUnderTyBinders (sourceChanges inner) C
                ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
          (sym (sourceStoreResult inner)) source⊑)

    target-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ μᵗ)
          ((zero , ★) ∷ ⟰ᵗ Σ))
        (sym (targetStoreResult inner)) sealᵗ

    target-widen =
      subst
        (λ Δ → instᵈ μᵗ ∣ suc Δ
          ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ (resultStore inner))
          ⊢ applyCoercionUnderTyBinders (targetTailChanges inner)
              (applyCoercionUnderTyBinder χ s′)
            ∶ applyTysUnderTyBinders (targetTailChanges inner)
                (applyTyUnderTyBinder χ C′)
              ⊑ ⇑ᵗ
                  (applyTys (targetTailChanges inner) (applyTy χ B′)))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → instᵈ μᵗ
            ∣ suc (applyTyCtxs (targetTailChanges inner)
              (applyTyCtx χ _))
            ∣ (zero , ★) ∷ ⟰ᵗ Σ
            ⊢ applyCoercionUnderTyBinders (targetTailChanges inner)
                (applyCoercionUnderTyBinder χ s′)
              ∶ applyTysUnderTyBinders (targetTailChanges inner)
                  (applyTyUnderTyBinder χ C′)
                ⊑ ⇑ᵗ
                    (applyTys (targetTailChanges inner) (applyTy χ B′)))
          (sym (targetStoreResult inner)) target⊑)

left-silent-matched-νcast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (all : WeakOneStepAllResult
    {N = N} {N₁′ = V′} {χ = keep} {ρ = ρ} q) →
  LeftSilentInvariant (weakResult all) →
  LeftSilentResult
    {M = ν ★ N s} {V′ = ν ★ V′ s′}
    {A = B} {B = B′} {ρ = ρ}
left-silent-matched-νcast-frameᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (weak-all-result inner innerAll)
    (left-silent-invariant refl refl)
    with lift-store-result (resultStore inner)
left-silent-matched-νcast-frameᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (weak-all-result inner innerAll)
    (left-silent-invariant refl refl)
    | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ s⊑
       | apply-widen-inst-under-ty-binders
      {χs = keep ∷ []} mode′ seal★′ s′⊑
left-silent-matched-νcast-frameᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (weak-all-result inner innerAll)
    (left-silent-invariant refl refl)
    | ρ′ , liftρ
    | μᵣ , modeᵣ , sealᵣ , source⊑
    | μᵗ , modeᵗ , sealᵗ , target⊑ =
  left-silent
    (weak-one-step-matched-νcast-frameᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll))
    (left-silent-invariant refl refl)

weak-one-step-source-ν-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (inner : WeakOneStepResult ρ N N₁′ (`∀ C) B′ χ) →
  WeakOneStepResult ρ (ν A N s) N₁′ B B′ χ
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    hA s↑ pB inner
    with weak-result-source-all inner
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    hA s↑ pB inner
    | q′ , innerResult
    with lift-left-store-result (resultStore inner)
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    hA s↑ pB inner
    | q′ , innerResult | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
weak-one-step-source-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    hA s↑ pB inner
    | q′ , innerResult | ρ′ , liftρ | μ′ , source↑ =
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
    ; resultType = transportType inner pB
    ; sourceCatchup = ν-↠ (sourceCatchup inner)
    ; targetTail = targetTail inner
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults =
        ν⊑ᵀ final-wf final-shift-wf source-reveal
          liftρ lift-left-ctx-[] innerResult
    }
  where
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

weak-one-step-source-νcast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (inner : WeakOneStepResult ρ N N₁′ (`∀ C) B′ χ) →
  WeakOneStepResult ρ (ν ★ N s) N₁′ B B′ χ
weak-one-step-source-νcast-frameᵀ
    {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    mode seal★ s⊑ pB inner
    with weak-result-source-all inner
weak-one-step-source-νcast-frameᵀ
    {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    mode seal★ s⊑ pB inner
    | q′ , innerResult
    with lift-left-store-result (resultStore inner)
weak-one-step-source-νcast-frameᵀ
    {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    mode seal★ s⊑ pB inner
    | q′ , innerResult | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ s⊑
weak-one-step-source-νcast-frameᵀ
    {B = B} {B′ = B′} {C = C} {N = N} {s = s} {χ = χ}
    mode seal★ s⊑ pB inner
    | q′ , innerResult | ρ′ , liftρ
    | μ′ , mode′ , seal★′ , source⊑ =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult =
        ν ★ (sourceResult inner)
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
    ; resultType = transportType inner pB
    ; sourceCatchup =
        subst
          (λ T → ν ★ N s —↠[ sourceChanges inner ]
            ν T (sourceResult inner)
              (applyCoercionUnderTyBinders (sourceChanges inner) s))
          (applyTys-★ (sourceChanges inner))
          (ν-↠ (sourceCatchup inner))
    ; targetTail = targetTail inner
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults =
        νcast⊑ᵀ mode′ source-seal source-widen
          liftρ lift-left-ctx-[] innerResult
    }
  where
    source-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ μ′)
          ((zero , ★) ∷ ⟰ᵗ Σ))
        (sym (sourceStoreResult inner)) seal★′

    source-widen =
      subst
        (λ Δ → instᵈ μ′ ∣ suc Δ
          ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ (resultStore inner))
          ⊢ applyCoercionUnderTyBinders (sourceChanges inner) s
            ∶ applyTysUnderTyBinders (sourceChanges inner) C
              ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
        (sym (sourceCtxResult inner))
        (subst
          (λ Σ → instᵈ μ′
            ∣ suc (applyTyCtxs (sourceChanges inner) _)
            ∣ (zero , ★) ∷ ⟰ᵗ Σ
            ⊢ applyCoercionUnderTyBinders (sourceChanges inner) s
              ∶ applyTysUnderTyBinders (sourceChanges inner) C
                ⊑ ⇑ᵗ (applyTys (sourceChanges inner) B))
          (sym (sourceStoreResult inner)) source⊑)

weak-one-step-target-ν-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′ N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WfTy Δᴿ A →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (inner : WeakOneStepResult ρ N N₁′ B (`∀ C′) χ) →
  WeakOneStepResult ρ N
    (ν (applyTy χ A) N₁′ (applyCoercionUnderTyBinder χ s))
    B B′ χ
weak-one-step-target-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    hA s↑ pB pC inner
    with lift-right-store-result (resultStore inner)
weak-one-step-target-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    hA s↑ pB pC inner
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} s↑
weak-one-step-target-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    hA s↑ pB pC inner
    | ρ′ , liftρ | μ′ , target↑
    with weak-result-target-all inner
weak-one-step-target-ν-frameᵀ
    {A = A} {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    hA s↑ pB pC inner
    | ρ′ , liftρ | μ′ , target↑ | q′ , innerResult =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult = sourceResult inner
    ; targetResult =
        ν (applyTys (targetTailChanges inner) (applyTy χ A))
          (targetResult inner)
          (applyCoercionUnderTyBinders (targetTailChanges inner)
            (applyCoercionUnderTyBinder χ s))
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
    ; resultType = transportType inner pB
    ; sourceCatchup = sourceCatchup inner
    ; targetTail = ν-↠ (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults =
        ⊑νᵀ final-wf final-shift-wf target-reveal
          liftρ lift-right-ctx-[]
          (transportRightBody inner pC) innerResult
    }
  where
    final-wf =
      subst
        (λ Δ → WfTy Δ
          (applyTys (targetTailChanges inner) (applyTy χ A)))
        (sym (targetCtxResult inner))
        (wfTy-applyTys
          (χ ∷ targetTailChanges inner) hA)

    final-shift-wf =
      renameᵗ-preserves-WfTy final-wf TyRenameWf-suc

    target-reveal =
      subst
        (λ Δ → RevealConversion μ′ (suc Δ)
          ((zero , ⇑ᵗ
              (applyTys (targetTailChanges inner) (applyTy χ A))) ∷
            ⟰ᵗ (rightStoreⁱ (resultStore inner)))
          zero (⇑ᵗ
            (applyTys (targetTailChanges inner) (applyTy χ A)))
          (applyCoercionUnderTyBinders (targetTailChanges inner)
            (applyCoercionUnderTyBinder χ s))
          (applyTysUnderTyBinders (targetTailChanges inner)
            (applyTyUnderTyBinder χ C′))
          (⇑ᵗ
            (applyTys (targetTailChanges inner) (applyTy χ B′))))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → RevealConversion μ′
            (suc (applyTyCtxs (targetTailChanges inner)
              (applyTyCtx χ _)))
            ((zero , ⇑ᵗ
                (applyTys (targetTailChanges inner) (applyTy χ A))) ∷
              ⟰ᵗ Σ)
            zero (⇑ᵗ
              (applyTys (targetTailChanges inner) (applyTy χ A)))
            (applyCoercionUnderTyBinders (targetTailChanges inner)
              (applyCoercionUnderTyBinder χ s))
            (applyTysUnderTyBinders (targetTailChanges inner)
              (applyTyUnderTyBinder χ C′))
            (⇑ᵗ
              (applyTys (targetTailChanges inner) (applyTy χ B′))))
          (sym (targetStoreResult inner)) target↑)

weak-one-step-target-νcast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (inner : WeakOneStepResult ρ N N₁′ B (`∀ C′) χ) →
  WeakOneStepResult ρ N
    (ν ★ N₁′ (applyCoercionUnderTyBinder χ s))
    B B′ χ
weak-one-step-target-νcast-frameᵀ
    {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    mode seal★ s⊑ pB pC inner
    with lift-right-store-result (resultStore inner)
weak-one-step-target-νcast-frameᵀ
    {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    mode seal★ s⊑ pB pC inner
    | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = χ ∷ targetTailChanges inner} mode seal★ s⊑
weak-one-step-target-νcast-frameᵀ
    {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    mode seal★ s⊑ pB pC inner
    | ρ′ , liftρ | μ′ , mode′ , seal★′ , target⊑
    with weak-result-target-all inner
weak-one-step-target-νcast-frameᵀ
    {B = B} {B′ = B′} {C′ = C′}
    {N = N} {N₁′ = N₁′} {s = s} {χ = χ}
    mode seal★ s⊑ pB pC inner
    | ρ′ , liftρ | μ′ , mode′ , seal★′ , target⊑
    | q′ , innerResult =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult = sourceResult inner
    ; targetResult =
        ν ★ (targetResult inner)
          (applyCoercionUnderTyBinders (targetTailChanges inner)
            (applyCoercionUnderTyBinder χ s))
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
    ; resultType = transportType inner pB
    ; sourceCatchup = sourceCatchup inner
    ; targetTail =
        subst
          (λ T → ν ★ N₁′ (applyCoercionUnderTyBinder χ s)
            —↠[ targetTailChanges inner ]
            ν T (targetResult inner)
              (applyCoercionUnderTyBinders (targetTailChanges inner)
                (applyCoercionUnderTyBinder χ s)))
          (applyTys-★ (targetTailChanges inner))
          (ν-↠ (targetTail inner))
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults =
        ⊑νcastᵀ mode′ target-seal target-widen
          liftρ lift-right-ctx-[]
          (transportRightBody inner pC) innerResult
    }
  where
    target-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ μ′)
          ((zero , ★) ∷ ⟰ᵗ Σ))
        (sym (targetStoreResult inner)) seal★′

    target-widen =
      subst
        (λ Δ → instᵈ μ′ ∣ suc Δ
          ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ (resultStore inner))
          ⊢ applyCoercionUnderTyBinders (targetTailChanges inner)
              (applyCoercionUnderTyBinder χ s)
            ∶ applyTysUnderTyBinders (targetTailChanges inner)
                (applyTyUnderTyBinder χ C′)
              ⊑ ⇑ᵗ
                  (applyTys (targetTailChanges inner) (applyTy χ B′)))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → instᵈ μ′
            ∣ suc (applyTyCtxs (targetTailChanges inner)
              (applyTyCtx χ _))
            ∣ (zero , ★) ∷ ⟰ᵗ Σ
            ⊢ applyCoercionUnderTyBinders (targetTailChanges inner)
                (applyCoercionUnderTyBinder χ s)
              ∶ applyTysUnderTyBinders (targetTailChanges inner)
                  (applyTyUnderTyBinder χ C′)
                ⊑ ⇑ᵗ
                    (applyTys (targetTailChanges inner) (applyTy χ B′)))
          (sym (targetStoreResult inner)) target⊑)

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
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepAllOutcome
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q →
  WeakOneStepOutcome ρ
    (ν A N s)
    (ν (applyTy χ A′) N₁′ (applyCoercionUnderTyBinder χ s′))
    B B′ χ
weak-one-step-matched-ν-frame-outcomeᵀ s↑ s′↑ pA pB =
  weak-all-outcome-map-target-ν
    (weak-one-step-matched-ν-frameᵀ s↑ s′↑ pA pB)
    (λ N↠ → _ , ν-blame-tail N↠)

weak-one-step-matched-νcast-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N N₁′ s s′ μ μ′ χ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepAllOutcome
    {N = N} {N₁′ = N₁′} {C = C} {C′ = C′}
    {χ = χ} {ρ = ρ} q →
  WeakOneStepOutcome ρ
    (ν ★ N s)
    (ν ★ N₁′ (applyCoercionUnderTyBinder χ s′))
    B B′ χ
weak-one-step-matched-νcast-frame-outcomeᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB =
  weak-all-outcome-map-target-ν
    (weak-one-step-matched-νcast-frameᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB)
    (λ N↠ → _ , ν-blame-tail N↠)

weak-one-step-source-ν-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepOutcome ρ N N₁′ (`∀ C) B′ χ →
  WeakOneStepOutcome ρ (ν A N s) N₁′ B B′ χ
weak-one-step-source-ν-frame-outcomeᵀ hA s↑ pB =
  weak-outcome-map-source
    (weak-one-step-source-ν-frameᵀ hA s↑ pB)
    (λ N↠ → _ , ν-blame-tail N↠)

weak-one-step-source-νcast-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepOutcome ρ N N₁′ (`∀ C) B′ χ →
  WeakOneStepOutcome ρ (ν ★ N s) N₁′ B B′ χ
weak-one-step-source-νcast-frame-outcomeᵀ mode seal★ s⊑ pB =
  weak-outcome-map-source
    (weak-one-step-source-νcast-frameᵀ mode seal★ s⊑ pB)
    (λ N↠ → _ , ν-blame-tail N↠)

weak-one-step-target-ν-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′ N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WfTy Δᴿ A →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  WeakOneStepOutcome ρ N N₁′ B (`∀ C′) χ →
  WeakOneStepOutcome ρ N
    (ν (applyTy χ A) N₁′ (applyCoercionUnderTyBinder χ s))
    B B′ χ
weak-one-step-target-ν-frame-outcomeᵀ hA s↑ pB pC =
  weak-outcome-map-target-ν
    (weak-one-step-target-ν-frameᵀ hA s↑ pB pC)

weak-one-step-target-νcast-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N₁′ s μ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  WeakOneStepOutcome ρ N N₁′ B (`∀ C′) χ →
  WeakOneStepOutcome ρ N
    (ν ★ N₁′ (applyCoercionUnderTyBinder χ s))
    B B′ χ
weak-one-step-target-νcast-frame-outcomeᵀ
    mode seal★ s⊑ pB pC =
  weak-outcome-map-target-ν
    (weak-one-step-target-νcast-frameᵀ
      mode seal★ s⊑ pB pC)

∀-imprecision-source-body-wf :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ B ⊣ Δᴿ →
  WfTy (suc Δᴸ) A
∀-imprecision-source-body-wf p with ⊑-src-wf p
∀-imprecision-source-body-wf p | wf∀ hA = hA

∀-imprecision-target-body-wf :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ `∀ B ⊣ Δᴿ →
  WfTy (suc Δᴿ) B
∀-imprecision-target-body-wf p with ⊑-tgt-wf p
∀-imprecision-target-body-wf p | wf∀ hB = hB

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

------------------------------------------------------------------------
-- Crossed stores realize two allocations in opposite logical orders
------------------------------------------------------------------------

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

crossed-source-body-typing :
  ∀ {Φ Δᴸ Δᴿ A W}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  No• W →
  suc Δᴸ ∣ leftStoreⁱ ρ₁ ∣ [] ⊢ W ⦂ A →
  suc (suc Δᴸ) ∣ leftStoreⁱ ρ₂ ∣ []
    ⊢ renameᵗᵐ suc W ⦂ renameᵗ suc A
crossed-source-body-typing {Δᴸ = Δᴸ} {A = A} {W = W}
    {ρ₁ = ρ₁} liftρ₂ noW W⊢ =
  subst
    (λ Σ → suc (suc Δᴸ) ∣ Σ ∣ []
      ⊢ renameᵗᵐ suc W ⦂ renameᵗ suc A)
    (sym (leftStoreⁱ-lift liftρ₂))
    (typing-renameᵀ
      {Δ = suc Δᴸ} {Δ′ = suc (suc Δᴸ)}
      {Σ = leftStoreⁱ ρ₁} {Γ = []} {M = W} {A = A}
      {ρ = suc} {ψ = predᵗ}
      TyRenameWf-suc RenameLeftInverse-suc castModeRenamer-suc
      noW W⊢)

crossed-target-body-typing :
  ∀ {Φ Δᴸ Δᴿ B W′}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  No• W′ →
  suc Δᴿ ∣ rightStoreⁱ ρ₁ ∣ [] ⊢ W′ ⦂ B →
  suc (suc Δᴿ) ∣ rightStoreⁱ ρ₂ ∣ []
    ⊢ renameᵗᵐ (extᵗ suc) W′ ⦂ renameᵗ (extᵗ suc) B
crossed-target-body-typing {Δᴿ = Δᴿ} {B = B} {W′ = W′}
    {ρ₁ = ρ₁} liftρ₁ liftρ₂ noW′ W′⊢ =
  subst
    (λ Σ → suc (suc Δᴿ) ∣ Σ ∣ []
      ⊢ renameᵗᵐ (extᵗ suc) W′ ⦂ renameᵗ (extᵗ suc) B)
    (rightStoreⁱ-crossed-body liftρ₁ liftρ₂)
    (typing-renameᵀ
      {Δ = suc Δᴿ} {Δ′ = suc (suc Δᴿ)}
      {Σ = rightStoreⁱ ρ₁} {Γ = []} {M = W′} {A = B}
      {ρ = extᵗ suc} {ψ = predᵗ}
      (TyRenameWf-ext TyRenameWf-suc)
      RenameLeftInverse-ext-suc-pred
      (castModeRenamer-ext castModeRenamer-suc) noW′ W′⊢)

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
  swapRight-bodyᵀ liftρ₁ liftρ₂ W⊑W′ refl refl refl refl
    (⊑-crossed-body-lift∀∀ᵢ _)
    (crossed-source-body-typing liftρ₂ noW
      (nu-term-imprecision-source-typing W⊑W′))
    (crossed-target-body-typing liftρ₁ liftρ₂ noW′
      (nu-term-imprecision-target-typing W⊑W′))

crossed-left-source-body-typing :
  ∀ {Φ Δᴸ Δᴿ A W}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  No• W →
  suc Δᴸ ∣ leftStoreⁱ ρ₁ ∣ [] ⊢ W ⦂ A →
  suc (suc Δᴸ) ∣ leftStoreⁱ ρ₂ ∣ []
    ⊢ renameᵗᵐ (extᵗ suc) W ⦂ renameᵗ (extᵗ suc) A
crossed-left-source-body-typing
    {Δᴸ = Δᴸ} {A = A} {W = W} {ρ₁ = ρ₁}
    liftρ₁ liftρ₂ noW W⊢ =
  subst
    (λ Σ → suc (suc Δᴸ) ∣ Σ ∣ []
      ⊢ renameᵗᵐ (extᵗ suc) W ⦂ renameᵗ (extᵗ suc) A)
    (leftStoreⁱ-crossed-body liftρ₁ liftρ₂)
    (typing-renameᵀ
      {Δ = suc Δᴸ} {Δ′ = suc (suc Δᴸ)}
      {Σ = leftStoreⁱ ρ₁} {Γ = []} {M = W} {A = A}
      {ρ = extᵗ suc} {ψ = predᵗ}
      (TyRenameWf-ext TyRenameWf-suc)
      RenameLeftInverse-ext-suc-pred
      (castModeRenamer-ext castModeRenamer-suc) noW W⊢)

crossed-left-target-body-typing :
  ∀ {Φ Δᴸ Δᴿ B W′}
    {ρ₁ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {ρ₂ : StoreImp (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))} →
  LiftStoreⁱ (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  No• W′ →
  suc Δᴿ ∣ rightStoreⁱ ρ₁ ∣ [] ⊢ W′ ⦂ B →
  suc (suc Δᴿ) ∣ rightStoreⁱ ρ₂ ∣ []
    ⊢ renameᵗᵐ suc W′ ⦂ renameᵗ suc B
crossed-left-target-body-typing
    {Δᴿ = Δᴿ} {B = B} {W′ = W′} {ρ₁ = ρ₁}
    liftρ₂ noW′ W′⊢ =
  subst
    (λ Σ → suc (suc Δᴿ) ∣ Σ ∣ []
      ⊢ renameᵗᵐ suc W′ ⦂ renameᵗ suc B)
    (sym (rightStoreⁱ-lift liftρ₂))
    (typing-renameᵀ
      {Δ = suc Δᴿ} {Δ′ = suc (suc Δᴿ)}
      {Σ = rightStoreⁱ ρ₁} {Γ = []} {M = W′} {A = B}
      {ρ = suc} {ψ = predᵗ}
      TyRenameWf-suc RenameLeftInverse-suc castModeRenamer-suc
      noW′ W′⊢)

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
  swapLeft-bodyᵀ liftρ₁ liftρ₂ W⊑W′ refl refl refl refl
    (⊑-crossed-left-body-lift∀∀ᵢ _)
    (crossed-left-source-body-typing liftρ₁ liftρ₂ noW
      (nu-term-imprecision-source-typing W⊑W′))
    (crossed-left-target-body-typing liftρ₂ noW′
      (nu-term-imprecision-target-typing W⊑W′))

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
  allocation-leftᵀ hAν liftρ M⊑M′
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

post-allocation-β-∀•-bare :
  ∀ {V c} →
  Value V →
  (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •
    —→[ keep ] ((⇑ᵗᵐ V) •) ⟨ c ⟩
post-allocation-β-∀•-bare {V = V} {c = c} vV =
  subst
    (λ d → (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •
      —→[ keep ] ((⇑ᵗᵐ V) •) ⟨ d ⟩)
    (open0-ext-suc-cancelᶜ c)
    (pure-step
      (β-∀• (renameᵗᵐ-preserves-Value suc vV)))

post-β-inst :
  ∀ {V B s} →
  Value V →
  V ⟨ inst B s ⟩ —→[ keep ] ν ★ V s
post-β-inst vV = pure-step (β-inst vV)

post-β-gen• :
  ∀ {V A c} →
  Value V →
  ((V ⟨ gen A c ⟩) •) —→[ keep ] (V ⟨ (c [ zero ]ᶜ) ⟩)
post-β-gen• vV = pure-step (β-gen• vV)

post-allocation-β-gen•-bare :
  ∀ {V A c} →
  Value V →
  (⇑ᵗᵐ (V ⟨ gen A c ⟩)) •
    —→[ keep ] (⇑ᵗᵐ V) ⟨ c ⟩
post-allocation-β-gen•-bare {V = V} {c = c} vV =
  subst
    (λ d → (⇑ᵗᵐ (V ⟨ gen _ c ⟩)) •
      —→[ keep ] (⇑ᵗᵐ V) ⟨ d ⟩)
    (open0-ext-suc-cancelᶜ c)
    (pure-step
      (β-gen• (renameᵗᵐ-preserves-Value suc vV)))

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
      allocation-crossedᵀ
        (⊑-src-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
        wf★ wf★
        (⊑-tgt-wf (⊑-crossed-double-lift∀∀ᵢ pObs))
        liftρ₁ liftρ₂
        (⊑-crossed-double-lift∀∀ᵢ pObs) id★
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
      crossed-up⊑upᵀ
        (gen-down⊑gen-downᵀ d⊒ d′⊒ allocated-body qD)
        (cast-ext (cast-inst cast-tag-or-id))
        seal★-ext-inst-tag-or-id u⊑
        seal★-inst-ext-tag-or-id u′⊑ pE
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
      allocation-crossedᵀ
        wf★ (⊑-src-wf pObs×) (⊑-tgt-wf pObs×) wf★
        liftρ₁ liftρ₂ id★ pObs× body⊑body′
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
      crossed-left-up⊑upᵀ
        (gen-down⊑gen-downᵀ d⊒ d′⊒ allocated-body qD)
        (cast-inst (cast-ext cast-tag-or-id))
        seal★-inst-ext-tag-or-id u⊑
        seal★-ext-inst-tag-or-id u′⊑ pE
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

Λ-value-body :
  ∀ {V} →
  Value (Λ V) →
  Value V
Λ-value-body (Λ vV) = vV

post-allocation-polymorphic-value-step :
  ∀ {Δ : TyCtx} {Σ : Store} {L A} →
  Value L →
  Δ ∣ Σ ∣ [] ⊢ L ⦂ `∀ A →
  ∃[ N ] ((⇑ᵗᵐ L) • —→[ keep ] N)
post-allocation-polymorphic-value-step
    {Δ = Δ} {Σ = Σ} {L = L} {A = A} vL L⊢
    with canonical-∀ {Δ = Δ} {Σ = Σ} {V = L} {A = A}
      vL (forget L⊢)
post-allocation-polymorphic-value-step {L = .(Λ V)} vL L⊢
    | av-Λ {W = V} refl =
  V , post-allocation-β-Λ•-bare (Λ-value-body vL)
post-allocation-polymorphic-value-step
    {L = .(V ⟨ `∀ c ⟩)} vL L⊢ | av-∀ {W = V} {c = c} vV refl =
  ((⇑ᵗᵐ V) •) ⟨ c ⟩ , post-allocation-β-∀•-bare vV
post-allocation-polymorphic-value-step
    {L = .(V ⟨ gen A c ⟩)} vL L⊢
    | av-gen {W = V} {A = A} {c = c} vV refl =
  (⇑ᵗᵐ V) ⟨ c ⟩ , post-allocation-β-gen•-bare vV

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

left-polymorphic-value-shapeᵀ :
  ∀ {Φ Δᴸ Δᴿ L N′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ N′ ⦂ `∀ A ⊑ B ∶ p →
  AllView L
left-polymorphic-value-shapeᵀ vL L⊑N′ =
  canonical-∀ vL
    (forget (nu-term-imprecision-source-typing L⊑N′))

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

weak-one-step-keep-source-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ M N N′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  WeakOneStepResult ρ M N′ A B keep
weak-one-step-keep-source-catchupᵀ source→ result =
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
    ; resultType = _
    ; sourceCatchup = ↠-step source→ ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }

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
      allocation-leftᵀ h⇑A liftρᵇ W⊑V′
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

------------------------------------------------------------------------
-- Synchronized polymorphic allocation
------------------------------------------------------------------------

matched-ν↑-allocation :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value N →
  No• N →
  Value N′ →
  No• N′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  (ν A N s —→[ bind A ] ((⇑ᵗᵐ N) •) ⟨ s ⟩) ×
  (ν A′ N′ s′ —→[ bind A′ ] ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩) ×
  (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣
    store-matched zero (⇑ᵗ A) zero (⇑ᵗ A′) A⇑⊑A′⇑ ∷ ρ′
    ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩
    ⦂ ⇑ᵗ B ⊑ ⇑ᵗ B′ ∶ ⊑-lift∀ᵢ pB)
matched-ν↑-allocation {q = q} vN noN vN′ noN′ s↑ s′↑ pB
    A⇑⊑A′⇑ liftρ N⊑N′ =
  ν-step vN noN ,
  ν-step vN′ noN′ ,
  conv⊑convᵀ
    (paired-conversion
      (paired-reveal (correspondence-stored (here refl))
        left-reveal right-reveal))
    (α⊑αᵀ vN noN vN′ noN′ A⇑⊑A′⇑ liftρ lift-ctx-[]
      N⊑N′ left-bullet-typing right-bullet-typing)
  where
    left-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (leftStoreⁱ-lift liftρ))
        s↑

    right-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (rightStoreⁱ-lift liftρ))
        s′↑

    left-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (leftStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-src-wf q) vN noN
          (nu-term-imprecision-source-typing N⊑N′))

    right-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (rightStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-tgt-wf q) vN′ noN′
          (nu-term-imprecision-target-typing N⊑N′))

weak-one-step-matched-ν↑ᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value N →
  No• N →
  Value N′ →
  No• N′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  WeakOneStepResult ρ
    (ν A N s) (((⇑ᵗᵐ N′) •) ⟨ s′ ⟩)
    B B′ (bind A′)
weak-one-step-matched-ν↑ᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′} {ρ′ = ρ′}
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
    with matched-ν↑-allocation vN noN vN′ noN′ s↑ s′↑
      pB A⇑⊑A′⇑ liftρ N⊑N′
weak-one-step-matched-ν↑ᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′} {ρ′ = ρ′}
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
    | source→ , _ , result =
  record
    { sourceChanges = bind A ∷ []
    ; targetTailChanges = []
    ; sourceResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
    ; targetResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
    ; resultCtx = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore =
        store-matched zero (⇑ᵗ A) zero (⇑ᵗ A′)
          A⇑⊑A′⇑ ∷ ρ′
    ; resultSourceType = ⇑ᵗ B
    ; resultTargetType = ⇑ᵗ B′
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = ⊑-lift∀ᵢ
    ; transportAllBody = ⊑-lift-under-∀ᵢ
    ; transportRightBody = ⊑-lift-under-rightᵢ
    ; resultType = ⊑-lift∀ᵢ pB
    ; sourceCatchup = ↠-step source→ ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult =
        cong ((zero , ⇑ᵗ A) ∷_) (leftStoreⁱ-lift liftρ)
    ; targetStoreResult =
        cong ((zero , ⇑ᵗ A′) ∷_) (rightStoreⁱ-lift liftρ)
    ; relatedResults = result
    }

weak-one-step-matched-ν↑-value-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Value V′ →
  No• V′ →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  Value (sourceResult (weakResult (catchupAllResult catchup))) →
  No• (sourceResult (weakResult (catchupAllResult catchup))) →
  WeakOneStepResult ρ
    (ν A N s) (((⇑ᵗᵐ V′) •) ⟨ s′ ⟩)
    B B′ (bind A′)
weak-one-step-matched-ν↑-value-catchupᵀ
    s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν↑-value-catchupᵀ
    s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = keep ∷ []} s′↑
weak-one-step-matched-ν↑-value-catchupᵀ
    s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW | ρ′ , liftρ₀ | μᵣ , source↑₀ | μᵗ , target↑₀
    with weak-result-source-reveal inner s↑
       | weak-result-target-reveal keep inner s′↑
weak-one-step-matched-ν↑-value-catchupᵀ
    s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW | ρ′ , liftρ₀ | μᵣ , source↑₀ | μᵗ , target↑₀
    | μˢ , source↑ | μᵗ′ , target↑ =
  weak-one-step-prepend-left-silentᵀ
    (left-silent
      (weak-one-step-matched-ν-frameᵀ
        s↑ s′↑ pA pB (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-ν↑ᵀ
      vW noW vV′ noV′ source↑ target↑
      (transportType inner pB)
      (⊑-lift∀ᵢ (transportType inner pA)) liftρ₀ innerAll)

weak-one-step-matched-ν↑-blame-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Value V′ →
  No• V′ →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  sourceResult (weakResult (catchupAllResult catchup)) ≡ blame →
  WeakOneStepResult ρ
    (ν A N s) (((⇑ᵗᵐ V′) •) ⟨ s′ ⟩)
    B B′ (bind A′)
weak-one-step-matched-ν↑-blame-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl
    with silent
weak-one-step-matched-ν↑-blame-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl | left-silent-invariant refl refl
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν↑-blame-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl | left-silent-invariant refl refl | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = keep ∷ []} s′↑
weak-one-step-matched-ν↑-blame-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl | left-silent-invariant refl refl | ρ′ , liftρ
    | μᵣ , source↑ | μᵗ , target↑ =
  let
    first = weak-one-step-matched-ν-frameᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll)

    target⊢ =
      nu-term-imprecision-target-typing (relatedResults first)

    second = weak-one-step-source-blame-right-allocationᵀ
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′
      (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
      target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silentᵀ
    (left-silent first (left-silent-invariant refl refl)) second

weak-one-step-matched-ν↑-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Value V′ →
  No• V′ →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepResult ρ
    (ν A N s) (((⇑ᵗᵐ V′) •) ⟨ s′ ⟩)
    B B′ (bind A′)
weak-one-step-matched-ν↑-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup
    with sourceIsValueOrBlame (catchupAllInvariant catchup)
weak-one-step-matched-ν↑-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup
    | inj₁ (vW , noW) =
  weak-one-step-matched-ν↑-value-catchupᵀ
    s↑ s′↑ pA pB vV′ noV′ catchup vW noW
weak-one-step-matched-ν↑-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup
    | inj₂ eq-blame =
  weak-one-step-matched-ν↑-blame-catchupᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup eq-blame

------------------------------------------------------------------------
-- Synchronized `inst` allocation
------------------------------------------------------------------------

matched-νcast-allocation :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value N →
  No• N →
  Value N′ →
  No• N′ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  (ν ★ N s —→[ bind ★ ] ((⇑ᵗᵐ N) •) ⟨ s ⟩) ×
  (ν ★ N′ s′ —→[ bind ★ ] ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩) ×
  (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣
    store-matched zero ★ zero ★ id★ ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩
    ⦂ ⇑ᵗ B ⊑ ⇑ᵗ B′ ∶ ⊑-lift∀ᵢ pB)
matched-νcast-allocation {q = q} vN noN vN′ noN′ mode seal★ mode′
    seal★′ s⊑ s′⊑ pB liftρ N⊑N′ =
  ν-step vN noN ,
  ν-step vN′ noN′ ,
  conv⊑convᵀ
    (paired-widening
      (cast-inst mode) left-seal left-widening
      (cast-inst mode′) right-seal right-widening)
    (α⊑αᵀ vN noN vN′ noN′ id★ liftρ lift-ctx-[] N⊑N′
      left-bullet-typing right-bullet-typing)
  where
    left-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ _) ((zero , ★) ∷ Σ))
        (sym (leftStoreⁱ-lift liftρ))
        seal★

    right-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ _) ((zero , ★) ∷ Σ))
        (sym (rightStoreⁱ-lift liftρ))
        seal★′

    left-widening =
      subst
        (λ Σ → instᵈ _ ∣ suc _ ∣ (zero , ★) ∷ Σ
          ⊢ _ ∶ _ ⊑ ⇑ᵗ _)
        (sym (leftStoreⁱ-lift liftρ))
        s⊑

    right-widening =
      subst
        (λ Σ → instᵈ _ ∣ suc _ ∣ (zero , ★) ∷ Σ
          ⊢ _ ∶ _ ⊑ ⇑ᵗ _)
        (sym (rightStoreⁱ-lift liftρ))
        s′⊑

    left-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ★) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (leftStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-src-wf q) vN noN
          (nu-term-imprecision-source-typing N⊑N′))

    right-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ★) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (rightStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-tgt-wf q) vN′ noN′
          (nu-term-imprecision-target-typing N⊑N′))

weak-one-step-matched-νcastᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value N →
  No• N →
  Value N′ →
  No• N′ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  WeakOneStepResult ρ
    (ν ★ N s) (((⇑ᵗᵐ N′) •) ⟨ s′ ⟩)
    B B′ (bind ★)
weak-one-step-matched-νcastᵀ
    {B = B} {B′ = B′} {ρ′ = ρ′}
    vN noN vN′ noN′ mode seal★ mode′ seal★′ s⊑ s′⊑
    pB liftρ N⊑N′
    with matched-νcast-allocation
      vN noN vN′ noN′ mode seal★ mode′ seal★′ s⊑ s′⊑
      pB liftρ N⊑N′
weak-one-step-matched-νcastᵀ
    {B = B} {B′ = B′} {ρ′ = ρ′}
    vN noN vN′ noN′ mode seal★ mode′ seal★′ s⊑ s′⊑
    pB liftρ N⊑N′
    | source→ , _ , result =
  record
    { sourceChanges = bind ★ ∷ []
    ; targetTailChanges = []
    ; sourceResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
    ; targetResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
    ; resultCtx = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = store-matched zero ★ zero ★ id★ ∷ ρ′
    ; resultSourceType = ⇑ᵗ B
    ; resultTargetType = ⇑ᵗ B′
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = ⊑-lift∀ᵢ
    ; transportAllBody = ⊑-lift-under-∀ᵢ
    ; transportRightBody = ⊑-lift-under-rightᵢ
    ; resultType = ⊑-lift∀ᵢ pB
    ; sourceCatchup = ↠-step source→ ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult =
        cong ((zero , ★) ∷_) (leftStoreⁱ-lift liftρ)
    ; targetStoreResult =
        cong ((zero , ★) ∷_) (rightStoreⁱ-lift liftρ)
    ; relatedResults = result
    }

weak-one-step-matched-νcast-value-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Value V′ →
  No• V′ →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  Value (sourceResult (weakResult (catchupAllResult catchup))) →
  No• (sourceResult (weakResult (catchupAllResult catchup))) →
  WeakOneStepResult ρ
    (ν ★ N s) (((⇑ᵗᵐ V′) •) ⟨ s′ ⟩)
    B B′ (bind ★)
weak-one-step-matched-νcast-value-catchupᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW
    with lift-store-result (resultStore inner)
weak-one-step-matched-νcast-value-catchupᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ s⊑
       | apply-widen-inst-under-ty-binders
      {χs = keep ∷ []} mode′ seal★′ s′⊑
weak-one-step-matched-νcast-value-catchupᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW | ρ′ , liftρ₀
    | μᵣ , modeᵣ , sealᵣ , source⊑₀
    | μᵗ , modeᵗ , sealᵗ , target⊑₀
    with weak-result-source-widen-inst inner mode seal★ s⊑
       | weak-result-target-widen-inst
          keep inner mode′ seal★′ s′⊑
weak-one-step-matched-νcast-value-catchupᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW | ρ′ , liftρ₀
    | μᵣ , modeᵣ , sealᵣ , source⊑₀
    | μᵗ , modeᵗ , sealᵗ , target⊑₀
    | μˢ , modeˢ , sealˢ , source⊑
    | μᵗ′ , modeᵗ′ , sealᵗ′ , target⊑ =
  weak-one-step-prepend-left-silentᵀ
    (left-silent
      (weak-one-step-matched-νcast-frameᵀ
        mode seal★ s⊑ mode′ seal★′ s′⊑ pB
        (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-νcastᵀ
      vW noW vV′ noV′ modeˢ sealˢ modeᵗ′ sealᵗ′
      source⊑ target⊑ (transportType inner pB) liftρ₀ innerAll)

weak-one-step-matched-νcast-blame-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Value V′ →
  No• V′ →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  sourceResult (weakResult (catchupAllResult catchup)) ≡ blame →
  WeakOneStepResult ρ
    (ν ★ N s) (((⇑ᵗᵐ V′) •) ⟨ s′ ⟩)
    B B′ (bind ★)
weak-one-step-matched-νcast-blame-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl
    with silent
weak-one-step-matched-νcast-blame-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl | left-silent-invariant refl refl
    with lift-store-result (resultStore inner)
weak-one-step-matched-νcast-blame-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl | left-silent-invariant refl refl | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ s⊑
       | apply-widen-inst-under-ty-binders
      {χs = keep ∷ []} mode′ seal★′ s′⊑
weak-one-step-matched-νcast-blame-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl | left-silent-invariant refl refl | ρ′ , liftρ
    | μᵣ , modeᵣ , sealᵣ , source⊑
    | μᵗ , modeᵗ , sealᵗ , target⊑ =
  let
    first = weak-one-step-matched-νcast-frameᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll)

    target⊢ =
      nu-term-imprecision-target-typing (relatedResults first)

    second = weak-one-step-source-blame-right-allocationᵀ
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′ wf★ target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silentᵀ
    (left-silent first (left-silent-invariant refl refl)) second

weak-one-step-matched-νcast-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  Value V′ →
  No• V′ →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepResult ρ
    (ν ★ N s) (((⇑ᵗᵐ V′) •) ⟨ s′ ⟩)
    B B′ (bind ★)
weak-one-step-matched-νcast-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup
    with sourceIsValueOrBlame (catchupAllInvariant catchup)
weak-one-step-matched-νcast-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup | inj₁ (vW , noW) =
  weak-one-step-matched-νcast-value-catchupᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup vW noW
weak-one-step-matched-νcast-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup | inj₂ eq-blame =
  weak-one-step-matched-νcast-blame-catchupᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup eq-blame

left-νcast-allocation :
  ∀ {Φ Δᴸ Δᴿ B B′ C N N′ s μ q occ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value N →
  No• N →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ ν occ q →
  (ν ★ N s —→[ bind ★ ] ((⇑ᵗᵐ N) •) ⟨ s ⟩) ×
  (N′ —↠[ [] ] N′) ×
  (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero ★ wf★ ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ N′
    ⦂ ⇑ᵗ B ⊑ B′ ∶ ⊑-source-liftνᵢ pB)
left-νcast-allocation {q = q} vN noN mode seal★ s⊑ pB liftρ
    N⊑N′ =
  ν-step vN noN ,
  ↠-refl ,
  cast⊑⊑ᵀ (cast-inst mode) left-seal left-widening
    (α⊑ᵀ vN noN wf★ liftρ lift-left-ctx-[] N⊑N′
      left-bullet-typing right-term-typing)
    (⊑-source-liftνᵢ pB)
  where
    left-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ _) ((zero , ★) ∷ Σ))
        (sym (leftStoreⁱ-lift-left liftρ))
        seal★

    left-widening =
      subst
        (λ Σ → instᵈ _ ∣ suc _ ∣ (zero , ★) ∷ Σ
          ⊢ _ ∶ _ ⊑ ⇑ᵗ _)
        (sym (leftStoreⁱ-lift-left liftρ))
        s⊑

    left-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ★) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (leftStoreⁱ-lift-left liftρ))
        (⊢• refl refl (⊑-src-wf q) vN noN
          (nu-term-imprecision-source-typing N⊑N′))

    right-term-typing =
      subst
        (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
        (sym (rightStoreⁱ-lift-left liftρ))
        (nu-term-imprecision-target-typing N⊑N′)

------------------------------------------------------------------------
-- Left-only polymorphic allocation
------------------------------------------------------------------------

left-ν↑-allocation :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N N′ s μ q occ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value N →
  No• N →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ ν occ q →
  (ν A N s —→[ bind A ] ((⇑ᵗᵐ N) •) ⟨ s ⟩) ×
  (N′ —↠[ [] ] N′) ×
  (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero (⇑ᵗ A) h⇑A ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ N′
    ⦂ ⇑ᵗ B ⊑ B′ ∶ ⊑-source-liftνᵢ pB)
left-ν↑-allocation {q = q} vN noN h⇑A s↑ pB liftρ N⊑N′ =
  ν-step vN noN ,
  ↠-refl ,
  conv↑⊑ᵀ left-reveal
    (α⊑ᵀ vN noN h⇑A liftρ lift-left-ctx-[] N⊑N′
      left-bullet-typing right-term-typing)
    (⊑-source-liftνᵢ pB)
  where
    left-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (leftStoreⁱ-lift-left liftρ))
        s↑

    left-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (leftStoreⁱ-lift-left liftρ))
        (⊢• refl refl (⊑-src-wf q) vN noN
          (nu-term-imprecision-source-typing N⊑N′))

    right-term-typing =
      subst
        (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
        (sym (rightStoreⁱ-lift-left liftρ))
        (nu-term-imprecision-target-typing N⊑N′)

------------------------------------------------------------------------
-- Right-only polymorphic allocation
------------------------------------------------------------------------

right-ν↑-allocation :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  Value N′ →
  No• N′ →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
  (N —↠[ [] ] N) ×
  (ν A N′ s —→[ bind A ] ((⇑ᵗᵐ N′) •) ⟨ s ⟩) ×
  (⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣
    store-right zero (⇑ᵗ A) h⇑A ∷ ρ′ ∣ []
    ⊢ᴺ N ⊑ ((⇑ᵗᵐ N′) •) ⟨ s ⟩
    ⦂ B ⊑ ⇑ᵗ B′ ∶ ⊑-target-lift-rightᵢ pB)
right-ν↑-allocation {q = q} vN′ noN′ h⇑A s′↑ pB pC liftρ
    N⊑N′ =
  ↠-refl ,
  ν-step vN′ noN′ ,
  ⊑conv↑ᵀ right-reveal
    (⊑αᵀ vN′ noN′ h⇑A liftρ lift-right-ctx-[] N⊑N′ pC
      left-term-typing right-bullet-typing)
    (⊑-target-lift-rightᵢ pB)
  where
    right-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (rightStoreⁱ-lift-right liftρ))
        s′↑

    left-term-typing =
      subst
        (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
        (sym (leftStoreⁱ-lift-right liftρ))
        (nu-term-imprecision-source-typing N⊑N′)

    right-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (rightStoreⁱ-lift-right liftρ))
        (⊢• refl refl (∀-imprecision-target-body-wf q) vN′ noN′
          (nu-term-imprecision-target-typing N⊑N′))

weak-one-step-right-ν↑ᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  Value N′ →
  No• N′ →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
  WeakOneStepResult ρ N (((⇑ᵗᵐ N′) •) ⟨ s ⟩)
    B B′ (bind A)
weak-one-step-right-ν↑ᵀ
    {A = A} {B = B} {B′ = B′} {ρ′ = ρ′}
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
    with right-ν↑-allocation
      vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
weak-one-step-right-ν↑ᵀ
    {A = A} {B = B} {B′ = B′} {ρ′ = ρ′}
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
    | _ , _ , result =
  record
    { sourceChanges = []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
    ; resultCtx = ⇑ᴿᵢ _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = store-right zero (⇑ᵗ A) h⇑A ∷ ρ′
    ; resultSourceType = B
    ; resultTargetType = ⇑ᵗ B′
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = ⊑-target-lift-rightᵢ
    ; transportAllBody = ⊑-target-lift-right-under-∀ᵢ
    ; transportRightBody = ⊑-target-lift-under-rightᵢ
    ; resultType = ⊑-target-lift-rightᵢ pB
    ; sourceCatchup = ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = leftStoreⁱ-lift-right liftρ
    ; targetStoreResult =
        cong ((zero , ⇑ᵗ A) ∷_) (rightStoreⁱ-lift-right liftρ)
    ; relatedResults = result
    }

------------------------------------------------------------------------
-- Right-only `inst` allocation
------------------------------------------------------------------------

right-νcast-allocation :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  Value N′ →
  No• N′ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
  (N —↠[ [] ] N) ×
  (ν ★ N′ s —→[ bind ★ ] ((⇑ᵗᵐ N′) •) ⟨ s ⟩) ×
  (⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣
    store-right zero ★ wf★ ∷ ρ′ ∣ []
    ⊢ᴺ N ⊑ ((⇑ᵗᵐ N′) •) ⟨ s ⟩
    ⦂ B ⊑ ⇑ᵗ B′ ∶ ⊑-target-lift-rightᵢ pB)
right-νcast-allocation {q = q} vN′ noN′ mode seal★ s⊑ pB pC
    liftρ N⊑N′ =
  ↠-refl ,
  ν-step vN′ noN′ ,
  ⊑cast⊑ᵀ (cast-inst mode) right-seal right-widening
    (⊑αᵀ vN′ noN′ wf★ liftρ lift-right-ctx-[] N⊑N′ pC
      left-term-typing right-bullet-typing)
    (⊑-target-lift-rightᵢ pB)
  where
    right-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ _) ((zero , ★) ∷ Σ))
        (sym (rightStoreⁱ-lift-right liftρ))
        seal★

    right-widening =
      subst
        (λ Σ → instᵈ _ ∣ suc _ ∣ (zero , ★) ∷ Σ
          ⊢ _ ∶ _ ⊑ ⇑ᵗ _)
        (sym (rightStoreⁱ-lift-right liftρ))
        s⊑

    left-term-typing =
      subst
        (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
        (sym (leftStoreⁱ-lift-right liftρ))
        (nu-term-imprecision-source-typing N⊑N′)

    right-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ★) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (rightStoreⁱ-lift-right liftρ))
        (⊢• refl refl (∀-imprecision-target-body-wf q) vN′ noN′
          (nu-term-imprecision-target-typing N⊑N′))

weak-one-step-right-νcastᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  Value N′ →
  No• N′ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
  WeakOneStepResult ρ N (((⇑ᵗᵐ N′) •) ⟨ s ⟩)
    B B′ (bind ★)
weak-one-step-right-νcastᵀ
    {B = B} {B′ = B′} {ρ′ = ρ′}
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
    with right-νcast-allocation
      vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
weak-one-step-right-νcastᵀ
    {B = B} {B′ = B′} {ρ′ = ρ′}
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
    | _ , _ , result =
  record
    { sourceChanges = []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
    ; resultCtx = ⇑ᴿᵢ _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = store-right zero ★ wf★ ∷ ρ′
    ; resultSourceType = B
    ; resultTargetType = ⇑ᵗ B′
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = ⊑-target-lift-rightᵢ
    ; transportAllBody = ⊑-target-lift-right-under-∀ᵢ
    ; transportRightBody = ⊑-target-lift-under-rightᵢ
    ; resultType = ⊑-target-lift-rightᵢ pB
    ; sourceCatchup = ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = leftStoreⁱ-lift-right liftρ
    ; targetStoreResult =
        cong ((zero , ★) ∷_) (rightStoreⁱ-lift-right liftρ)
    ; relatedResults = result
    }

------------------------------------------------------------------------
-- `β-inst` followed by `ν ★` allocation
------------------------------------------------------------------------

matched-β-inst-νcast-allocation :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value N →
  No• N →
  Value N′ →
  No• N′ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  CastMode μ′ →
  SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  instᵈ μ′ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
  (N ⟨ inst B s ⟩
    —↠[ keep ∷ bind ★ ∷ [] ] ((⇑ᵗᵐ N) •) ⟨ s ⟩) ×
  (N′ ⟨ inst B′ s′ ⟩
    —↠[ keep ∷ bind ★ ∷ [] ] ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩) ×
  (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣
    store-matched zero ★ zero ★ id★ ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩
    ⦂ ⇑ᵗ B ⊑ ⇑ᵗ B′ ∶ ⊑-lift∀ᵢ pB)
matched-β-inst-νcast-allocation vN noN vN′ noN′ mode seal★
    mode′ seal★′ s⊑ s′⊑ pB liftρ N⊑N′
    with matched-νcast-allocation vN noN vN′ noN′ mode seal★
      mode′ seal★′ s⊑ s′⊑ pB liftρ N⊑N′
matched-β-inst-νcast-allocation vN noN vN′ noN′ mode seal★
    mode′ seal★′ s⊑ s′⊑ pB liftρ N⊑N′
    | N→ , N′→ , result =
  ↠-step (post-β-inst vN) (↠-step N→ ↠-refl) ,
  ↠-step (post-β-inst vN′) (↠-step N′→ ↠-refl) ,
  result

left-β-inst-νcast-allocation :
  ∀ {Φ Δᴸ Δᴿ B B′ C N N′ s μ q occ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value N →
  No• N →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ ν occ q →
  (N ⟨ inst B s ⟩
    —↠[ keep ∷ bind ★ ∷ [] ] ((⇑ᵗᵐ N) •) ⟨ s ⟩) ×
  (N′ —↠[ [] ] N′) ×
  (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero ★ wf★ ∷ ρ′ ∣ []
    ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩ ⊑ N′
    ⦂ ⇑ᵗ B ⊑ B′ ∶ ⊑-source-liftνᵢ pB)
left-β-inst-νcast-allocation vN noN mode seal★ s⊑ pB liftρ N⊑N′
    with left-νcast-allocation vN noN mode seal★ s⊑ pB liftρ N⊑N′
left-β-inst-νcast-allocation vN noN mode seal★ s⊑ pB liftρ N⊑N′
    | N→ , N′→ , result =
  ↠-step (post-β-inst vN) (↠-step N→ ↠-refl) ,
  N′→ ,
  result

right-β-inst-νcast-allocation :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  Value N′ →
  No• N′ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴿ ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
  (N —↠[ [] ] N) ×
  (N′ ⟨ inst B′ s ⟩
    —↠[ keep ∷ bind ★ ∷ [] ] ((⇑ᵗᵐ N′) •) ⟨ s ⟩) ×
  (⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣
    store-right zero ★ wf★ ∷ ρ′ ∣ []
    ⊢ᴺ N ⊑ ((⇑ᵗᵐ N′) •) ⟨ s ⟩
    ⦂ B ⊑ ⇑ᵗ B′ ∶ ⊑-target-lift-rightᵢ pB)
right-β-inst-νcast-allocation vN′ noN′ mode seal★ s⊑ pB pC liftρ
    N⊑N′
    with right-νcast-allocation vN′ noN′ mode seal★ s⊑ pB pC
      liftρ N⊑N′
right-β-inst-νcast-allocation vN′ noN′ mode seal★ s⊑ pB pC liftρ
    N⊑N′ | N→ , N′→ , result =
  N→ ,
  ↠-step (post-β-inst vN′) (↠-step N′→ ↠-refl) ,
  result

------------------------------------------------------------------------
-- Allocation followed by `β-Λ•`
------------------------------------------------------------------------

matched-ν↑-β-Λ• :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ V V′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ q →
  (ν A (Λ V) s —↠[ bind A ∷ keep ∷ [] ] V ⟨ s ⟩) ×
  (ν A′ (Λ V′) s′
    —↠[ bind A′ ∷ keep ∷ [] ] V′ ⟨ s′ ⟩) ×
  (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣
    store-matched zero (⇑ᵗ A) zero (⇑ᵗ A′) A⇑⊑A′⇑ ∷ ρ′
    ∣ []
    ⊢ᴺ V ⟨ s ⟩ ⊑ V′ ⟨ s′ ⟩
    ⦂ ⇑ᵗ B ⊑ ⇑ᵗ B′ ∶ ⊑-lift∀ᵢ pB)
matched-ν↑-β-Λ• {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {A′ = A′}
    {C = C} {C′ = C′} {V = V} {V′ = V′} {ρ′ = ρ′}
    vV noV vV′ noV′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ
    V⊑V′ =
  ↠-step (ν-step (Λ vV) (no•-Λ noV))
    (↠-step (post-allocation-β-Λ• vV) ↠-refl) ,
  ↠-step (ν-step (Λ vV′) (no•-Λ noV′))
    (↠-step (post-allocation-β-Λ• vV′) ↠-refl) ,
  conv⊑convᵀ
    (paired-conversion
      (paired-reveal (correspondence-stored (here refl))
        left-reveal right-reveal))
    (allocation-matchedᵀ A⇑⊑A′⇑ liftρ V⊑V′
      left-body-typing right-body-typing)
  where
    left-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (leftStoreⁱ-lift liftρ))
        s↑

    right-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (rightStoreⁱ-lift liftρ))
        s′↑

    left-body-typing :
      suc Δᴸ ∣ (zero , ⇑ᵗ A) ∷ leftStoreⁱ ρ′ ∣ [] ⊢ V ⦂ C
    left-body-typing =
      term-weaken {Δ = suc Δᴸ} {Δ′ = suc Δᴸ}
        {Σ = leftStoreⁱ ρ′}
        {Σ′ = (zero , ⇑ᵗ A) ∷ leftStoreⁱ ρ′}
        {Γ = []} {M = V} {A = C} ≤-refl StoreIncl-drop noV
        (nu-term-imprecision-source-typing V⊑V′)

    right-body-typing :
      suc Δᴿ ∣ (zero , ⇑ᵗ A′) ∷ rightStoreⁱ ρ′ ∣ []
        ⊢ V′ ⦂ C′
    right-body-typing =
      term-weaken {Δ = suc Δᴿ} {Δ′ = suc Δᴿ}
        {Σ = rightStoreⁱ ρ′}
        {Σ′ = (zero , ⇑ᵗ A′) ∷ rightStoreⁱ ρ′}
        {Γ = []} {M = V′} {A = C′} ≤-refl StoreIncl-drop noV′
        (nu-term-imprecision-target-typing V⊑V′)

left-ν↑-β-Λ• :
  ∀ {Φ Δᴸ Δᴿ A B B′ C V N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ C ⊑ B′ ∶ q →
  (ν A (Λ V) s —↠[ bind A ∷ keep ∷ [] ] V ⟨ s ⟩) ×
  (N′ —↠[ [] ] N′) ×
  (((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero (⇑ᵗ A) h⇑A ∷ ρ′ ∣ []
    ⊢ᴺ V ⟨ s ⟩ ⊑ N′
    ⦂ ⇑ᵗ B ⊑ B′ ∶ ⊑-source-liftνᵢ pB)
left-ν↑-β-Λ• {Δᴸ = Δᴸ} {A = A} {C = C} {V = V}
    {ρ′ = ρ′} vV noV h⇑A s↑ pB liftρ V⊑N′ =
  ↠-step (ν-step (Λ vV) (no•-Λ noV))
    (↠-step (post-allocation-β-Λ• vV) ↠-refl) ,
  ↠-refl ,
  conv↑⊑ᵀ left-reveal
    (allocation-leftᵀ h⇑A liftρ V⊑N′
      source-body-typing
      (nu-term-imprecision-target-typing V⊑N′))
    (⊑-source-liftνᵢ pB)
  where
    left-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (leftStoreⁱ-lift-left liftρ))
        s↑

    source-body-typing :
      suc Δᴸ ∣ (zero , ⇑ᵗ A) ∷ leftStoreⁱ ρ′ ∣ [] ⊢ V ⦂ C
    source-body-typing =
      term-weaken {Δ = suc Δᴸ} {Δ′ = suc Δᴸ}
        {Σ = leftStoreⁱ ρ′}
        {Σ′ = (zero , ⇑ᵗ A) ∷ leftStoreⁱ ρ′}
        {Γ = []} {M = V} {A = C} ≤-refl StoreIncl-drop noV
        (nu-term-imprecision-source-typing V⊑N′)

------------------------------------------------------------------------
-- Matched allocation followed by `β-gen•`
------------------------------------------------------------------------

matched-post-allocation-β-genᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν Aν′ A A′ B B′ V V′ c c′ p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γ′ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  Value V →
  Value V′ →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ gen A c ∶ A ⊒ `∀ B →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ gen A′ c′ ∶ A′ ⊒ `∀ B′ →
  (pν : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ Aν ⊑ Aν′ ⊣ suc Δᴿ) →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ
    ∣ store-matched zero Aν zero Aν′ pν ∷ ρ′ ∣ γ′
    ⊢ᴺ ⇑ᵗᵐ V ⊑ ⇑ᵗᵐ V′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ A′ ∶ p →
  (q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ B ⊑ᵖ B′ ⊣ suc Δᴿ) →
  (((⇑ᵗᵐ (V ⟨ gen A c ⟩)) •
      —→[ keep ] (⇑ᵗᵐ V) ⟨ c ⟩) ×
   ((⇑ᵗᵐ (V′ ⟨ gen A′ c′ ⟩)) •
      —→[ keep ] (⇑ᵗᵐ V′) ⟨ c′ ⟩) ×
   (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ
      ∣ store-matched zero Aν zero Aν′ pν ∷ ρ′ ∣ γ′
      ⊢ᴺᵖ (⇑ᵗᵐ V) ⟨ c ⟩ ⊑ (⇑ᵗᵐ V′) ⟨ c′ ⟩
      ⦂ B ⊑ᵖ B′ ∶ q))
matched-post-allocation-β-genᵀ {Aν = Aν} {Aν′ = Aν′} vV vV′
    c⊒ c′⊒ pν liftρ V⊑V′ q =
  post-allocation-β-gen•-bare vV ,
  post-allocation-β-gen•-bare vV′ ,
  gen-down⊑gen-downᵀ
    (narrow-mode-relax (ModeIncl-gen id-only≤tag-or-idᵈ) left-body)
    (narrow-mode-relax (ModeIncl-gen id-only≤tag-or-idᵈ) right-body)
    V⊑V′ q
  where
    left-body =
      subst
        (λ Σ → genᵈ id-onlyᵈ ∣ _ ∣ (zero , Aν) ∷ Σ
          ⊢ _ ∶ _ ⊒ _)
        (sym (leftStoreⁱ-lift liftρ))
        (allocate-gen-narrowing {Aν = Aν} c⊒)

    right-body =
      subst
        (λ Σ → genᵈ id-onlyᵈ ∣ _ ∣ (zero , Aν′) ∷ Σ
          ⊢ _ ∶ _ ⊒ _)
        (sym (rightStoreⁱ-lift liftρ))
        (allocate-gen-narrowing {Aν = Aν′} c′⊒)
