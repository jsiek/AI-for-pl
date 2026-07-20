module proof.NuImprecisionAllocationSimulation where

-- File Charter:
--   * Collects completed synchronized, left-only, and right-only allocation
--     simulations after the universal catch-up layer.
--   * Covers ordinary `ν`, `ν ★`, `inst`, post-allocation `β-Λ•`, and
--     post-allocation `β-gen•` boundaries.
--   * Depends on `NuImprecisionSimulationCore` and
--     `NuImprecisionSimulation`; it is kept separate so these stable cases
--     can be cached while active catch-up work changes.

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

open import proof.NuImprecisionSimulationCore
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionSimulation

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

weak-one-step-matched-ν↑-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  (vN : Value N) →
  (noN : No• N) →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (liftρ : LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  WeakOneStepTransport
    (weak-one-step-matched-ν↑ᵀ
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′)
weak-one-step-matched-ν↑-transportᵀ
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
    with matched-ν↑-allocation
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
weak-one-step-matched-ν↑-transportᵀ
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
    | source→ , target→ , result =
  weak-step-transport
    (matched-lift-prefix-bodyᵀ liftρ (prefix-∷ⁱ prefix-reflⁱ))

weak-one-step-matched-ν↑-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  (vN : Value N) →
  (noN : No• N) →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (liftρ : LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-ν↑ᵀ
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′)
weak-one-step-matched-ν↑-type-coherenceᵀ
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
    with matched-ν↑-allocation
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
weak-one-step-matched-ν↑-type-coherenceᵀ
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ liftρ N⊑N′
    | source→ , target→ , result =
  weak-step-type-coherence (λ pC pD → refl) (λ q′ → refl)

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
    vW noW =
  weak-one-step-prepend-left-silentᵀ
    (left-silent
      (weak-one-step-matched-ν-frameᵀ
        s↑ s′↑ pA pB (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-ν↑ᵀ
      vW noW vV′ noV′ source↑ target↑
      (transportType inner pB)
      (⊑-lift∀ᵢ (transportType inner pA)) liftρ₀ innerAll)
  where
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source↑ = proj₂ (weak-result-source-reveal inner s↑)
  target↑ = proj₂ (weak-result-target-reveal keep inner s′↑)

weak-one-step-matched-ν↑-value-catchup-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (vW : Value
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  (noW : No•
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  WeakOneStepTransport (weakResult (catchupAllResult catchup)) →
  WeakOneStepTransport
    (weak-one-step-matched-ν↑-value-catchupᵀ
      s↑ s′↑ pA pB vV′ noV′ catchup vW noW)
weak-one-step-matched-ν↑-value-catchup-transportᵀ
    s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW inner-transport =
  weak-one-step-prepend-left-silent-preserves-transportᵀ
    (left-silent
      (weak-one-step-matched-ν-frameᵀ
        s↑ s′↑ pA pB (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-ν↑ᵀ
      vW noW vV′ noV′ source↑ target↑
      (transportType inner pB)
      (⊑-lift∀ᵢ (transportType inner pA)) liftρ₀ innerAll)
    (weak-one-step-matched-ν-frame-preserves-transportᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll)
      inner-transport)
    (weak-one-step-matched-ν↑-transportᵀ
      vW noW vV′ noV′ source↑ target↑
      (transportType inner pB)
      (⊑-lift∀ᵢ (transportType inner pA)) liftρ₀ innerAll)
  where
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source↑ = proj₂ (weak-result-source-reveal inner s↑)
  target↑ = proj₂ (weak-result-target-reveal keep inner s′↑)

weak-one-step-matched-ν↑-value-catchup-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (vW : Value
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  (noW : No•
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  WeakOneStepTypeCoherence (weakResult (catchupAllResult catchup)) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-ν↑-value-catchupᵀ
      s↑ s′↑ pA pB vV′ noV′ catchup vW noW)
weak-one-step-matched-ν↑-value-catchup-type-coherenceᵀ
    s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW inner-coherence =
  weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
    (left-silent
      (weak-one-step-matched-ν-frameᵀ
        s↑ s′↑ pA pB (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-ν↑ᵀ
      vW noW vV′ noV′ source↑ target↑
      (transportType inner pB)
      (⊑-lift∀ᵢ (transportType inner pA)) liftρ₀ innerAll)
    (weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll)
      inner-coherence)
    (weak-one-step-matched-ν↑-type-coherenceᵀ
      vW noW vV′ noV′ source↑ target↑
      (transportType inner pB)
      (⊑-lift∀ᵢ (transportType inner pA)) liftρ₀ innerAll)
  where
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source↑ = proj₂ (weak-result-source-reveal inner s↑)
  target↑ = proj₂ (weak-result-target-reveal keep inner s′↑)

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
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl
    with silent
weak-one-step-matched-ν↑-blame-catchupᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
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
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
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
      {A = applyTys (sourceChanges inner) A}
      {A′ = applyTys (targetTailChanges inner) (applyTy keep A′)}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′
      (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
      target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silentᵀ
    (left-silent first (left-silent-invariant refl refl)) second

weak-one-step-matched-ν↑-blame-catchup-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (eq-blame :
    sourceResult (weakResult (catchupAllResult catchup)) ≡ blame) →
  WeakOneStepTransport (weakResult (catchupAllResult catchup)) →
  WeakOneStepTransport
    (weak-one-step-matched-ν↑-blame-catchupᵀ
      wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup eq-blame)
weak-one-step-matched-ν↑-blame-catchup-transportᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport
    with silent
weak-one-step-matched-ν↑-blame-catchup-transportᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport | left-silent-invariant refl refl
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν↑-blame-catchup-transportᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport | left-silent-invariant refl refl
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = keep ∷ []} s′↑
weak-one-step-matched-ν↑-blame-catchup-transportᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport | left-silent-invariant refl refl
    | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
  let
    first = weak-one-step-matched-ν-frameᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll)

    target⊢ =
      nu-term-imprecision-target-typing (relatedResults first)

    second = weak-one-step-source-blame-right-allocationᵀ
      {A = applyTys (sourceChanges inner) A}
      {A′ = applyTys (targetTailChanges inner) (applyTy keep A′)}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′
      (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
      target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silent-preserves-transportᵀ
    (left-silent first (left-silent-invariant refl refl))
    second
    (weak-one-step-matched-ν-frame-preserves-transportᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll)
      inner-transport)
    (weak-one-step-source-blame-right-allocation-transportᵀ
      {A = applyTys (sourceChanges inner) A}
      {A′ = applyTys (targetTailChanges inner) (applyTy keep A′)}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′
      (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
      target⊢ (transportType inner pB))

weak-one-step-matched-ν↑-blame-catchup-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (eq-blame :
    sourceResult (weakResult (catchupAllResult catchup)) ≡ blame) →
  WeakOneStepTypeCoherence (weakResult (catchupAllResult catchup)) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-ν↑-blame-catchupᵀ
      wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup eq-blame)
weak-one-step-matched-ν↑-blame-catchup-type-coherenceᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence
    with silent
weak-one-step-matched-ν↑-blame-catchup-type-coherenceᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence | left-silent-invariant refl refl
    with lift-store-result (resultStore inner)
weak-one-step-matched-ν↑-blame-catchup-type-coherenceᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence | left-silent-invariant refl refl
    | ρ′ , liftρ
    with apply-reveal-under-ty-binders
      {χs = sourceChanges inner} s↑
       | apply-reveal-under-ty-binders
      {χs = keep ∷ []} s′↑
weak-one-step-matched-ν↑-blame-catchup-type-coherenceᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence | left-silent-invariant refl refl
    | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
  let
    first = weak-one-step-matched-ν-frameᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll)

    target⊢ =
      nu-term-imprecision-target-typing (relatedResults first)

    second = weak-one-step-source-blame-right-allocationᵀ
      {A = applyTys (sourceChanges inner) A}
      {A′ = applyTys (targetTailChanges inner) (applyTy keep A′)}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′
      (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
      target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
    (left-silent first (left-silent-invariant refl refl))
    second
    (weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
      s↑ s′↑ pA pB (weak-all-result inner innerAll)
      inner-coherence)
    (weak-one-step-source-blame-right-allocation-type-coherenceᵀ
      {A = applyTys (sourceChanges inner) A}
      {A′ = applyTys (targetTailChanges inner) (applyTy keep A′)}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′
      (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
      target⊢ (transportType inner pB))

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

weak-one-step-matched-ν↑-catchup-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepTransport (weakResult (catchupAllResult catchup)) →
  WeakOneStepTransport
    (weak-one-step-matched-ν↑-catchupᵀ
      wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup)
weak-one-step-matched-ν↑-catchup-transportᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup transport
    with sourceIsValueOrBlame (catchupAllInvariant catchup)
weak-one-step-matched-ν↑-catchup-transportᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup transport
    | inj₁ (vW , noW) =
  weak-one-step-matched-ν↑-value-catchup-transportᵀ
    s↑ s′↑ pA pB vV′ noV′ catchup vW noW transport
weak-one-step-matched-ν↑-catchup-transportᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup transport
    | inj₂ eq-blame =
  weak-one-step-matched-ν↑-blame-catchup-transportᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup eq-blame
    transport

weak-one-step-matched-ν↑-catchup-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepTypeCoherence (weakResult (catchupAllResult catchup)) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-ν↑-catchupᵀ
      wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup)
weak-one-step-matched-ν↑-catchup-type-coherenceᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup coherence
    with sourceIsValueOrBlame (catchupAllInvariant catchup)
weak-one-step-matched-ν↑-catchup-type-coherenceᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup coherence
    | inj₁ (vW , noW) =
  weak-one-step-matched-ν↑-value-catchup-type-coherenceᵀ
    s↑ s′↑ pA pB vV′ noV′ catchup vW noW coherence
weak-one-step-matched-ν↑-catchup-type-coherenceᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup coherence
    | inj₂ eq-blame =
  weak-one-step-matched-ν↑-blame-catchup-type-coherenceᵀ
    wfΣ′ s↑ s′↑ pA pB vV′ noV′ catchup eq-blame
    coherence

weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (s↑ : RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B)) →
  (s′↑ : RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup : LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepIndexedOutcome
    {M = ν A N s}
    {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
    {A = B} {B = B′} {χ = bind A′} {ρ = ρ} pB
weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    with final
weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₁ (vW , noW) =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result type-eq)
    transport coherence
  where
  old-catchup = left-all-catchup
    (weak-indexed-all-resultᵀ indexed inner-coherence)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

  result =
    weak-one-step-matched-ν↑-value-catchupᵀ
      s↑ s′↑ pA pB vV′ noV′ old-catchup vW noW

  inner = weakResult (catchupAllResult old-catchup)
  innerAll = canonicalAllResults (catchupAllResult old-catchup)
  first = weak-one-step-matched-ν-frameᵀ
    s↑ s′↑ pA pB (catchupAllResult old-catchup)
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source↑ = proj₂ (weak-result-source-reveal inner s↑)
  target↑ = proj₂ (weak-result-target-reveal keep inner s′↑)
  second = weak-one-step-matched-ν↑ᵀ
    vW noW vV′ noV′ source↑ target↑
    (transportType inner pB)
    (⊑-lift∀ᵢ (transportType inner pA)) liftρ₀ innerAll

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx result ∣ resultLeftCtx result
          ⊢ S ⊑ T ⊣ resultRightCtx result}
        (sourceTypeResult result)
        (targetTypeResult result)
        (resultType result))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second pB)))

  transport =
    weak-one-step-matched-ν↑-value-catchup-transportᵀ
      s↑ s′↑ pA pB vV′ noV′ old-catchup vW noW
      inner-transport

  coherence =
    weak-one-step-matched-ν↑-value-catchup-type-coherenceᵀ
      s↑ s′↑ pA pB vV′ noV′ old-catchup vW noW
      inner-coherence
weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {s = s} {s′ = s′}
    wfΣ′ s↑ s′↑ pA pB vV′ noV′
    (left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₂ refl =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result type-eq)
    transport coherence
  where
  old-catchup = left-all-catchup
    (weak-indexed-all-resultᵀ indexed inner-coherence)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

  inner = weakResult (catchupAllResult old-catchup)
  first = weak-one-step-matched-ν-frameᵀ
    s↑ s′↑ pA pB (catchupAllResult old-catchup)
  target⊢ = nu-term-imprecision-target-typing (relatedResults first)
  second = weak-one-step-source-blame-right-allocationᵀ
    {A = applyTys (sourceChanges inner) A}
    {A′ = applyTys (targetTailChanges inner) (applyTy keep A′)}
    {B = applyTys (sourceChanges inner) B}
    {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
    {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
    {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
      (applyCoercionUnderTyBinder keep s′)}
    {ρ = resultStore inner}
    (weak-result-right-wf-silent inner
      (left-silent-invariant refl refl) wfΣ′)
    vV′ noV′
    (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
    target⊢ (transportType inner pB)

  result =
    weak-one-step-prepend-left-silentᵀ
      (left-silent first (left-silent-invariant refl refl)) second

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx result ∣ resultLeftCtx result
          ⊢ S ⊑ T ⊣ resultRightCtx result}
        (sourceTypeResult result)
        (targetTypeResult result)
        (resultType result))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second pB)))

  transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      (weak-one-step-matched-ν-frame-preserves-transportᵀ
        s↑ s′↑ pA pB (catchupAllResult old-catchup)
        inner-transport)
      (weak-one-step-source-blame-right-allocation-transportᵀ
        {A = applyTys (sourceChanges inner) A}
        {A′ = applyTys (targetTailChanges inner)
          (applyTy keep A′)}
        {B = applyTys (sourceChanges inner) B}
        {B′ = applyTys (targetTailChanges inner)
          (applyTy keep B′)}
        {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
        {s′ = applyCoercionUnderTyBinders
          (targetTailChanges inner)
          (applyCoercionUnderTyBinder keep s′)}
        {ρ = resultStore inner}
        (weak-result-right-wf-silent inner
          (left-silent-invariant refl refl) wfΣ′)
        vV′ noV′
        (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
        target⊢ (transportType inner pB))

  coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      (weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
        s↑ s′↑ pA pB (catchupAllResult old-catchup)
        inner-coherence)
      (weak-one-step-source-blame-right-allocation-type-coherenceᵀ
        {A = applyTys (sourceChanges inner) A}
        {A′ = applyTys (targetTailChanges inner)
          (applyTy keep A′)}
        {B = applyTys (sourceChanges inner) B}
        {B′ = applyTys (targetTailChanges inner)
          (applyTy keep B′)}
        {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
        {s′ = applyCoercionUnderTyBinders
          (targetTailChanges inner)
          (applyCoercionUnderTyBinder keep s′)}
        {ρ = resultStore inner}
        (weak-result-right-wf-silent inner
          (left-silent-invariant refl refl) wfΣ′)
        vV′ noV′
        (⊑-tgt-wf (⊑-lift∀ᵢ (transportType inner pA)))
        target⊢ (transportType inner pB))

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

weak-one-step-matched-νcast-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  (vN : Value N) →
  (noN : No• N) →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (liftρ : LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  WeakOneStepTransport
    (weak-one-step-matched-νcastᵀ
      vN noN vN′ noN′ mode seal★ mode′ seal★′
      s⊑ s′⊑ pB liftρ N⊑N′)
weak-one-step-matched-νcast-transportᵀ
    vN noN vN′ noN′ mode seal★ mode′ seal★′
    s⊑ s′⊑ pB liftρ N⊑N′
    with matched-νcast-allocation
      vN noN vN′ noN′ mode seal★ mode′ seal★′
      s⊑ s′⊑ pB liftρ N⊑N′
weak-one-step-matched-νcast-transportᵀ
    vN noN vN′ noN′ mode seal★ mode′ seal★′
    s⊑ s′⊑ pB liftρ N⊑N′
    | source→ , target→ , result =
  weak-step-transport
    (matched-lift-prefix-bodyᵀ liftρ (prefix-∷ⁱ prefix-reflⁱ))

weak-one-step-matched-νcast-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N N′ s s′ μ μ′ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  (vN : Value N) →
  (noN : No• N) →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (liftρ : LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-νcastᵀ
      vN noN vN′ noN′ mode seal★ mode′ seal★′
      s⊑ s′⊑ pB liftρ N⊑N′)
weak-one-step-matched-νcast-type-coherenceᵀ
    vN noN vN′ noN′ mode seal★ mode′ seal★′
    s⊑ s′⊑ pB liftρ N⊑N′
    with matched-νcast-allocation
      vN noN vN′ noN′ mode seal★ mode′ seal★′
      s⊑ s′⊑ pB liftρ N⊑N′
weak-one-step-matched-νcast-type-coherenceᵀ
    vN noN vN′ noN′ mode seal★ mode′ seal★′
    s⊑ s′⊑ pB liftρ N⊑N′ | source→ , target→ , result =
  weak-step-type-coherence (λ pC pD → refl) (λ q′ → refl)

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
    vW noW =
  weak-one-step-prepend-left-silentᵀ
    (left-silent
      (weak-one-step-matched-νcast-frameᵀ
        mode seal★ s⊑ mode′ seal★′ s′⊑ pB
        (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-νcastᵀ
      vW noW vV′ noV′ modeˢ sealˢ modeᵗ′ sealᵗ′
      source⊑ target⊑ (transportType inner pB) liftρ₀ innerAll)
  where
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source = weak-result-source-widen-inst inner mode seal★ s⊑
  modeˢ = proj₁ (proj₂ source)
  sealˢ = proj₁ (proj₂ (proj₂ source))
  source⊑ = proj₂ (proj₂ (proj₂ source))
  target = weak-result-target-widen-inst
    keep inner mode′ seal★′ s′⊑
  modeᵗ′ = proj₁ (proj₂ target)
  sealᵗ′ = proj₁ (proj₂ (proj₂ target))
  target⊑ = proj₂ (proj₂ (proj₂ target))

weak-one-step-matched-νcast-value-catchup-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (vW : Value
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  (noW : No•
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  WeakOneStepTransport (weakResult (catchupAllResult catchup)) →
  WeakOneStepTransport
    (weak-one-step-matched-νcast-value-catchupᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ catchup vW noW)
weak-one-step-matched-νcast-value-catchup-transportᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW inner-transport =
  weak-one-step-prepend-left-silent-preserves-transportᵀ
    (left-silent
      (weak-one-step-matched-νcast-frameᵀ
        mode seal★ s⊑ mode′ seal★′ s′⊑ pB
        (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-νcastᵀ
      vW noW vV′ noV′ modeˢ sealˢ modeᵗ′ sealᵗ′
      source⊑ target⊑ (transportType inner pB) liftρ₀ innerAll)
    (weak-one-step-matched-νcast-frame-preserves-transportᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll) inner-transport)
    (weak-one-step-matched-νcast-transportᵀ
      vW noW vV′ noV′ modeˢ sealˢ modeᵗ′ sealᵗ′
      source⊑ target⊑ (transportType inner pB) liftρ₀ innerAll)
  where
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source = weak-result-source-widen-inst inner mode seal★ s⊑
  modeˢ = proj₁ (proj₂ source)
  sealˢ = proj₁ (proj₂ (proj₂ source))
  source⊑ = proj₂ (proj₂ (proj₂ source))
  target = weak-result-target-widen-inst
    keep inner mode′ seal★′ s′⊑
  modeᵗ′ = proj₁ (proj₂ target)
  sealᵗ′ = proj₁ (proj₂ (proj₂ target))
  target⊑ = proj₂ (proj₂ (proj₂ target))

weak-one-step-matched-νcast-value-catchup-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (vW : Value
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  (noW : No•
    (sourceResult (weakResult (catchupAllResult catchup)))) →
  WeakOneStepTypeCoherence (weakResult (catchupAllResult catchup)) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-νcast-value-catchupᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ catchup vW noW)
weak-one-step-matched-νcast-value-catchup-type-coherenceᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW inner-coherence =
  weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
    (left-silent
      (weak-one-step-matched-νcast-frameᵀ
        mode seal★ s⊑ mode′ seal★′ s′⊑ pB
        (weak-all-result inner innerAll))
      (left-silent-invariant refl refl))
    (weak-one-step-matched-νcastᵀ
      vW noW vV′ noV′ modeˢ sealˢ modeᵗ′ sealᵗ′
      source⊑ target⊑ (transportType inner pB) liftρ₀ innerAll)
    (weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll) inner-coherence)
    (weak-one-step-matched-νcast-type-coherenceᵀ
      vW noW vV′ noV′ modeˢ sealˢ modeᵗ′ sealᵗ′
      source⊑ target⊑ (transportType inner pB) liftρ₀ innerAll)
  where
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source = weak-result-source-widen-inst inner mode seal★ s⊑
  modeˢ = proj₁ (proj₂ source)
  sealˢ = proj₁ (proj₂ (proj₂ source))
  source⊑ = proj₂ (proj₂ (proj₂ source))
  target = weak-result-target-widen-inst
    keep inner mode′ seal★′ s′⊑
  modeᵗ′ = proj₁ (proj₂ target)
  sealᵗ′ = proj₁ (proj₂ (proj₂ target))
  target⊑ = proj₂ (proj₂ (proj₂ target))

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
    {B = B} {B′ = B′} {s = s} {s′ = s′}
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
      {A = ★} {A′ = ★}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′ wf★ target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silentᵀ
    (left-silent first (left-silent-invariant refl refl)) second

weak-one-step-matched-νcast-blame-catchup-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (eq-blame :
    sourceResult (weakResult (catchupAllResult catchup)) ≡ blame) →
  WeakOneStepTransport (weakResult (catchupAllResult catchup)) →
  WeakOneStepTransport
    (weak-one-step-matched-νcast-blame-catchupᵀ
      wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ catchup eq-blame)
weak-one-step-matched-νcast-blame-catchup-transportᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport
    with silent
weak-one-step-matched-νcast-blame-catchup-transportᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport | left-silent-invariant refl refl
    with lift-store-result (resultStore inner)
weak-one-step-matched-νcast-blame-catchup-transportᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport | left-silent-invariant refl refl
    | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ s⊑
       | apply-widen-inst-under-ty-binders
      {χs = keep ∷ []} mode′ seal★′ s′⊑
weak-one-step-matched-νcast-blame-catchup-transportᵀ
    {B = B} {B′ = B′} {s = s} {s′ = s′}
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-transport | left-silent-invariant refl refl
    | ρ′ , liftρ
    | μᵣ , modeᵣ , sealᵣ , source⊑
    | μᵗ , modeᵗ , sealᵗ , target⊑ =
  let
    first = weak-one-step-matched-νcast-frameᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll)

    target⊢ =
      nu-term-imprecision-target-typing (relatedResults first)

    second = weak-one-step-source-blame-right-allocationᵀ
      {A = ★} {A′ = ★}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′ wf★ target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silent-preserves-transportᵀ
    (left-silent first (left-silent-invariant refl refl))
    second
    (weak-one-step-matched-νcast-frame-preserves-transportᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll) inner-transport)
    (weak-one-step-source-blame-right-allocation-transportᵀ
      {A = ★} {A′ = ★}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′ wf★ target⊢ (transportType inner pB))

weak-one-step-matched-νcast-blame-catchup-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  (eq-blame :
    sourceResult (weakResult (catchupAllResult catchup)) ≡ blame) →
  WeakOneStepTypeCoherence (weakResult (catchupAllResult catchup)) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-νcast-blame-catchupᵀ
      wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ catchup eq-blame)
weak-one-step-matched-νcast-blame-catchup-type-coherenceᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence
    with silent
weak-one-step-matched-νcast-blame-catchup-type-coherenceᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence | left-silent-invariant refl refl
    with lift-store-result (resultStore inner)
weak-one-step-matched-νcast-blame-catchup-type-coherenceᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence | left-silent-invariant refl refl
    | ρ′ , liftρ
    with apply-widen-inst-under-ty-binders
      {χs = sourceChanges inner} mode seal★ s⊑
       | apply-widen-inst-under-ty-binders
      {χs = keep ∷ []} mode′ seal★′ s′⊑
weak-one-step-matched-νcast-blame-catchup-type-coherenceᵀ
    {B = B} {B′ = B′} {s = s} {s′ = s′}
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    (left-all-catchup (weak-all-result inner innerAll)
      (left-catchup-invariant silent final))
    refl inner-coherence | left-silent-invariant refl refl
    | ρ′ , liftρ
    | μᵣ , modeᵣ , sealᵣ , source⊑
    | μᵗ , modeᵗ , sealᵗ , target⊑ =
  let
    first = weak-one-step-matched-νcast-frameᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll)

    target⊢ =
      nu-term-imprecision-target-typing (relatedResults first)

    second = weak-one-step-source-blame-right-allocationᵀ
      {A = ★} {A′ = ★}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′ wf★ target⊢ (transportType inner pB)
  in
  weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
    (left-silent first (left-silent-invariant refl refl))
    second
    (weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      (weak-all-result inner innerAll) inner-coherence)
    (weak-one-step-source-blame-right-allocation-type-coherenceᵀ
      {A = ★} {A′ = ★}
      {B = applyTys (sourceChanges inner) B}
      {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
      {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
      {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
        (applyCoercionUnderTyBinder keep s′)}
      {ρ = resultStore inner}
      (weak-result-right-wf-silent inner
        (left-silent-invariant refl refl) wfΣ′)
      vV′ noV′ wf★ target⊢ (transportType inner pB))

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

weak-one-step-matched-νcast-catchup-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepTransport (weakResult (catchupAllResult catchup)) →
  WeakOneStepTransport
    (weak-one-step-matched-νcast-catchupᵀ
      wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ catchup)
weak-one-step-matched-νcast-catchup-transportᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    catchup transport
    with sourceIsValueOrBlame (catchupAllInvariant catchup)
weak-one-step-matched-νcast-catchup-transportᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    catchup transport | inj₁ (vW , noW) =
  weak-one-step-matched-νcast-value-catchup-transportᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup vW noW transport
weak-one-step-matched-νcast-catchup-transportᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    catchup transport | inj₂ eq-blame =
  weak-one-step-matched-νcast-blame-catchup-transportᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup eq-blame transport

weak-one-step-matched-νcast-catchup-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup :
    LeftCatchupAllResult {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepTypeCoherence (weakResult (catchupAllResult catchup)) →
  WeakOneStepTypeCoherence
    (weak-one-step-matched-νcast-catchupᵀ
      wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ catchup)
weak-one-step-matched-νcast-catchup-type-coherenceᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    catchup coherence
    with sourceIsValueOrBlame (catchupAllInvariant catchup)
weak-one-step-matched-νcast-catchup-type-coherenceᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    catchup coherence | inj₁ (vW , noW) =
  weak-one-step-matched-νcast-value-catchup-type-coherenceᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup vW noW coherence
weak-one-step-matched-νcast-catchup-type-coherenceᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB vV′ noV′
    catchup coherence | inj₂ eq-blame =
  weak-one-step-matched-νcast-blame-catchup-type-coherenceᵀ
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′ catchup eq-blame coherence

weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C C′ N V′ s s′ μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ s ∶ C ⊑ ⇑ᵗ B) →
  (mode′ : CastMode μ′) →
  (seal★′ : SealModeStore★ (instᵈ μ′)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s′⊑ : instᵈ μ′ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup : LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q) →
  WeakOneStepIndexedOutcome
    {M = ν ★ N s}
    {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
    {A = B} {B = B′} {χ = bind ★} {ρ = ρ} pB
weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ
    {B = B} {B′ = B′} {s = s} {s′ = s′}
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′
    (left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    with final
weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ
    {B = B} {B′ = B′} {s = s} {s′ = s′}
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′
    (left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₁ (vW , noW) =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result type-eq)
    transport coherence
  where
  old-catchup = left-all-catchup
    (weak-indexed-all-resultᵀ indexed inner-coherence)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

  result =
    weak-one-step-matched-νcast-value-catchupᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ old-catchup vW noW

  inner = weakResult (catchupAllResult old-catchup)
  innerAll = canonicalAllResults (catchupAllResult old-catchup)
  first = weak-one-step-matched-νcast-frameᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (catchupAllResult old-catchup)
  liftρ₀ = proj₂ (lift-store-result (resultStore inner))
  source = weak-result-source-widen-inst inner mode seal★ s⊑
  modeˢ = proj₁ (proj₂ source)
  sealˢ = proj₁ (proj₂ (proj₂ source))
  source⊑ = proj₂ (proj₂ (proj₂ source))
  target = weak-result-target-widen-inst
    keep inner mode′ seal★′ s′⊑
  modeᵗ′ = proj₁ (proj₂ target)
  sealᵗ′ = proj₁ (proj₂ (proj₂ target))
  target⊑ = proj₂ (proj₂ (proj₂ target))
  second = weak-one-step-matched-νcastᵀ
    vW noW vV′ noV′ modeˢ sealˢ modeᵗ′ sealᵗ′
    source⊑ target⊑ (transportType inner pB) liftρ₀ innerAll

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx result ∣ resultLeftCtx result
          ⊢ S ⊑ T ⊣ resultRightCtx result}
        (sourceTypeResult result)
        (targetTypeResult result)
        (resultType result))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second pB)))

  transport =
    weak-one-step-matched-νcast-value-catchup-transportᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ old-catchup vW noW inner-transport

  coherence =
    weak-one-step-matched-νcast-value-catchup-type-coherenceᵀ
      mode seal★ s⊑ mode′ seal★′ s′⊑ pB
      vV′ noV′ old-catchup vW noW inner-coherence
weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ
    {B = B} {B′ = B′} {s = s} {s′ = s′}
    wfΣ′ mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    vV′ noV′
    (left-indexed-all-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final)
      inner-transport inner-coherence)
    | inj₂ refl =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result type-eq)
    transport coherence
  where
  old-catchup = left-all-catchup
    (weak-indexed-all-resultᵀ indexed inner-coherence)
    (left-catchup-invariant
      (left-silent-invariant refl refl) final)

  inner = weakResult (catchupAllResult old-catchup)
  first = weak-one-step-matched-νcast-frameᵀ
    mode seal★ s⊑ mode′ seal★′ s′⊑ pB
    (catchupAllResult old-catchup)
  target⊢ = nu-term-imprecision-target-typing (relatedResults first)
  second = weak-one-step-source-blame-right-allocationᵀ
    {A = ★} {A′ = ★}
    {B = applyTys (sourceChanges inner) B}
    {B′ = applyTys (targetTailChanges inner) (applyTy keep B′)}
    {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
    {s′ = applyCoercionUnderTyBinders (targetTailChanges inner)
      (applyCoercionUnderTyBinder keep s′)}
    {ρ = resultStore inner}
    (weak-result-right-wf-silent inner
      (left-silent-invariant refl refl) wfΣ′)
    vV′ noV′ wf★ target⊢ (transportType inner pB)

  result =
    weak-one-step-prepend-left-silentᵀ
      (left-silent first (left-silent-invariant refl refl)) second

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx result ∣ resultLeftCtx result
          ⊢ S ⊑ T ⊣ resultRightCtx result}
        (sourceTypeResult result)
        (targetTypeResult result)
        (resultType result))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second pB)))

  transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      (weak-one-step-matched-νcast-frame-preserves-transportᵀ
        mode seal★ s⊑ mode′ seal★′ s′⊑ pB
        (catchupAllResult old-catchup) inner-transport)
      (weak-one-step-source-blame-right-allocation-transportᵀ
        {A = ★} {A′ = ★}
        {B = applyTys (sourceChanges inner) B}
        {B′ = applyTys (targetTailChanges inner)
          (applyTy keep B′)}
        {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
        {s′ = applyCoercionUnderTyBinders
          (targetTailChanges inner)
          (applyCoercionUnderTyBinder keep s′)}
        {ρ = resultStore inner}
        (weak-result-right-wf-silent inner
          (left-silent-invariant refl refl) wfΣ′)
        vV′ noV′ wf★ target⊢ (transportType inner pB))

  coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first (left-silent-invariant refl refl)) second
      (weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
        mode seal★ s⊑ mode′ seal★′ s′⊑ pB
        (catchupAllResult old-catchup) inner-coherence)
      (weak-one-step-source-blame-right-allocation-type-coherenceᵀ
        {A = ★} {A′ = ★}
        {B = applyTys (sourceChanges inner) B}
        {B′ = applyTys (targetTailChanges inner)
          (applyTy keep B′)}
        {s = applyCoercionUnderTyBinders (sourceChanges inner) s}
        {s′ = applyCoercionUnderTyBinders
          (targetTailChanges inner)
          (applyCoercionUnderTyBinder keep s′)}
        {ρ = resultStore inner}
        (weak-result-right-wf-silent inner
          (left-silent-invariant refl refl) wfΣ′)
        vV′ noV′ wf★ target⊢ (transportType inner pB))

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

weak-one-step-right-ν↑-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  (s′↑ : RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  WeakOneStepTransport
    (weak-one-step-right-ν↑ᵀ
      vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′)
weak-one-step-right-ν↑-transportᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
    with right-ν↑-allocation
      vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
weak-one-step-right-ν↑-transportᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
    | source→ , target→ , result =
  weak-step-transport
    (right-lift-prefix-bodyᵀ liftρ (prefix-∷ⁱ prefix-reflⁱ))

weak-one-step-right-ν↑-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  (s′↑ : RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  WeakOneStepTypeCoherence
    (weak-one-step-right-ν↑ᵀ
      vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′)
weak-one-step-right-ν↑-type-coherenceᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
    with right-ν↑-allocation
      vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
weak-one-step-right-ν↑-type-coherenceᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
    | source→ , target→ , result =
  weak-step-type-coherence
    (λ pD pE → HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ oneStep pD pE)
        (≡-to-≅
          (⊑-target-lift-right-arrow-coherentᵢ pD pE))))
    (λ r → HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ oneStep r)
        (≡-to-≅ (⊑-target-lift-right-all-coherentᵢ r))))
  where
  oneStep = weak-one-step-right-ν↑ᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′

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

weak-one-step-right-νcast-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  WeakOneStepTransport
    (weak-one-step-right-νcastᵀ
      vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′)
weak-one-step-right-νcast-transportᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
    with right-νcast-allocation
      vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
weak-one-step-right-νcast-transportᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
    | source→ , target→ , result =
  weak-step-transport
    (right-lift-prefix-bodyᵀ liftρ (prefix-∷ⁱ prefix-reflⁱ))

weak-one-step-right-νcast-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  WeakOneStepTypeCoherence
    (weak-one-step-right-νcastᵀ
      vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′)
weak-one-step-right-νcast-type-coherenceᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
    with right-νcast-allocation
      vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
weak-one-step-right-νcast-type-coherenceᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
    | source→ , target→ , result =
  weak-step-type-coherence
    (λ pD pE → HE.≅-to-≡
      (HE.trans
        (transportArrowType-to-raw≅ oneStep pD pE)
        (≡-to-≅
          (⊑-target-lift-right-arrow-coherentᵢ pD pE))))
    (λ r → HE.≅-to-≡
      (HE.trans
        (transportAllType-to-raw≅ oneStep r)
        (≡-to-≅ (⊑-target-lift-right-all-coherentᵢ r))))
  where
  oneStep = weak-one-step-right-νcastᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′

weak-one-step-source-blame-right-allocation-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ V′ s s′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (wfΣ′ : StoreWf Δᴿ (rightStoreⁱ ρ)) →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (h⇑A′ : WfTy (suc Δᴿ) (⇑ᵗ A′)) →
  (target⊢ : Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ ν A′ V′ s′ ⦂ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = ν A blame s}
    {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
    {A = B} {B = B′} {χ = bind A′} {ρ = ρ} pB
weak-one-step-source-blame-right-allocation-indexed-outcomeᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {V′ = V′} {s = s} {s′ = s′} {ρ = ρ}
    wfΣ′ vV′ noV′ h⇑A′ target⊢ pB =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result refl)
    (weak-one-step-source-blame-right-allocation-transportᵀ
      {ρ = ρ} wfΣ′ vV′ noV′ h⇑A′ target⊢ pB)
    (weak-one-step-source-blame-right-allocation-type-coherenceᵀ
      {ρ = ρ} wfΣ′ vV′ noV′ h⇑A′ target⊢ pB)
  where
  result = weak-one-step-source-blame-right-allocationᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {V′ = V′} {s = s} {s′ = s′} {ρ = ρ}
    wfΣ′ vV′ noV′ h⇑A′ target⊢ pB

weak-one-step-right-ν↑-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  (s′↑ : RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  WeakOneStepIndexedOutcome
    {M = N} {N′ = ((⇑ᵗᵐ N′) •) ⟨ s ⟩}
    {A = B} {B = B′} {χ = bind A} {ρ = ρ} pB
weak-one-step-right-ν↑-indexed-outcomeᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′ =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result refl)
    (weak-one-step-right-ν↑-transportᵀ
      vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′)
    (weak-one-step-right-ν↑-type-coherenceᵀ
      vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′)
  where
  result = weak-one-step-right-ν↑ᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′

weak-one-step-right-νcast-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C′ N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  WeakOneStepIndexedOutcome
    {M = N} {N′ = ((⇑ᵗᵐ N′) •) ⟨ s ⟩}
    {A = B} {B = B′} {χ = bind ★} {ρ = ρ} pB
weak-one-step-right-νcast-indexed-outcomeᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′ =
  indexed-outcome-related
    (weak-one-step-index-resultᵀ result refl)
    (weak-one-step-right-νcast-transportᵀ
      vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′)
    (weak-one-step-right-νcast-type-coherenceᵀ
      vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′)
  where
  result = weak-one-step-right-νcastᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′

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
    (allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) V⊑V′
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
    (allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) V⊑N′
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
