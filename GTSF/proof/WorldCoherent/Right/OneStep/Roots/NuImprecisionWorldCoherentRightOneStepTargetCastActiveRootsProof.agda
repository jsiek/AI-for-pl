module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastActiveRootsProof
  where

-- File Charter:
--   * Assembles all active target-cast root dispatch from seven explicit
--     semantic cells plus the completed atomic-identity and target-blame
--     leaves.
--   * Closes every impossible cast-grammar/direction combination by
--     narrowing/widening inversion.
--   * Passes exact QTI cast shapes and composition triangles unchanged to
--     every semantic cell.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     termination bypass, or conversion-root case.

import Coercions as C
import NarrowWiden as NW
import CastImprecisionShape as CastShape
open import Coercions using (Coercion; ModeEnv; id-onlyᵈ)
open import Data.List using ([])
open import Data.Product using (_,_)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( keep
  ; _—→_
  ; β-id
  ; β-inst
  ; β-seq
  ; blame-⟨⟩
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; ＇_
  ; ‵_
  ; ★
  )
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsDef
  using
  ( WorldCoherentRightOneStepAtomicAndBlameRoots
  ; rightStepTargetAtomicIdentityRoot
  ; rightStepTargetBlameRoot
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastActiveRootsDef
  using
  ( WorldCoherentRightOneStepTargetCastActiveRoots
  ; WorldCoherentRightOneStepTargetCastSemanticRoots
  ; rightStepTargetIdWidenInstantiationRoot
  ; rightStepTargetIdWidenSequenceRoot
  ; rightStepTargetNarrowSequenceRoot
  ; rightStepTargetNarrowUntagRoot
  ; rightStepTargetWidenInstantiationRoot
  ; rightStepTargetWidenSequenceRoot
  ; rightStepTargetWidenUnsealRoot
  )


world-coherent-right-one-step-target-cast-active-roots-proofᵀ :
  WorldCoherentRightOneStepAtomicAndBlameRoots →
  WorldCoherentRightOneStepTargetCastSemanticRoots →
  WorldCoherentRightOneStepTargetCastActiveRoots
world-coherent-right-one-step-target-cast-active-roots-proofᵀ
    atomic semantic =
  record
    { rightStepTargetNarrowCastRoot = narrow-root
    ; rightStepTargetWidenCastRoot = widen-root
    ; rightStepTargetIdWidenCastRoot = id-widen-root
    }
  where
  narrow-root :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ N′ : Term} {A A′ B′ : Ty}
      {c′ : Coercion} {μ′ : ModeEnv}
      {shape : ImprecisionShape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK (M′ ⟨ c′ ⟩) →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
    CastShape.narrowing CastShape.⊢ᶜ c′ ⦂ shape →
    ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    M′ ⟨ c′ ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★
      (C.cast-id _ _ , NW.cross (NW.id-＇ α))
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (＇ α) vV inner
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★
      (C.cast-id _ _ , NW.cross (NW.id-‵ ι))
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (‵ ι) vV inner
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★
      (C.cast-id _ _ , NW.id★)
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique ★ vV inner
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ sequence⊒ shape comp inner
      root@(β-seq vV) =
    rightStepTargetNarrowSequenceRoot semantic
      coherent exclusive unique wfL wfR okM okCast mode seal★
      sequence⊒ shape comp inner root
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ (c′⊢ , NW.cross ()) shape comp inner
      (β-inst vV)
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ untag⊒ shape comp inner
      root@(tag-untag-ok vV) =
    rightStepTargetNarrowUntagRoot semantic
      coherent exclusive unique wfL wfR okM okCast mode seal★
      untag⊒ shape comp inner root
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ untag⊒ shape comp inner
      root@(tag-untag-bad vV G≢H) =
    rightStepTargetNarrowUntagRoot semantic
      coherent exclusive unique wfL wfR okM okCast mode seal★
      untag⊒ shape comp inner root
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ (c′⊢ , NW.cross ()) shape comp inner
      (seal-unseal vV)
  narrow-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ narrowing shape comp inner blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner

  widen-root :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ N′ : Term} {A A′ B′ : Ty}
      {c′ : Coercion} {μ′ : ModeEnv}
      {shape : ImprecisionShape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK (M′ ⟨ c′ ⟩) →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
    CastShape.widening CastShape.⊢ᶜ c′ ⦂ shape →
    ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    M′ ⟨ c′ ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★
      (C.cast-id _ _ , NW.cross (NW.id-＇ α))
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (＇ α) vV inner
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★
      (C.cast-id _ _ , NW.cross (NW.id-‵ ι))
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (‵ ι) vV inner
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★
      (C.cast-id _ _ , NW.id★)
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique ★ vV inner
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ sequence⊑ shape comp inner
      root@(β-seq vV) =
    rightStepTargetWidenSequenceRoot semantic
      coherent exclusive unique wfL wfR okM okCast mode seal★
      sequence⊑ shape comp inner root
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ inst⊑ shape comp inner
      root@(β-inst vV) =
    rightStepTargetWidenInstantiationRoot semantic
      coherent exclusive unique wfL wfR okM okCast mode seal★
      inst⊑ shape comp inner root
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ (c′⊢ , NW.cross ()) shape comp inner
      (tag-untag-ok vV)
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ (c′⊢ , NW.cross ()) shape comp inner
      (tag-untag-bad vV G≢H)
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ unseal⊑ shape comp inner
      root@(seal-unseal vV) =
    rightStepTargetWidenUnsealRoot semantic
      coherent exclusive unique wfL wfR okM okCast mode seal★
      unseal⊑ shape comp inner root
  widen-root coherent exclusive unique wfL wfR okM okCast
      mode seal★ widening shape comp inner blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner

  id-widen-root :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ N′ : Term} {A A′ B′ : Ty}
      {c′ : Coercion}
      {shape : ImprecisionShape}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK (M′ ⟨ c′ ⟩) →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ c′ ∶ A′ ⊑ B′ →
    CastShape.widening CastShape.⊢ᶜ c′ ⦂ shape →
    ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    M′ ⟨ c′ ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★
      (C.cast-id _ _ , NW.cross (NW.id-＇ α))
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (＇ α) vV inner
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★
      (C.cast-id _ _ , NW.cross (NW.id-‵ ι))
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (‵ ι) vV inner
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★
      (C.cast-id _ _ , NW.id★)
      shape comp inner (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique ★ vV inner
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★ sequence⊑ shape comp inner
      root@(β-seq vV) =
    rightStepTargetIdWidenSequenceRoot semantic
      coherent exclusive unique wfL wfR okM okCast seal★
      sequence⊑ shape comp inner root
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★ inst⊑ shape comp inner
      root@(β-inst vV) =
    rightStepTargetIdWidenInstantiationRoot semantic
      coherent exclusive unique wfL wfR okM okCast seal★
      inst⊑ shape comp inner root
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★ (c′⊢ , NW.cross ()) shape comp inner
      (tag-untag-ok vV)
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★ (c′⊢ , NW.cross ()) shape comp inner
      (tag-untag-bad vV G≢H)
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★
      (C.cast-unseal hA α∈Σ () , NW.unsealʷ α A)
      shape comp inner (seal-unseal vV)
  id-widen-root coherent exclusive unique wfL wfR okM okCast
      seal★ widening shape comp inner blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
