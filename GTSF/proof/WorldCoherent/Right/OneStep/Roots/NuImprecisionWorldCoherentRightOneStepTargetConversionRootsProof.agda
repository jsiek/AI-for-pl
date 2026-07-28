module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetConversionRootsProof
  where

-- File Charter:
--   * Implements every active target reveal and conceal conversion root.
--   * Delegates atomic identities and target blame to their strict leaves and
--     reveal-unseal to the exact-world target-seal cancellation square.
--   * Contains no context-frame case, recursion, postulate, hole, or
--     permissive option.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( blame-⟨⟩
  ; keep
  ; seal-unseal
  ; β-id
  ; _—→_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
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
open import Types using
  ( Ty
  ; TyCtx
  ; ＇_
  ; ‵_
  ; ★
  )
open import proof.Core.Properties.NuRuntimeProperties using (runtime-⟨⟩)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTargetRevealRootDef
  using (WorldCoherentTargetRevealRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsDef
  using
  ( WorldCoherentRightOneStepAtomicAndBlameRoots
  ; rightStepTargetAtomicIdentityRoot
  ; rightStepTargetBlameRoot
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetConversionRootsDef
  using (WorldCoherentRightOneStepTargetConversionRoots)


world-coherent-right-one-step-target-conversion-roots-proofᵀ :
  WorldCoherentRightOneStepAtomicAndBlameRoots →
  WorldCoherentTargetRevealRootᵀ →
  WorldCoherentRightOneStepTargetConversionRoots
world-coherent-right-one-step-target-conversion-roots-proofᵀ
    atomic reveal-root =
  record
    { rightStepTargetRevealConversionRoot = reveal
    ; rightStepTargetConcealConversionRoot = conceal
    }
  where
  reveal :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ N′ : Term} {A A′ B′ : Ty}
      {c′ μ′ β X′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK (M′ ⟨ c′ ⟩) →
    RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ A′ B′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    p [ β ↦ X′ ]ᴿ q →
    M′ ⟨ c′ ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
  reveal coherent exclusive unique wfL wfR okM okCast
      (reveal-id-var hY ok) inner replace (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (＇ _) vV inner
  reveal coherent exclusive unique wfL wfR okM okCast
      reveal-id-base inner replace (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (‵ _) vV inner
  reveal coherent exclusive unique wfL wfR okM okCast
      reveal-id-★ inner replace (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique ★ vV inner
  reveal coherent exclusive unique wfL wfR okM okCast
      (reveal-unseal hX′ β∈Σ ok) inner replace
      (seal-unseal vV) =
    reveal-root coherent exclusive unique wfL wfR okM
      (runtime-⟨⟩ okCast) vV β∈Σ inner _
  reveal coherent exclusive unique wfL wfR okM okCast
      (reveal-id-var hY ok) inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  reveal coherent exclusive unique wfL wfR okM okCast
      reveal-id-base inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  reveal coherent exclusive unique wfL wfR okM okCast
      reveal-id-★ inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  reveal coherent exclusive unique wfL wfR okM okCast
      (reveal-unseal hX′ β∈Σ ok) inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  reveal coherent exclusive unique wfL wfR okM okCast
      (reveal-fun concealment revelation) inner replace
      blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  reveal coherent exclusive unique wfL wfR okM okCast
      (reveal-all revelation) inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner

  conceal :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ N′ : Term} {A A′ B′ : Ty}
      {c′ μ′ β X′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK (M′ ⟨ c′ ⟩) →
    ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ A′ B′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    q [ β ↦ X′ ]ᴿ p →
    M′ ⟨ c′ ⟩ —→ N′ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
  conceal coherent exclusive unique wfL wfR okM okCast
      (conceal-id-var hY ok) inner replace (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (＇ _) vV inner
  conceal coherent exclusive unique wfL wfR okM okCast
      conceal-id-base inner replace (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique (‵ _) vV inner
  conceal coherent exclusive unique wfL wfR okM okCast
      conceal-id-★ inner replace (β-id vV) =
    rightStepTargetAtomicIdentityRoot atomic
      coherent exclusive unique ★ vV inner
  conceal coherent exclusive unique wfL wfR okM okCast
      (conceal-id-var hY ok) inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  conceal coherent exclusive unique wfL wfR okM okCast
      conceal-id-base inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  conceal coherent exclusive unique wfL wfR okM okCast
      conceal-id-★ inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  conceal coherent exclusive unique wfL wfR okM okCast
      (conceal-seal hX′ β∈Σ ok) inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  conceal coherent exclusive unique wfL wfR okM okCast
      (conceal-fun revelation concealment) inner replace
      blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
  conceal coherent exclusive unique wfL wfR okM okCast
      (conceal-all concealment) inner replace blame-⟨⟩ =
    rightStepTargetBlameRoot atomic okM inner
