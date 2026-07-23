module proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueProof where

-- File Charter:
--   * Proves the backward-value terminal contract from its two major
--     dependency contracts.
--   * Proves the target-step dispatcher and already-terminal value catch-up
--     interfaces sufficient by fuel induction on the observed target trace.
--   * Packages all accumulated traces, worlds, types, and store equalities.
--   * Does not import either live partial implementation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; s≤s⁻¹; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; applyStore
  ; applyStores
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
  ; _—→[_]_
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; No•; _∣_∣_⊢_⦂_; blame)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import proof.Core.Properties.ReductionProperties using
  ( applyStores-++
  ; applyTyCtxs-++
  ; applyTys-++
  ; ↠-trans
  )
open import TermTyping using (forget)
open import proof.DGG.Core.NuDGGTraceAlignment using
  (weak-result-target-prefix-valueᵀ)
open import proof.DGG.Core.NuDGGTraceMeasure using
  (aligned-residual-shorter)
open import proof.DGG.Core.NuDGGWeakResultPreservation using
  ( weak-result-source-store-wf
  ; weak-result-source-runtime
  ; weak-result-target-store-wf
  ; weak-result-target-runtime
  )
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueDef using
  (BackwardTargetValueOrSourceBlameᵀ)
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.OneStep.NuImprecisionOneStepDef using
  (WeakOneStepIndexedSimulationᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; WeakOneStepIndexedOutcome
  ; WeakOneStepIndexedResult
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceIsValueOrBlame
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetIsUnchanged
  ; targetTailChanges
  ; targetTailIsEmpty
  ; targetStoreResult
  ; transportType
  ; weakIndexedResult
  )
open import proof.NuCore.Misc.NuImprecisionValueCatchupDef using
  (LeftValueCatchupᵀ)


normalize-empty-runtime-context :
  ∀ {Δ Σ Γ M A} →
  Γ ≡ [] →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A
normalize-empty-runtime-context refl M⊢ = M⊢

empty-context-source-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A
empty-context-source-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-empty-runtime-context
    {Γ = leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (forget
      (nu-term-imprecision-source-typing
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
        {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′))

empty-context-target-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B
empty-context-target-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-empty-runtime-context
    {Γ = rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (forget
      (nu-term-imprecision-target-typing
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
        {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′))


prepend-weak-related-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ ψs θs V V′ ηs Ψ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
  ψs ≡ targetTailChanges (weakIndexedResult indexed) ++ θs →
  (ρ′ : StoreImp Ψ
    (applyTyCtxs ηs (resultLeftCtx (weakIndexedResult indexed)))
    (applyTyCtxs θs (resultRightCtx (weakIndexedResult indexed)))) →
  (q : Ψ
    ∣ applyTyCtxs ηs (resultLeftCtx (weakIndexedResult indexed))
    ⊢ applyTys ηs
        (applyTys (sourceChanges (weakIndexedResult indexed)) A)
      ⊑ applyTys θs
        (applyTys (targetTailChanges (weakIndexedResult indexed))
          (applyTy χ B))
    ⊣ applyTyCtxs θs
        (resultRightCtx (weakIndexedResult indexed))) →
  sourceResult (weakIndexedResult indexed) —↠[ ηs ] V →
  Value V →
  leftStoreⁱ ρ′ ≡
    applyStores ηs (leftStoreⁱ (resultStore (weakIndexedResult indexed))) →
  rightStoreⁱ ρ′ ≡
    applyStores θs
      (rightStoreⁱ (resultStore (weakIndexedResult indexed))) →
  Ψ
    ∣ applyTyCtxs ηs (resultLeftCtx (weakIndexedResult indexed))
    ∣ applyTyCtxs θs (resultRightCtx (weakIndexedResult indexed))
    ∣ ρ′ ∣ []
    ⊢ᴺ V ⊑ V′
    ⦂ applyTys ηs
        (applyTys (sourceChanges (weakIndexedResult indexed)) A)
      ⊑ applyTys θs
        (applyTys (targetTailChanges (weakIndexedResult indexed))
          (applyTy χ B)) ∶ q →
  Σ[ ρ′′ ∈ StoreImp Ψ
      (applyTyCtxs
        (sourceChanges (weakIndexedResult indexed) ++ ηs) Δᴸ)
      (applyTyCtxs (χ ∷ ψs) Δᴿ) ]
  (Σ[ q′ ∈
      (Ψ
        ∣ applyTyCtxs
            (sourceChanges (weakIndexedResult indexed) ++ ηs) Δᴸ
        ⊢ applyTys
            (sourceChanges (weakIndexedResult indexed) ++ ηs) A
          ⊑ applyTys (χ ∷ ψs) B
        ⊣ applyTyCtxs (χ ∷ ψs) Δᴿ) ]
    ((M —↠[
        sourceChanges (weakIndexedResult indexed) ++ ηs ] V) ×
     Value V ×
     (leftStoreⁱ ρ′′ ≡
       applyStores
         (sourceChanges (weakIndexedResult indexed) ++ ηs)
         (leftStoreⁱ ρ)) ×
     (rightStoreⁱ ρ′′ ≡
       applyStores (χ ∷ ψs) (rightStoreⁱ ρ)) ×
     Ψ
       ∣ applyTyCtxs
           (sourceChanges (weakIndexedResult indexed) ++ ηs) Δᴸ
       ∣ applyTyCtxs (χ ∷ ψs) Δᴿ
       ∣ ρ′′ ∣ []
       ⊢ᴺ V ⊑ V′
       ⦂ applyTys
           (sourceChanges (weakIndexedResult indexed) ++ ηs) A
         ⊑ applyTys (χ ∷ ψs) B ∶ q′))
prepend-weak-related-valueᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    {χ = χ} {ψs = ψs} {θs = θs} {ηs = ηs} {ρ = ρ}
    indexed trace-eq ρ′ q source-tail vV left-eq right-eq V⊑V′
    with sourceCtxResult (weakIndexedResult indexed)
       | targetCtxResult (weakIndexedResult indexed)
       | trace-eq
prepend-weak-related-valueᵀ
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    {χ = χ} {ψs = ._} {θs = θs} {ηs = ηs} {ρ = ρ}
    indexed refl ρ′ q source-tail vV left-eq right-eq V⊑V′
    | refl | refl | refl
    rewrite applyTyCtxs-++
              (sourceChanges (weakIndexedResult indexed)) ηs Δᴸ
          | applyTyCtxs-++
              (targetTailChanges (weakIndexedResult indexed)) θs
              (applyTyCtx χ Δᴿ)
          | applyTys-++
              (sourceChanges (weakIndexedResult indexed)) ηs A
          | applyTys-++
              (targetTailChanges (weakIndexedResult indexed)) θs
              (applyTy χ B)
          | applyStores-++
              (sourceChanges (weakIndexedResult indexed)) ηs
              (leftStoreⁱ ρ)
          | applyStores-++
              (targetTailChanges (weakIndexedResult indexed)) θs
              (applyStore χ (rightStoreⁱ ρ)) =
      ρ′ , q ,
      ↠-trans (sourceCatchup (weakIndexedResult indexed)) source-tail ,
      vV ,
      trans left-eq
        (cong (applyStores ηs)
          (sourceStoreResult (weakIndexedResult indexed))) ,
      trans right-eq
        (cong (applyStores θs)
          (targetStoreResult (weakIndexedResult indexed))) ,
      V⊑V′


backward-target-value-or-source-blame-proofᵀ :
  WeakOneStepIndexedSimulationᵀ →
  LeftValueCatchupᵀ →
  BackwardTargetValueOrSourceBlameᵀ
backward-target-value-or-source-blame-proofᵀ
    one-step target-value-catchup wfL wfR okM okM′ M⊑M′
    V′ χs′ M′↠V′ vV′ =
  go (length χs′) wfL wfR okM okM′ M⊑M′
    V′ χs′ M′↠V′ vV′ ≤-refl
  where
  go :
    ∀ (fuel : ℕ) { Φ Δᴸ Δᴿ M M′ A B }
      { ρ : StoreImp Φ Δᴸ Δᴿ }
      { p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ } →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    ∀ (V′ : Term) (ψs : StoreChanges) →
    M′ —↠[ ψs ] V′ →
    Value V′ →
    length ψs ≤ fuel →
      (∃[ V ] (Σ[ χs ∈ StoreChanges ]
      (∃[ Ψ ] (Σ[ ρ′ ∈
          StoreImp Ψ
            (applyTyCtxs χs Δᴸ) (applyTyCtxs ψs Δᴿ) ]
      (Σ[ q ∈
          (Ψ ∣ applyTyCtxs χs Δᴸ
            ⊢ applyTys χs A ⊑ applyTys ψs B
            ⊣ applyTyCtxs ψs Δᴿ) ]
        ((M —↠[ χs ] V) ×
         Value V ×
         (leftStoreⁱ ρ′ ≡ applyStores χs (leftStoreⁱ ρ)) ×
         (rightStoreⁱ ρ′ ≡ applyStores ψs (rightStoreⁱ ρ)) ×
         Ψ ∣ applyTyCtxs χs Δᴸ ∣ applyTyCtxs ψs Δᴿ ∣ ρ′ ∣ []
           ⊢ᴺ V ⊑ V′
           ⦂ applyTys χs A ⊑ applyTys ψs B ∶ q)))))
      ⊎ (∃[ χs ] (M —↠[ χs ] blame)))
  go zero wfL wfR okM okM′ M⊑M′ V′ [] ↠-refl vV′ bound
    with target-value-catchup okM vV′
      (runtime-value-no• okM′ vV′) M⊑M′
  go zero wfL wfR okM okM′ M⊑M′ V′ [] ↠-refl vV′ bound
    | catchup
    with sourceIsValueOrBlame
      (catchupIndexedInvariant catchup)
  go zero {p = p} wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound
    | catchup | inj₁ (vV , noV)
    with sourceCtxResult
           (weakIndexedResult (catchupIndexedResult catchup))
       | targetCtxResult
           (weakIndexedResult (catchupIndexedResult catchup))
       | targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant catchup))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant catchup))
  go zero {p = p} wfL wfR okM okM′ M⊑M′ V′ []
      ↠-refl vV′ bound
    | catchup | inj₁ (vV , noV) | refl | refl | refl | refl =
      inj₁
        ( sourceResult (weakIndexedResult (catchupIndexedResult catchup))
        , sourceChanges (weakIndexedResult (catchupIndexedResult catchup))
        , resultCtx (weakIndexedResult (catchupIndexedResult catchup))
        , resultStore (weakIndexedResult (catchupIndexedResult catchup))
        , transportType
            (weakIndexedResult (catchupIndexedResult catchup)) p
        , sourceCatchup
            (weakIndexedResult (catchupIndexedResult catchup))
        , vV
        , sourceStoreResult
            (weakIndexedResult (catchupIndexedResult catchup))
        , targetStoreResult
            (weakIndexedResult (catchupIndexedResult catchup))
        , canonicalIndexedResults (catchupIndexedResult catchup)
        )
  go zero wfL wfR okM okM′ M⊑M′ V′ [] ↠-refl vV′ bound
    | catchup | inj₂ refl =
      inj₂
        ( sourceChanges (weakIndexedResult (catchupIndexedResult catchup))
        , sourceCatchup
            (weakIndexedResult (catchupIndexedResult catchup))
        )
  go zero wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ ()
  go (suc fuel) wfL wfR okM okM′ M⊑M′ V′ [] ↠-refl vV′ bound =
    go zero wfL wfR okM okM′ M⊑M′ V′ [] ↠-refl vV′ ≤-refl
  go (suc fuel) wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    with one-step wfR okM okM′ M⊑M′ target-step
  go (suc fuel) wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | indexed-outcome-source-blame {χs = source-blame-changes}
        source-blame =
      inj₂ (source-blame-changes , source-blame)
  go (suc fuel) wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | indexed-outcome-related indexed
    with weak-result-target-prefix-valueᵀ
      (weakIndexedResult indexed) target-rest vV′
  go (suc fuel) wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | indexed-outcome-related indexed
    | residual-changes , target-result↠V′ , trace-eq
    with go fuel
      (weak-result-source-store-wf
        (weakIndexedResult indexed) wfL okM
        (empty-context-source-typing M⊑M′))
      (weak-result-target-store-wf
        (weakIndexedResult indexed) wfR okM′
        (empty-context-target-typing M⊑M′) target-step)
      (weak-result-source-runtime
        (weakIndexedResult indexed) wfL okM
        (empty-context-source-typing M⊑M′))
      (weak-result-target-runtime
        (weakIndexedResult indexed) wfR okM′
        (empty-context-target-typing M⊑M′) target-step)
      (canonicalIndexedResults indexed)
      V′ residual-changes target-result↠V′ vV′
      (s≤s⁻¹
        (≤-trans
          (aligned-residual-shorter
            {χ = χ}
            {observed = ψs}
            {administrative =
              targetTailChanges (weakIndexedResult indexed)}
            {residual = residual-changes}
            trace-eq)
          bound))
  go (suc fuel) wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | indexed-outcome-related indexed
    | residual-changes , target-result↠V′ , trace-eq
    | inj₂ (result-blame-changes , source-result↠blame) =
      inj₂
        (sourceChanges (weakIndexedResult indexed) ++ result-blame-changes ,
         ↠-trans (sourceCatchup (weakIndexedResult indexed))
                 source-result↠blame)
  go (suc fuel) wfL wfR okM okM′ M⊑M′ V′
      (χ ∷ ψs) (↠-step target-step target-rest) vV′ bound
    | indexed-outcome-related indexed
    | residual-changes , target-result↠V′ , trace-eq
    | inj₁ (V , result-source-changes , Ψ , ρ′ , q ,
        source-result↠V , vV , left-store-eq , right-store-eq , V⊑V′) =
      inj₁
        ( V
        , sourceChanges (weakIndexedResult indexed) ++
            result-source-changes
        , Ψ
        , prepend-weak-related-valueᵀ
            indexed trace-eq ρ′ q source-result↠V vV
            left-store-eq right-store-eq V⊑V′
        )
