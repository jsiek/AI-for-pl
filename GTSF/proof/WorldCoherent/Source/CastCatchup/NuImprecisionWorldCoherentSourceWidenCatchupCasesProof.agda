module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupCasesProof
  where

-- File Charter:
--   * Proves the coherent identity, inert, sequence, and source-only
--     instantiation cases for one source widening cast.
--   * Requires the source-only `ν` index explicitly in the instantiation case.
--   * Does not assemble the former arbitrary-index widening contract: that
--     contract admitted the invalid paired-`∀ⁱ` source-instantiation path.
--   * Uses only strict framing/composition helpers for local proof plumbing.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (Coercion; Inert; ModeEnv; _︔_)
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; widening
  ; shape-inst
  ; shape-sequence-widening
  )
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ImprecisionWf using
  (NonVar; _ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_; ν)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_; comp-ν)
import NarrowWiden as NW
open import NarrowWiden using
  ( Widening
  ; widen-weaken
  ; widen-renameᵗ
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; blame-⟨⟩
  ; keep
  ; pure-step
  ; β-seq
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ok-⟨⟩
  ; ok-no
  ; ok-ν
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; nu-term-imprecision-target-typing
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)
open import Store using (StoreIncl-cons; StoreIncl-drop)
import Relation.Binary.HeterogeneousEquality as HE
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-weaken
  )
open import Types using
  ( Atom
  ; Ty
  ; TyCtx
  ; occurs
  ; ★
  ; `∀
  )
import Types as T

open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import proof.Catchup.Core.NuImprecisionCatchupSourceCastTerminal using
  ( left-catchup-indexed-source-cast-blame-frameᵀ
  ; left-catchup-indexed-source-inert-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( post-catchup-β-inst
  ; weak-one-step-source-cast-frame-coherenceᵀ
  ; weak-one-step-source-cast-frame-silentᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( left-catchup-indexed-relatedᵀ
  ; subst²-to-≅
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silentᵀ
  ; weak-one-step-reindexᵀ
  ; weak-one-step-source-νcast-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetResult
  ; targetTailChanges
  ; targetTypeResult
  ; transportType
  ; transportShapeCoherent
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointDef using
  (SourceCastSequenceMidpointᵀ; widening-midpoint)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof using
  (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )
open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceConcealCatchup using
  ( applyTys-preserves-Atom
  ; atomic-source-value-reindexᵀ
  ; post-catchup-β-id
  )
open import proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef using
  (WorldCoherentLeftValueCatchupPrefixᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using (WorldCoherent)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercions-preserves-Inert)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using
  ( modeRename-suc-weakenCast
  ; seal★-inst
  ; seal★-weaken
  ; seal★-weakenCast-bind
  )
open import proof.Core.Properties.TypeProperties using (TyRenameWf-suc)
open import proof.Core.Properties.NuWideningTransport using (apply-widens-typing)


transport-source-widening-composition :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ C D E s}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ C ⊑ E ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    (result : WeakOneStepResult ρ M M′ A B χ) →
  WeakOneStepTypeCoherence result →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  s ； ⌊ transportType result q ⌋ ≋
    ⌊ transportType result p ⌋
transport-source-widening-composition result coherence comp =
  imprecision-composition-shape-transport
    refl
    (transportShapeCoherent coherence _)
    (transportShapeCoherent coherence _)
    comp


applyCoercions-seq :
  ∀ χs s t →
  applyCoercions χs (s ︔ t) ≡
    applyCoercions χs s ︔ applyCoercions χs t
applyCoercions-seq [] s t = refl
applyCoercions-seq (keep ∷ χs) s t =
  applyCoercions-seq χs s t
applyCoercions-seq (bind A ∷ χs) s t =
  applyCoercions-seq χs (C.⇑ᶜ s) (C.⇑ᶜ t)


post-catchup-β-seq :
  ∀ χs {V s t} →
  Value V →
  V ⟨ applyCoercions χs (s ︔ t) ⟩ —→[ keep ]
    V ⟨ applyCoercions χs s ⟩ ⟨ applyCoercions χs t ⟩
post-catchup-β-seq χs {s = s} {t = t} vV
    rewrite applyCoercions-seq χs s t =
  pure-step (β-seq vV)


applyCoercions-preserves-Widening :
  ∀ χs {c} →
  Widening c →
  Widening (applyCoercions χs c)
applyCoercions-preserves-Widening [] cʷ = cʷ
applyCoercions-preserves-Widening (keep ∷ χs) cʷ =
  applyCoercions-preserves-Widening χs cʷ
applyCoercions-preserves-Widening (bind A ∷ χs) cʷ =
  applyCoercions-preserves-Widening χs (NW.renameʷ suc cʷ)


apply-widens-typing₂ :
  ∀ {χs μ Δ Σ s t A C B} →
  CastMode μ →
  SealModeStore★ μ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ C →
  μ ∣ Δ ∣ Σ ⊢ t ∶ C ⊑ B →
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (applyStores χs Σ) ×
    (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
      ⊢ applyCoercions χs s ∶ applyTys χs A ⊑ applyTys χs C) ×
    (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
      ⊢ applyCoercions χs t ∶ applyTys χs C ⊑ applyTys χs B)
apply-widens-typing₂ {χs = []} {μ = μ} mode seal★ s⊑ t⊑ =
  μ , mode , seal★ , s⊑ , t⊑
apply-widens-typing₂ {χs = keep ∷ χs} mode seal★ s⊑ t⊑ =
  apply-widens-typing₂ {χs = χs} mode seal★ s⊑ t⊑
apply-widens-typing₂ {χs = bind Aχ ∷ χs} mode seal★ s⊑ t⊑ =
  apply-widens-typing₂ {χs = χs}
    (cast-weaken mode)
    (seal★-weakenCast-bind seal★)
    (widen-weaken ≤-refl StoreIncl-drop
      (widen-renameᵗ TyRenameWf-suc modeRename-suc-weakenCast s⊑))
    (widen-weaken ≤-refl StoreIncl-drop
      (widen-renameᵗ TyRenameWf-suc modeRename-suc-weakenCast t⊑))


indexed-source-precision :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = keep} {ρ = ρ} p) →
  let inner = weakIndexedResult indexed in
  resultCtx inner ∣ resultLeftCtx inner
    ⊢ applyTys (sourceChanges inner) A
      ⊑ applyTys (targetTailChanges inner) B
      ⊣ resultRightCtx inner
indexed-source-precision {p = p} indexed =
  transportType (weakIndexedResult indexed) p


result-widening-typingᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B C c μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ B ⊑ C →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = keep} {ρ = ρ⁺} p) →
  let inner = weakIndexedResult indexed in
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner)) ×
    (μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C)
result-widening-typingᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {c = c}
    prefix mode seal★ c⊑ indexed
    with apply-widens-typing
      {χs = sourceChanges (weakIndexedResult indexed)}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
result-widening-typingᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {c = c}
    prefix mode seal★ c⊑ indexed
    | μ′ , mode′ , seal★′ , c′⊑ =
  μ′ , mode′ , final-seal , final-cast
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
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) B
            ⊑ applyTys (sourceChanges inner) C)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) B
              ⊑ applyTys (sourceChanges inner) C)
        (sym (sourceStoreResult inner)) c′⊑)


result-widening-typing₂ᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B C D s t μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ B ⊑ C →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C ⊑ D →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = keep} {ρ = ρ⁺} p) →
  let inner = weakIndexedResult indexed in
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner)) ×
    (μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) s
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C) ×
    (μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) t
        ∶ applyTys (sourceChanges inner) C
          ⊑ applyTys (sourceChanges inner) D)
result-widening-typing₂ᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {D = D} {s = s} {t = t}
    prefix mode seal★ s⊑ t⊑ indexed
    with apply-widens-typing₂
      {χs = sourceChanges (weakIndexedResult indexed)}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) s⊑)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) t⊑)
result-widening-typing₂ᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {D = D} {s = s} {t = t}
    prefix mode seal★ s⊑ t⊑ indexed
    | μ′ , mode′ , seal★′ , s′⊑ , t′⊑ =
  μ′ , mode′ , final-seal , final-cast-s , final-cast-t
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast-s :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) s
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C
  final-cast-s =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) s
          ∶ applyTys (sourceChanges inner) B
            ⊑ applyTys (sourceChanges inner) C)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) s
            ∶ applyTys (sourceChanges inner) B
              ⊑ applyTys (sourceChanges inner) C)
        (sym (sourceStoreResult inner)) s′⊑)

  final-cast-t :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) t
        ∶ applyTys (sourceChanges inner) C
          ⊑ applyTys (sourceChanges inner) D
  final-cast-t =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) t
          ∶ applyTys (sourceChanges inner) C
            ⊑ applyTys (sourceChanges inner) D)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) t
            ∶ applyTys (sourceChanges inner) C
              ⊑ applyTys (sourceChanges inner) D)
        (sym (sourceStoreResult inner)) t′⊑)


world-coherent-source-inert-widen-castᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ A B B′ c μ s}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  Inert c →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c} {ρ⁺ = ρ⁺}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c} {ρ⁺ = ρ⁺}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c} {ρ⁺ = ρ⁺}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
    world-coherent-left-indexed-catchup
      (left-indexed-catchup framed
        (left-catchup-invariant first-silent
          (inj₁ (vW ⟨ inert′ ⟩ , no•-⟨⟩ noW))))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  inert′ =
    applyCoercions-preserves-Inert (sourceChanges inner) inert

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)
world-coherent-source-inert-widen-castᵀ
    {N = N} {V′ = V′} {c = c} {ρ⁺ = ρ⁺}
    inert prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-source-cast-blame-frameᵀ
        catchup framed refl first-silent
        first-transport first-coherence refl)
      terminal-combined-lineage
      coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-second-lineage =
    weak-step-store-lineage
      (resultStore terminal-first)
      rel-store-embedding-reflⁱ prefix-reflⁱ

  terminal-combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent terminal-first
        (left-silent-invariant refl refl))
      terminal-second
      terminal-first-lineage terminal-second-lineage


world-coherent-source-id-widen-castᵀ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ N V′ A B′ μ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  Atom A →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ C.id A ∶ A ⊑ A →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ C.id A ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ C.id A ⟩} {V′ = V′} {ρ = ρ⁺} q
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  world-coherent-left-indexed-catchup
    (left-indexed-catchup
      (weak-one-step-index-resultᵀ combined type-eq
        combined-transport combined-coherence)
      (left-catchup-invariant
        (left-silent-invariant refl refl) (inj₁ (vW , noW))))
    combined-lineage
    coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  source-atom =
    applyTys-preserves-Atom (sourceChanges inner) atom

  second-relation =
    atomic-source-value-reindexᵀ source-atom vW
      (canonicalIndexedResults indexed) (transportType inner q)

  second = weak-one-step-keep-source-catchupᵀ
    (post-catchup-β-id (sourceChanges inner) vW)
    second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  second-lineage =
    weak-step-store-lineage
      (resultStore first) rel-store-embedding-reflⁱ prefix-reflⁱ

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first first-silent) second
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      second-lineage

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-id (sourceChanges inner) vW)
        second-relation)
world-coherent-source-id-widen-castᵀ atom prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-source-cast-blame-frameᵀ
      catchup framed refl first-silent
      first-transport first-coherence refl)
    terminal-combined-lineage
    coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-second-lineage =
    weak-step-store-lineage
      (resultStore terminal-first)
      rel-store-embedding-reflⁱ prefix-reflⁱ

  terminal-combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent terminal-first
        (left-silent-invariant refl refl))
      terminal-second
      terminal-first-lineage terminal-second-lineage


terminal-world-catchupᵀ :
  ∀ {Φ Δᴸ Δᴿ W V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  Value W →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ B ∶ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = W} {V′ = V′} {ρ = ρ} p
terminal-world-catchupᵀ coherent exclusive unique wfL vW noW relation =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-relatedᵀ (inj₁ (vW , noW)) relation)
    (weak-step-store-lineage
      _ rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL


world-coherent-source-seq-widen-castᵀ :
  ∀ {Φ Δᴸ Δᴿ N V′ A C B B′ s t μ sequence-shape}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  SourceCastSequenceMidpointᵀ →
  WorldCoherentLeftValueCatchupPrefixᵀ →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ A ⊑ C →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C ⊑ B →
  Widening (s ︔ t) →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ s ︔ t ⦂ sequence-shape →
  sequence-shape ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ s ︔ t ⟩} {V′ = V′} {ρ = ρ⁺} q
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    with result-widening-typingᵀ prefix mode seal★
      (C.cast-seq (proj₁ s⊑) (proj₁ t⊑) , seqʷ) indexed
       | result-widening-typing₂ᵀ
           prefix mode seal★ s⊑ t⊑ indexed
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    with final
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent-result
    combined-lineage
    (value-prefix prefix-reflⁱ coherent exclusive unique wfL runtime
      vV′ noV′ (canonicalIndexedResults first-indexed))
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ modec final-seal-c final-cast-c
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (sourceChanges inner) sequence-shape-proof)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  source-p =
    indexed-source-precision indexed

  source-q =
    transportType inner q

  seqʷ′ =
    subst Widening (applyCoercions-seq (sourceChanges inner) _ _)
      (applyCoercions-preserves-Widening (sourceChanges inner) seqʷ)

  midpoint-result =
    widening-midpoint midpoint prefix-reflⁱ coherent exclusive wfL
      modest final-seal-st (proj₁ final-cast-s) (proj₁ final-cast-t)
      seqʷ′ source-p source-q
      (cast-shape-applyCoercions (sourceChanges inner) s-shape)
      (cast-shape-applyCoercions (sourceChanges inner) t-shape)
      sequence-comp
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  source-mid = proj₁ midpoint-result

  s-triangle = proj₁ (proj₂ midpoint-result)

  t-triangle = proj₂ (proj₂ midpoint-result)

  s-relation =
    cast⊑⊑ᵀ modest final-seal-st final-cast-s
      (canonicalIndexedResults indexed) source-mid
      (cast-shape-applyCoercions (sourceChanges inner) s-shape)
      s-triangle

  second-relation =
    cast⊑⊑ᵀ modest final-seal-st final-cast-t
      s-relation source-q
      (cast-shape-applyCoercions (sourceChanges inner) t-shape)
      t-triangle

  second = weak-one-step-keep-source-catchupᵀ
    (post-catchup-β-seq (sourceChanges inner) vW)
    second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  second-lineage =
    weak-step-store-lineage
      (resultStore first) rel-store-embedding-reflⁱ prefix-reflⁱ

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first first-silent) second
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      second-lineage

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      (left-silent first first-silent) second
      first-transport
      (weak-one-step-keep-source-catchup-transportᵀ
        (post-catchup-β-seq (sourceChanges inner) vW)
        second-relation)

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      (left-silent first first-silent) second
      first-coherence
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        (post-catchup-β-seq (sourceChanges inner) vW)
        second-relation)

  first-indexed = weak-one-step-index-resultᵀ combined type-eq
    combined-transport combined-coherence

  runtime =
    ok-⟨⟩ (ok-⟨⟩ (ok-no noW))

  first-silent-result =
    left-silent-indexed first-indexed
      (left-silent-invariant refl refl) runtime
world-coherent-source-seq-widen-castᵀ
    midpoint value-prefix
    prefix mode seal★ s⊑ t⊑ seqʷ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q
    sequence-shape-proof@(
      shape-sequence-widening s-shape t-shape sequence-comp)
    outer-comp
    | μc , modec , final-seal-c , final-cast-c
    | μst , modest , final-seal-st , final-cast-s , final-cast-t
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-source-cast-blame-frameᵀ
      catchup framed refl first-silent
      first-transport first-coherence refl)
    terminal-combined-lineage
    coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ modec final-seal-c final-cast-c
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions
        (sourceChanges inner) sequence-shape-proof)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) outer-comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-second-lineage =
    weak-step-store-lineage
      (resultStore terminal-first)
      rel-store-embedding-reflⁱ prefix-reflⁱ

  terminal-combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent terminal-first
        (left-silent-invariant refl refl))
      terminal-second
      terminal-first-lineage terminal-second-lineage


world-coherent-source-inst-widen-castᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  ∀ {Φ Δᴸ Δᴿ N V′ A B B′ c μ s}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {index-occ : occurs zero A ≡ true}
    {r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar A}} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ C.inst B c ∶ `∀ A ⊑ B →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺}
    (ν safe index-occ r) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ C.inst B c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ ν safe index-occ r ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ C.inst B c ⟩} {V′ = V′} {ρ = ρ⁺} q
world-coherent-source-inst-widen-castᵀ value-prefix
    prefix mode seal★ c⊑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    with result-widening-typingᵀ prefix mode seal★ c⊑ indexed
world-coherent-source-inst-widen-castᵀ value-prefix
    prefix mode seal★ c⊑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    with final
world-coherent-source-inst-widen-castᵀ value-prefix
    prefix mode seal★ c⊑@(C.cast-inst hB occ s⊢ , NW.inst sʷ)
    vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape@(shape-inst inner-shape)
      comp@(comp-ν inner-comp)
    | μ′ , mode′ , final-seal , final-cast
    | inj₁ (vW , noW) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent-result
    combined-lineage
    (value-prefix prefix-reflⁱ coherent exclusive unique wfL runtime
      vV′ noV′ (canonicalIndexedResults first-indexed))
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  ν-seal★ =
    seal★-inst
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)

  source-cast =
    widen-weaken ≤-refl source-store-incl
      (s⊢ , NW.instSafe→widening sʷ)

  ν-framed = weak-one-step-source-νcast-frameᵀ
    mode ν-seal★ source-cast q inner-shape inner-comp indexed

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
    (post-catchup-β-inst (sourceChanges inner) vW)
    second-relation

  combined = weak-one-step-prepend-left-silentᵀ
    (left-silent first first-silent) second

  second-lineage =
    weak-step-store-lineage
      (resultStore first) rel-store-embedding-reflⁱ prefix-reflⁱ

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first first-silent) second
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      second-lineage

  type-eq = HE.≅-to-≡
    (HE.trans
      (subst²-to-≅
        {P = λ S T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ S ⊑ T ⊣ resultRightCtx combined}
        (sourceTypeResult combined)
        (targetTypeResult combined)
        (resultType combined))
      (HE.sym (weak-one-step-compose-type-to-nested≅
        first second q)))

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

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

  first-indexed = weak-one-step-index-resultᵀ combined type-eq
    combined-transport combined-coherence

  runtime =
    ok-ν (ok-no noW)

  first-silent-result =
    left-silent-indexed first-indexed
      (left-silent-invariant refl refl) runtime
world-coherent-source-inst-widen-castᵀ value-prefix
    prefix mode seal★ c⊑ vV′ noV′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      (weak-step-store-lineage
        lineage-store lineage-embedding lineage-prefix)
      coherent exclusive unique wfL)
    q c-shape comp
    | μ′ , mode′ , final-seal , final-cast
    | inj₂ refl =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-source-cast-blame-frameᵀ
      catchup framed refl first-silent
      first-transport first-coherence refl)
    terminal-combined-lineage
    coherent exclusive unique wfL
  where
  inner = weakIndexedResult indexed

  final-relation =
    cast⊑⊑ᵀ mode′ final-seal final-cast
      (canonicalIndexedResults indexed) (transportType inner q)
      (cast-shape-applyCoercions (sourceChanges inner) c-shape)
      (transport-source-widening-composition inner
        (weakIndexedTypeCoherence indexed) comp)

  first = weak-one-step-source-cast-frameᵀ inner final-relation

  framed = weak-indexed-result first (relatedResults first)
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed))
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed))

  first-silent =
    weak-one-step-source-cast-frame-silentᵀ
      inner final-relation silent

  first-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)

  first-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)

  terminal-first =
    weak-one-step-reindexᵀ first refl refl
      (canonicalIndexedResults framed)

  terminal-target⊢ =
    nu-term-imprecision-target-typing
      (relatedResults terminal-first)

  terminal-second-relation = blame⊑ᵀ terminal-target⊢

  terminal-second = weak-one-step-keep-source-catchupᵀ
    {p = resultType terminal-first}
    (pure-step blame-⟨⟩) terminal-second-relation

  terminal-first-lineage =
    weak-step-store-lineage
      lineage-store lineage-embedding lineage-prefix

  terminal-second-lineage =
    weak-step-store-lineage
      (resultStore terminal-first)
      rel-store-embedding-reflⁱ prefix-reflⁱ

  terminal-combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent terminal-first
        (left-silent-invariant refl refl))
      terminal-second
      terminal-first-lineage terminal-second-lineage
