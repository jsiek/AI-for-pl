module proof.NuImprecisionWorldCoherentValueCatchupPrefixProof where

-- File Charter:
--   * Implements ambient-prefix world-coherent target-value catch-up.
--   * Takes source-runtime and final quotient semantics as whole
--     higher-order contracts.
--   * Handles terminal, target-frame, prefix, and quotient transport cases
--     structurally without importing the permissive scratch dispatcher.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Product using (_,_)

open import Coercions using
  (Inert; genᵈ; id-onlyᵈ; tag-or-idᵈ)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NarrowWiden using (genSafe→inert)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; lift-left-ctx-[]
  ; rightStoreⁱ
  )
open import NuStore using (StoreWf)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Value
  ; no•-⟨⟩
  ; ok-⟨⟩
  ; ƛ_
  ; Λ_
  ; $
  ; _⟨_⟩
  )
open import QuotientedTermImprecision
open import proof.NuImprecisionCatchupPrefixSupport
open import proof.NuImprecisionCatchupQuotientSupport
open import proof.NuImprecisionQuotientWideningTransport using
  (weak-one-step-transport-quotient-widening-pairᵀ)
open import proof.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import proof.NuImprecisionWorldCoherentCatchupPrefixFrames
open import proof.NuImprecisionWorldCoherentQuotientFinalCatchupDef using
  (WorldCoherentQuotientFinalCatchupᵀ)
open import proof.NuImprecisionWorldCoherentResultDef
open import proof.NuImprecisionWorldCoherentSourceRuntimeCatchupDef
open import proof.NuImprecisionWorldCoherentValueCatchupPrefixDef using
  (WorldCoherentLeftValueCatchupPrefixᵀ)
open import proof.NuPreservation using (runtime-ν; runtime-⟨⟩)


world-coherent-left-catchup-prefix-down-upᵀ :
  WorldCoherentQuotientFinalCatchupᵀ →
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ d d′ u u′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  Value M′ →
  No• M′ →
  Inert d′ →
  Inert u′ →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ C′ ⊒ D′ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = M′} {ρ = ρ⁺} pC →
  WorldCoherentLeftCatchupIndexedResult
    {N = (M ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ⁺} pA
world-coherent-left-catchup-prefix-down-upᵀ
    quotient-final {qD = qD} prefix okM
    vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        invariant@(left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent final-exclusive final-wfL) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    (left-silent-indexed-prefix-down-up-from-finalᵀ
      prefix widening catchup final-down)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    (quotient-final coherent final-exclusive final-wfL final-ok
      vM′ noM′ inert-d′ inert-u′
      final-down final-widening final)
  where
  inner = weakIndexedResult indexed

  final-down = weak-one-step-transport-id-downᵀ {qD = qD}
    prefix indexed silent d⊒ d′⊒

  final-widening =
    weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner silent widening

  final-ok = ok-⟨⟩ (ok-⟨⟩ (left-catchup-final-runtime invariant))


world-coherent-left-catchup-prefix-gen-down-upᵀ :
  WorldCoherentQuotientFinalCatchupᵀ →
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ d d′ u u′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  Value M′ →
  No• M′ →
  Inert d′ →
  Inert u′ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
    ⊢ d ∶ C ⊒ D →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ d′ ∶ C′ ⊒ D′ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = M′} {ρ = ρ⁺} pC →
  WorldCoherentLeftCatchupIndexedResult
    {N = (M ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ⁺} pA
world-coherent-left-catchup-prefix-gen-down-upᵀ
    quotient-final {qD = qD} prefix okM
    vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        invariant@(left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent final-exclusive final-wfL) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    (left-silent-indexed-prefix-down-up-from-finalᵀ
      prefix widening catchup final-down)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    (quotient-final coherent final-exclusive final-wfL final-ok
      vM′ noM′ inert-d′ inert-u′
      final-down final-widening final)
  where
  inner = weakIndexedResult indexed

  final-down = weak-one-step-transport-gen-downᵀ {qD = qD}
    prefix indexed silent d⊒ d′⊒

  final-widening =
    weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner silent widening

  final-ok = ok-⟨⟩ (ok-⟨⟩ (left-catchup-final-runtime invariant))


world-coherent-left-value-catchup-prefix-proofᵀ :
  WorldCoherentSourceRuntimeCatchupᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentLeftValueCatchupPrefixᵀ
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    rel@(blame⊑ᵀ V′⊢) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-blameᵀ prefix noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM′))
    (up⊑upᵀ
      (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD) widening pA) =
  world-coherent-left-catchup-prefix-down-upᵀ
    quotient-catchup {qD = qD}
    prefix okN vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vM′ noM′ M⊑M′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM′))
    (up⊑upᵀ
      (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
      widening pA) =
  world-coherent-left-catchup-prefix-gen-down-upᵀ
    quotient-catchup {qD = qD}
    prefix okN vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ widening inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vM′ noM′ M⊑M′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (allocation-prefixᵀ prefix₀ inner N⊢ V′⊢) =
  world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive wfL okN vV′ noV′ inner
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊒ᵀ mode seal★ c⊒ rel q) =
  world-coherent-left-catchup-prefix-target-narrow-castᵀ
    prefix mode seal★ c⊒ inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊑ᵀ mode seal★ c⊑ rel q) =
  world-coherent-left-catchup-prefix-target-widen-castᵀ
    prefix mode seal★ c⊑ inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊑idᵀ seal★ c⊑ rel q) =
  world-coherent-left-catchup-prefix-target-widen-id-castᵀ
    prefix seal★ c⊑ inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑conv↑ᵀ c↑ rel q) =
  world-coherent-left-catchup-prefix-target-reveal-castᵀ
    prefix c↑ inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑conv↓ᵀ c↓ rel q) =
  world-coherent-left-catchup-prefix-target-conceal-castᵀ
    prefix c↓ inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (x⊑xᵀ x∈)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    rel@(ƛ⊑ƛᵀ hA hA′ body) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (ƛ _) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (·⊑·ᵀ L⊑L′ M⊑M′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    rel@(Λ⊑Λᵀ liftρ liftγ vV vW′ body) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (Λ vV) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    rel@(Λ⊑ᵀ occ liftρ liftγ vV body) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (Λ vV) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ
      L⊑L′ L•⊢ L′•⊢)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (α⊑ᵀ vL noL h⇑A liftρ lift-left-ctx-[]
      L⊑V′ L•⊢ V′⊢) =
  source-bullet source-runtime h⇑A prefix coherent exclusive wfL okN
    vV′ noV′ vL noL liftρ lift-left-ctx-[] L⊑V′ L•⊢ V′⊢
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (⊑αᵀ vL′ noL′ h⇑A liftρ liftγ N⊑L′ r N⊢ L′•⊢)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑ liftρ liftγ N⊑N′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (ν⊑ᵀ hA h⇑A s↑ liftρ lift-left-ctx-[] N⊑V′) =
  source-ν source-runtime prefix hA h⇑A s↑ liftρ lift-left-ctx-[]
    vV′ noV′ inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-ν okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (⊑νᵀ hA h⇑A s↑ liftρ liftγ pC N⊑N′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ compat liftρ liftγ N⊑N′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (νcast⊑ᵀ mode seal★ s⊑ liftρ lift-left-ctx-[] N⊑V′) =
  source-νcast source-runtime prefix mode seal★ s⊑
    liftρ lift-left-ctx-[] vV′ noV′ inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-ν okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ pC N⊑N′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′ rel@κ⊑κᵀ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN ($ _) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN () noV′
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vW noW
    rel@(gen⊑groundᵀ mode seal★ (c⊢ , NW.gen safe)
      gH vV vW′ W⊢ V⊑Wtag q) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (vV ⟨ genSafe→inert (NW.safe-gen safe) ⟩) noW rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (cast⊒⊑ᵀ mode seal★ c⊒ N⊑V′ q) =
  source-narrow source-runtime prefix mode seal★ c⊒
    vV′ noV′ inner q
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (cast⊑⊑ᵀ mode seal★ c⊑ N⊑V′ q) =
  source-widen source-runtime prefix mode seal★ c⊑
    vV′ noV′ inner q
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (conv⊑convᵀ conversion N⊑V′) =
  source-paired-cast source-runtime prefix conversion
    vV′ noV′ inert inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (conv↑⊑ᵀ c↑ N⊑V′ q) =
  source-reveal source-runtime prefix c↑ vV′ noV′ inner q
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive wfL okN vV′ noV′
    (conv↓⊑ᵀ c↓ N⊑V′ q) =
  source-conceal source-runtime prefix c↓ vV′ noV′ inner q
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
