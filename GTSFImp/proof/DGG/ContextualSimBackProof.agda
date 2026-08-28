{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimBackProof where

-- File Charter:
--   * Develops whole-root backward simulation by induction on the focused
--     target reduction while retaining the canonical CTI zipper.
--   * Installs every structural recursive call before discharging dynamic
--     root families, including contextual source catch-up before right-focus
--     application and primitive calls.
--   * Never transports a dormant sibling through source world evolution.

open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import CastTerms
import Conversion as Conv
open import Reduction

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.ContextualCatchupToLessPreciseDef using
  (ContextualCatchupToLessPreciseᵀ)
open import proof.DGG.ContextualSimBackDef using (ContextualSimBackᵀ)
open import proof.DGG.SourcePathBlameLemma using
  (source-path-blame-after)
open import proof.DGG.TargetBlameCatchupLemma using
  (target-blame-catchup)
open import proof.DGG.SimBackCastClosingDef using
  (SimBackPairedCastClosingᵀ; SimBackTargetCastClosingᵀ)
open import proof.DGG.SimBackPairedAllClosingDef using
  (SimBackPairedAllClosingᵀ)
open import proof.DGG.SimBackPairedFunClosingDef using
  (SimBackPairedFunClosingᵀ)
open import proof.DGG.SimBackPrimitiveClosingDef using
  (SimBackPrimitiveClosingᵀ)
open import proof.DGG.SimBackRebasedConversionDef using
  ( SimBackPairedRevealClosingᵀ
  ; SimBackTargetRevealRebaseClosingᵀ
  ; SimBackTargetRevealRebaseFrameᵀ
  )
open import proof.DGG.SimBackSourceLambdaDef using
  (SimBackSourceLambdaᵀ)
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.SimBackContextDef
open import proof.DGG.World
open import proof.Reduction using
  (appL-↠; appR-↠; applyTerms-preserves-Value)
open import proof.Reduction using (_++χ_; _—↠+[_]⟨_⟩_)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; composeMultiWorldEvolution
  ; multi-no-open-frames
  )


transport-target-rebuild : ∀ {Cᴸ Cᴸ′ Cᴿ Δᴿ′}
    {outer focus : RelatedConfiguration Cᴸ Cᴿ}
    {outer′ focus′ : RelatedConfiguration Cᴸ′ Cᴿ}
    {path : outer ↘ᶜ* focus} {path′ : outer′ ↘ᶜ* focus′}
    {χᴿ : StoreChange (Δᵉ Cᴿ) Δᴿ′}
    {focus-result root-result : Term Δᴿ′}
  → SourcePathEvolution path path′
  → RebuildTarget path χᴿ focus-result root-result
  → RebuildTarget path′ χᴿ focus-result root-result
transport-target-rebuild evolve-source-here
    (rebuild-target-here result-eq) =
  rebuild-target-here result-eq
transport-target-rebuild
    (evolve-source-there
      (evolve-source-edge frame-eq ready) tail-evolution)
    (rebuild-target-there tail-rebuild
      (rebuild-target-edge outer-eq))
    rewrite frame-eq =
  rebuild-target-there
    (transport-target-rebuild tail-evolution tail-rebuild)
    (rebuild-target-edge outer-eq)


module _
    (contextual-catchup : ContextualCatchupToLessPreciseᵀ)
    (sim-back-paired-fun-closing : SimBackPairedFunClosingᵀ)
    (sim-back-paired-all-closing : SimBackPairedAllClosingᵀ)
    (sim-back-paired-cast-closing : SimBackPairedCastClosingᵀ)
    (sim-back-target-cast-closing : SimBackTargetCastClosingᵀ)
    (sim-back-paired-reveal-closing : SimBackPairedRevealClosingᵀ)
    (sim-back-target-reveal-rebase-closing :
      SimBackTargetRevealRebaseClosingᵀ)
    (sim-back-primitive-closing : SimBackPrimitiveClosingᵀ)
    (sim-back-source-lambda : SimBackSourceLambdaᵀ)
    (sim-back-target-reveal-rebase-frame :
      SimBackTargetRevealRebaseFrameᵀ)
  where

  contextual-sim-back-worker : ∀
      {Δᴸ Δᴿ Δᴿ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ γᶠ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {root-source focus-source : Term Δᴸ}
      {root-target focus-target : Term Δᴿ}
      {root-source-type focus-source-type : Ty Δᴸ}
      {root-target-type focus-target-type : Ty Δᴿ}
      {root-type-related :
        root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
      {focus-type-related :
        focus-source-type ⊑ᵀ⟨ γᶠ ⟩ focus-target-type}
      {χᴿ : StoreChange Δᴿ Δᴿ′}
      {P′ N′ : Term Δᴿ′}
    → openFramesᶜ γ ≡ []
    → (root-related :
        γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
    → (focus-related :
        γᶠ CTI.⊢² focus-source ⊑ focus-target ∶
          focus-type-related)
    → (path : pack root-related ↘ᶜ* pack focus-related)
    → focus-target —→[ χᴿ ] P′
    → RebuildTarget path χᴿ P′ N′
    → (Σ[ Δᴸ′ ∈ TyCtx ]
        Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
        Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        Σ[ root′ ∈ RelatedConfiguration
          (⟨ Δᴸ′ , Σᴸ′ , [] ⟩)
          (⟨ Δᴿ′ , applyStore χᴿ Σᴿ , [] ⟩) ]
          (root-source —↠[ χsᴸ ] sourceTerm root′)
          × targetTerm root′ ≡ N′
          × MultiWorldEvolution
              {W = γ} {W′ = world root′} χsᴸ (χᴿ ∷ []) )
      ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
        Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
          (root-source —↠[ χsᴸ ] blame))
  contextual-sim-back-worker no-open root-related
      (CTI.x⊑x² source∋ target∋) path (pure-step ()) rebuild

  contextual-sim-back-worker no-open root-related
      (CTI.ƛ⊑ƛ² related) path (pure-step ()) rebuild

  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related) path
      (ξ-·₁ function-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related function-related
      (extend-focus path (focus-·₁ function-related argument-related))
      function-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))

  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ target-value argument-step refl) rebuild
      with contextual-catchup no-open
        (extend-focus path
          (focus-·₁ function-related argument-related))
        target-value
  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ target-value argument-step refl) rebuild
    | inj₂ (DeltaL1 , SigmaL1 , changesL1 , world1 , source-blame ,
        evolution1) =
      inj₂ (DeltaL1 , changesL1 , source-blame)
  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ target-value argument-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
      with split-source-extended-path
        {path = path}
        {edge = focus-·₁ function-related argument-related}
        path-evolution1
  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ target-value argument-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-·₁ function-related1 argument-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
      with contextual-sim-back-worker
        (multi-no-open-frames evolution1 no-open)
        root-related1 argument-related1
        (extend-focus prefix1
          (focus-·₂ function-related1 argument-related1
            source-value1))
        argument-step
        (extend-target-rebuild
          (transport-target-rebuild prefix-evolution1 rebuild)
          (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ target-value argument-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-·₁ function-related1 argument-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
    | inj₁
        (DeltaL2 , SigmaL2 , changesL2 , pack root-related2 ,
          source-steps2 , target-eq2 , evolution2) =
      inj₁
        (DeltaL2 , SigmaL2 , changesL1 ++χ changesL2 ,
          pack root-related2 ,
          (sourceTerm (pack root-related)
           —↠+[ changesL1 ]⟨ source-steps1 ⟩
           sourceTerm (pack root-related1)
           —↠[ changesL2 ]⟨ source-steps2 ⟩
           sourceTerm (pack root-related2) ∎[]) ,
          target-eq2 ,
          composeMultiWorldEvolution evolution1 evolution2)
  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ target-value argument-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-·₁ function-related1 argument-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
    | inj₂ (DeltaL2 , changesL2 , source-blame2) =
      inj₂
        (DeltaL2 , changesL1 ++χ changesL2 ,
          (sourceTerm (pack root-related)
           —↠+[ changesL1 ]⟨ source-steps1 ⟩
           sourceTerm (pack root-related1)
           —↠[ changesL2 ]⟨ source-blame2 ⟩
           blame ∎[]))

  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) focus-here
      (pure-step (β target-value)) (rebuild-target-here refl) = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail)
      (pure-step (β target-value)) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) focus-here
      (pure-step (β-⇒ function-value argument-value))
      (rebuild-target-here refl) = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail)
      (pure-step (β-⇒ function-value argument-value)) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) focus-here
      (pure-step (β-reveal-⇒ function-value argument-value))
      (rebuild-target-here refl) = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail)
      (pure-step (β-reveal-⇒ function-value argument-value))
      rebuild = {! !}

  contextual-sim-back-worker no-open root-related
        (CTI.·⊑·² function-related argument-related) focus-here
      (pure-step (β-conceal-⇒ function-value argument-value))
      (rebuild-target-here refl) = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail)
      (pure-step (β-conceal-⇒ function-value argument-value))
      rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² {L = L} {M = M}
        function-related argument-related)
      path (pure-step blame-·₁) rebuild
      with target-blame-catchup function-related
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² {L = L} {M = M}
        function-related argument-related)
      path (pure-step blame-·₁) rebuild
    | DeltaL1 , changesL1 , function-blame
      with source-path-blame-after path
        (L · M
         —↠+[ changesL1 ]⟨ appL-↠ function-blame ⟩
         blame · applyTerms changesL1 M
         —→[ keep ]⟨ pure-step blame-·₁ ⟩
         blame ∎[])
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² {L = L} {M = M}
        function-related argument-related)
      path (pure-step blame-·₁) rebuild
    | DeltaL1 , changesL1 , function-blame
    | changesL2 , source-blame , evolve =
      inj₂ (DeltaL1 , changesL2 , source-blame)

  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path (pure-step (blame-·₂ target-value)) rebuild
      with contextual-catchup no-open
        (extend-focus path
          (focus-·₁ function-related argument-related))
        target-value
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path (pure-step (blame-·₂ target-value)) rebuild
    | inj₂ (DeltaL1 , SigmaL1 , changesL1 , world1 , source-blame ,
        evolution1) =
      inj₂ (DeltaL1 , changesL1 , source-blame)
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path (pure-step (blame-·₂ target-value)) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
      with split-source-extended-path
        {path = path}
        {edge = focus-·₁ function-related argument-related}
        path-evolution1
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path (pure-step (blame-·₂ target-value)) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-·₁ function-related1 argument-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
      with target-blame-catchup argument-related1
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path (pure-step (blame-·₂ target-value)) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-·₁ function-related1 argument-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
    | DeltaL2 , changesL2 , argument-blame
      with source-path-blame-after prefix1
        (sourceTerm (pack function-related1)
           · sourceTerm (pack argument-related1)
         —↠+[ changesL2 ]⟨
           appR-↠ source-value1 argument-blame ⟩
         applyTerms changesL2 (sourceTerm (pack function-related1))
           · blame
         —→[ keep ]⟨ pure-step
           (blame-·₂
             (applyTerms-preserves-Value changesL2 source-value1)) ⟩
         blame ∎[])
  contextual-sim-back-worker no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path (pure-step (blame-·₂ target-value)) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack function-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-·₁ function-related1 argument-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
    | DeltaL2 , changesL2 , argument-blame
    | changesL3 , source-blame3 , evolve =
      inj₂
        (DeltaL2 , changesL1 ++χ changesL3 ,
          (sourceTerm (pack root-related)
           —↠+[ changesL1 ]⟨ source-steps1 ⟩
           sourceTerm (pack root-related1)
           —↠[ changesL3 ]⟨ source-blame3 ⟩
           blame ∎[]))

  contextual-sim-back-worker no-open root-related
      (CTI.Λ⊑Λ² source-value target-value related q) path
      (pure-step ()) rebuild

  contextual-sim-back-worker no-open root-related
      (CTI.Λ⊑² nonvar occurs source-value target⊢ related q)
      focus-here target-step (rebuild-target-here refl) = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.Λ⊑² nonvar occurs source-value target⊢ related q)
      path@(focus-there edge tail) target-step rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.•⊑•² p∀ related q r) path
      (ξ-• target-step refl refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path (focus-•-paired p∀ related q r))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.•⊑•² p∀ related q r) path
      (pure-step (β-∀ target-value instantiated))
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.•⊑•² p∀ related q r) path (pure-step blame-•)
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.•⊑•² p∀ related q r) path (β-Λ target-value)
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.•⊑•² p∀ related q r) path
      (β-gen target-value target≠★ safe) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.•⊑•² p∀ related q r) path
      (β-reveal-∀ target-value) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.•⊑•² p∀ related q r) path
      (β-conceal-∀ target-value) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.•⊑² p∀ related q r) path target-step rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path (focus-•-source p∀ related q r))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))

  contextual-sim-back-worker no-open root-related
      (CTI.κ⊑κ² constant q) path (pure-step ()) rebuild

  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (ξ-⟨⟩ target-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-cast-paired source-cast target-cast related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (pure-step (β-id target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (pure-step (ground target-value unequal)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (pure-step (expand target-value unequal)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (pure-step (tag-untag target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (pure-step (tag-untag-bad target-value unequal))
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (pure-step (blame-bot-intro target-value))
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (pure-step blame-⟨⟩) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path
      (β-inst target-value target≠★) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (ξ-⟨⟩ target-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path (focus-cast-target target-cast related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (pure-step (β-id target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (pure-step (ground target-value unequal)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (pure-step (expand target-value unequal)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (pure-step (tag-untag target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (pure-step (tag-untag-bad target-value unequal))
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (pure-step (blame-bot-intro target-value))
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (pure-step blame-⟨⟩) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (β-inst target-value target≠★) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.cast⊑² source-cast related q) path target-step rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path (focus-cast-source source-cast related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))

  contextual-sim-back-worker no-open root-related
      (CTI.⊑reveal-identity conversion position related q) path
      (ξ-reveal target-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-target-reveal-identity conversion position related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.⊑reveal-identity conversion position related q) path
      (pure-step (id-reveal target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
        (CTI.⊑reveal-identity
          (Conv.⊢↑-unseal member) () related q)
      path (pure-step (conceal-reveal target-value)) rebuild
  contextual-sim-back-worker no-open root-related
      (CTI.⊑reveal-identity conversion position related q) path
      (pure-step blame-reveal) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.⊑conceal-identity conversion position related q) path
      (ξ-conceal target-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-target-conceal-identity conversion position related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.⊑conceal-identity conversion position related q) path
      (pure-step (id-conceal target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑conceal-identity conversion position related q) path
      (pure-step blame-conceal) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.reveal⊑-identity c⊢ absent related q) path target-step
      rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-source-reveal-identity c⊢ absent related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related q)
      path target-step rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-source-reveal-only
          c⊢ present mark free represented related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.conceal⊑-identity c⊢ absent related q) path target-step
      rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-source-conceal-identity c⊢ absent related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.conceal⊑-only² c⊢ present mark free represented related q)
      path target-step rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-source-conceal-only
          c⊢ present mark free represented related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))

  contextual-sim-back-worker no-open root-related
      (CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related q) path
      (ξ-reveal target-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-reveal-paired
          c⊢ c′⊢ positions aligned represented related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related q) path
      (pure-step (id-reveal target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related q) path
      (pure-step (conceal-reveal target-value))
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related q) path
      (pure-step blame-reveal) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented related q) path
      (ξ-conceal target-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-conceal-paired
          c⊢ c′⊢ positions aligned represented related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented related q) path
      (pure-step (id-conceal target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented related q) path
      (pure-step blame-conceal) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.⊑reveal-rebase² c′⊢ rebase related q) path
      (ξ-reveal target-step refl) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑reveal-rebase² c′⊢ rebase related q) path
      (pure-step (id-reveal target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑reveal-rebase² c′⊢ rebase related q) path
      (pure-step (conceal-reveal target-value))
      rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑reveal-rebase² c′⊢ rebase related q) path
      (pure-step blame-reveal) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.⊑conceal-rebase² c′⊢ rebase related q) path
      (ξ-conceal target-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related related
      (extend-focus path
        (focus-target-conceal-rebase c′⊢ rebase related q))
      target-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.⊑conceal-rebase² c′⊢ rebase related q) path
      (pure-step (id-conceal target-value)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊑conceal-rebase² c′⊢ rebase related q) path
      (pure-step blame-conceal) rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.blame⊑² target⊢ q) path target-step rebuild = {! !}

  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (ξ-⊕₁ left-step refl) rebuild =
    contextual-sim-back-worker no-open
      root-related left-related
      (extend-focus path
        (focus-⊕₁ left-related right-related r))
      left-step
      (extend-target-rebuild rebuild (rebuild-target-edge refl))

  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (ξ-⊕₂ target-value right-step refl) rebuild
      with contextual-catchup no-open
        (extend-focus path
          (focus-⊕₁ left-related right-related r))
        target-value
  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (ξ-⊕₂ target-value right-step refl) rebuild
    | inj₂ (DeltaL1 , SigmaL1 , changesL1 , world1 , source-blame ,
        evolution1) =
      inj₂ (DeltaL1 , changesL1 , source-blame)
  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (ξ-⊕₂ target-value right-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack left-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
      with split-source-extended-path
        {path = path}
        {edge = focus-⊕₁ left-related right-related r}
        path-evolution1
  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (ξ-⊕₂ target-value right-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack left-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-⊕₁ left-related1 right-related1 result-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
      with contextual-sim-back-worker
        (multi-no-open-frames evolution1 no-open)
        root-related1 right-related1
        (extend-focus prefix1
          (focus-⊕₂ left-related1 right-related1 result-related1
            source-value1))
        right-step
        (extend-target-rebuild
          (transport-target-rebuild prefix-evolution1 rebuild)
          (rebuild-target-edge refl))
  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (ξ-⊕₂ target-value right-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack left-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-⊕₁ left-related1 right-related1 result-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
    | inj₁
        (DeltaL2 , SigmaL2 , changesL2 , pack root-related2 ,
          source-steps2 , target-eq2 , evolution2) =
      inj₁
        (DeltaL2 , SigmaL2 , changesL1 ++χ changesL2 ,
          pack root-related2 ,
          (sourceTerm (pack root-related)
           —↠+[ changesL1 ]⟨ source-steps1 ⟩
           sourceTerm (pack root-related1)
           —↠[ changesL2 ]⟨ source-steps2 ⟩
           sourceTerm (pack root-related2) ∎[]) ,
          target-eq2 ,
          composeMultiWorldEvolution evolution1 evolution2)
  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (ξ-⊕₂ target-value right-step refl) rebuild
    | inj₁
        (DeltaL1 , SigmaL1 , changesL1 , pack root-related1 ,
          pack left-related0 , path1 ,
          source-steps1 , source-value1 , root-target-eq1 ,
          refl , path-evolution1 , evolution1)
    | evolved-source-extended-path prefix1
        (focus-⊕₁ left-related1 right-related1 result-related1) refl
        prefix-evolution1
        (evolve-source-edge refl source-ready1)
    | inj₂ (DeltaL2 , changesL2 , source-blame2) =
      inj₂
        (DeltaL2 , changesL1 ++χ changesL2 ,
          (sourceTerm (pack root-related)
           —↠+[ changesL1 ]⟨ source-steps1 ⟩
           sourceTerm (pack root-related1)
           —↠[ changesL2 ]⟨ source-blame2 ⟩
           blame ∎[]))

  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (pure-step (δ-⊕ primitive-step)) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (pure-step blame-⊕₁) rebuild = {! !}
  contextual-sim-back-worker no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path
      (pure-step (blame-⊕₂ target-value))
      rebuild = {! !}

  contextual-sim-back : ContextualSimBackᵀ
  contextual-sim-back
      {root = pack root-related} {focus = pack focus-related}
      no-open path target-step rebuild =
    contextual-sim-back-worker no-open root-related focus-related path
      target-step rebuild
