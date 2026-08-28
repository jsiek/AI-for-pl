{-# OPTIONS --safe #-}

module proof.DGG.ContextualSimProof where

-- File Charter:
--   * Develops whole-root forward simulation by induction on a focused CTI
--     node and its source step beneath the canonical CTI zipper.
--   * Installs every structural recursive call before discharging dynamic
--     roots, including contextual target catch-up before right-focus calls.
--   * Uses the whole-caller target reveal/rebase boundary at the selected
--     reveal edge and never transports application or primitive siblings by
--     the broad source-evolution CTI transport theorem.

open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym; trans)

open import CastTerms using
  ( Term; Value; ⟨_,_,_⟩; _·_; _⦂∀_[_]; _⟨_⟩; _↑_; _↓_; _⊕[_]_
  )
open import CastTerms using (_《_》; fun)
open import Imprecision using (⇒⊑⇒)
open import Reduction
open import proof.Reduction using (_++χ_; _—↠+[_]⟨_⟩_; applyTys-++)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.Catchup.ContextualCatchupToMorePreciseDef using
  (ContextualCatchupToMorePreciseᵀ)
open import proof.DGG.ContextualSimDef using (ContextualSimᵀ)
open import proof.DGG.ContextualSimPairedFunValuesDef using
  (ContextualSimPairedFunValuesᵀ)
open import proof.DGG.SimPairedAllClosingDef using
  (SimPairedAllClosingᵀ)
open import proof.DGG.SimPairedCastValuesDef using
  (SimPairedCastValuesᵀ)
open import proof.DGG.SimPairedFunClosingDef using
  (SimPairedFunClosingᵀ)
open import proof.DGG.SimPairedRevealClosingDef using
  (SimPairedRevealClosingᵀ)
open import proof.DGG.SimPrimitiveClosingDef using
  (SimPrimitiveClosingᵀ)
open import proof.DGG.SimSourceAllClosingDef using
  (SimSourceAllClosingᵀ)
open import proof.DGG.SimSourceCastValuesDef using
  (SimSourceCastValuesᵀ)
open import proof.DGG.SimSourceRevealClosingDef using
  (SimSourceRevealClosingᵀ)
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.World using (openFramesᶜ; _⊑ᶜ_; _⊑ᵀ⟨_⟩_)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; composeMultiWorldEvolution; multi-no-open-frames )


module _
    (contextual-catchup : ContextualCatchupToMorePreciseᵀ)
    (contextual-sim-paired-fun-values :
      ContextualSimPairedFunValuesᵀ)
    (sim-paired-fun-closing : SimPairedFunClosingᵀ)
    (sim-paired-all-closing : SimPairedAllClosingᵀ)
    (sim-source-all-closing : SimSourceAllClosingᵀ)
    (sim-paired-cast-values : SimPairedCastValuesᵀ)
    (sim-source-cast-values : SimSourceCastValuesᵀ)
    (sim-source-reveal-closing : SimSourceRevealClosingᵀ)
    (sim-paired-reveal-closing : SimPairedRevealClosingᵀ)
    (sim-primitive-closing : SimPrimitiveClosingᵀ)
    (whole-target-reveal-rebase-closing :
      WholeContextualTargetRevealRebaseClosingᵀ)
  where

  contextual-sim-paired-fun-context : ∀
      {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ γᶠ :
        ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {root-source root-result focus-result : Term Δᴸ}
      {root-target : Term Δᴿ}
      {root-source-type : Ty Δᴸ}
      {root-target-type : Ty Δᴿ}
      {function argument : Term Δᴸ}
      {target-function target-argument : Term Δᴿ}
      {argument-type result-type : Ty Δᴸ}
      {argument-type′ result-type′ : Ty Δᴿ}
      {root-type-related :
        root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
      {argument-type-related :
        argument-type ⊑ᵀ⟨ γᶠ ⟩ argument-type′}
      {result-type-related :
        result-type ⊑ᵀ⟨ γᶠ ⟩ result-type′}
    → openFramesᶜ γ ≡ []
    → (root-related :
        γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
    → (function-related :
        γᶠ CTI.⊢² function ⊑ target-function ∶
          ⇒⊑⇒ argument-type-related result-type-related)
    → (argument-related :
        γᶠ CTI.⊢² argument ⊑ target-argument ∶
          argument-type-related)
    → (path : pack root-related ↘ᶜ*
        pack (CTI.·⊑·² function-related argument-related))
    → TargetReady path
    → Value function
    → Value argument
    → function · argument —→ focus-result
    → RebuildSource path keep focus-result root-result
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ result-target ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ final-related ∈
        applyTy keep root-source-type ⊑ᵀ⟨ γ′ ⟩
          applyTys χsᴿ root-target-type ]
        (root-target —↠[ χsᴿ ] result-target)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (keep ∷ []) χsᴿ
        × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
      with contextual-catchup no-open root-related function-related
        (extend-focus path (focus-·₁ function-related argument-related))
        (extend-path-target-ready path
          (focus-·₁ function-related argument-related) ready _)
        function-value
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
      with split-target-extended-path path-evolution₁
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
      with application-left-edge-view
        {M = sourceTerm (pack argument-related)} edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₁))
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
      with contextual-catchup
        (multi-no-open-frames evolution₁ no-open) root-related₁
        argument-related₁
        (extend-focus prefix₁
          (focus-·₂ function-related₂ argument-related₁
            (subst Value (cong sourceTerm function-focus-eq₁)
              function-value)))
        (extend-path-target-ready prefix₁
          (focus-·₂ function-related₂ argument-related₁
            (subst Value (cong sourceTerm function-focus-eq₁)
              function-value))
          (target-path-ready prefix-evolution₁)
          (subst Value (cong targetTerm function-focus-eq₁)
            target-function-value₁))
        argument-value
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ ,
      γᶠ₂ , root-type₂ , argument-type₂ , root-steps₂ ,
      target-argument-value₂ , evolution₂ , root-related₂ ,
      argument-related₂ , argument-path₂ , path-evolution₂
      with split-target-extended-path path-evolution₂
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ ,
      γᶠ₂ , root-type₂ , argument-type₂ , root-steps₂ ,
      target-argument-value₂ , evolution₂ , root-related₂ ,
      argument-related₂ , argument-path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
      with application-right-edge-view edge₂
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₂))
        (TargetEdgeEvolution.target-edge-ready edge-evolution₂)
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ ,
      γᶠ₂ , root-type₂ , argument-type₂ , root-steps₂ ,
      target-argument-value₂ , evolution₂ , root-related₂ ,
      argument-related₂ , argument-path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
      with cong sourceTerm function-focus-eq₁
         | cong sourceTerm argument-focus-eq₂
         | cong targetTerm argument-focus-eq₂
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ ,
      γᶠ₂ , root-type₂ , argument-type₂ , root-steps₂ ,
      target-argument-value₂ , evolution₂ , root-related₂ ,
      argument-related₂ , argument-path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
    | refl | refl | refl
      with contextual-sim-paired-fun-values
        (multi-no-open-frames evolution₂
          (multi-no-open-frames evolution₁ no-open))
        root-related₂ function-related₃ argument-related₃ prefix₂
        (target-path-ready
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂))
        source-function-value₃ argument-value target-function-value₃
        target-argument-value₂ source-root-step
        (transport-rebuild
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂)
          rebuild)
  contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready function-value
      argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ ,
      γ₁ , γᶠ₁ , root-type₁ , function-type₁ , root-steps₁ ,
      target-function-value₁ , evolution₁ , root-related₁ ,
      function-related₁ , function-path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ ,
      γᶠ₂ , root-type₂ , argument-type₂ , root-steps₂ ,
      target-argument-value₂ , evolution₂ , root-related₂ ,
      argument-related₂ , argument-path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
    | refl | refl | refl
    | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result-target , γ₃ , result-type₃ ,
      values-steps , values-evolution , result-relation =
    let
      target-type-eq =
        trans
          (applyTys-++ χsᴿ₂ χsᴿ₃ (applyTys χsᴿ₁ _))
          (applyTys-++ χsᴿ₁ (χsᴿ₂ ++χ χsᴿ₃) _)
      normalized-result =
        subst
          (λ T →
            Σ[ q ∈ _ ⊑ᵀ⟨ γ₃ ⟩ T ]
              γ₃ CTI.⊢² _ ⊑ result-target ∶ q)
          target-type-eq (result-type₃ , result-relation)
      final-type = proj₁ normalized-result
      final-related = proj₂ normalized-result
    in
      Δᴿ₃ , Σᴿ₃ , χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃) , result-target , γ₃ ,
      final-type ,
      (targetTerm (pack root-related)
         —↠+[ χsᴿ₁ ]⟨ root-steps₁ ⟩
       root-target₁
         —↠+[ χsᴿ₂ ]⟨ root-steps₂ ⟩
       root-target₂
         —↠[ χsᴿ₃ ]⟨ values-steps ⟩
       result-target ∎[]) ,
      composeMultiWorldEvolution evolution₁
        (composeMultiWorldEvolution evolution₂ values-evolution) ,
      final-related

  contextual-sim : ContextualSimᵀ
  contextual-sim no-open root-related
      (CTI.x⊑x² source∋ target∋) path ready (pure-step ()) rebuild

  contextual-sim no-open root-related (CTI.ƛ⊑ƛ² related) path ready
      (pure-step ()) rebuild

  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (ξ-·₁ function-step refl) rebuild =
    contextual-sim no-open root-related function-related
      (extend-focus path (focus-·₁ function-related argument-related))
      (extend-path-target-ready path
        (focus-·₁ function-related argument-related) ready _)
      function-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (ξ-·₂ {χ = χᴸ} function-value argument-step refl) rebuild
      with contextual-catchup no-open root-related function-related
        (extend-focus path (focus-·₁ function-related argument-related))
        (extend-path-target-ready path
          (focus-·₁ function-related argument-related) ready _)
        function-value
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (ξ-·₂ {χ = χᴸ} function-value argument-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , function-type₁ , root-steps₁ , target-value ,
      evolution₁ , root-related₁ , function-related₁ , function-path₁ ,
      path-evolution
      with split-target-extended-path path-evolution
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (ξ-·₂ {χ = χᴸ} function-value argument-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , function-type₁ , root-steps₁ , target-value ,
      evolution₁ , root-related₁ , function-related₁ , function-path₁ ,
      path-evolution
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution edge-evolution
      with application-left-edge-view edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution))
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (ξ-·₂ {χ = χᴸ} function-value argument-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , function-type₁ , root-steps₁ , target-value ,
      evolution₁ , root-related₁ , function-related₁ , function-path₁ ,
      path-evolution
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution edge-evolution
    | application-left-edge function-related₂ argument-related₂ refl
        function-focus-eq
      with contextual-sim
        (multi-no-open-frames evolution₁ no-open) root-related₁
        argument-related₂
        (extend-focus prefix₁
          (focus-·₂ function-related₂ argument-related₂
            (subst Value (cong sourceTerm function-focus-eq)
              function-value)))
        (extend-path-target-ready prefix₁
          (focus-·₂ function-related₂ argument-related₂
            (subst Value (cong sourceTerm function-focus-eq)
              function-value))
          (target-path-ready prefix-evolution)
          (subst Value (cong targetTerm function-focus-eq) target-value))
        argument-step
        (extend-rebuild (transport-rebuild prefix-evolution rebuild)
          (rebuild-edge
            (cong (λ K → applyTerm χᴸ K · _)
              (cong sourceTerm function-focus-eq))))
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (ξ-·₂ {χ = χᴸ} function-value argument-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , function-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , function-type₁ , root-steps₁ , target-value ,
      evolution₁ , root-related₁ , function-related₁ , function-path₁ ,
      path-evolution
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution edge-evolution
    | application-left-edge function-related₂ argument-related₂ refl
        function-focus-eq
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , γ₂ , result-type₂ ,
      root-steps₂ , evolution₂ , root-related₂ =
    let
      target-type-eq = applyTys-++ χsᴿ₁ χsᴿ₂ _
      normalized-result =
        subst
          (λ T →
            Σ[ q ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ CTI.⊢² _ ⊑ root-target₂ ∶ q)
          target-type-eq (result-type₂ , root-related₂)
      final-type = proj₁ normalized-result
      final-related = proj₂ normalized-result
    in
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , root-target₂ , γ₂ , final-type ,
      (targetTerm (pack root-related)
         —↠+[ χsᴿ₁ ]⟨ root-steps₁ ⟩
       root-target₁
         —↠[ χsᴿ₂ ]⟨ root-steps₂ ⟩
       root-target₂ ∎[]) ,
      composeMultiWorldEvolution evolution₁ evolution₂ ,
      final-related

  contextual-sim no-open
      relation@(CTI.·⊑·² {M = argument}
        function-related argument-related)
      .relation focus-here tt
      (pure-step (root@(β {N = body} argument-value)))
      (rebuild-here refl) =
    sim-paired-fun-closing no-open function-related argument-related
      (CastTerms.Value.ƛ body) argument-value root
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail) ready
      (pure-step (root@(β {N = body} argument-value))) rebuild =
    contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready
      (CastTerms.Value.ƛ body) argument-value root rebuild

  contextual-sim no-open
      relation@(CTI.·⊑·² function-related argument-related)
      .relation focus-here tt
      (pure-step (root@(β-⇒ function-value argument-value)))
      (rebuild-here refl) =
    sim-paired-fun-closing no-open function-related argument-related
      (function-value 《 fun 》) argument-value root
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail) ready
      (pure-step (root@(β-⇒ function-value argument-value))) rebuild =
    contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready
      (function-value 《 fun 》) argument-value root rebuild

  contextual-sim no-open
      relation@(CTI.·⊑·² function-related argument-related)
      .relation focus-here tt
      (pure-step (root@(β-reveal-⇒ function-value argument-value)))
      (rebuild-here refl) =
    sim-paired-fun-closing no-open function-related argument-related
      (function-value ↑ fun) argument-value root
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail) ready
      (pure-step (root@(β-reveal-⇒ function-value argument-value)))
      rebuild =
    contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready
      (function-value ↑ fun) argument-value root rebuild

  contextual-sim no-open
      relation@(CTI.·⊑·² function-related argument-related)
      .relation focus-here tt
      (pure-step (root@(β-conceal-⇒ function-value argument-value)))
      (rebuild-here refl) =
    sim-paired-fun-closing no-open function-related argument-related
      (function-value ↓ fun) argument-value root
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related)
      path@(focus-there edge tail) ready
      (pure-step (root@(β-conceal-⇒ function-value argument-value)))
      rebuild =
    contextual-sim-paired-fun-context no-open root-related
      function-related argument-related path ready
      (function-value ↓ fun) argument-value root rebuild

  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (pure-step blame-·₁) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.·⊑·² function-related argument-related) path ready
      (pure-step (blame-·₂ function-value)) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.Λ⊑Λ² source-value target-value related q) path ready
      (pure-step ()) rebuild

  contextual-sim no-open root-related
      (CTI.Λ⊑² nonvar occurs source-value target⊢ related q) path ready
      (pure-step ()) rebuild

  contextual-sim no-open root-related
      (CTI.•⊑•² p∀ related q r) path ready
      (ξ-• source-step refl refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path (focus-•-paired p∀ related q r))
      (extend-path-target-ready path
        (focus-•-paired p∀ related q r) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.•⊑•² p∀ related q r) path ready
      (pure-step (β-∀ source-value instantiated)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑•² p∀ related q r) path ready
      (pure-step blame-•) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑•² p∀ related q r) path ready
      (β-Λ source-value) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑•² p∀ related q r) path ready
      (β-gen source-value source≠★ safe) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑•² p∀ related q r) path ready
      (β-reveal-∀ source-value) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑•² p∀ related q r) path ready
      (β-conceal-∀ source-value) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.•⊑² p∀ related q r) path ready
      (ξ-• source-step refl refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path (focus-•-source p∀ related q r))
      (extend-path-target-ready path
        (focus-•-source p∀ related q r) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.•⊑² p∀ related q r) path ready
      (pure-step (β-∀ source-value instantiated)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑² p∀ related q r) path ready
      (pure-step blame-•) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑² p∀ related q r) path ready
      (β-Λ source-value) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑² p∀ related q r) path ready
      (β-gen source-value source≠★ safe) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑² p∀ related q r) path ready
      (β-reveal-∀ source-value) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.•⊑² p∀ related q r) path ready
      (β-conceal-∀ source-value) rebuild = {! !}

  contextual-sim no-open root-related (CTI.κ⊑κ² constant p) path ready
      (pure-step ()) rebuild

  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (ξ-⟨⟩ source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-cast-paired source-cast target-cast related q))
      (extend-path-target-ready path
        (focus-cast-paired source-cast target-cast related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (pure-step (β-id source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (pure-step (ground source-value unequal)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (pure-step (expand source-value unequal)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (pure-step (tag-untag source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (pure-step (tag-untag-bad source-value unequal)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (pure-step (blame-bot-intro source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (pure-step blame-⟨⟩) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑cast² source-cast target-cast related q) path ready
      (β-inst source-value source≠★) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.⊑cast² target-cast related q) path ready source-step rebuild =
    contextual-sim no-open root-related related
      (extend-focus path (focus-cast-target target-cast related q))
      (extend-path-target-ready path
        (focus-cast-target target-cast related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))

  contextual-sim no-open root-related
      (CTI.⊑reveal-identity c′⊢ absent related q) path ready
      source-step rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-target-reveal-identity c′⊢ absent related q))
      (extend-path-target-ready path
        (focus-target-reveal-identity c′⊢ absent related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))

  contextual-sim no-open root-related
      (CTI.⊑conceal-identity c′⊢ absent related q) path ready
      source-step rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-target-conceal-identity c′⊢ absent related q))
      (extend-path-target-ready path
        (focus-target-conceal-identity c′⊢ absent related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))

  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (ξ-⟨⟩ source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path (focus-cast-source source-cast related q))
      (extend-path-target-ready path
        (focus-cast-source source-cast related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (pure-step (β-id source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (pure-step (ground source-value unequal)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (pure-step (expand source-value unequal)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (pure-step (tag-untag source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (pure-step (tag-untag-bad source-value unequal)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (pure-step (blame-bot-intro source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (pure-step blame-⟨⟩) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.cast⊑² source-cast related q) path ready
      (β-inst source-value source≠★) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.reveal⊑-identity c⊢ absent related q) path ready
      (ξ-reveal source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-source-reveal-identity c⊢ absent related q))
      (extend-path-target-ready path
        (focus-source-reveal-identity c⊢ absent related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.reveal⊑-identity c⊢ absent related q) path ready
      (pure-step (id-reveal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.reveal⊑-identity c⊢ absent related q) path ready
      (pure-step (conceal-reveal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.reveal⊑-identity c⊢ absent related q) path ready
      (pure-step blame-reveal) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related q)
      path ready (ξ-reveal source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-source-reveal-only c⊢ present mark free represented
          related q))
      (extend-path-target-ready path
        (focus-source-reveal-only c⊢ present mark free represented
          related q)
        ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related q)
      path ready (pure-step (id-reveal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related q)
      path ready (pure-step (conceal-reveal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related q)
      path ready (pure-step blame-reveal) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.conceal⊑-identity c⊢ absent related q) path ready
      (ξ-conceal source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-source-conceal-identity c⊢ absent related q))
      (extend-path-target-ready path
        (focus-source-conceal-identity c⊢ absent related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.conceal⊑-identity c⊢ absent related q) path ready
      (pure-step (id-conceal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.conceal⊑-identity c⊢ absent related q) path ready
      (pure-step blame-conceal) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.conceal⊑-only² c⊢ present mark free represented related q)
      path ready (ξ-conceal source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-source-conceal-only c⊢ present mark free represented
          related q))
      (extend-path-target-ready path
        (focus-source-conceal-only c⊢ present mark free represented
          related q)
        ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.conceal⊑-only² c⊢ present mark free represented related q)
      path ready (pure-step (id-conceal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.conceal⊑-only² c⊢ present mark free represented related q)
      path ready (pure-step blame-conceal) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related q)
      path ready (ξ-reveal source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-reveal-paired c⊢ c′⊢ positions aligned represented
          related q))
      (extend-path-target-ready path
        (focus-reveal-paired c⊢ c′⊢ positions aligned represented
          related q)
        ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related q)
      path ready (pure-step (id-reveal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related q)
      path ready (pure-step (conceal-reveal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related q)
      path ready (pure-step blame-reveal) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented
        related q)
      path ready (ξ-conceal source-step refl) rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-conceal-paired c⊢ c′⊢ positions aligned represented
          related q))
      (extend-path-target-ready path
        (focus-conceal-paired c⊢ c′⊢ positions aligned represented
          related q)
        ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented
        related q)
      path ready (pure-step (id-conceal source-value)) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented
        related q)
      path ready (pure-step blame-conceal) rebuild = {! !}

  contextual-sim no-open root-related
      (CTI.⊑reveal-rebase² c′⊢ rebase related q) path ready
      source-step rebuild =
    whole-target-reveal-rebase-closing no-open root-related c′⊢ rebase
      related q related
      (extend-focus path
        (focus-target-reveal-rebase c′⊢ rebase related q))
      (select-appended-reveal path) source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  contextual-sim no-open root-related
      (CTI.⊑conceal-rebase² c′⊢ rebase related q) path ready
      source-step rebuild =
    contextual-sim no-open root-related related
      (extend-focus path
        (focus-target-conceal-rebase c′⊢ rebase related q))
      (extend-path-target-ready path
        (focus-target-conceal-rebase c′⊢ rebase related q) ready _)
      source-step (extend-rebuild rebuild (rebuild-edge refl))

  contextual-sim no-open root-related (CTI.blame⊑² target⊢ p) path ready
      (pure-step ()) rebuild

  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (ξ-⊕₁ left-step refl) rebuild =
    contextual-sim no-open root-related left-related
      (extend-focus path (focus-⊕₁ left-related right-related r))
      (extend-path-target-ready path
        (focus-⊕₁ left-related right-related r) ready _)
      left-step (extend-rebuild rebuild (rebuild-edge refl))
  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (ξ-⊕₂ {χ = χᴸ} left-value right-step refl) rebuild
      with contextual-catchup no-open root-related left-related
        (extend-focus path (focus-⊕₁ left-related right-related r))
        (extend-path-target-ready path
          (focus-⊕₁ left-related right-related r) ready _)
        left-value
  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (ξ-⊕₂ {χ = χᴸ} left-value right-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , left-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , left-type₁ , root-steps₁ , target-value , evolution₁ ,
      root-related₁ , left-related₁ , left-path₁ , path-evolution
      with split-target-extended-path path-evolution
  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (ξ-⊕₂ {χ = χᴸ} left-value right-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , left-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , left-type₁ , root-steps₁ , target-value , evolution₁ ,
      root-related₁ , left-related₁ , left-path₁ , path-evolution
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution edge-evolution
      with primitive-left-edge-view edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution))
  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (ξ-⊕₂ {χ = χᴸ} left-value right-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , left-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , left-type₁ , root-steps₁ , target-value , evolution₁ ,
      root-related₁ , left-related₁ , left-path₁ , path-evolution
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution edge-evolution
    | primitive-left-edge left-related₂ right-related₂ result-related₂
        refl left-focus-eq
      with contextual-sim
        (multi-no-open-frames evolution₁ no-open) root-related₁
        right-related₂
        (extend-focus prefix₁
          (focus-⊕₂ left-related₂ right-related₂ result-related₂
            (subst Value (cong sourceTerm left-focus-eq) left-value)))
        (extend-path-target-ready prefix₁
          (focus-⊕₂ left-related₂ right-related₂ result-related₂
            (subst Value (cong sourceTerm left-focus-eq) left-value))
          (target-path-ready prefix-evolution)
          (subst Value (cong targetTerm left-focus-eq) target-value))
        right-step
        (extend-rebuild (transport-rebuild prefix-evolution rebuild)
          (rebuild-edge
            (cong (λ K → applyTerm χᴸ K ⊕[ op ] _)
              (cong sourceTerm left-focus-eq))))
  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (ξ-⊕₂ {χ = χᴸ} left-value right-step refl) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , left-target₁ , γ₁ , γᶠ₁ ,
      root-type₁ , left-type₁ , root-steps₁ , target-value , evolution₁ ,
      root-related₁ , left-related₁ , left-path₁ , path-evolution
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution edge-evolution
    | primitive-left-edge left-related₂ right-related₂ result-related₂
        refl left-focus-eq
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , γ₂ , result-type₂ ,
      root-steps₂ , evolution₂ , root-related₂ =
    let
      target-type-eq = applyTys-++ χsᴿ₁ χsᴿ₂ _
      normalized-result =
        subst
          (λ T →
            Σ[ q ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ CTI.⊢² _ ⊑ root-target₂ ∶ q)
          target-type-eq (result-type₂ , root-related₂)
      final-type = proj₁ normalized-result
      final-related = proj₂ normalized-result
    in
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , root-target₂ , γ₂ , final-type ,
      (targetTerm (pack root-related)
         —↠+[ χsᴿ₁ ]⟨ root-steps₁ ⟩
       root-target₁
         —↠[ χsᴿ₂ ]⟨ root-steps₂ ⟩
       root-target₂ ∎[]) ,
      composeMultiWorldEvolution evolution₁ evolution₂ ,
      final-related

  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step))
      rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (pure-step blame-⊕₁) rebuild = {! !}
  contextual-sim no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path ready
      (pure-step (blame-⊕₂ left-value)) rebuild = {! !}
