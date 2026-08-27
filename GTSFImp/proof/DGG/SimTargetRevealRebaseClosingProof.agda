{-# OPTIONS --safe #-}

module proof.DGG.SimTargetRevealRebaseClosingProof where

-- File Charter:
--   * Develops target-reveal/rebase closing by recursion on a focused CTI
--     node and source step under the canonical CTI evaluation-context zipper.
--   * Installs the recursive call in every contextual case before discharging
--     any dynamic root case.
--   * Is parameterized by canonical CTI transport and target-value catch-up;
--     it carries no parallel source-rebase stack.

open import Reduction
open import Data.List using ([])
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; subst; sym; trans)
open import CastTerms using (Term; ⟨_,_,_⟩; _↑_)
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
import Conversion as Conv
open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecisionTyping using (target-typing)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; generator-here)
open import proof.DGG.Catchup.MorePreciseTargetRevealRebaseCatchupDef using
  (MorePreciseTargetRevealRebaseCatchupᵀ)
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World using (_⊑ᶜ_; _⊑ᵀ⟨_⟩_)
open import proof.Reduction using
  (renamedConceal-term; renamedReveal-term)
open import proof.DGG.WorldEvolutionSequence using
  ( append-left-keep
  ; evolutions-refl
  ; multi-aligned
  ; multi-source-conceal
  ; multi-source-conceal-position
  ; multi-source-disaligned
  ; multi-source-mark
  ; multi-source-reveal
  ; multi-source-reveal-position
  ; multi-target-conceal
  ; multi-target-conceal-position
  ; multi-target-reveal
  ; multi-target-reveal-position
  ; multi-⊑ᵀ
  ; MultiWorldEvolution
  )
import proof.Imprecision as PI


generator-here≠absent : generator-here ≢ generator-absent
generator-here≠absent ()


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-target-reveal-rebase :
      MorePreciseTargetRevealRebaseCatchupᵀ)
  where

  replay-edge-keep : ∀
      {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
      {Σᴸᶠ : TyStore Δᴸ} {Σᴿᶠ : TyStore Δᴿ}
      {Γᴸᶠ : TermCtx Δᴸ} {Γᴿᶠ : TermCtx Δᴿ}
      {γᶠ : ⟨ Δᴸ , Σᴸᶠ , Γᴸᶠ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿᶠ , Γᴿᶠ ⟩}
      {L : Term Δᴸ} {L′ : Term Δᴿ}
      {C : Ty Δᴸ} {D : Ty Δᴿ} {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
    → (outer-related : γ CTI.⊢² M ⊑ M′ ∶ p)
    → (inner-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
    → (edge : pack outer-related ↘ᶜ pack inner-related)
    → ∀ {P N : Term Δᴸ}
    → γᶠ CTI.⊢² P ⊑ L′ ∶ s
    → RebuildSourceEdge edge keep P N
    → γ CTI.⊢² N ⊑ M′ ∶ p

  replay-edge-keep
      (CTI.·⊑·² function-related argument-related)
      .function-related
      (focus-·₁ .function-related .argument-related)
      related′ (rebuild-edge refl) =
    CTI.·⊑·² related′ argument-related
  replay-edge-keep
      (CTI.·⊑·² function-related argument-related)
      .argument-related
      (focus-·₂ .function-related .argument-related source-value)
      related′ (rebuild-edge refl) =
    CTI.·⊑·² function-related related′
  replay-edge-keep
      (CTI.⊕⊑⊕² op left-related right-related r)
      .left-related
      (focus-⊕₁ .left-related .right-related .r)
      related′ (rebuild-edge refl) =
    CTI.⊕⊑⊕² op related′ right-related r
  replay-edge-keep
      (CTI.⊕⊑⊕² op left-related right-related r)
      .right-related
      (focus-⊕₂ .left-related .right-related .r source-value)
      related′ (rebuild-edge refl) =
    CTI.⊕⊑⊕² op left-related related′ r
  replay-edge-keep
      (CTI.•⊑•² p∀ related q r) .related
      (focus-•-paired .p∀ .related .q .r)
      related′ (rebuild-edge refl) =
    CTI.•⊑•² p∀ related′ q r
  replay-edge-keep
      (CTI.•⊑² p∀ related q r) .related
      (focus-•-source .p∀ .related .q .r)
      related′ (rebuild-edge refl) =
    CTI.•⊑² p∀ related′ q r
  replay-edge-keep
      (CTI.cast⊑cast² source-cast target-cast related q) .related
      (focus-cast-paired .source-cast .target-cast .related .q)
      related′ (rebuild-edge refl) =
    CTI.cast⊑cast² source-cast target-cast related′ q
  replay-edge-keep
      (CTI.⊑cast² target-cast related q) .related
      (focus-cast-target .target-cast .related .q)
      related′ (rebuild-edge refl) =
    CTI.⊑cast² target-cast related′ q
  replay-edge-keep
      (CTI.cast⊑² source-cast related q) .related
      (focus-cast-source .source-cast .related .q)
      related′ (rebuild-edge refl) =
    CTI.cast⊑² source-cast related′ q
  replay-edge-keep
      (CTI.⊑reveal-identity target-reveal absent related q) .related
      (focus-target-reveal-identity .target-reveal .absent .related .q)
      related′ (rebuild-edge refl) =
    CTI.⊑reveal-identity target-reveal absent related′ q
  replay-edge-keep
      (CTI.⊑conceal-identity target-conceal absent related q) .related
      (focus-target-conceal-identity .target-conceal .absent .related .q)
      related′ (rebuild-edge refl) =
    CTI.⊑conceal-identity target-conceal absent related′ q
  replay-edge-keep {γ = γ} {M′ = M′}
      (CTI.reveal⊑-identity {c = c} source-reveal absent related q) .related
      (focus-source-reveal-identity .source-reveal .absent .related .q)
      related′ (rebuild-edge refl) =
    let evolution = append-left-keep {W = γ} evolutions-refl
        source-reveal′ = multi-source-reveal evolution source-reveal
    in
      subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑-identity {γ = γ} source-reveal′
          (trans (multi-source-reveal-position evolution source-reveal)
            absent)
          related′ (multi-⊑ᵀ evolution q))
  replay-edge-keep {γ = γ} {M′ = M′}
      (CTI.conceal⊑-identity {c = c} source-conceal absent related q) .related
      (focus-source-conceal-identity .source-conceal .absent .related .q)
      related′ (rebuild-edge refl) =
    let evolution = append-left-keep {W = γ} evolutions-refl
        source-conceal′ = multi-source-conceal evolution source-conceal
    in
      subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑-identity {γ = γ} source-conceal′
          (trans (multi-source-conceal-position evolution source-conceal)
            absent)
          related′ (multi-⊑ᵀ evolution q))
  replay-edge-keep {γ = γ} {M′ = M′}
      (CTI.reveal⊑-only² {c = c} source-reveal present mark free represented
        related q)
      .related
      (focus-source-reveal-only .source-reveal .present .mark .free
        .represented .related .q)
      related′ (rebuild-edge refl) =
    let evolution = append-left-keep {W = γ} evolutions-refl
        source-reveal′ = multi-source-reveal evolution source-reveal
        position = multi-source-reveal-position evolution source-reveal
    in
      subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑-only² {γ = γ} source-reveal′
          (λ absent → present (trans (sym position) absent))
          (multi-source-mark evolution mark)
          (multi-source-disaligned evolution free)
          (multi-⊑ᵀ evolution represented)
          related′ (multi-⊑ᵀ evolution q))
  replay-edge-keep {γ = γ} {M′ = M′}
      (CTI.conceal⊑-only² {c = c} source-conceal present mark free represented
        related q)
      .related
      (focus-source-conceal-only .source-conceal .present .mark .free
        .represented .related .q)
      related′ (rebuild-edge refl) =
    let evolution = append-left-keep {W = γ} evolutions-refl
        source-conceal′ = multi-source-conceal evolution source-conceal
        position = multi-source-conceal-position evolution source-conceal
    in
      subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑-only² {γ = γ} source-conceal′
          (λ absent → present (trans (sym position) absent))
          (multi-source-mark evolution mark)
          (multi-source-disaligned evolution free)
          (multi-⊑ᵀ evolution represented)
          related′ (multi-⊑ᵀ evolution q))
  replay-edge-keep {γ = γ} {M′ = M′}
      (CTI.reveal⊑reveal² {c = c} source-reveal target-reveal positions aligned
        represented related q)
      .related
      (focus-reveal-paired .source-reveal .target-reveal .positions .aligned
        .represented .related .q)
      related′ (rebuild-edge refl) =
    let evolution = append-left-keep {W = γ} evolutions-refl
        source-reveal′ = multi-source-reveal evolution source-reveal
    in
      subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
        (sym (renamedReveal-term _ c))
        (CTI.reveal⊑reveal² {γ = γ} source-reveal′ target-reveal
          (trans (multi-source-reveal-position evolution source-reveal)
            positions)
          (multi-aligned evolution aligned)
          (multi-⊑ᵀ evolution represented)
          related′ (multi-⊑ᵀ evolution q))
  replay-edge-keep {γ = γ} {M′ = M′}
      (CTI.conceal⊑conceal² {c = c} source-conceal target-conceal
        positions aligned represented related q)
      .related
      (focus-conceal-paired .source-conceal .target-conceal .positions
        .aligned .represented .related .q)
      related′ (rebuild-edge refl) =
    let evolution = append-left-keep {W = γ} evolutions-refl
        source-conceal′ = multi-source-conceal evolution source-conceal
    in
      subst (λ K → γ CTI.⊢² K ⊑ M′ ∶ q)
        (sym (renamedConceal-term _ c))
        (CTI.conceal⊑conceal² {γ = γ} source-conceal′ target-conceal
          (trans (multi-source-conceal-position evolution source-conceal)
            positions)
          (multi-aligned evolution aligned)
          (multi-⊑ᵀ evolution represented)
          related′ (multi-⊑ᵀ evolution q))
  replay-edge-keep
      (CTI.⊑reveal-rebase² target-reveal rebase related q) .related
      (focus-target-reveal-rebase .target-reveal .rebase .related .q)
      related′ (rebuild-edge refl) =
    CTI.⊑reveal-rebase² target-reveal rebase related′ q
  replay-edge-keep
      (CTI.⊑conceal-rebase² target-conceal rebase related q) .related
      (focus-target-conceal-rebase .target-conceal .rebase .related .q)
      related′ (rebuild-edge refl) =
    CTI.⊑conceal-rebase² target-conceal rebase related′ q

  replay-context-keep : ∀
      {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
      {Σᴸᶠ : TyStore Δᴸ} {Σᴿᶠ : TyStore Δᴿ}
      {Γᴸᶠ : TermCtx Δᴸ} {Γᴿᶠ : TermCtx Δᴿ}
      {γᶠ : ⟨ Δᴸ , Σᴸᶠ , Γᴸᶠ ⟩ ⊑ᶜ
        ⟨ Δᴿ , Σᴿᶠ , Γᴿᶠ ⟩}
      {L : Term Δᴸ} {L′ : Term Δᴿ}
      {C : Ty Δᴸ} {D : Ty Δᴿ} {s : C ⊑ᵀ⟨ γᶠ ⟩ D}
    → (outer-related : γ CTI.⊢² M ⊑ M′ ∶ p)
    → (focus-related : γᶠ CTI.⊢² L ⊑ L′ ∶ s)
    → (path : pack outer-related ↘ᶜ* pack focus-related)
    → ∀ {P N : Term Δᴸ}
    → γᶠ CTI.⊢² P ⊑ L′ ∶ s
    → RebuildSource path keep P N
    → γ CTI.⊢² N ⊑ M′ ∶ p
  replay-context-keep related .related focus-here related′
      (rebuild-here refl) = related′
  replay-context-keep outer-related focus-related
      (focus-there {middle = pack middle-related} edge tail) related′
      (rebuild-there tail-rebuild edge-rebuild) =
    replay-edge-keep outer-related middle-related edge
      (replay-context-keep middle-related focus-related tail related′
        tail-rebuild)
      edge-rebuild

  close-root-keep : ∀
      {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ γᵖ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {N : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {c′ : Conv↑ Δᴿ B B′}
    → (c′⊢ : Σᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
    → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    → γᵖ CTI.⊢² N ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ r ∈ applyTy keep A ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
        (M′ ↑ c′ —↠[ χsᴿ ] N′)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (keep ∷ []) χsᴿ
        × (γ′ CTI.⊢² N ⊑ N′ ∶ r)
  close-root-keep {Δᴿ = Δᴿ} {Σᴿ = Σᴿ} {γ = γ} {M′ = M′} {c′ = c′}
      c′⊢ rebase related q =
    Δᴿ , Σᴿ , [] , M′ ↑ c′ , γ , q ,
    (M′ ↑ c′ ∎[]) , append-left-keep {W = γ} evolutions-refl ,
    CTI.⊑reveal-rebase² c′⊢ rebase related q

  contextual-target-reveal-rebase-closing :
    ContextualTargetRevealRebaseClosingᵀ

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.x⊑x² source∋ target∋) path (pure-step ()) rebuild

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.ƛ⊑ƛ² related) path (pure-step ()) rebuild

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (ξ-·₁ function-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q function-related
      (extend-focus path (focus-·₁ function-related argument-related))
      function-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ function-value argument-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q argument-related
      (extend-focus path
        (focus-·₂ function-related argument-related function-value))
      argument-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β argument-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β-⇒ function-value argument-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β-reveal-⇒ function-value argument-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β-conceal-⇒ function-value argument-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.·⊑·² {pB = result-related}
        function-related argument-related) path
      (pure-step blame-·₁) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.·⊑·² {pB = result-related}
        function-related argument-related) path
      (pure-step (blame-·₂ source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.Λ⊑Λ² source-value target-value related s) path
      (pure-step ()) rebuild

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.Λ⊑² nonvar occurs source-value target⊢ related s) path
      (pure-step ()) rebuild

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (ξ-• source-step refl refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-•-paired p∀ related type-related result-related))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (pure-step (β-∀ source-value instantiated)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.•⊑•² p∀ related type-related result-related) path
      (pure-step blame-•) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-Λ source-value) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-gen source-value source≢★ safe) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-reveal-∀ source-value) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-conceal-∀ source-value) rebuild = {!!}

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (ξ-• source-step refl refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-•-source p∀ related type-related result-related))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (pure-step (β-∀ source-value instantiated)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.•⊑² p∀ related type-related result-related) path
      (pure-step blame-•) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-Λ source-value) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-gen source-value source≢★ safe) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-reveal-∀ source-value) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-conceal-∀ source-value) rebuild = {!!}

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.κ⊑κ² constant s) path (pure-step ()) rebuild

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (ξ-⟨⟩ source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-cast-paired source-cast target-cast related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (β-id source-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (ground source-value unequal)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (expand source-value unequal)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (tag-untag source-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (tag-untag-bad source-value unequal)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (blame-bot-intro source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step blame-⟨⟩) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (β-inst source-value source≢★) rebuild = {!!}

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑cast² target-cast related s) path source-step rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path (focus-cast-target target-cast related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (ξ-⟨⟩ source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path (focus-cast-source source-cast related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (pure-step (β-id source-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (pure-step (ground source-value unequal)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (pure-step (expand source-value unequal)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (pure-step (tag-untag source-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑² source-cast related s) path
      (pure-step (tag-untag-bad source-value unequal)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑² source-cast related s) path
      (pure-step (blame-bot-intro source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑² source-cast related s) path
      (pure-step blame-⟨⟩) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (β-inst source-value source≢★) rebuild = {!!}

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑reveal-identity c⊢ absent related s) path
      source-step rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-reveal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑conceal-identity c⊢ absent related s) path
      source-step rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-conceal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-identity c⊢ absent related s) path
      (ξ-reveal source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-reveal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑-identity {p = inner-type}
        c⊢ absent related s) path
      (pure-step (id-reveal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r)
          (PI.⊑-unique inner-type s) related)
        rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-identity (Conv.⊢↑-unseal member) absent related s)
      path (pure-step (conceal-reveal source-value)) rebuild =
    ⊥-elim (generator-here≠absent absent)
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑-identity c⊢ absent related s) path
      (pure-step blame-reveal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (ξ-reveal source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-reveal-only c⊢ present mark free represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-var member X≠Y) present mark free represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    ⊥-elim (present refl)
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-base member) present mark free represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    ⊥-elim (present refl)
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-star member) present mark free represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    ⊥-elim (present refl)
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (pure-step (conceal-reveal source-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑-only²
        c⊢ present mark free represented related s) path
      (pure-step blame-reveal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-identity c⊢ absent related s) path
      (ξ-conceal source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-conceal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑-identity {p = inner-type}
        c⊢ absent related s) path
      (pure-step (id-conceal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r)
          (PI.⊑-unique inner-type s) related)
        rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑-identity c⊢ absent related s) path
      (pure-step blame-conceal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only² c⊢ present mark free represented related s) path
      (ξ-conceal source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-conceal-only c⊢ present mark free represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-var member X≠Y) present mark free represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    ⊥-elim (present refl)
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-base member) present mark free represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    ⊥-elim (present refl)
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-star member) present mark free represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    ⊥-elim (present refl)
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑-only²
        c⊢ present mark free represented related s) path
      (pure-step blame-conceal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (ξ-reveal source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-reveal-paired c⊢ c′⊢ positions aligned represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        (Conv.⊢↑-id-var member X≠Y) c′⊢ positions aligned represented
        related s)
      path (pure-step (id-reveal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑reveal-identity c′⊢ (sym positions) related s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        (Conv.⊢↑-id-base member) c′⊢ positions aligned represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑reveal-identity c′⊢ (sym positions) related s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        (Conv.⊢↑-id-star member) c′⊢ positions aligned represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑reveal-identity c′⊢ (sym positions) related s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (pure-step (conceal-reveal source-value)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related s)
      path (pure-step blame-reveal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented related s)
      path (ξ-conceal source-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-conceal-paired c⊢ c′⊢ positions aligned represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        (Conv.⊢↓-id-var member X≠Y) c′⊢ positions aligned represented
        related s)
      path (pure-step (id-conceal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑conceal-identity c′⊢ (sym positions) related s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        (Conv.⊢↓-id-base member) c′⊢ positions aligned represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑conceal-identity c′⊢ (sym positions) related s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        (Conv.⊢↓-id-star member) c′⊢ positions aligned represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑conceal-identity c′⊢ (sym positions) related s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented related s)
      path (pure-step blame-conceal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑reveal-rebase² c⊢ nested-rebase related s) path
      source-step rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-reveal-rebase c⊢ nested-rebase related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑conceal-rebase² c⊢ nested-rebase related s) path
      source-step rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-conceal-rebase c⊢ nested-rebase related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.blame⊑² target⊢ s) path (pure-step ()) rebuild

  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (ξ-⊕₁ left-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q left-related
      (extend-focus path (focus-⊕₁ left-related right-related s))
      left-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (ξ-⊕₂ left-value right-step refl) rebuild =
    contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q right-related
      (extend-focus path
        (focus-⊕₂ left-related right-related s left-value))
      right-step
      (extend-rebuild rebuild (rebuild-edge refl))
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step (δ-⊕ primitive-step)) rebuild = {!!}
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step blame-⊕₁) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  contextual-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step (blame-⊕₂ source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q


  sim-target-reveal-rebase-closing : SimTargetRevealRebaseClosingᵀ
  sim-target-reveal-rebase-closing =
    contextual-closing-adapter contextual-target-reveal-rebase-closing
