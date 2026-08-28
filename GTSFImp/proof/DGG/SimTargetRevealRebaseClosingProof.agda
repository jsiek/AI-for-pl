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
import Data.Nat as Nat
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; subst; sym; trans)
open import CastTerms using
  ( Term; Value; ⟨_,_,_⟩; _·_; Λ_; _⦂∀_[_]; _《_》; _↑_; _↓_
  ; fun; all; genᵥ
  )
open import Conversion using (Conv↑; _⊢↑[_⦂_]_)
import Conversion as Conv
open import Imprecision using (⇒⊑⇒)
open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx; TyVar; ★; `∀; _[_]ᵗ)
open import TyStore using (TyStore)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecisionTyping using (target-typing)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; generator-here)
open import proof.DGG.Catchup.MorePreciseTargetRevealRebaseCatchupDef using
  (MorePreciseTargetRevealRebaseCatchupᵀ)
open import
  proof.DGG.Catchup.MorePreciseTargetRevealRebaseContextCatchupDef using
  (MorePreciseTargetRevealRebaseContextCatchupᵀ)
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.SimTargetRevealRebaseContextPairedAllValuesDef using
  (SimTargetRevealRebaseContextPairedAllValuesᵀ)
open import proof.DGG.SimTargetRevealRebaseContextPairedFunValuesDef using
  (SimTargetRevealRebaseContextPairedFunValuesᵀ)
open import proof.DGG.SimTargetRevealRebaseContextPrimitiveValuesDef using
  (SimTargetRevealRebaseContextPrimitiveValuesᵀ)
open import proof.DGG.SimTargetRevealRebaseContextSourceAllValuesDef using
  (SimTargetRevealRebaseContextSourceAllValuesᵀ)
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.SourceRebase using (SourceRebaseᶜ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World using
  (openFramesᶜ; _⊑ᶜ_; _⊑ᵀ⟨_⟩_)
open import proof.Reduction using
  (_++χ_; _—↠+[_]⟨_⟩_; applyReveals; applyTys-++;
  renamedConceal-term; renamedReveal-term)
open import proof.DGG.WorldEvolutionSequence using
  ( append-left-keep
  ; composeMultiWorldEvolution
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
  ; multi-no-open-frames
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
    (catchup-target-reveal-rebase-context :
      MorePreciseTargetRevealRebaseContextCatchupᵀ)
    (sim-context-paired-all-values :
      SimTargetRevealRebaseContextPairedAllValuesᵀ)
    (sim-context-paired-fun-values :
      SimTargetRevealRebaseContextPairedFunValuesᵀ)
    (sim-context-primitive-values :
      SimTargetRevealRebaseContextPrimitiveValuesᵀ)
    (sim-context-source-all-values :
      SimTargetRevealRebaseContextSourceAllValuesᵀ)
  where

  replay-edge-keep : ∀
      {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
      {γᶠ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
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
      {γᶠ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
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

  close-context-application : ∀
      {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ γᵖ γᶠ :
        ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {root-source root-result focus-result : Term Δᴸ}
      {root-target L′ M′ : Term Δᴿ}
      {root-source-type : Ty Δᴸ}
      {root-target-type revealed-target-type : Ty Δᴿ}
      {representation : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {target-reveal : Conv↑ Δᴿ root-target-type revealed-target-type}
      {L M : Term Δᴸ}
      {argument-type result-type : Ty Δᴸ}
      {argument-type′ result-type′ : Ty Δᴿ}
      {argument-related : argument-type ⊑ᵀ⟨ γᶠ ⟩ argument-type′}
      {result-related : result-type ⊑ᵀ⟨ γᶠ ⟩ result-type′}
    → openFramesᶜ γ ≡ []
    → (target-reveal⊢ :
        Σᴿ ⊢↑[ Xᴿ ⦂ representation ] target-reveal)
    → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
    → {root-related-type :
        root-source-type ⊑ᵀ⟨ γᵖ ⟩ root-target-type}
    → (root-related :
        γᵖ CTI.⊢² root-source ⊑ root-target ∶ root-related-type)
    → (revealed-related :
        root-source-type ⊑ᵀ⟨ γ ⟩ revealed-target-type)
    → (function-related :
        γᶠ CTI.⊢² L ⊑ L′ ∶
          ⇒⊑⇒ argument-related result-related)
    → (argument-related-term :
        γᶠ CTI.⊢² M ⊑ M′ ∶ argument-related)
    → (path : pack root-related ↘ᶜ*
        pack (CTI.·⊑·² function-related argument-related-term))
    → Value L
    → Value M
    → L · M —→ focus-result
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
          applyTys χsᴿ revealed-target-type ]
        (root-target ↑ target-reveal —↠[ χsᴿ ] result-target)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (keep ∷ []) χsᴿ
        × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)

  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
      with catchup-target-reveal-rebase-context
        no-open target-reveal⊢ rebase root-related revealed-related
        function-related
        (extend-focus path
          (focus-·₁ function-related argument-related-term))
        source-function-value
  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
      with split-target-extended-path path-evolution₁
  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
      with application-left-edge-view edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₁))
  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
      with catchup-target-reveal-rebase-context
        (multi-no-open-frames evolution₁ no-open)
        (multi-target-reveal evolution₁ target-reveal⊢)
        rebase₁ root-related₁ (multi-⊑ᵀ evolution₁ revealed-related)
        argument-related₁
        (extend-focus prefix₁
          (focus-·₂ function-related₂ argument-related₁
            (subst Value (cong sourceTerm function-focus-eq₁)
              source-function-value)))
        source-argument-value
  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
      with split-target-extended-path path-evolution₂
  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
      with application-right-edge-view edge₂
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₂))
        (TargetEdgeEvolution.target-edge-ready edge-evolution₂)
  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
      with cong sourceTerm function-focus-eq₁
         | cong sourceTerm argument-focus-eq₂
         | cong targetTerm argument-focus-eq₂
  close-context-application
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
    | refl | refl | refl
      with sim-context-paired-fun-values
        (multi-no-open-frames evolution₂
          (multi-no-open-frames evolution₁ no-open))
        (multi-target-reveal evolution₂
          (multi-target-reveal evolution₁ target-reveal⊢))
        rebase₂ root-related₂
        (multi-⊑ᵀ evolution₂ (multi-⊑ᵀ evolution₁ revealed-related))
        function-related₃ argument-related₃ prefix₂
        (target-path-ready
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂))
        source-function-value₃ source-argument-value
        target-function-value₃ target-argument-value₂ source-root-step
        (transport-rebuild
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂)
          rebuild)
  close-context-application {target-reveal = target-reveal}
      no-open target-reveal⊢ rebase root-related revealed-related
      function-related argument-related-term path source-function-value
      source-argument-value source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
    | refl | refl | refl
    | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result-target , γ₃ , result-related₃ ,
      values-steps , values-evolution , result-relation =
    let
      target-type-eq =
        trans
          (applyTys-++ χsᴿ₂ χsᴿ₃ (applyTys χsᴿ₁ _))
          (applyTys-++ χsᴿ₁ (χsᴿ₂ ++χ χsᴿ₃) _)
      normalized-result =
        subst
          (λ T →
            Σ[ r ∈ _ ⊑ᵀ⟨ γ₃ ⟩ T ]
              γ₃ CTI.⊢² _ ⊑ result-target ∶ r)
          target-type-eq (result-related₃ , result-relation)
      final-related = proj₁ normalized-result
      final-relation = proj₂ normalized-result
    in
      Δᴿ₃ , Σᴿ₃ , χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃) , result-target , γ₃ ,
      final-related ,
      (targetTerm (pack root-related) ↑ target-reveal
         —↠+[ χsᴿ₁ ]⟨ function-steps₁ ⟩
       root-target₁ ↑ applyReveals χsᴿ₁ target-reveal
         —↠+[ χsᴿ₂ ]⟨ argument-steps₂ ⟩
       root-target₂ ↑
         applyReveals χsᴿ₂ (applyReveals χsᴿ₁ target-reveal)
         —↠[ χsᴿ₃ ]⟨ values-steps ⟩
       result-target ∎[]) ,
      composeMultiWorldEvolution evolution₁
        (composeMultiWorldEvolution evolution₂ values-evolution) ,
      final-relation

  close-context-paired-all : ∀
      {Δᴸ Δᴿ Δᴸ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ γᵖ γᶠ :
        ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {root-source : Term Δᴸ}
      {root-result focus-result : Term Δᴸ′}
      {root-target target-head : Term Δᴿ}
      {root-source-type : Ty Δᴸ}
      {root-target-type revealed-target-type : Ty Δᴿ}
      {representation : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {target-reveal : Conv↑ Δᴿ root-target-type revealed-target-type}
      {source-head : Term Δᴸ}
      {source-body : Ty (Nat.suc Δᴸ)}
      {source-argument : Ty Δᴸ}
      {target-body : Ty (Nat.suc Δᴿ)}
      {target-argument : Ty Δᴿ}
      {universal-related :
        `∀ source-body ⊑ᵀ⟨ γᶠ ⟩ `∀ target-body}
    → openFramesᶜ γ ≡ []
    → (target-reveal⊢ :
        Σᴿ ⊢↑[ Xᴿ ⦂ representation ] target-reveal)
    → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
    → {root-related-type :
        root-source-type ⊑ᵀ⟨ γᵖ ⟩ root-target-type}
    → (root-related :
        γᵖ CTI.⊢² root-source ⊑ root-target ∶ root-related-type)
    → (revealed-related :
        root-source-type ⊑ᵀ⟨ γ ⟩ revealed-target-type)
    → (head-related :
        γᶠ CTI.⊢² source-head ⊑ target-head ∶ universal-related)
    → (argument-related :
        source-argument ⊑ᵀ⟨ γᶠ ⟩ target-argument)
    → (result-related :
        source-body [ source-argument ]ᵗ ⊑ᵀ⟨ γᶠ ⟩
          target-body [ target-argument ]ᵗ)
    → (path : pack root-related ↘ᶜ*
        pack (CTI.•⊑•² universal-related head-related
          argument-related result-related))
    → Value source-head
    → source-head ⦂∀ source-body [ source-argument ]
        —→[ χᴸ ] focus-result
    → RebuildSource path χᴸ focus-result root-result
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ result-target ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ final-related ∈
        applyTy χᴸ root-source-type ⊑ᵀ⟨ γ′ ⟩
          applyTys χsᴿ revealed-target-type ]
        (root-target ↑ target-reveal —↠[ χsᴿ ] result-target)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (χᴸ ∷ []) χsᴿ
        × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)

  close-context-paired-all {universal-related = universal-related}
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
      with catchup-target-reveal-rebase-context
        no-open target-reveal⊢ rebase root-related revealed-related
        head-related
        (extend-focus path
          (focus-•-paired universal-related head-related
            argument-related result-related))
        source-value
  close-context-paired-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
      with split-target-extended-path path-evolution₁
  close-context-paired-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
      with paired-type-application-edge-view edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₁))
  close-context-paired-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | paired-type-application-edge universal-related₁ head-related₂
        argument-related₁ result-related₁ refl head-focus-eq₁
      with cong sourceTerm head-focus-eq₁
         | cong targetTerm head-focus-eq₁
  close-context-paired-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | paired-type-application-edge universal-related₁ head-related₂
        argument-related₁ result-related₁ refl head-focus-eq₁
    | refl | refl
      with sim-context-paired-all-values
        (multi-no-open-frames evolution₁ no-open)
        (multi-target-reveal evolution₁ target-reveal⊢)
        rebase₁ root-related₁ (multi-⊑ᵀ evolution₁ revealed-related)
        head-related₂ argument-related₁ result-related₁ prefix₁
        (target-path-ready prefix-evolution₁)
        source-value target-head-value₁ source-root-step
        (transport-rebuild prefix-evolution₁ rebuild)
  close-context-paired-all {target-reveal = target-reveal}
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | paired-type-application-edge universal-related₁ head-related₂
        argument-related₁ result-related₁ refl head-focus-eq₁
    | refl | refl
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result-target , γ₂ , result-related₂ ,
      values-steps , values-evolution , result-relation =
    let
      target-type-eq = applyTys-++ χsᴿ₁ χsᴿ₂ _
      normalized-result =
        subst
          (λ T →
            Σ[ r ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ CTI.⊢² _ ⊑ result-target ∶ r)
          target-type-eq (result-related₂ , result-relation)
      final-related = proj₁ normalized-result
      final-relation = proj₂ normalized-result
    in
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , result-target , γ₂ ,
      final-related ,
      (targetTerm (pack root-related) ↑ target-reveal
         —↠+[ χsᴿ₁ ]⟨ head-steps₁ ⟩
       root-target₁ ↑ applyReveals χsᴿ₁ target-reveal
         —↠[ χsᴿ₂ ]⟨ values-steps ⟩
       result-target ∎[]) ,
      composeMultiWorldEvolution evolution₁ values-evolution ,
      final-relation

  close-context-source-all : ∀
      {Δᴸ Δᴿ Δᴸ′ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ γᵖ γᶠ :
        ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {χᴸ : StoreChange Δᴸ Δᴸ′}
      {root-source : Term Δᴸ}
      {root-result focus-result : Term Δᴸ′}
      {root-target target-head : Term Δᴿ}
      {root-source-type : Ty Δᴸ}
      {root-target-type revealed-target-type : Ty Δᴿ}
      {representation : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {target-reveal : Conv↑ Δᴿ root-target-type revealed-target-type}
      {source-head : Term Δᴸ}
      {source-body : Ty (Nat.suc Δᴸ)}
      {source-argument : Ty Δᴸ} {target-type : Ty Δᴿ}
      {universal-related : `∀ source-body ⊑ᵀ⟨ γᶠ ⟩ target-type}
    → openFramesᶜ γ ≡ []
    → (target-reveal⊢ :
        Σᴿ ⊢↑[ Xᴿ ⦂ representation ] target-reveal)
    → (rebase : SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ)
    → {root-related-type :
        root-source-type ⊑ᵀ⟨ γᵖ ⟩ root-target-type}
    → (root-related :
        γᵖ CTI.⊢² root-source ⊑ root-target ∶ root-related-type)
    → (revealed-related :
        root-source-type ⊑ᵀ⟨ γ ⟩ revealed-target-type)
    → (head-related :
        γᶠ CTI.⊢² source-head ⊑ target-head ∶ universal-related)
    → (argument-related : source-argument ⊑ᵀ⟨ γᶠ ⟩ ★)
    → (result-related :
        source-body [ source-argument ]ᵗ ⊑ᵀ⟨ γᶠ ⟩ target-type)
    → (path : pack root-related ↘ᶜ*
        pack (CTI.•⊑² universal-related head-related
          argument-related result-related))
    → Value source-head
    → source-head ⦂∀ source-body [ source-argument ]
        —→[ χᴸ ] focus-result
    → RebuildSource path χᴸ focus-result root-result
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ result-target ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , applyStore χᴸ Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ final-related ∈
        applyTy χᴸ root-source-type ⊑ᵀ⟨ γ′ ⟩
          applyTys χsᴿ revealed-target-type ]
        (root-target ↑ target-reveal —↠[ χsᴿ ] result-target)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (χᴸ ∷ []) χsᴿ
        × (γ′ CTI.⊢² root-result ⊑ result-target ∶ final-related)

  close-context-source-all {universal-related = universal-related}
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
      with catchup-target-reveal-rebase-context
        no-open target-reveal⊢ rebase root-related revealed-related
        head-related
        (extend-focus path
          (focus-•-source universal-related head-related
            argument-related result-related))
        source-value
  close-context-source-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
      with split-target-extended-path path-evolution₁
  close-context-source-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
      with source-type-application-edge-view edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₁))
  close-context-source-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | source-type-application-edge universal-related₁ head-related₂
        argument-related₁ result-related₁ refl head-focus-eq₁
      with cong sourceTerm head-focus-eq₁
         | cong targetTerm head-focus-eq₁
  close-context-source-all
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | source-type-application-edge universal-related₁ head-related₂
        argument-related₁ result-related₁ refl head-focus-eq₁
    | refl | refl
      with sim-context-source-all-values
        (multi-no-open-frames evolution₁ no-open)
        (multi-target-reveal evolution₁ target-reveal⊢)
        rebase₁ root-related₁ (multi-⊑ᵀ evolution₁ revealed-related)
        head-related₂ argument-related₁ result-related₁ prefix₁
        (target-path-ready prefix-evolution₁)
        source-value target-head-value₁ source-root-step
        (transport-rebuild prefix-evolution₁ rebuild)
  close-context-source-all {target-reveal = target-reveal}
      no-open target-reveal⊢ rebase root-related revealed-related
      head-related argument-related result-related path source-value
      source-root-step rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-head₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , head-type₁ , head-steps₁ , target-head-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , head-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack type-application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | source-type-application-edge universal-related₁ head-related₂
        argument-related₁ result-related₁ refl head-focus-eq₁
    | refl | refl
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , result-target , γ₂ , result-related₂ ,
      values-steps , values-evolution , result-relation =
    let
      target-type-eq = applyTys-++ χsᴿ₁ χsᴿ₂ _
      normalized-result =
        subst
          (λ T →
            Σ[ r ∈ _ ⊑ᵀ⟨ γ₂ ⟩ T ]
              γ₂ CTI.⊢² _ ⊑ result-target ∶ r)
          target-type-eq (result-related₂ , result-relation)
      final-related = proj₁ normalized-result
      final-relation = proj₂ normalized-result
    in
      Δᴿ₂ , Σᴿ₂ , χsᴿ₁ ++χ χsᴿ₂ , result-target , γ₂ ,
      final-related ,
      (targetTerm (pack root-related) ↑ target-reveal
         —↠+[ χsᴿ₁ ]⟨ head-steps₁ ⟩
       root-target₁ ↑ applyReveals χsᴿ₁ target-reveal
         —↠[ χsᴿ₂ ]⟨ values-steps ⟩
       result-target ∎[]) ,
      composeMultiWorldEvolution evolution₁ values-evolution ,
      final-relation

  selected-target-reveal-rebase-closing :
    ContextualTargetRevealRebaseClosingᵀ

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.x⊑x² source∋ target∋) path (pure-step ()) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.ƛ⊑ƛ² related) path (pure-step ()) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (ξ-·₁ function-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q function-related
      (extend-focus path (focus-·₁ function-related argument-related))
      function-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (ξ-·₂ function-value argument-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q argument-related
      (extend-focus path
        (focus-·₂ function-related argument-related function-value))
      argument-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
      with catchup-target-reveal-rebase-context
        no-open target-reveal rebase root-related q function-related
        (extend-focus path
          (focus-·₁ function-related argument-related))
        (CastTerms.Value.ƛ body)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
      with split-target-extended-path path-evolution₁
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
      with application-left-edge-view edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₁))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
      with catchup-target-reveal-rebase-context
        (multi-no-open-frames evolution₁ no-open)
        (multi-target-reveal evolution₁ target-reveal)
        rebase₁ root-related₁ (multi-⊑ᵀ evolution₁ q)
        argument-related₁
        (extend-focus prefix₁
          (focus-·₂ function-related₂ argument-related₁
            (subst Value (cong sourceTerm function-focus-eq₁)
              (CastTerms.Value.ƛ body))))
        argument-value
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
      with split-target-extended-path path-evolution₂
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
      with application-right-edge-view edge₂
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₂))
        (TargetEdgeEvolution.target-edge-ready edge-evolution₂)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
      with cong sourceTerm function-focus-eq₁
         | cong sourceTerm argument-focus-eq₂
         | cong targetTerm argument-focus-eq₂
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
    | refl | refl | refl
      with sim-context-paired-fun-values
        (multi-no-open-frames evolution₂
          (multi-no-open-frames evolution₁ no-open))
        (multi-target-reveal evolution₂
          (multi-target-reveal evolution₁ target-reveal))
        rebase₂ root-related₂
        (multi-⊑ᵀ evolution₂ (multi-⊑ᵀ evolution₁ q))
        function-related₃ argument-related₃ prefix₂
        (target-path-ready
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂))
        source-function-value₃ argument-value target-function-value₃
        target-argument-value₂ (β argument-value)
        (transport-rebuild
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂)
          rebuild)
  selected-target-reveal-rebase-closing {c′ = c′}
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β {N = body} argument-value)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-function₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , function-type₁ , function-steps₁ ,
      target-function-value₁ , evolution₁ , rebase₁ , root-related₁ ,
      function-related₁ , path₁ , path-evolution₁
    | evolved-extended-path {middle′ = pack application-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | application-left-edge function-related₂ argument-related₁ refl
        function-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-argument₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , argument-type₂ , argument-steps₂ ,
      target-argument-value₂ , evolution₂ , rebase₂ , root-related₂ ,
      argument-related₂ , path₂ , path-evolution₂
    | evolved-extended-path {middle′ = pack application-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | application-right-edge function-related₃ argument-related₃
        source-function-value₃ target-function-value₃ refl
        argument-focus-eq₂
    | refl | refl | refl
    | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result-target , γ₃ , result-related ,
      values-steps , values-evolution , result-relation =
    let
      target-type-eq =
        trans
          (applyTys-++ χsᴿ₂ χsᴿ₃ (applyTys χsᴿ₁ _))
          (applyTys-++ χsᴿ₁ (χsᴿ₂ ++χ χsᴿ₃) _)
      normalized-result =
        subst
          (λ T →
            Σ[ r ∈ _ ⊑ᵀ⟨ γ₃ ⟩ T ]
              γ₃ CTI.⊢² _ ⊑ result-target ∶ r)
          target-type-eq (result-related , result-relation)
      final-related = proj₁ normalized-result
      final-relation = proj₂ normalized-result
    in
      Δᴿ₃ , Σᴿ₃ , χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃) , result-target , γ₃ ,
      final-related ,
      (targetTerm (pack root-related) ↑ c′
         —↠+[ χsᴿ₁ ]⟨ function-steps₁ ⟩
       root-target₁ ↑ applyReveals χsᴿ₁ c′
         —↠+[ χsᴿ₂ ]⟨ argument-steps₂ ⟩
       root-target₂ ↑
         applyReveals χsᴿ₂ (applyReveals χsᴿ₁ c′)
         —↠[ χsᴿ₃ ]⟨ values-steps ⟩
       result-target ∎[]) ,
      composeMultiWorldEvolution evolution₁
        (composeMultiWorldEvolution evolution₂ values-evolution) ,
      final-relation
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β-⇒ function-value argument-value)) rebuild =
    close-context-application
      no-open target-reveal rebase root-related q
      function-related argument-related path (function-value 《 fun 》)
      argument-value
      (β-⇒ function-value argument-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β-reveal-⇒ function-value argument-value)) rebuild =
    close-context-application
      no-open target-reveal rebase root-related q
      function-related argument-related path (function-value ↑ fun)
      argument-value
      (β-reveal-⇒ function-value argument-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.·⊑·² function-related argument-related) path
      (pure-step (β-conceal-⇒ function-value argument-value)) rebuild =
    close-context-application
      no-open target-reveal rebase root-related q
      function-related argument-related path (function-value ↓ fun)
      argument-value
      (β-conceal-⇒ function-value argument-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.·⊑·² {pB = result-related}
        function-related argument-related) path
      (pure-step blame-·₁) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.·⊑·² {pB = result-related}
        function-related argument-related) path
      (pure-step (blame-·₂ source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.Λ⊑Λ² source-value target-value related s) path
      (pure-step ()) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.Λ⊑² nonvar occurs source-value target⊢ related s) path
      (pure-step ()) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (ξ-• source-step refl refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-•-paired p∀ related type-related result-related))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (pure-step (β-∀ source-value instantiated)) rebuild =
    close-context-paired-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value 《 all 》)
      (pure-step (β-∀ source-value instantiated)) rebuild
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.•⊑•² p∀ related type-related result-related) path
      (pure-step blame-•) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-Λ source-value) rebuild =
    close-context-paired-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (Λ source-value) (β-Λ source-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-gen source-value source≢★ safe) rebuild =
    close-context-paired-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value 《 genᵥ source≢★ safe 》)
      (β-gen source-value source≢★ safe) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-reveal-∀ source-value) rebuild =
    close-context-paired-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value ↑ all)
      (β-reveal-∀ source-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑•² p∀ related type-related result-related) path
      (β-conceal-∀ source-value) rebuild =
    close-context-paired-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value ↓ all)
      (β-conceal-∀ source-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (ξ-• source-step refl refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-•-source p∀ related type-related result-related))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (pure-step (β-∀ source-value instantiated)) rebuild =
    close-context-source-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value 《 all 》)
      (pure-step (β-∀ source-value instantiated)) rebuild
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.•⊑² p∀ related type-related result-related) path
      (pure-step blame-•) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) result-related) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-Λ source-value) rebuild =
    close-context-source-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (Λ source-value) (β-Λ source-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-gen source-value source≢★ safe) rebuild =
    close-context-source-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value 《 genᵥ source≢★ safe 》)
      (β-gen source-value source≢★ safe) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-reveal-∀ source-value) rebuild =
    close-context-source-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value ↑ all)
      (β-reveal-∀ source-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.•⊑² p∀ related type-related result-related) path
      (β-conceal-∀ source-value) rebuild =
    close-context-source-all
      no-open target-reveal rebase root-related q related type-related
      result-related path (source-value ↓ all)
      (β-conceal-∀ source-value) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.κ⊑κ² constant s) path (pure-step ()) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (ξ-⟨⟩ source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-cast-paired source-cast target-cast related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑cast²
        source-cast target-cast related s) path
      (pure-step (β-id source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑cast² target-cast related s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (ground source-value unequal)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (expand source-value unequal)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (tag-untag source-value)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (tag-untag-bad source-value unequal)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step (blame-bot-intro source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑cast² source-cast target-cast related s) path
      (pure-step blame-⟨⟩) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (β-inst source-value source≢★) rebuild = {!!}

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑cast² target-cast related s) path source-step rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path (focus-cast-target target-cast related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (ξ-⟨⟩ source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path (focus-cast-source source-cast related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑² {p = inner-type} source-cast related s) path
      (pure-step (β-id source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r)
          (PI.⊑-unique inner-type s) related)
        rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (pure-step (ground source-value unequal)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (pure-step (expand source-value unequal)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (pure-step (tag-untag source-value)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑² source-cast related s) path
      (pure-step (tag-untag-bad source-value unequal)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑² source-cast related s) path
      (pure-step (blame-bot-intro source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.cast⊑² source-cast related s) path
      (pure-step blame-⟨⟩) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.cast⊑² source-cast related s) path
      (β-inst source-value source≢★) rebuild = {!!}

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑reveal-identity c⊢ absent related s) path
      source-step rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-reveal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑conceal-identity c⊢ absent related s) path
      source-step rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-conceal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-identity c⊢ absent related s) path
      (ξ-reveal source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-reveal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
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
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-identity (Conv.⊢↑-unseal member) absent related s)
      path (pure-step (conceal-reveal source-value)) rebuild =
    ⊥-elim (generator-here≠absent absent)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑-identity c⊢ absent related s) path
      (pure-step blame-reveal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (ξ-reveal source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-reveal-only c⊢ present mark free represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-var member X≠Y) present mark free represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    ⊥-elim (present refl)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-base member) present mark free represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    ⊥-elim (present refl)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only²
        (Conv.⊢↑-id-star member) present mark free represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    ⊥-elim (present refl)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (pure-step (conceal-reveal source-value)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑-only²
        c⊢ present mark free represented related s) path
      (pure-step blame-reveal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-identity c⊢ absent related s) path
      (ξ-conceal source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-conceal-identity c⊢ absent related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
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
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑-identity c⊢ absent related s) path
      (pure-step blame-conceal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only² c⊢ present mark free represented related s) path
      (ξ-conceal source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-source-conceal-only c⊢ present mark free represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-var member X≠Y) present mark free represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    ⊥-elim (present refl)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-base member) present mark free represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    ⊥-elim (present refl)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑-only²
        (Conv.⊢↓-id-star member) present mark free represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    ⊥-elim (present refl)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑-only²
        c⊢ present mark free represented related s) path
      (pure-step blame-conceal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (ξ-reveal source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-reveal-paired c⊢ c′⊢ positions aligned represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        (Conv.⊢↑-id-var member X≠Y) c′⊢ positions aligned represented
        related s)
      path (pure-step (id-reveal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑reveal-identity c′⊢ (sym positions) related s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        (Conv.⊢↑-id-base member) c′⊢ positions aligned represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑reveal-identity c′⊢ (sym positions) related s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        (Conv.⊢↑-id-star member) c′⊢ positions aligned represented related s)
      path (pure-step (id-reveal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑reveal-identity c′⊢ (sym positions) related s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (pure-step (conceal-reveal source-value)) rebuild = {!!}
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related s)
      path (pure-step blame-reveal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented related s)
      path (ξ-conceal source-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-conceal-paired c⊢ c′⊢ positions aligned represented related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        (Conv.⊢↓-id-var member X≠Y) c′⊢ positions aligned represented
        related s)
      path (pure-step (id-conceal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑conceal-identity c′⊢ (sym positions) related s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        (Conv.⊢↓-id-base member) c′⊢ positions aligned represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑conceal-identity c′⊢ (sym positions) related s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        (Conv.⊢↓-id-star member) c′⊢ positions aligned represented related s)
      path (pure-step (id-conceal source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.⊑conceal-identity c′⊢ (sym positions) related s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented related s)
      path (pure-step blame-conceal) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑reveal-rebase² c⊢ nested-rebase related s) path
      source-step rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-reveal-rebase c⊢ nested-rebase related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊑conceal-rebase² c⊢ nested-rebase related s) path
      source-step rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q related
      (extend-focus path
        (focus-target-conceal-rebase c⊢ nested-rebase related s))
      source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.blame⊑² target⊢ s) path (pure-step ()) rebuild

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (ξ-⊕₁ left-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q left-related
      (extend-focus path (focus-⊕₁ left-related right-related s))
      left-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (ξ-⊕₂ left-value right-step refl) rebuild =
    selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q right-related
      (extend-focus path
        (focus-⊕₂ left-related right-related s left-value))
      right-step
      (extend-rebuild rebuild (rebuild-edge refl))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
      with catchup-target-reveal-rebase-context
        no-open target-reveal rebase root-related q left-related
        (extend-focus path (focus-⊕₁ left-related right-related s))
        (CastTerms.Value.$ κ)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
      with split-target-extended-path path-evolution₁
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
      with primitive-left-edge-view edge₁
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₁))
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | primitive-left-edge left-related₂ right-related₁ result-related₁
        refl left-focus-eq₁
      with catchup-target-reveal-rebase-context
        (multi-no-open-frames evolution₁ no-open)
        (multi-target-reveal evolution₁ target-reveal)
        rebase₁ root-related₁ (multi-⊑ᵀ evolution₁ q)
        right-related₁
        (extend-focus prefix₁
          (focus-⊕₂ left-related₂ right-related₁ result-related₁
            (subst Value (cong sourceTerm left-focus-eq₁)
              (CastTerms.Value.$ κ))))
        (CastTerms.Value.$ κ′)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | primitive-left-edge left-related₂ right-related₁ result-related₁
        refl left-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-right₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , right-type₂ , right-steps₂ , target-right-value₂ ,
      evolution₂ , rebase₂ , root-related₂ , right-related₂ , path₂ ,
      path-evolution₂
      with split-target-extended-path path-evolution₂
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | primitive-left-edge left-related₂ right-related₁ result-related₁
        refl left-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-right₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , right-type₂ , right-steps₂ , target-right-value₂ ,
      evolution₂ , rebase₂ , root-related₂ , right-related₂ , path₂ ,
      path-evolution₂
    | evolved-extended-path {middle′ = pack primitive-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
      with primitive-right-edge-view edge₂
        (sym (TargetEdgeEvolution.same-source-frame edge-evolution₂))
        (TargetEdgeEvolution.target-edge-ready edge-evolution₂)
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | primitive-left-edge left-related₂ right-related₁ result-related₁
        refl left-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-right₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , right-type₂ , right-steps₂ , target-right-value₂ ,
      evolution₂ , rebase₂ , root-related₂ , right-related₂ , path₂ ,
      path-evolution₂
    | evolved-extended-path {middle′ = pack primitive-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | primitive-right-edge left-related₃ right-related₃ result-related₃
        source-left-value₃ target-left-value₃ refl right-focus-eq₂
      with cong sourceTerm left-focus-eq₁
         | cong sourceTerm right-focus-eq₂
         | cong targetTerm right-focus-eq₂
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | primitive-left-edge left-related₂ right-related₁ result-related₁
        refl left-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-right₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , right-type₂ , right-steps₂ , target-right-value₂ ,
      evolution₂ , rebase₂ , root-related₂ , right-related₂ , path₂ ,
      path-evolution₂
    | evolved-extended-path {middle′ = pack primitive-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | primitive-right-edge left-related₃ right-related₃ result-related₃
        source-left-value₃ target-left-value₃ refl right-focus-eq₂
    | refl | refl | refl
      with sim-context-primitive-values
        (multi-no-open-frames evolution₂
          (multi-no-open-frames evolution₁ no-open))
        (multi-target-reveal evolution₂
          (multi-target-reveal evolution₁ target-reveal))
        rebase₂ root-related₂
        (multi-⊑ᵀ evolution₂ (multi-⊑ᵀ evolution₁ q))
        left-related₃ right-related₃ result-related₃ prefix₂
        (target-path-ready
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂))
        target-left-value₃ target-right-value₂ primitive-step
        (transport-rebuild
          (compose-target-path-evolution
            prefix-evolution₁ prefix-evolution₂)
          rebuild)
  selected-target-reveal-rebase-closing {c′ = c′}
      no-open target-reveal rebase root-related q
      (CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step)) rebuild
    | Δᴿ₁ , Σᴿ₁ , χsᴿ₁ , root-target₁ , target-left₁ , γ₁ , γᵖ₁ ,
      γᶠ₁ , p₁ , left-type₁ , left-steps₁ , target-left-value₁ ,
      evolution₁ , rebase₁ , root-related₁ , left-related₁ , path₁ ,
      path-evolution₁
    | evolved-extended-path {middle′ = pack primitive-related₁}
        prefix₁ edge₁ refl prefix-evolution₁ edge-evolution₁
    | primitive-left-edge left-related₂ right-related₁ result-related₁
        refl left-focus-eq₁
    | Δᴿ₂ , Σᴿ₂ , χsᴿ₂ , root-target₂ , target-right₂ , γ₂ , γᵖ₂ ,
      γᶠ₂ , p₂ , right-type₂ , right-steps₂ , target-right-value₂ ,
      evolution₂ , rebase₂ , root-related₂ , right-related₂ , path₂ ,
      path-evolution₂
    | evolved-extended-path {middle′ = pack primitive-related₂}
        prefix₂ edge₂ refl prefix-evolution₂ edge-evolution₂
    | primitive-right-edge left-related₃ right-related₃ result-related₃
        source-left-value₃ target-left-value₃ refl right-focus-eq₂
    | refl | refl | refl
    | Δᴿ₃ , Σᴿ₃ , χsᴿ₃ , result-target , γ₃ , result-related ,
      values-steps , values-evolution , result-relation =
    let
      target-type-eq =
        trans
          (applyTys-++ χsᴿ₂ χsᴿ₃ (applyTys χsᴿ₁ _))
          (applyTys-++ χsᴿ₁ (χsᴿ₂ ++χ χsᴿ₃) _)
      normalized-result =
        subst
          (λ T →
            Σ[ r ∈ _ ⊑ᵀ⟨ γ₃ ⟩ T ]
              γ₃ CTI.⊢² _ ⊑ result-target ∶ r)
          target-type-eq (result-related , result-relation)
      final-related = proj₁ normalized-result
      final-relation = proj₂ normalized-result
    in
      Δᴿ₃ , Σᴿ₃ , χsᴿ₁ ++χ (χsᴿ₂ ++χ χsᴿ₃) , result-target , γ₃ ,
      final-related ,
      (targetTerm (pack root-related) ↑ c′
         —↠+[ χsᴿ₁ ]⟨ left-steps₁ ⟩
       root-target₁ ↑ applyReveals χsᴿ₁ c′
         —↠+[ χsᴿ₂ ]⟨ right-steps₂ ⟩
       root-target₂ ↑
         applyReveals χsᴿ₂ (applyReveals χsᴿ₁ c′)
         —↠[ χsᴿ₃ ]⟨ values-steps ⟩
       result-target ∎[]) ,
      composeMultiWorldEvolution evolution₁
        (composeMultiWorldEvolution evolution₂ values-evolution) ,
      final-relation

  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step blame-⊕₁) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q
  selected-target-reveal-rebase-closing
      no-open target-reveal rebase root-related q
      relation@(CTI.⊕⊑⊕² op left-related right-related s) path
      (pure-step (blame-⊕₂ source-value)) rebuild =
    close-root-keep target-reveal rebase
      (replay-context-keep root-related relation path
        (CTI.blame⊑² (target-typing relation) s) rebuild)
      q


  whole-contextual-target-reveal-rebase-closing :
    WholeContextualTargetRevealRebaseClosingᵀ

  whole-contextual-target-reveal-rebase-closing
      no-open
      (CTI.⊑reveal-rebase² target-reveal rebase inner-related
        selected-related)
      target-reveal rebase inner-related selected-related focus-related
      (focus-there
        (focus-target-reveal-rebase .target-reveal .rebase
          .inner-related .selected-related)
        tail)
      selected-here step
      (rebuild-there rebuild (rebuild-edge refl)) =
    selected-target-reveal-rebase-closing no-open target-reveal rebase
      inner-related selected-related focus-related tail step rebuild

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.ƛ⊑ƛ² related) path
      (selected-there selected) (pure-step ()) rebuild

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected) (ξ-·₁ function-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related function-related
      (extend-focus path (focus-·₁ function-related argument-related))
      (extend-selected-reveal (selected-there selected)) function-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected)
      (ξ-·₂ function-value argument-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related argument-related
      (extend-focus path
        (focus-·₂ function-related argument-related function-value))
      (extend-selected-reveal (selected-there selected)) argument-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected)
      (pure-step (β {N = body} argument-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected)
      (pure-step (β-⇒ function-value argument-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected)
      (pure-step (β-reveal-⇒ function-value argument-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected)
      (pure-step (β-conceal-⇒ function-value argument-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected) (pure-step blame-·₁) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.·⊑·² function-related argument-related) path
      (selected-there selected)
      (pure-step (blame-·₂ function-value)) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.Λ⊑Λ² source-value target-value related q) path
      (selected-there selected) (pure-step ()) rebuild

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.Λ⊑² nonvar occurs source-value target⊢ related q) path
      (selected-there selected) (pure-step ()) rebuild

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      relation@(CTI.•⊑•² p∀ related type-related result-related) path
      (selected-there selected) (ξ-• source-step refl refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-•-paired p∀ related type-related result-related))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑•² p∀ related type-related result-related) path
      (selected-there selected)
      (pure-step (β-∀ source-value instantiated)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑•² p∀ related type-related result-related) path
      (selected-there selected) (pure-step blame-•) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑•² p∀ related type-related result-related) path
      (selected-there selected) (β-Λ source-value) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑•² p∀ related type-related result-related) path
      (selected-there selected)
      (β-gen source-value source≠★ safe) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑•² p∀ related type-related result-related) path
      (selected-there selected) (β-reveal-∀ source-value) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑•² p∀ related type-related result-related) path
      (selected-there selected) (β-conceal-∀ source-value) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑² p∀ related type-related result-related) path
      (selected-there selected) (ξ-• source-step refl refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-•-source p∀ related type-related result-related))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑² p∀ related type-related result-related) path
      (selected-there selected)
      (pure-step (β-∀ source-value instantiated)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑² p∀ related type-related result-related) path
      (selected-there selected) (pure-step blame-•) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑² p∀ related type-related result-related) path
      (selected-there selected) (β-Λ source-value) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑² p∀ related type-related result-related) path
      (selected-there selected)
      (β-gen source-value source≠★ safe) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑² p∀ related type-related result-related) path
      (selected-there selected) (β-reveal-∀ source-value) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.•⊑² p∀ related type-related result-related) path
      (selected-there selected) (β-conceal-∀ source-value) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.κ⊑κ² constant p) path
      (selected-there selected) (pure-step ()) rebuild
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected) (ξ-⟨⟩ source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-cast-paired source-cast target-cast related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected)
      (pure-step (β-id source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected)
      (pure-step (ground source-value unequal)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected)
      (pure-step (expand source-value unequal)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected)
      (pure-step (tag-untag source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected)
      (pure-step (tag-untag-bad source-value unequal)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected)
      (pure-step (blame-bot-intro source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected) (pure-step blame-⟨⟩) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.cast⊑cast² source-cast target-cast related s) path
      (selected-there selected)
      (β-inst source-value source≠★) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.⊑cast² target-cast related s) path
      (selected-there selected) source-step rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path (focus-cast-target target-cast related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.⊑reveal-identity c⊢ absent related s) path
      (selected-there selected) source-step rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-target-reveal-identity c⊢ absent related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.⊑conceal-identity c⊢ absent related s) path
      (selected-there selected) source-step rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-target-conceal-identity c⊢ absent related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected) (ξ-⟨⟩ source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path (focus-cast-source source-cast related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected)
      (pure-step (β-id source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected)
      (pure-step (ground source-value unequal)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected)
      (pure-step (expand source-value unequal)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected)
      (pure-step (tag-untag source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected)
      (pure-step (tag-untag-bad source-value unequal)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected)
      (pure-step (blame-bot-intro source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected) (pure-step blame-⟨⟩) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.cast⊑² source-cast related s) path
      (selected-there selected)
      (β-inst source-value source≠★) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.reveal⊑-identity c⊢ absent related s) path
      (selected-there selected) (ξ-reveal source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-source-reveal-identity c⊢ absent related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.reveal⊑-identity c⊢ absent related s) path
      (selected-there selected)
      (pure-step (id-reveal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.reveal⊑-identity c⊢ absent related s) path
      (selected-there selected)
      (pure-step (conceal-reveal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.reveal⊑-identity c⊢ absent related s) path
      (selected-there selected) (pure-step blame-reveal) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (selected-there selected) (ξ-reveal source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-source-reveal-only c⊢ present mark free represented
          related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (selected-there selected)
      (pure-step (id-reveal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (selected-there selected)
      (pure-step (conceal-reveal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑-only² c⊢ present mark free represented related s) path
      (selected-there selected) (pure-step blame-reveal) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.conceal⊑-identity c⊢ absent related s) path
      (selected-there selected) (ξ-conceal source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-source-conceal-identity c⊢ absent related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.conceal⊑-identity c⊢ absent related s) path
      (selected-there selected)
      (pure-step (id-conceal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.conceal⊑-identity c⊢ absent related s) path
      (selected-there selected) (pure-step blame-conceal) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.conceal⊑-only² c⊢ present mark free represented related s) path
      (selected-there selected) (ξ-conceal source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-source-conceal-only c⊢ present mark free represented
          related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.conceal⊑-only² c⊢ present mark free represented related s) path
      (selected-there selected)
      (pure-step (id-conceal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.conceal⊑-only² c⊢ present mark free represented related s) path
      (selected-there selected) (pure-step blame-conceal) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (selected-there selected) (ξ-reveal source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-reveal-paired c⊢ c′⊢ positions aligned represented
          related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (selected-there selected)
      (pure-step (id-reveal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (selected-there selected)
      (pure-step (conceal-reveal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.reveal⊑reveal² c⊢ c′⊢ positions aligned represented related s)
      path (selected-there selected) (pure-step blame-reveal) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented
        related s)
      path (selected-there selected) (ξ-conceal source-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-conceal-paired c⊢ c′⊢ positions aligned represented
          related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented
        related s)
      path (selected-there selected)
      (pure-step (id-conceal source-value)) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.conceal⊑conceal² c⊢ c′⊢ positions aligned represented
        related s)
      path (selected-there selected) (pure-step blame-conceal) rebuild = {! !}

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.⊑reveal-rebase² c⊢ nested-rebase related s) path
      (selected-there selected) source-step rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-target-reveal-rebase c⊢ nested-rebase related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related
      (CTI.⊑conceal-rebase² c⊢ nested-rebase related s) path
      (selected-there selected) source-step rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related related
      (extend-focus path
        (focus-target-conceal-rebase c⊢ nested-rebase related s))
      (extend-selected-reveal (selected-there selected)) source-step
      (extend-rebuild rebuild (rebuild-edge refl))

  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.blame⊑² target⊢ p) path
      (selected-there selected) (pure-step ()) rebuild
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.⊕⊑⊕² op left-related right-related s) path
      (selected-there selected) (ξ-⊕₁ left-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related left-related
      (extend-focus path (focus-⊕₁ left-related right-related s))
      (extend-selected-reveal (selected-there selected)) left-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.⊕⊑⊕² op left-related right-related s) path
      (selected-there selected)
      (ξ-⊕₂ left-value right-step refl) rebuild =
    whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related right-related
      (extend-focus path
        (focus-⊕₂ left-related right-related s left-value))
      (extend-selected-reveal (selected-there selected)) right-step
      (extend-rebuild rebuild (rebuild-edge refl))
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.⊕⊑⊕² op left-related right-related s) path
      (selected-there selected)
      (pure-step
        (δ-⊕ {κ = κ} {κ′ = κ′} {κ″ = κ″} primitive-step))
      rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.⊕⊑⊕² op left-related right-related s) path
      (selected-there selected) (pure-step blame-⊕₁) rebuild = {! !}
  whole-contextual-target-reveal-rebase-closing
      no-open root-related target-reveal rebase inner-related
      selected-related (CTI.⊕⊑⊕² op left-related right-related s) path
      (selected-there selected)
      (pure-step (blame-⊕₂ left-value)) rebuild = {! !}

  sim-target-reveal-rebase-closing : SimTargetRevealRebaseClosingᵀ
  sim-target-reveal-rebase-closing =
    contextual-closing-adapter
      (whole-closing-specializes-to-contextual
        whole-contextual-target-reveal-rebase-closing)
