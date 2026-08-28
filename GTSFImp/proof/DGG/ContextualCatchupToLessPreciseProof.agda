{-# OPTIONS --safe #-}

module proof.DGG.ContextualCatchupToLessPreciseProof where

-- File Charter:
--   * Develops contextual source value catch-up by structural recursion on
--     the focused CTI derivation while retaining the whole root and zipper.
--   * Exposes all nineteen source blame-context edges and installs recursive
--     calls beneath each target-only wrapper before local reconstruction.
--   * Uses the existing lower source catch-up interfaces only at the root;
--     contextual dynamic-root obligations remain explicit local goals.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym; cong)

import CastTerms as CT
open import CastTerms using
  (Ctx; Δᵉ; Term; Value; blame; ⟨_,_,_⟩; _《_》; _↑_; _↓_)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Reduction using
  ( StoreChanges; applyTys; applyTerms; keep; pure-step
  ; blame-·₁; blame-⊕₁; _—↠[_]_; ↠-refl; ↠-step
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
open import proof.Reduction using
  ( _++χ_; composeReduction; appL-↠; appR-blame-↠; primL-↠
  ; primR-↠; typeApp-blame-↠; cast-blame-↠; reveal-blame-↠
  ; conceal-blame-↠; applyTerms-preserves-Value
  )

import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.Catchup.ContextualLeftSourceCastCatchupDef using
  (ContextualLeftSourceCastCatchupAt)
open import proof.DGG.Catchup.ContextualLeftSourceTypeAppCatchupDef using
  (ContextualLeftSourceTypeAppCatchupAt)
open import proof.DGG.Catchup.LeftPairedConversionCatchupDef using
  (LeftPairedRevealCatchupAt; LeftPairedConcealCatchupAt)
open import proof.DGG.Catchup.LeftSourceCastCatchupDef using
  (LeftSourceCastCatchupAt)
open import proof.DGG.Catchup.LeftSourceConversionCatchupDef using
  (LeftSourceRevealCatchupAt; LeftSourceConcealCatchupAt)
open import proof.DGG.Catchup.LeftSourceTypeAppCatchupDef using
  (LeftSourceTypeAppCatchupAt)
open import proof.DGG.Catchup.LeftTargetRevealRebaseCatchupDef using
  (LeftTargetRevealRebaseCatchupAt)
open import proof.DGG.Catchup.LeftValueCatchupDef using
  (SourceCastBound; sourceCastBudget)
open import proof.DGG.Catchup.LeftValueCatchupLemma using
  (source-cast-bound)
open import proof.DGG.ContextualCatchupToLessPreciseDef using
  (ContextualCatchupToLessPreciseᵀ)
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.SimBackContextDef using
  ( world; SourcePathEvolution; source-path-reflexive
  ; evolve-source-here; evolve-source-there
  ; split-source-extended-path; evolved-source-extended-path
  ; evolve-source-edge
  )
open import proof.DGG.World
open import proof.DGG.SourceRebase using
  (open-source-rebase-nonempty)
open import proof.DGG.WorldEvolutionSequence using
  (MultiWorldEvolution; append-left-keep; evolutions-refl)


source-path-blame : ∀ {Cᴸ Cᴿ : Ctx} {W : Cᴸ ⊑ᶜ Cᴿ}
    {root focus : RelatedConfiguration Cᴸ Cᴿ}
  → (path : root ↘ᶜ* focus)
  → sourceTerm focus ≡ blame
  → Σ[ χsᴸ ∈ StoreChanges (Δᵉ Cᴸ) (Δᵉ Cᴸ) ]
      (sourceTerm root —↠[ χsᴸ ] blame)
      × MultiWorldEvolution {W = W} {W′ = W} χsᴸ []ˢ
source-path-blame focus-here focus-blame =
  []ˢ , subst (λ M → M —↠[ []ˢ ] blame)
    (sym focus-blame) ↠-refl , evolutions-refl
source-path-blame
    {W = W}
    (focus-there
      (focus-·₁ {M = M} function-rel argument-rel) tail)
    focus-blame
    with source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there
      (focus-·₁ {M = M} function-rel argument-rel) tail)
    focus-blame
  | χsᴸ , inner-steps , evolution =
    χsᴸ ++χ (keep ∷ˢ []ˢ)
  , composeReduction (appL-↠ inner-steps)
      (↠-step (pure-step blame-·₁) ↠-refl)
  , append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-·₂ function-rel argument-rel source-value) tail)
    focus-blame
    with source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there
      (focus-·₂ function-rel argument-rel source-value) tail)
    focus-blame
  | χsᴸ , inner-steps , evolution =
    χsᴸ ++χ (keep ∷ˢ []ˢ)
  , appR-blame-↠ source-value inner-steps
  , append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-⊕₁ {M = M} left-rel right-rel r) tail)
    focus-blame
    with source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there
      (focus-⊕₁ {M = M} left-rel right-rel r) tail)
    focus-blame
  | χsᴸ , inner-steps , evolution =
    χsᴸ ++χ (keep ∷ˢ []ˢ)
  , composeReduction (primL-↠ inner-steps)
      (↠-step (pure-step blame-⊕₁) ↠-refl)
  , append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-⊕₂ left-rel right-rel r source-value) tail)
    focus-blame
    with source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there
      (focus-⊕₂ left-rel right-rel r source-value) tail)
    focus-blame
  | χsᴸ , inner-steps , evolution =
    χsᴸ ++χ (keep ∷ˢ []ˢ)
  , composeReduction (primR-↠ source-value inner-steps)
      (↠-step
        (pure-step
          (Reduction.blame-⊕₂
            (applyTerms-preserves-Value χsᴸ source-value)))
        ↠-refl)
  , append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there (focus-•-paired p∀ related q r) tail) focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , typeApp-blame-↠ inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there (focus-•-source p∀ related q r) tail) focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , typeApp-blame-↠ inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there (focus-cast-paired c c′ related q) tail) focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , cast-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there (focus-cast-target c′ related q) tail) focus-blame =
  source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there (focus-cast-source c related q) tail) focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , cast-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-target-reveal-identity c′⊢ absent related q) tail)
    focus-blame =
  source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there
      (focus-target-conceal-identity c′⊢ absent related q) tail)
    focus-blame =
  source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there
      (focus-source-reveal-identity {c = c} c⊢ absent related q) tail)
    focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , reveal-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-source-conceal-identity {c = c} c⊢ absent related q) tail)
    focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , conceal-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-source-reveal-only
        {c = c} c⊢ present mark free represented related q) tail)
    focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , reveal-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-source-conceal-only
        {c = c} c⊢ present mark free represented related q) tail)
    focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , conceal-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-reveal-paired
        {c = c} c⊢ c′⊢ positions aligned represented related q) tail)
    focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , reveal-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-conceal-paired
        {c = c} c⊢ c′⊢ positions aligned represented related q) tail)
    focus-blame =
  let χsᴸ , inner-steps , evolution =
        source-path-blame {W = W} tail focus-blame
  in χsᴸ ++χ (keep ∷ˢ []ˢ) , conceal-blame-↠ c inner-steps ,
    append-left-keep evolution
source-path-blame
    {W = W}
    (focus-there
      (focus-target-reveal-rebase c′⊢ rebase related q) tail)
    focus-blame =
  source-path-blame {W = W} tail focus-blame
source-path-blame
    {W = W}
    (focus-there
      (focus-target-conceal-rebase c′⊢ rebase related q) tail)
    focus-blame =
  source-path-blame {W = W} tail focus-blame


root-catchup-result : ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    (related : γ CTI.⊢² M ⊑ V′ ∶ p)
  → ((Σ[ Δᴸ′ ∈ TyCtx ]
        Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
        Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        Σ[ V ∈ Term Δᴸ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        Σ[ q ∈ applyTys χsᴸ A ⊑ᵀ⟨ γ′ ⟩ B ]
          (M —↠[ χsᴸ ] V)
          × Value V
          × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ
          × (γ′ CTI.⊢² V ⊑ V′ ∶ q))
      ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
        Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
        Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
          (M —↠[ χsᴸ ] blame)
          × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ))
  → (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ root′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ focus′ ∈ RelatedConfiguration
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
      Σ[ path′ ∈ root′ ↘ᶜ* focus′ ]
        (M —↠[ χsᴸ ] sourceTerm root′)
        × Value (sourceTerm focus′)
        × targetTerm root′ ≡ V′
        × targetTerm focus′ ≡ V′
        × (SourcePathEvolution
            (focus-here {related = pack related}) path′)
        × MultiWorldEvolution {W = γ} {W′ = world root′} χsᴸ []ˢ)
    ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
      Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
      Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        (M —↠[ χsᴸ ] blame)
        × MultiWorldEvolution {W = γ} {W′ = γ′} χsᴸ []ˢ)
root-catchup-result related (inj₂ blame-result) = inj₂ blame-result
root-catchup-result related
    (inj₁
      (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , q , source-steps , source-value ,
        evolution , value-related)) =
  inj₁
    (Δᴸ′ , Σᴸ′ , χsᴸ , pack value-related , pack value-related ,
      focus-here , source-steps , source-value , refl , refl ,
      evolve-source-here , evolution)


module _
    (source-cast-catchup : ∀ {fuel} → LeftSourceCastCatchupAt fuel)
    (contextual-source-cast-catchup : ∀ {fuel}
      → ContextualLeftSourceCastCatchupAt fuel)
    (source-type-app-catchup : ∀ {fuel}
      → LeftSourceTypeAppCatchupAt fuel)
    (contextual-source-type-app-catchup : ∀ {fuel}
      → ContextualLeftSourceTypeAppCatchupAt fuel)
    (source-reveal-catchup : ∀ {fuel}
      → LeftSourceRevealCatchupAt fuel)
    (source-conceal-catchup : ∀ {fuel}
      → LeftSourceConcealCatchupAt fuel)
    (paired-reveal-catchup : ∀ {fuel}
      → LeftPairedRevealCatchupAt fuel)
    (paired-conceal-catchup : ∀ {fuel}
      → LeftPairedConcealCatchupAt fuel)
    (target-reveal-rebase-catchup : ∀ {fuel}
      → LeftTargetRevealRebaseCatchupAt fuel)
  where

  contextual-left-value-catchup : ∀ {fuel : ℕ}
      {Δᴸ Δᴿ : TyCtx} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ γᶠ :
        ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {root-source focus-source : Term Δᴸ}
      {root-target focus-target : Term Δᴿ}
      {root-source-type focus-source-type : Ty Δᴸ}
      {root-target-type focus-target-type : Ty Δᴿ}
      {root-type-related :
        root-source-type ⊑ᵀ⟨ γ ⟩ root-target-type}
      {focus-type-related :
        focus-source-type ⊑ᵀ⟨ γᶠ ⟩ focus-target-type}
    → openFramesᶜ γ ≡ []
    → (root-related :
        γ CTI.⊢² root-source ⊑ root-target ∶ root-type-related)
    → (focus-related :
        γᶠ CTI.⊢² focus-source ⊑ focus-target ∶ focus-type-related)
    → (path : pack root-related ↘ᶜ* pack focus-related)
    → Value focus-target
    → SourceCastBound fuel focus-related
    → (Σ[ Δᴸ′ ∈ TyCtx ]
        Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
        Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        Σ[ root′ ∈ RelatedConfiguration
          ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        Σ[ focus′ ∈ RelatedConfiguration
          ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
        Σ[ path′ ∈ root′ ↘ᶜ* focus′ ]
          (root-source —↠[ χsᴸ ] sourceTerm root′)
          × Value (sourceTerm focus′)
          × targetTerm root′ ≡ root-target
          × targetTerm focus′ ≡ focus-target
          × SourcePathEvolution path path′
          × MultiWorldEvolution
              {W = γ} {W′ = world root′} χsᴸ []ˢ)
      ⊎ (Σ[ Δᴸ′ ∈ TyCtx ]
        Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
        Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩ ]
          (root-source —↠[ χsᴸ ] blame)
          × MultiWorldEvolution
              {W = γ} {W′ = γ′} χsᴸ []ˢ)

  contextual-left-value-catchup no-open root-related
      (CTI.x⊑x² source∋ target∋) path () bound

  contextual-left-value-catchup {γ = γ} no-open root-related
      focus-related@(CTI.ƛ⊑ƛ² related) path target-value bound =
    inj₁ (_ , _ , []ˢ , pack root-related , pack focus-related , path ,
      ↠-refl , CT.ƛ _ , refl , refl , source-path-reflexive path ,
      evolutions-refl)

  contextual-left-value-catchup no-open root-related
      (CTI.·⊑·² function-related argument-related) path () bound

  contextual-left-value-catchup {γ = γ} no-open root-related
      focus-related@(CTI.Λ⊑Λ² source-value target-value related q)
      path target-all-value bound =
    inj₁ (_ , _ , []ˢ , pack root-related , pack focus-related , path ,
      ↠-refl , CT.Λ source-value , refl , refl ,
      source-path-reflexive path , evolutions-refl)

  contextual-left-value-catchup {γ = γ} no-open root-related
      focus-related@(CTI.Λ⊑² nonvar occurs source-value target⊢ related q)
      path target-value bound =
    inj₁ (_ , _ , []ˢ , pack root-related , pack focus-related , path ,
      ↠-refl , CT.Λ source-value , refl , refl ,
      source-path-reflexive path , evolutions-refl)

  contextual-left-value-catchup no-open root-related
      (CTI.•⊑•² p∀ related q r) path () bound

  contextual-left-value-catchup no-open
      .(CTI.•⊑² p∀ related q r)
      (CTI.•⊑² p∀ related q r) focus-here target-value bound
      with source-type-app-catchup no-open related target-value bound
  contextual-left-value-catchup no-open
      .(CTI.•⊑² p∀ related q r)
      (CTI.•⊑² p∀ related q r) focus-here target-value bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-steps , evolution) =
      inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-steps , evolution)
  contextual-left-value-catchup no-open
      .(CTI.•⊑² p∀ related q r)
      (CTI.•⊑² p∀ related q r) focus-here target-value bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , source-value , γ′ , q′ , source-steps ,
          value-source , evolution , value-related) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , pack value-related , pack value-related ,
          focus-here , source-steps , value-source , refl , refl ,
          evolve-source-here , evolution)
  contextual-left-value-catchup no-open root-related
      (CTI.•⊑² p∀ related q r) path@(focus-there edge tail)
      target-value bound =
    contextual-source-type-app-catchup no-open path target-value bound

  contextual-left-value-catchup {γ = γ} no-open root-related
      focus-related@(CTI.κ⊑κ² constant q) path target-value bound =
    inj₁ (_ , _ , []ˢ , pack root-related , pack focus-related , path ,
      ↠-refl , CT.$ constant , refl , refl ,
      source-path-reflexive path , evolutions-refl)

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.cast⊑cast²
        source-cast target-cast related q)
      focus-here target-value bound
      with source-cast-catchup no-open focus-related target-value bound
  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.cast⊑cast²
        source-cast target-cast related q)
      focus-here target-value bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-steps , evolution) =
      inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-steps , evolution)
  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.cast⊑cast²
        source-cast target-cast related q)
      focus-here target-value bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , source-value , γ′ , q′ , source-steps ,
          value-source , evolution , value-related) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , pack value-related , pack value-related ,
          focus-here , source-steps , value-source , refl , refl ,
          evolve-source-here , evolution)
  contextual-left-value-catchup no-open root-related
      focus-related@(CTI.cast⊑cast²
        source-cast target-cast related q)
      path@(focus-there edge tail) target-value bound =
    contextual-source-cast-catchup no-open path target-value bound

  contextual-left-value-catchup no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (target-value 《 inert 》) bound
      with contextual-left-value-catchup no-open root-related related
        (extend-focus path
          (focus-cast-target target-cast related q))
        target-value bound
  contextual-left-value-catchup no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (target-value 《 inert 》) bound
    | inj₂ blame-result = inj₂ blame-result
  contextual-left-value-catchup no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (target-value 《 inert 》) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
      with split-source-extended-path path-evolution
  contextual-left-value-catchup no-open root-related
      (CTI.⊑cast² target-cast related q) path
      (target-value 《 inert 》) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
    | evolved-source-extended-path prefix′
        (focus-cast-target target-cast′ related′ q′) refl
        prefix-evolution (evolve-source-edge refl source-ready) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ ,
          pack (CTI.⊑cast² target-cast′ related′ q′) , prefix′ ,
          source-steps , source-value , root-target-eq ,
          cong (λ M → CT._⟨_⟩ M target-cast) focus-target-eq ,
          prefix-evolution , evolution)

  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-identity
        {c′ = target-reveal} c′⊢ absent related q) path
      (target-value ↑ reveal) bound
      with contextual-left-value-catchup no-open root-related related
        (extend-focus path
          (focus-target-reveal-identity c′⊢ absent related q))
        target-value bound
  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-identity
        {c′ = target-reveal} c′⊢ absent related q) path
      (target-value ↑ reveal) bound
    | inj₂ blame-result = inj₂ blame-result
  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-identity
        {c′ = target-reveal} c′⊢ absent related q) path
      (target-value ↑ reveal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
      with split-source-extended-path path-evolution
  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-identity
        {c′ = target-reveal} c′⊢ absent related q) path
      (target-value ↑ reveal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
    | evolved-source-extended-path prefix′
        (focus-target-reveal-identity
          {c′ = target-reveal′} c′⊢′ absent′ related′ q′) refl
        prefix-evolution (evolve-source-edge refl source-ready) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ ,
          pack (CTI.⊑reveal-identity c′⊢′ absent′ related′ q′) ,
          prefix′ , source-steps , source-value , root-target-eq ,
          cong (λ M → M ↑ target-reveal) focus-target-eq ,
          prefix-evolution , evolution)

  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-identity
        {c′ = target-conceal} c′⊢ absent related q) path
      (target-value ↓ conceal) bound
      with contextual-left-value-catchup no-open root-related related
        (extend-focus path
          (focus-target-conceal-identity c′⊢ absent related q))
        target-value bound
  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-identity
        {c′ = target-conceal} c′⊢ absent related q) path
      (target-value ↓ conceal) bound
    | inj₂ blame-result = inj₂ blame-result
  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-identity
        {c′ = target-conceal} c′⊢ absent related q) path
      (target-value ↓ conceal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
      with split-source-extended-path path-evolution
  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-identity
        {c′ = target-conceal} c′⊢ absent related q) path
      (target-value ↓ conceal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
    | evolved-source-extended-path prefix′
        (focus-target-conceal-identity
          {c′ = target-conceal′} c′⊢′ absent′ related′ q′) refl
        prefix-evolution (evolve-source-edge refl source-ready) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ ,
          pack (CTI.⊑conceal-identity c′⊢′ absent′ related′ q′) ,
          prefix′ , source-steps , source-value , root-target-eq ,
          cong (λ M → M ↓ target-conceal) focus-target-eq ,
          prefix-evolution , evolution)

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.cast⊑² source-cast related q)
      focus-here target-value bound
      with source-cast-catchup no-open focus-related target-value bound
  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.cast⊑² source-cast related q)
      focus-here target-value bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-steps , evolution) =
      inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , source-steps , evolution)
  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.cast⊑² source-cast related q)
      focus-here target-value bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , source-value , γ′ , q′ , source-steps ,
          value-source , evolution , value-related) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , pack value-related , pack value-related ,
          focus-here , source-steps , value-source , refl , refl ,
          evolve-source-here , evolution)
  contextual-left-value-catchup no-open root-related
      (CTI.cast⊑² source-cast related q)
      path@(focus-there edge tail) target-value bound =
    contextual-source-cast-catchup no-open path target-value bound

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.reveal⊑-identity c⊢ absent related q)
      focus-here target-value bound =
    root-catchup-result focus-related
      (source-reveal-catchup no-open focus-related target-value bound)
  contextual-left-value-catchup no-open root-related
      (CTI.reveal⊑-identity c⊢ absent related q)
      (focus-there edge tail) target-value bound = {! !}

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.reveal⊑-only²
        c⊢ present mark free represented related q)
      focus-here target-value bound =
    root-catchup-result focus-related
      (source-reveal-catchup no-open focus-related target-value bound)
  contextual-left-value-catchup no-open root-related
      (CTI.reveal⊑-only²
        c⊢ present mark free represented related q)
      (focus-there edge tail) target-value bound = {! !}

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.conceal⊑-identity c⊢ absent related q)
      focus-here target-value bound =
    root-catchup-result focus-related
      (source-conceal-catchup no-open focus-related target-value bound)
  contextual-left-value-catchup no-open root-related
      (CTI.conceal⊑-identity c⊢ absent related q)
      (focus-there edge tail) target-value bound = {! !}

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.conceal⊑-only²
        c⊢ present mark free represented related q)
      focus-here target-value bound =
    root-catchup-result focus-related
      (source-conceal-catchup no-open focus-related target-value bound)
  contextual-left-value-catchup no-open root-related
      (CTI.conceal⊑-only²
        c⊢ present mark free represented related q)
      (focus-there edge tail) target-value bound = {! !}

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related q)
      focus-here target-value bound =
    root-catchup-result focus-related
      (paired-reveal-catchup no-open focus-related target-value bound)
  contextual-left-value-catchup no-open root-related
      (CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented related q)
      (focus-there edge tail) target-value bound = {! !}

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented related q)
      focus-here target-value bound =
    root-catchup-result focus-related
      (paired-conceal-catchup no-open focus-related target-value bound)
  contextual-left-value-catchup no-open root-related
      (CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented related q)
      (focus-there edge tail) target-value bound = {! !}

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.⊑reveal-rebase² c′⊢ rebase related q)
      focus-here target-value bound =
    root-catchup-result focus-related
      (target-reveal-rebase-catchup no-open focus-related target-value
        bound)
  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-rebase²
        {c′ = target-reveal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↑ reveal) bound
      with contextual-left-value-catchup no-open root-related related
        (extend-focus path
          (focus-target-reveal-rebase c′⊢ rebase related q))
        target-value bound
  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-rebase²
        {c′ = target-reveal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↑ reveal) bound
    | inj₂ blame-result = inj₂ blame-result
  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-rebase²
        {c′ = target-reveal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↑ reveal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
      with split-source-extended-path
        {path = path}
        {edge = focus-target-reveal-rebase c′⊢ rebase related q}
        path-evolution
  contextual-left-value-catchup no-open root-related
      (CTI.⊑reveal-rebase²
        {c′ = target-reveal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↑ reveal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
    | evolved-source-extended-path prefix′
        (focus-target-reveal-rebase
          {c′ = target-reveal′} c′⊢′ rebase′ related′ q′) refl
        prefix-evolution (evolve-source-edge refl source-ready) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ ,
          pack (CTI.⊑reveal-rebase² c′⊢′ rebase′ related′ q′) ,
          prefix′ , source-steps , source-value , root-target-eq ,
          cong (λ M → M ↑ target-reveal) focus-target-eq ,
          prefix-evolution , evolution)

  contextual-left-value-catchup no-open .focus-related
      focus-related@(CTI.⊑conceal-rebase² c′⊢ rebase related q)
      focus-here target-value bound =
    ⊥-elim (open-source-rebase-nonempty rebase no-open)
  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-rebase²
        {c′ = target-conceal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↓ conceal) bound
      with contextual-left-value-catchup no-open root-related related
        (extend-focus path
          (focus-target-conceal-rebase c′⊢ rebase related q))
        target-value bound
  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-rebase²
        {c′ = target-conceal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↓ conceal) bound
    | inj₂ blame-result = inj₂ blame-result
  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-rebase²
        {c′ = target-conceal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↓ conceal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
      with split-source-extended-path
        {path = path}
        {edge = focus-target-conceal-rebase c′⊢ rebase related q}
        path-evolution
  contextual-left-value-catchup no-open root-related
      (CTI.⊑conceal-rebase²
        {c′ = target-conceal} c′⊢ rebase related q)
      path@(focus-there edge tail) (target-value ↓ conceal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ , focus′ , path′ , source-steps ,
          source-value , root-target-eq , focus-target-eq , path-evolution ,
          evolution)
    | evolved-source-extended-path prefix′
        (focus-target-conceal-rebase
          {c′ = target-conceal′} c′⊢′ rebase′ related′ q′) refl
        prefix-evolution (evolve-source-edge refl source-ready) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , root′ ,
          pack (CTI.⊑conceal-rebase² c′⊢′ rebase′ related′ q′) ,
          prefix′ , source-steps , source-value , root-target-eq ,
          cong (λ M → M ↓ target-conceal) focus-target-eq ,
          prefix-evolution , evolution)

  contextual-left-value-catchup {γ = γ} no-open root-related
      (CTI.blame⊑² target⊢ p) path target-value bound
      with source-path-blame {W = γ} path refl
  contextual-left-value-catchup {γ = γ} no-open root-related
      (CTI.blame⊑² target⊢ p) path target-value bound
    | χsᴸ , source-steps , evolution =
      inj₂ (_ , _ , χsᴸ , γ , source-steps , evolution)

  contextual-left-value-catchup no-open root-related
      (CTI.⊕⊑⊕² op left-related right-related r) path () bound

  contextual-catchup-to-less-precise :
    ContextualCatchupToLessPreciseᵀ
  contextual-catchup-to-less-precise
      {root = pack root-related} {focus = pack focus-related}
      no-open path target-value =
    contextual-left-value-catchup no-open root-related focus-related path
      target-value
      (source-cast-bound focus-related)
