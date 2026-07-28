module proof.Quotient.NuImprecisionPairedDownRenameLemma where

-- File Charter:
--   * Adapts the generic paired quotient-narrowing renaming proof to the
--     canonical relational-world embedding and source-only store renaming
--     structures used by live QTI consumers.
--   * Owns the two public adapter names formerly defined by the simulation
--     core, keeping quotient-specific witness threading out of that monolith.
--   * Imports the simulation core only for stable world/store transport
--     records and their primitive cast-typing operations.

open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (narrowing)
open import Coercions using (id-onlyᵈ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTerms using (renameᵗᵐ; _⟨_⟩)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  (CtxImp)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import QuotientImprecisionCompatibility using
  (SpineCastMode; gradual↓; id-only↓)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (renameᵗ)
open import
  proof.Core.Permutation.ForallPermutationProperties
  using (⊑ᵖ-rename-leftᵢ; ⊑ᵖ-rename²ᵢ)
open import proof.Core.Properties.CoercionProperties using
  (ModeRename; modeRename-id-only)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (⊑-rename-leftᵢ)
open import proof.Core.Properties.TypePreservation using (CastModeRenamer)
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ; ⊑-renameᵗ²ᵢ)
open import
  proof.Quotient.NuImprecisionPairedDownRenameProof
  using (paired-down-rename-leftᵀ; paired-down-rename²ᵀ)
open import
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibility
  using (QuotientNarrowingEliminationCompatible)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( LeftStoreRenameⁱ
  ; RelWorldEmbeddingⁱ
  ; left-embedding-cast-renamer
  ; left-narrowing-rel-embed-mode
  ; left-narrowing-rename-modeⁱ
  ; left-seal-rel-embed
  ; left-seal★-renameⁱ
  ; right-embedding-cast-renamer
  ; right-narrowing-left-renameⁱ
  ; right-narrowing-rel-embed-mode
  ; right-seal-rel-embed
  ; right-seal★-left-renameⁱ
  )


private
  left-spine-cast-mode-rel-embed :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
      {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
      {μ} →
    (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
      {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
    SpineCastMode (leftStoreⁱ ρ) μ →
    ∃[ μ′ ]
      (ModeRename τ μ μ′ × SpineCastMode (leftStoreⁱ ρ′) μ′)
  left-spine-cast-mode-rel-embed {τ = τ} emb id-only↓ =
    id-onlyᵈ , modeRename-id-only τ , id-only↓
  left-spine-cast-mode-rel-embed emb (gradual↓ mode seal★) =
    CastModeRenamer.targetᵈ (left-embedding-cast-renamer emb) mode ,
    CastModeRenamer.target-rename
      (left-embedding-cast-renamer emb) mode ,
    gradual↓
      (CastModeRenamer.target-mode
        (left-embedding-cast-renamer emb) mode)
      (left-seal-rel-embed emb mode seal★)

  right-spine-cast-mode-rel-embed :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
      {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
      {μ} →
    (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
      {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
    SpineCastMode (rightStoreⁱ ρ) μ →
    ∃[ μ′ ]
      (ModeRename σ μ μ′ × SpineCastMode (rightStoreⁱ ρ′) μ′)
  right-spine-cast-mode-rel-embed {σ = σ} emb id-only↓ =
    id-onlyᵈ , modeRename-id-only σ , id-only↓
  right-spine-cast-mode-rel-embed emb (gradual↓ mode seal★) =
    CastModeRenamer.targetᵈ (right-embedding-cast-renamer emb) mode ,
    CastModeRenamer.target-rename
      (right-embedding-cast-renamer emb) mode ,
    gradual↓
      (CastModeRenamer.target-mode
        (right-embedding-cast-renamer emb) mode)
      (right-seal-rel-embed emb mode seal★)

  left-spine-cast-mode-renameⁱ :
    ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
      {μ} →
    CastModeRenamer τ →
    (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
    SpineCastMode (leftStoreⁱ ρ) μ →
    ∃[ μ′ ]
      (ModeRename τ μ μ′ × SpineCastMode (leftStoreⁱ ρ′) μ′)
  left-spine-cast-mode-renameⁱ {τ = τ} modeτ renameρ id-only↓ =
    id-onlyᵈ , modeRename-id-only τ , id-only↓
  left-spine-cast-mode-renameⁱ modeτ renameρ
      (gradual↓ mode seal★) =
    CastModeRenamer.targetᵈ modeτ mode ,
    CastModeRenamer.target-rename modeτ mode ,
    gradual↓
      (CastModeRenamer.target-mode modeτ mode)
      (left-seal★-renameⁱ modeτ renameρ mode seal★)

  right-spine-cast-mode-left-renameⁱ :
    ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
      {μ} →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    SpineCastMode (rightStoreⁱ ρ) μ →
    SpineCastMode (rightStoreⁱ ρ′) μ
  right-spine-cast-mode-left-renameⁱ renameρ id-only↓ = id-only↓
  right-spine-cast-mode-left-renameⁱ renameρ
      (gradual↓ mode seal★) =
    gradual↓ mode (right-seal★-left-renameⁱ renameρ seal★)


rel-world-paired-down-embedᵀ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ C C′ D D′ pC d d′ s s′ qD μ μ′} →
  (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ C ⊑ renameᵗ σ C′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ pC →
  SpineCastMode (leftStoreⁱ ρ) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ C ⊒ D →
  CastShape.narrowing ⊢ᶜ d ⦂ s →
  SpineCastMode (rightStoreⁱ ρ) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD s s′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ (M ⟨ d ⟩)
      ⊑ renameᵗᵐ σ (M′ ⟨ d′ ⟩)
    ⦂ renameᵗ τ D ⊑ᵖ renameᵗ σ D′
    ∶ ⊑ᵖ-rename²ᵢ assm hτ hσ qD
rel-world-paired-down-embedᵀ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    emb M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape
    square compatible
    with left-spine-cast-mode-rel-embed emb mode
       | right-spine-cast-mode-rel-embed emb mode′
rel-world-paired-down-embedᵀ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    emb M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape
    square compatible
    | μᴿ , mode-rename , modeᴿ
    | μ′ᴿ , mode′-rename , mode′ᴿ =
  paired-down-rename²ᵀ M⊑M′ modeᴿ
    (left-narrowing-rel-embed-mode emb mode-rename d⊒)
    d-shape mode′ᴿ
    (right-narrowing-rel-embed-mode emb mode′-rename d′⊒)
    d′-shape square compatible


left-rename-paired-downᵀ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
    {assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ C C′ D D′ d d′ s s′ qD μ μ′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  CastModeRenamer τ →
  (renameρ : LeftStoreRenameⁱ τ assm hτ ρ ρ′) →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ C ⊑ C′ ∶ ⊑-rename-leftᵢ τ assm hτ pC →
  SpineCastMode (leftStoreⁱ ρ) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ C ⊒ D →
  CastShape.narrowing ⊢ᶜ d ⦂ s →
  SpineCastMode (rightStoreⁱ ρ) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD s s′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ (M ⟨ d ⟩) ⊑ M′ ⟨ d′ ⟩
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ qD
left-rename-paired-downᵀ
    {τ = τ} {assm = assm} {hτ = hτ}
    modeτ renameρ M⊑M′ mode d⊒ d-shape
    mode′ d′⊒ d′-shape square compatible
    with left-spine-cast-mode-renameⁱ modeτ renameρ mode
left-rename-paired-downᵀ
    {τ = τ} {assm = assm} {hτ = hτ}
    modeτ renameρ M⊑M′ mode d⊒ d-shape
    mode′ d′⊒ d′-shape square compatible
    | μᴿ , mode-rename , modeᴿ =
  paired-down-rename-leftᵀ M⊑M′ modeᴿ
    (left-narrowing-rename-modeⁱ mode-rename renameρ d⊒)
    d-shape
    (right-spine-cast-mode-left-renameⁱ renameρ mode′)
    (right-narrowing-left-renameⁱ renameρ d′⊒)
    d′-shape square compatible
