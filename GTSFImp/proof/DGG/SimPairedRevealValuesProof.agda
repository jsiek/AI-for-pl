module proof.DGG.SimPairedRevealValuesProof where

-- File Charter:
--   * Provides a checked residualized skeleton for paired reveal value
--     simulation.
--   * Names the paired conceal/reveal keep row separately from the paired
--     id-reveal target-replay row.
--   * Refutes source frame steps from value irreducibility.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Unit.Base using (⊤; tt)

open import Types using (Ty; TyCtx)
open import Conversion using (Conv↑)
open import CastTerms using (Term; Value; _↑_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ; pure-step
  ; id-reveal
  ; conceal-reveal
  ; blame-reveal
  ; ξ-reveal
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.CatchupToMorePreciseDef
  using (ValueCatchupResult; source-reveal-boundary)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using
  ( World
  ; ImpEnvMono
  ; RebaseAt
  ; sourceStoreʷ
  ; targetStoreʷ
  ; same-[]
  ; _⊢↑[_]_
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )
open import proof.DGG.SimPairedRevealValuesDef
  using (SimPairedRevealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


PairedRevealRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ [] ⊢² M ⊑ M′ ∶ p → Set
PairedRevealRel (CTI2.reveal⊑reveal² _ _ _ _ _ _ _) = ⊤
PairedRevealRel _ = Data.Empty.⊥

IdRevealStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
IdRevealStep (pure-step (id-reveal _)) = ⊤
IdRevealStep _ = Data.Empty.⊥

ConcealRevealStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ConcealRevealStep (pure-step (conceal-reveal _)) = ⊤
ConcealRevealStep _ = Data.Empty.⊥


record SimPairedRevealValuesResiduals : Set₁ where
  field
    paired-id-reveal-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W Wᵖ : World Δᴸ Δᴿ Δ}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
        {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (mono : ImpEnvMono W Wᵖ)
      → (rebase : RebaseAt W Wᵖ Xᴸ Xᴿ)
      → sourceStoreʷ W ⊢↑[ just Xᴸ ] c
      → targetStoreʷ W ⊢↑[ just Xᴿ ] c′
      → (rel : W ∣ [] ⊢² V ↑ c ⊑ M′ ↑ c′ ∶ q)
      → PairedRevealRel rel
      → Value V
      → (step : V ↑ c —→[ χᴸ ] N)
      → IdRevealStep step
      → ValueCatchupResult
          {W = W} {Wᵖ = Wᵖ} {kind = source-reveal-boundary}
          {Xᴸ? = just Xᴸ} {Xᴿ? = just Xᴿ}
          {V = V} {M′ = M′} {A = A} {B = A′}
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)

    paired-conceal-reveal-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W Wᵖ : World Δᴸ Δᴿ Δ}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
        {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
        {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (mono : ImpEnvMono W Wᵖ)
      → (rebase : RebaseAt W Wᵖ Xᴸ Xᴿ)
      → sourceStoreʷ W ⊢↑[ just Xᴸ ] c
      → targetStoreʷ W ⊢↑[ just Xᴿ ] c′
      → (rel : W ∣ [] ⊢² V ↑ c ⊑ M′ ↑ c′ ∶ q)
      → PairedRevealRel rel
      → Value V
      → (step : V ↑ c —→[ χᴸ ] N)
      → ConcealRevealStep step
      → ValueCatchupResult
          {W = W} {Wᵖ = Wᵖ} {kind = source-reveal-boundary}
          {Xᴸ? = just Xᴸ} {Xᴿ? = just Xᴿ}
          {V = V} {M′ = M′} {A = A} {B = A′}
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
          (M′ ↑ c′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)


sim-paired-reveal-values-with :
  SimPairedRevealValuesResiduals → SimPairedRevealValuesᵀ
sim-paired-reveal-values-with residuals parked mono rebase c⊢ c′⊢
    rel q vV step@(pure-step (id-reveal _)) caught =
  SimPairedRevealValuesResiduals.paired-id-reveal-row residuals
    parked mono rebase c⊢ c′⊢
    (CTI2.reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ rel q) tt
    vV step tt caught
sim-paired-reveal-values-with residuals parked mono rebase c⊢ c′⊢
    rel q vV step@(pure-step (conceal-reveal _)) caught =
  SimPairedRevealValuesResiduals.paired-conceal-reveal-row residuals
    parked mono rebase c⊢ c′⊢
    (CTI2.reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ rel q) tt
    vV step tt caught
sim-paired-reveal-values-with residuals _ _ _ _ _ _ _ ()
    (pure-step blame-reveal) _
sim-paired-reveal-values-with residuals _ _ _ _ _ _ _ vV
    (ξ-reveal step _) _ =
  ⊥-elim (value-no-step vV step)
