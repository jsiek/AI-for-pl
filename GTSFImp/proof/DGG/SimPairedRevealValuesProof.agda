module proof.DGG.SimPairedRevealValuesProof where

-- File Charter:
--   * Provides a checked residualized skeleton for paired reveal value
--     simulation.
--   * Names the paired conceal/reveal keep row separately from the paired
--     id-reveal target-replay row.
--   * Threads the paired constructor's generator evidence without a wrapper.
--   * Refutes source frame steps from value irreducibility.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

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
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition)
open import proof.DGG.CatchupToMorePreciseDef
  using (ValueCatchupResult; source-reveal-boundary)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  (World;
   ImpEnvMono;
   RebaseAt;
   sourceStoreʷ;
   targetStoreʷ;
   same-[];
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.DGG.SimPairedRevealValuesDef
  using (SimPairedRevealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


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
        {Rᴸ : Ty Δᴸ} {Rᴿ : Ty Δᴿ}
        {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (c⊢ : sourceStoreʷ W Conv.⊢↑[ Xᴸ ⦂ Rᴸ ] c)
      → (c′⊢ : targetStoreʷ W Conv.⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
      → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
      → revealGeneratorPosition c⊢ ≢ generator-absent
      → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
      → (mono : ImpEnvMono W Wᵖ)
      → (rebase : RebaseAt W Wᵖ Xᴸ Xᴿ)
      → (rel : W ∣ [] ⊢² V ↑ c ⊑ M′ ↑ c′ ∶ q)
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
        {Rᴸ : Ty Δᴸ} {Rᴿ : Ty Δᴿ}
        {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
        {q : B ⊑ᵂ⟨ W ⟩ B′}
      → ParkedWorld W
      → (c⊢ : sourceStoreʷ W Conv.⊢↑[ Xᴸ ⦂ Rᴸ ] c)
      → (c′⊢ : targetStoreʷ W Conv.⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
      → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
      → revealGeneratorPosition c⊢ ≢ generator-absent
      → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
      → (mono : ImpEnvMono W Wᵖ)
      → (rebase : RebaseAt W Wᵖ Xᴸ Xᴿ)
      → (rel : W ∣ [] ⊢² V ↑ c ⊑ M′ ↑ c′ ∶ q)
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
sim-paired-reveal-values-with residuals parked c⊢ c′⊢ aligned
    nonabsent represented mono rebase
    rel q vV step@(pure-step (id-reveal _)) caught =
  SimPairedRevealValuesResiduals.paired-id-reveal-row residuals
    parked c⊢ c′⊢ aligned nonabsent represented mono rebase
    (CTI2.reveal⊑reveal² c⊢ c′⊢ aligned nonabsent represented mono
      rebase same-[] rel q)
    vV step tt caught
sim-paired-reveal-values-with residuals parked c⊢ c′⊢ aligned
    nonabsent represented mono rebase
    rel q vV step@(pure-step (conceal-reveal _)) caught =
  SimPairedRevealValuesResiduals.paired-conceal-reveal-row residuals
    parked c⊢ c′⊢ aligned nonabsent represented mono rebase
    (CTI2.reveal⊑reveal² c⊢ c′⊢ aligned nonabsent represented mono
      rebase same-[] rel q)
    vV step tt caught
sim-paired-reveal-values-with residuals _ _ _ _ _ _ _ _ _ _ ()
    (pure-step blame-reveal) _
sim-paired-reveal-values-with residuals _ _ _ _ _ _ _ _ _ _ vV
    (ξ-reveal step _) _ =
  ⊥-elim (value-no-step vV step)
