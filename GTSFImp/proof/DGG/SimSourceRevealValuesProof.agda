module proof.DGG.SimSourceRevealValuesProof where

-- File Charter:
--   * Implements the source-only reveal value simulation rows that are
--     already supported by the current catchup package.
--   * Leaves the conceal/reveal keep row as a named residual, to be supplied
--     by the two-sided/source-opened peel plumbing.
--   * Refutes source frame steps from value irreducibility.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit.Base using (⊤; tt)

open import Types using (Ty; TyCtx; TyVar)
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
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.CatchupToMorePreciseDef
  using
    ( ValueCatchupResult
    ; boundary-source-reveal
    ; source-reveal-boundary
    ; targetPivotᴸ
    )
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve; evolve-keepᴸ)
open CTI2 using
  ( World
  ; ImpEnvMono
  ; RebaseAtᴸ
  ; sourceStoreʷ
  ; same-[]
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )
open import proof.DGG.SimSourceRevealValuesDef
  using (SimSourceRevealValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


SourceRevealRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ [] ⊢² M ⊑ M′ ∶ p → Set
SourceRevealRel (CTI2.reveal⊑² _ _ _ _ _ _) = ⊤
SourceRevealRel _ = Data.Empty.⊥

ConcealRevealStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ConcealRevealStep (pure-step (conceal-reveal _)) = ⊤
ConcealRevealStep _ = Data.Empty.⊥


record SimSourceRevealValuesResiduals : Set₁ where
  field
    source-conceal-reveal-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W Wᵖ : World Δᴸ Δᴿ Δ}
        {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
        {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
        {Xᴸ? : Maybe (TyVar Δᴸ)} {c : Conv↑ Δᴸ A A′}
        {q : A′ ⊑ᵂ⟨ W ⟩ B}
      → ParkedWorld W
      → (mono : ImpEnvMono W Wᵖ)
      → (rebase : RebaseAtᴸ W Wᵖ Xᴸ?)
      → sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c
      → (rel : W ∣ [] ⊢² V ↑ c ⊑ M′ ∶ q)
      → SourceRevealRel rel
      → Value V
      → (step : V ↑ c —→[ χᴸ ] N)
      → ConcealRevealStep step
      → ValueCatchupResult
          {W = W} {Wᵖ = Wᵖ} {kind = source-reveal-boundary}
          {Xᴸ? = Xᴸ?} {Xᴿ? = targetPivotᴸ rebase}
          {V = V} {M′ = M′} {A = A} {B = B}
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
        Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
        Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
          (M′ —↠[ χsᴿ ] N′) ×
          ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)


sim-source-reveal-values-with :
  SimSourceRevealValuesResiduals → SimSourceRevealValuesᵀ
sim-source-reveal-values-with residuals _ _ CTI2.rebase-idᴸ
    Conv.⊢↑-idˣ _ _ vV (pure-step (id-reveal _))
    (Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , .W′ , _ ,
      boundary-source-reveal _ CTI2.tag-rebase-idᴸ , q′ ,
      _ , M′↠V′ , _ , evol , _ , _ , rel′) =
  Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , q′ ,
  M′↠V′ , evolve-keepᴸ evol , rel′
sim-source-reveal-values-with residuals parked mono rebase c⊢
    rel q vV step@(pure-step (conceal-reveal _)) caught =
  SimSourceRevealValuesResiduals.source-conceal-reveal-row residuals
    parked mono rebase c⊢
    (CTI2.reveal⊑² mono rebase same-[] c⊢ rel q) tt
    vV step tt caught
sim-source-reveal-values-with residuals _ _ _ _ _ _ ()
    (pure-step blame-reveal) _
sim-source-reveal-values-with residuals _ _ _ _ _ _ vV (ξ-reveal step _) _ =
  ⊥-elim (value-no-step vV step)
