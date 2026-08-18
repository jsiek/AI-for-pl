module proof.DGG.SimSourceConcealValuesDef where

-- File Charter:
--   * States source-only conceal closing after the target body has caught up
--     to a related value.
--   * Takes the catchup result as evidence; it does not perform catchup.
--   * Contains no source-conceal value proof.

open import Data.List using ([])
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; TyVar)
open import Conversion using (Conv↓)
open import CastTerms using (Term; Value; _↓_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.CatchupToMorePreciseDef
  using (ValueCatchupResult; source-conceal-boundary)
open CTI2 using
  ( World
  ; SourceConcealOK
  ; ImpEnvMono
  ; TagRebaseAtᴸ
  ; sourceStoreʷ
  ; _⊢↓[_]_
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


SimSourceConcealValuesᵀ : Set₁
SimSourceConcealValuesᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {c : Conv↓ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → SourceConcealOK Wᵖ V c Xᴿ? M′
  → (mono : ImpEnvMono W Wᵖ)
  → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
  → Wᵖ ∣ [] ⊢² V ⊑ M′ ∶ p
  → (q : A′ ⊑ᵂ⟨ W ⟩ B)
  → Value V
  → V ↓ c —→[ χᴸ ] N
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = source-conceal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTy χᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)
