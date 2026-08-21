module proof.DGG.SimPairedConcealValuesDef where

-- File Charter:
--   * States paired conceal closing after both bodies are related values.
--   * Exposes generator representations and structural-position agreement.
--   * Takes the catchup result as evidence; it does not perform catchup.
--   * Contains no paired-conceal value proof.

open import Data.Fin using (Fin)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyCtx)
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
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; concealGeneratorPosition)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.CatchupToMorePreciseDef
  using (ValueCatchupResult; source-conceal-boundary)
open CTX using
  (World;
   ImpEnvMono;
   RebaseAt;
   sourceStoreʷ;
   targetStoreʷ;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SimPairedConcealValuesᵀ : Set₁
SimPairedConcealValuesᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {N : Term Δᴸ′}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {Rᴸ : Ty Δᴸ} {Rᴿ : Ty Δᴿ}
    {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
  → ParkedWorld W
  → (c⊢ : sourceStoreʷ W Conv.⊢↓[ Xᴸ ⦂ Rᴸ ] c)
  → (c′⊢ : targetStoreʷ W Conv.⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
  → concealGeneratorPosition c⊢ ≢ generator-absent
  → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
  → (mono : ImpEnvMono W Wᵖ)
  → (rebase : RebaseAt Wᵖ W Xᴸ Xᴿ)
  → Wᵖ ∣ [] ⊢² V ⊑ M′ ∶ p
  → (q : B ⊑ᵂ⟨ W ⟩ B′)
  → Value V
  → V ↓ c —→[ χᴸ ] N
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = source-conceal-boundary}
      {Xᴸ? = just Xᴸ} {Xᴿ? = just Xᴿ}
      {V = V} {M′ = M′} {A = A} {B = A′}
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ applyTys χsᴿ B′ ]
      (M′ ↓ c′ —↠[ χsᴿ ] N′) ×
      ParkedEvolve (χᴸ ∷ˢ []ˢ) χsᴿ W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r)
