module proof.DGG.SimBackSourceLambdaDef where

-- File Charter:
--   * States the ordinary and smart source-lambda cases of backward
--     simulation whose premise relation lives under a left-lifted world.
--   * Exposes the live lambda-rule evidence and the full simulation
--     conclusion directly, without a case classifier or result wrapper.
--   * Contains no source-lambda simulation proof.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat as Nat using ()
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; `∀)
open import CastTerms using
  (Term; Value; blame; ⟨_,_,_⟩; _⊢_⦂_; Λ_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  ( World
  ; SmartCommaLiftᴸ
  ; liftWorldLeft
  ; targetStoreʷ
  ; _⊑ᵂ⟨_⟩_
  )
open CTI2 using (_∣_⊢²_⊑_∶_)


SimBackSourceLambdaᵀ : Set
SimBackSourceLambdaᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W : World Δᴸ Δᴿ Δ}
    {V : Term (Nat.suc Δᴸ)} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ liftWorldLeft W ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → NonVar A
  → Fin.zero ∈ᵗ A
  → Value V
  → ⟨ Δᴿ , targetStoreʷ W , [] ⟩ ⊢ M′ ⦂ B
  → liftWorldLeft W ∣ [] ⊢² V ⊑ M′ ∶ p
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
  → M′ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTys χsᴸ (`∀ A) ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (Λ V —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ˢ []ˢ) W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (Λ V —↠[ χsᴸ ] blame))


SimBackSmartSourceLambdaᵀ : Set
SimBackSmartSourceLambdaᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′ Δᵐ} {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {V : Term (Nat.suc Δᴸ)} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵐ ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → NonVar A
  → Fin.zero ∈ᵗ A
  → SmartCommaLiftᴸ W Wᵐ
  → Value V
  → ⟨ Δᴿ , targetStoreʷ W , [] ⟩ ⊢ M′ ⦂ B
  → Wᵐ ∣ [] ⊢² V ⊑ M′ ∶ p
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
  → M′ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTys χsᴸ (`∀ A) ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (Λ V —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ˢ []ˢ) W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (Λ V —↠[ χsᴸ ] blame))
