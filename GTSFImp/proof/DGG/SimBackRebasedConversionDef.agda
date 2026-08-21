module proof.DGG.SimBackRebasedConversionDef where

-- File Charter:
--   * States backward simulation for source-rebased reveal and for paired
--     reveal/conceal body frames whose premise relation uses a rebased world.
--   * Exposes the live conversion, generator, representation, and rebase
--     evidence with the full simulation conclusion at the outer world.
--   * Contains no rebased-conversion simulation proof and introduces no case
--     classifier or result wrapper.

open import Data.Fin using (Fin)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyCtx)
open import TyStore using (_∋_⦂_)
open import Conversion using (Conv↑; Conv↓)
import Conversion as Conv
open import CastTerms using (Term; blame; _↑_; _↓_)
open import Reduction using
  ( StoreChange
  ; StoreChanges
  ; applyTy
  ; applyTys
  ; applyVar
  ; _—→[_]_
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.ConversionPivotAlignment using
  ( generator-absent
  ; revealGeneratorPosition
  ; concealGeneratorPosition
  )
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTX using
  ( World
  ; ImpEnvMono
  ; RebaseAt
  ; sourceStoreʷ
  ; targetStoreʷ
  ; _⊑ᵂ⟨_⟩_
  )
open CTI2 using (_∣_⊢²_⊑_∶_)


SimBackSourceRevealRebaseᵀ : Set
SimBackSourceRevealRebaseᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A A′ Rᴸ : Ty Δᴸ} {B Rᴿ : Ty Δᴿ}
    {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {c : Conv↑ Δᴸ A A′} {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
    {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (c⊢ : sourceStoreʷ W Conv.⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → revealGeneratorPosition c⊢ ≢ generator-absent
  → targetStoreʷ W ∋ Xᴿ ⦂ Rᴿ
  → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
  → ImpEnvMono W Wᵖ
  → RebaseAt W Wᵖ Xᴸ Xᴿ
  → Wᵖ ∣ [] ⊢² M ⊑ M′ ∶ p
  → (q : A′ ⊑ᵂ⟨ W ⟩ B)
  → M′ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTys χsᴸ A′ ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B ]
      (M ↑ c —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ˢ []ˢ) W W′ ×
      (W′ ∣ [] ⊢² N ⊑ N′ ∶ r))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M ↑ c —↠[ χsᴸ ] blame))


SimBackPairedRevealFrameᵀ : Set
SimBackPairedRevealFrameᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A B Rᴸ : Ty Δᴸ} {A′ B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′} {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (c⊢ : sourceStoreʷ W Conv.⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → (c′⊢ : targetStoreʷ W Conv.⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
  → revealGeneratorPosition c⊢ ≢ generator-absent
  → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
  → ImpEnvMono W Wᵖ
  → RebaseAt W Wᵖ Xᴸ Xᴿ
  → Wᵖ ∣ [] ⊢² M ⊑ M′ ∶ p
  → (q : B ⊑ᵂ⟨ W ⟩ B′)
  → M′ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTys χsᴸ B ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B′ ]
      (M ↑ c —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ˢ []ˢ) W W′ ×
      (W′ ∣ [] ⊢² N ⊑
        N′ ↑ Conv.rename↑ (applyVar χᴿ) c′ ∶ r))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M ↑ c —↠[ χsᴸ ] blame))


SimBackPairedConcealFrameᵀ : Set
SimBackPairedConcealFrameᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ′} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {N′ : Term Δᴿ′}
    {A B Rᴸ : Ty Δᴸ} {A′ B′ Rᴿ : Ty Δᴿ}
    {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′} {χᴿ : StoreChange Δᴿ Δᴿ′}
  → ParkedWorld W
  → (c⊢ : sourceStoreʷ W Conv.⊢↓[ Xᴸ ⦂ Rᴸ ] c)
  → (c′⊢ : targetStoreʷ W Conv.⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
  → concealGeneratorPosition c⊢ ≢ generator-absent
  → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
  → ImpEnvMono W Wᵖ
  → RebaseAt Wᵖ W Xᴸ Xᴿ
  → Wᵖ ∣ [] ⊢² M ⊑ M′ ∶ p
  → (q : B ⊑ᵂ⟨ W ⟩ B′)
  → M′ —→[ χᴿ ] N′
  → (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
    Σ[ N ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ′ Δᴿ′ Δ′ ]
    Σ[ r ∈ applyTys χsᴸ B ⊑ᵂ⟨ W′ ⟩ applyTy χᴿ B′ ]
      (M ↓ c —↠[ χsᴸ ] N) ×
      ParkedEvolve χsᴸ (χᴿ ∷ˢ []ˢ) W W′ ×
      (W′ ∣ [] ⊢² N ⊑
        N′ ↓ Conv.rename↓ (applyVar χᴿ) c′ ∶ r))
    ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        (M ↓ c —↠[ χsᴸ ] blame))
