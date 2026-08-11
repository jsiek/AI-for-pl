module TargetExtendScratch where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyVar; renameᵗ)
open import Consistency using (_↪ᵗ_; keep; toRenameᵗ; wk↪ᵗ)
open import Imprecision using (X⊑★)
open import Conversion using (Conv↑; rename↑)
open import CastTerms using (Term; renameᵗᵐ; _↑_)
open import proof.TypeInTermSubst using (StoreRename)
open import proof.DGG.CenterRename using (preimage?)
import proof.DGG.CastTermImprecision2 as CTI2

open CTI2 using
  ( World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_
  ; RebaseAtᴿ; ImpEnvMono; SameCtx; _⊢↑[_]_
  )

mapPivot : ∀ {Δ Δ′}
  → (TyVar Δ → TyVar Δ′)
  → Maybe (TyVar Δ)
  → Maybe (TyVar Δ′)
mapPivot ρ (just X) = just (ρ X)
mapPivot ρ nothing = nothing

record TargetInsert {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    (ρ : Δᴿ ↪ᵗ Δᴿ′)
    (π : Δ ↪ᵗ Δ′)
    (W : World Δᴸ Δᴿ Δ)
    (W′ : World Δᴸ Δᴿ′ Δ′) : Set₁ where
  field
    sourceStore-kept : CTI2.sourceStoreʷ W′ ≡ CTI2.sourceStoreʷ W

    transport⊑ᵂ : ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B
      → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B

    targetStore-rename :
      StoreRename (toRenameᵗ ρ) (CTI2.targetStoreʷ W)
        (CTI2.targetStoreʷ W′)

    source-resolve : ∀ Xᴸ
      → CTI2.resolveVar (CTI2.sourceStoreʷ W′) Xᴸ
          ≡ CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ

    target-resolve : ∀ Xᴿ
      → CTI2.resolveVar (CTI2.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ)
          ≡ renameᵗ (toRenameᵗ ρ)
              (CTI2.resolveVar (CTI2.targetStoreʷ W) Xᴿ)

    align-insert : ∀ {Xᴸ Xᴿ}
      → CTI2.CenterAligned W Xᴸ Xᴿ
      → CTI2.CenterAligned W′ Xᴸ (toRenameᵗ ρ Xᴿ)

    source-insert : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W′) Xᴸ
          ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)

    target-insert : ∀ Xᴿ
      → toRenameᵗ (CTI2.ηᴿʷ W′) (toRenameᵗ ρ Xᴿ)
          ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)

    impEnv-insert : ∀ Z
      → CTI2.impEnvʷ W′ (toRenameᵗ π Z) ≡ CTI2.impEnvʷ W Z

    impEnv-off-insert : ∀ {Z′}
      → preimage? π Z′ ≡ nothing
      → CTI2.impEnvʷ W′ Z′ ≡ X⊑★

    target-source-reflect : ∀ {Xᴸ Y′}
      → CTI2.CenterAligned W′ Xᴸ Y′
      → Σ[ Y ∈ TyVar Δᴿ ]
          Y′ ≡ toRenameᵗ ρ Y × CTI2.CenterAligned W Xᴸ Y

open TargetInsert public

mapCtxᵀ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W′
  → CtxImp W
  → CtxImp W′
mapCtxᵀ ins [] = []
mapCtxᵀ {ρ = ρ} ins (CTI2.ctx-imp A B p ∷ γ) =
  CTI2.ctx-imp A (renameᵗ (toRenameᵗ ρ) B) (transport⊑ᵂ ins p) ∷
    mapCtxᵀ ins γ

TargetExtendOPEᵀ : Set₁
TargetExtendOPEᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : TargetInsert ρ π W W′)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W′ ∣ mapCtxᵀ ins γ
      ⊢² M ⊑ renameᵗᵐ ρ M′ ∶ transport⊑ᵂ ins p

RevealRightCommuteᵀ : Set₁
RevealRightCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → RebaseAtᴿ W Wᵖ Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      RebaseAtᴿ W⁺ Wᵖ⁺
        (mapPivot (toRenameᵗ ρ) Xᴿ?)

RevealRightWrapperᵀ : TargetExtendOPEᵀ → RevealRightCommuteᵀ → Set₁
RevealRightWrapperᵀ target-extend commute =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {Xᴿ? : Maybe (TyVar Δᴿ)}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
    {c′ : Conv↑ Δᴿ B B′}
  → (ins : TargetInsert ρ π W W⁺)
  → ImpEnvMono W Wᵖ
  → RebaseAtᴿ W Wᵖ Xᴿ?
  → SameCtx γ γᵖ
  → CTI2.targetStoreʷ W ⊢↑[ Xᴿ? ] c′
  → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
  → W⁺ ∣ mapCtxᵀ ins γ
      ⊢² M ⊑ renameᵗᵐ ρ (M′ ↑ c′)
        ∶ transport⊑ᵂ ins q
