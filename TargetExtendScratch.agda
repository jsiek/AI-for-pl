module TargetExtendScratch where

open import Types using (Ty; renameᵗ)
open import Imprecision using (VarImp)
open import Consistency using (_↪ᵗ_; keep; toRenameᵗ; wk↪ᵗ)
open import CastTerms using (Term; renameᵗᵐ)
import proof.DGG.CastTermImprecision2 as CTI2

open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

data TargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    → (ρ : Δᴿ ↪ᵗ Δᴿ′)
    → World Δᴸ Δᴿ Δ
    → World Δᴸ Δᴿ′ Δ′
    → Set₁ where
  insert-front : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    → TargetInsert wk↪ᵗ W (CTI2.rightOnlyWorld W B)

  insert-keep : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W′ : World Δᴸ Δᴿ′ Δ′}
    → TargetInsert ρ W W′
    → (v : VarImp)
    → TargetInsert (keep ρ)
        (CTI2.liftWorldBoth v W)
        (CTI2.liftWorldBoth v W′)

  insert-left : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W′ : World Δᴸ Δᴿ′ Δ′}
    → TargetInsert ρ W W′
    → (v : VarImp)
    → TargetInsert ρ
        (CTI2.liftWorldLeft v W)
        (CTI2.liftWorldLeft v W′)

TargetExtendOPEᵀ : Set₁
TargetExtendOPEᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : TargetInsert ρ W W′)
  → (transport⊑ᵂ : ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B
      → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B)
  → (mapCtxᵀ : CtxImp W → CtxImp W′)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W′ ∣ mapCtxᵀ γ ⊢² M ⊑ renameᵗᵐ ρ M′ ∶ transport⊑ᵂ p
