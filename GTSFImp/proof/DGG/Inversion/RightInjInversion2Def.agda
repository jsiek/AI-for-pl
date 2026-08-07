module proof.DGG.Inversion.RightInjInversion2Def where

-- File Charter:
--   * States the M3 version-2 right-injection inversion theorem.
--   * Uses the frozen `RebaseAt` relation directly; no ParkedWorld or
--     OpenStrata premise appears in the public statement.
--   * Depends on the stable SpineValueDef surface and CastTermImprecision2.

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!)
open import CastTerms using (Term; Value; _⟨_⟩)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

RightInjInversion² : Set
RightInjInversion² =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ} {A : Ty Δᴸ} {H : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
    {p : A ⊑ᵂ⟨ W ⟩ ★}
  → SpineValue M
  → Value N
  → W ∣ γ ⊢² M
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : A ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² M ⊑ N ∶ q
