{-# OPTIONS --safe #-}

module proof.DGG.Inversion.RightInjInversion2Def where

-- File Charter:
--   * States the M3 version-2 right-injection inversion theorem.
--   * Uses the canonical complete-context world and cast-term imprecision.
--   * Depends only on the stable SpineValueDef surface and the live relation.
--
-- Refuted route, kept here so the bare-seal proof does not retry it:
-- peeling the target tag first asks a wrapper head such as `Λ⊑²` to prove
-- a premise with a non-variable source type against a right variable,
-- schematically
--
--   nonvar-left ⊑ ＇Y
--
-- But `SPT.right-var-obligation-view` forces the left side of any
-- `A ⊑ ＇Y` obligation to be a variable, while `Λ⊑²` carries `NonVar A`
-- and a bound-variable occurrence premise.  Thus the tag-peel-first family
-- (including rebuilding a wrapper head against a lifted target variable)
-- is dead; the proof must rebuild at the target-chain terminus instead.

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!)
open import CastTerms using (Ctx; Δᵉ; Term; Value; _⟨_⟩)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTI using (_⊢²_⊑_∶_)

RightInjInversion² : Set
RightInjInversion² =
  ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {N : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {H : Ty (Δᵉ Γᴿ)}
    {ν : Env∼ (Δᵉ Γᴿ)}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
    {p : A ⊑ᵀ⟨ γ ⟩ ★}
  → SpineValue M
  → Value N
  → γ ⊢² M
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : A ⊑ᵀ⟨ γ ⟩ H)
  → γ ⊢² M ⊑ N ∶ q
