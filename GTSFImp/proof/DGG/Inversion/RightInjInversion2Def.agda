module proof.DGG.Inversion.RightInjInversion2Def where

-- File Charter:
--   * States the M3 version-2 right-injection inversion theorem.
--   * Uses the frozen `RebaseAt` relation directly; no ParkedWorld or
--     OpenStrata premise appears in the public statement.
--   * Depends on the stable SpineValueDef surface and CastTermImprecision2.
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
open import CastTerms using (Term; Value; _⟨_⟩)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

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
