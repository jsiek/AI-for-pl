module RightInjInversion2StatementScratch where

-- File Charter:
--   * Scratch validation for the M3 right-injection inversion statement.
--   * States the no-ParkedWorld version as a Set-level carrier.
--   * Checks the consumer-facing application shape on an Examples2 instance.
--   * Records the M2 negative center-crossing premise exposed by the probe.

open import Data.List using ([])
open import Primitives using (κℕ)
open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!)
open import CastTerms using (Term; Value; _⟨_⟩; _↓_; $; seal)
import CastTerms as CTerms
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Example12Worlds as Ex12
import proof.DGG.Examples2 as Ex2
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.CenterCrossingProbe as CCP
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

RightInjInversion²Statement : Set
RightInjInversion²Statement =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ} {A : Ty Δᴸ} {H : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
    {p : A ⊑ᵂ⟨ W ⟩ ★}
  → SVD.SpineValue M
  → Value N
  → W ∣ γ ⊢² M
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : A ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² M ⊑ N ∶ q

example12-source-spine :
  SVD.SpineValue (($ (κℕ 7)) ↓ Ex2.example12-source-X-seal)
example12-source-spine = SVD.sv-seal (SVD.sv-$ (κℕ 7))

example12-target-value :
  Value (($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
example12-target-value = CTerms.$ (κℕ 7) CTerms.↓ CTerms.seal

example12-consumes-no-parked :
  RightInjInversion²Statement
  → Ex12.example12-world-X ∣ [] ⊢²
      ($ (κℕ 7)) ↓ Ex2.example12-source-X-seal
      ⊑ ($ (κℕ 7)) ↓ Ex2.example12-target-X-seal ∶
        Ex2.example12-X-var⊑
example12-consumes-no-parked inv =
  inv example12-source-spine example12-target-value
    Ex2.example12-target-X!-checkpoint₃ Ex2.example12-X-var⊑

old-center-crossing-target-input-unconstructible =
  CCP.no-center-crossing-target

old-center-crossing-outerᴿ-input-unconstructible =
  CCP.no-center-crossing-outerᴿ
