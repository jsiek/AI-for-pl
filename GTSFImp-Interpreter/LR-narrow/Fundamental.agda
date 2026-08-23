module LR-narrow.Fundamental where

-- File Charter:
--   * Exposes derivation-indexed one-sided universal fundamental cases.
--   * Uses the phase-aware body motive from LR-narrow.TermRelation.
--   * Delegates constructor-facing proof scripts to the proof namespace.

open import Data.Nat using (suc)
import Data.Fin as Fin

open import Types
open import CastTerms
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.Fundamental as Proof

right-universal-fundamental : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
    (nonvar : NonVar Aᴾ)
    (occurs : Fin.zero ∈ᵗ Aᴾ)
    (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
    (vVᴾ : Value Vᴾ)
    (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
      CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ)
    (body : CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Mᴵ ∶ p)
    (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → RightUniversalBodyFundamentalProperty
      {W = W} {Γ = Γ}
      {Wᵇ = CTI.liftWorldLeft I.X⊑★ (forgetWorld W)} {Γᵇ = Γ′}
      {p = p} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ} q body
  → FundamentalProperty
      (CTIR.Λ⊑² nonvar occurs liftΓ vVᴾ target⊢ body q)
right-universal-fundamental = Proof.right-universal-fundamental

right-universal-smart-fundamental : ∀ {Δᴾ Δᴵ Δᶜ Δᵐ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Wᵐ : CTI.World (suc Δᴾ) Δᴵ Δᵐ}
    {Γᵐ : CTI.CtxImp Wᵐ}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨ Wᵐ ⟩ Bᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
    (nonvar : NonVar Aᴾ)
    (occurs : Fin.zero ∈ᵗ Aᴾ)
    (smart : CTI.SmartCommaLiftᴸ (forgetWorld W) Wᵐ)
    (liftΓ : CTI.SmartLiftCtxᴸ Γ Γᵐ)
    (vVᴾ : Value Vᴾ)
    (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
      CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ)
    (body : Wᵐ ∣ Γᵐ ⊢² Vᴾ ⊑ Mᴵ ∶ p)
    (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → RightUniversalBodyFundamentalProperty
      {W = W} {Γ = Γ} {Wᵇ = Wᵐ} {Γᵇ = Γᵐ}
      {p = p} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ} q body
  → FundamentalProperty
      (CTIR.Λ⊑²-smart-comma nonvar occurs smart liftΓ vVᴾ target⊢
        body q)
right-universal-smart-fundamental =
  Proof.right-universal-smart-fundamental
