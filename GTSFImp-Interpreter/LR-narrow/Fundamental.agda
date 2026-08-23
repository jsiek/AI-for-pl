module LR-narrow.Fundamental where

-- File Charter:
--   * Exposes derivation-indexed one-sided universal fundamental cases.
--   * Exposes the symmetric universal body motive and constructor case.
--   * Uses the phase-aware body motive from LR-narrow.TermRelation.
--   * Packages ordinary universal relations as target-first body motives.
--   * Commutes target casts outward through right-universal body motives.
--   * Delegates constructor-facing proof scripts to the proof namespace.

open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin

open import Types
open import CastTerms
import Consistency
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.TermRelation
open import LR-narrow.Universal using
  (universal-body-imprecision; right-universal-body-imprecision)
open import LR-narrow.CastObligations using (CastValueObligations)
import proof.LR-narrow.Fundamental as Proof

universal-body-fundamental-from-relation : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Γᵇ : CTI.CtxImp
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W))}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
    (body : CTI.liftWorldBoth I.X⊑X (forgetWorld W) ∣ Γᵇ
      ⊢² Vᴾ ⊑ Vᴵ ∶ p)
  → (∀ k → CompiledUniversalBodyRelation
      {W = W} (universal-body-imprecision {W = W} p)
      Aᴾ Aᴵ k Γ Vᴾ Vᴵ)
  → UniversalBodyFundamentalProperty {W = W} {Γ = Γ} {Γᵇ = Γᵇ}
      {p = p} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
      (universal-body-imprecision {W = W} p) body
universal-body-fundamental-from-relation =
  Proof.universal-body-fundamental-from-relation

universal-fundamental : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Γᵇ : CTI.CtxImp
      (CTI.liftWorldBoth I.X⊑X (forgetWorld W))}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
    (liftΓ : CTI.LiftCtx I.X⊑X Γ Γᵇ)
    (vVᴾ : Value Vᴾ)
    (vVᴵ : Value Vᴵ)
    (body : CTI.liftWorldBoth I.X⊑X (forgetWorld W) ∣ Γᵇ
      ⊢² Vᴾ ⊑ Vᴵ ∶ p)
    (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ `∀ Aᴵ)
  → UniversalBodyFundamentalProperty {W = W} {Γ = Γ} {Γᵇ = Γᵇ}
      {p = p} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
      (universal-body-imprecision {W = W} p) body
  → FundamentalProperty (CTIR.Λ⊑Λ² liftΓ vVᴾ vVᴵ body q)
universal-fundamental = Proof.universal-fundamental

right-universal-body-fundamental-from-relation : ∀
    {Δᴾ Δᴵ Δᶜ Δᵇ Aᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Wᵇ : CTI.World (suc Δᴾ) Δᴵ Δᵇ}
    {Γᵇ : CTI.CtxImp Wᵇ}
    {p : Aᴾ CTI.⊑ᵂ⟨ Wᵇ ⟩ Bᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
    (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
    (body : Wᵇ ∣ Γᵇ ⊢² Vᴾ ⊑ Mᴵ ∶ p)
  → Value Vᴾ
  → (∀ k → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Mᴵ)
  → RightUniversalBodyFundamentalProperty
      {W = W} {Γ = Γ} {Wᵇ = Wᵇ} {Γᵇ = Γᵇ}
      {p = p} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ} q body
right-universal-body-fundamental-from-relation =
  Proof.right-universal-body-fundamental-from-relation

right-universal-target-cast-body-fundamental : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Bᴵ Dᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {r : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Dᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
    {μᴵ : Consistency.Env∼ Δᴵ}
    (ob : CastValueObligations)
    (nonvar : NonVar Aᴾ)
    (occurs : Fin.zero ∈ᵗ Aᴾ)
    (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
    (vVᴾ : Value Vᴾ)
    (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
      CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ)
    (cᴵ : μᴵ Consistency.⊢ Bᴵ ∼ Dᴵ)
    (body : CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Mᴵ ∶ p)
    (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
    (s : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Dᴵ)
  → RightUniversalBodyFundamentalProperty
      {W = W} {Γ = Γ}
      {Wᵇ = CTI.liftWorldLeft I.X⊑★ (forgetWorld W)} {Γᵇ = Γ′}
      {p = p} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ} q body
  → RightUniversalBodyFundamentalProperty
      {W = W} {Γ = Γ}
      {Wᵇ = CTI.liftWorldLeft I.X⊑★ (forgetWorld W)} {Γᵇ = Γ′}
      {p = r} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ ⟨ cᴵ ⟩} s
      (CTIR.⊑cast² cᴵ body r)
right-universal-target-cast-body-fundamental =
  Proof.right-universal-target-cast-body-fundamental

right-universal-value-body-fundamental : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
    (nonvar : NonVar Aᴾ)
    (occurs : Fin.zero ∈ᵗ Aᴾ)
    (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
    (vVᴾ : Value Vᴾ)
    (vVᴵ : Value Vᴵ)
    (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
      CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ)
    (body : CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p)
    (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → CompiledRightUniversalTestRelation {W = W}
      (right-universal-body-imprecision {W = W} p)
      Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → RightUniversalBodyFundamentalProperty
      {W = W} {Γ = Γ}
      {Wᵇ = CTI.liftWorldLeft I.X⊑★ (forgetWorld W)} {Γᵇ = Γ′}
      {p = p} {Vᴾ = Vᴾ} {Mᴵ = Vᴵ} q body
right-universal-value-body-fundamental =
  Proof.right-universal-value-body-fundamental

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

right-universal-value-fundamental : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
    (nonvar : NonVar Aᴾ)
    (occurs : Fin.zero ∈ᵗ Aᴾ)
    (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
    (vVᴾ : Value Vᴾ)
    (vVᴵ : Value Vᴵ)
    (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
      CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ)
    (body : CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
      ⊢² Vᴾ ⊑ Vᴵ ∶ p)
    (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → CompiledRightUniversalTestRelation {W = W}
      (right-universal-body-imprecision {W = W} p)
      Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → FundamentalProperty
      (CTIR.Λ⊑² nonvar occurs liftΓ vVᴾ target⊢ body q)
right-universal-value-fundamental =
  Proof.right-universal-value-fundamental

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
