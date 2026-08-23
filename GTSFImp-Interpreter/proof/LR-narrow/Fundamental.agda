module proof.LR-narrow.Fundamental where

-- File Charter:
--   * Constructs derivation-indexed fundamental-property evidence.
--   * Handles the ordinary and smart one-sided universal constructors.
--   * Keeps the constructor-facing proof applications out of the public API.

open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin

open import Types
open import CastTerms
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.TermRelation
open import LR-narrow.Universal

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
right-universal-value-body-fundamental nonvar occurs liftΓ vVᴾ vVᴵ
    target⊢ body q body-tests =
  right-universal-body-proof λ k →
    right-universal-value-phase-from-body nonvar occurs liftΓ vVᴾ vVᴵ
      target⊢ body q (λ i i≤k → body-tests i)

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
right-universal-fundamental nonvar occurs liftΓ vVᴾ target⊢ body q
    body-fundamental =
  fundamental-proof λ k →
    right-universal-compatible-from-body nonvar occurs liftΓ vVᴾ target⊢
      body q (right-universal-body-relation body-fundamental k)

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
right-universal-value-fundamental nonvar occurs liftΓ vVᴾ vVᴵ
    target⊢ body q body-tests =
  right-universal-fundamental nonvar occurs liftΓ vVᴾ target⊢ body q
    (right-universal-value-body-fundamental nonvar occurs liftΓ vVᴾ vVᴵ
      target⊢ body q body-tests)

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
right-universal-smart-fundamental nonvar occurs smart liftΓ vVᴾ target⊢
    body q body-fundamental =
  fundamental-proof λ k →
    right-universal-smart-compatible-from-body nonvar occurs smart liftΓ
      vVᴾ target⊢ body q
      (right-universal-body-relation body-fundamental k)
