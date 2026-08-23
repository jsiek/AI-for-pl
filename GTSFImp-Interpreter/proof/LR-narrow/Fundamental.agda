module proof.LR-narrow.Fundamental where

-- File Charter:
--   * Constructs derivation-indexed fundamental-property evidence.
--   * Packages and consumes symmetric universal body motives.
--   * Handles the ordinary and smart one-sided universal constructors.
--   * Packages compatible universal terms as target-first body motives.
--   * Commutes target casts outward through right-universal body motives.
--   * Keeps the constructor-facing proof applications out of the public API.

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
open import LR-narrow.Universal
open import LR-narrow.Cast using (right-cast-compatible)

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
universal-body-fundamental-from-relation body related =
  universal-body-proof related

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
universal-fundamental liftΓ vVᴾ vVᴵ body q body-fundamental =
  fundamental-proof λ k →
    universal-compatible-from-body liftΓ vVᴾ vVᴵ body q
      (λ i _ → universal-body-relation body-fundamental i)

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
right-universal-body-fundamental-from-relation q body vVᴾ related =
  right-universal-body-proof λ k →
    right-universal-body-phase-from-relation vVᴾ q (related k)

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
right-universal-target-cast-body-fundamental {r = r} nonvar occurs
    liftΓ vVᴾ target⊢ cᴵ body q s body-fundamental =
  right-universal-body-fundamental-from-relation s
    (CTIR.⊑cast² cᴵ body r) vVᴾ
    (right-cast-compatible cᴵ s
      (λ k → right-universal-compatible-from-body nonvar occurs liftΓ
        vVᴾ target⊢ body q
        (right-universal-body-relation body-fundamental k)))
  where
  universal-derivation =
    CTIR.Λ⊑² nonvar occurs liftΓ vVᴾ target⊢ body q

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
