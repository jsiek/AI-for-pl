module proof.DGG.Inversion.TargetDescentDef where

-- File Charter:
--   * States the M3 target-seal descent surface used by right-injection
--     inversion.
--   * Splits terminal target-star descent from variable-payload descent:
--     `★` returns an existential paired-rebuild premise, while `＇ Y`
--     returns an exposed premise and a continuation that re-emits the
--     frozen target wrapper.
--   * Keeps the statement independent of OpenStrata, ParkedWorld, and
--     SealChain so M4 can reuse the same package directly.

open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _↓_)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   sourceStoreʷ; targetStoreʷ)

record TargetSealTerminal {Δᴸ Δᴿ Δ}
    (W₀ : World Δᴸ Δᴿ Δ) (γ₀ : CtxImp W₀)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (Xᵒ : TyVar Δᴸ) (Yᵒ : TyVar Δᴿ) : Set where
  constructor target-terminal
  field
    Wᵒ : World Δᴸ Δᴿ Δ
    γᵒ : CtxImp Wᵒ
    rebaseᵒ : RebaseAt Wᵒ W₀ Xᵒ Yᵒ
    monoᵒ : CTI2.ImpEnvMono W₀ Wᵒ
    sameᵒ : CTI2.SameCtx γ₀ γᵒ
    premiseᵒ : Wᵒ ∣ γᵒ ⊢² P ⊑ U ∶ ★⊑★
    partnerᵒ : CTI2.MatchedConcealPartnerOK Wᵒ P (seal Xᵒ ★) (just Yᵒ) U

record TargetSealReemit {Δᴸ Δᴿ Δ}
    (W₀ : World Δᴸ Δᴿ Δ) (γ₀ : CtxImp W₀)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (Xᵒ : TyVar Δᴸ) (Yᵒ : TyVar Δᴿ)
    (Y′ : TyVar Δᴿ)
    (qᵒ : (＇ Xᵒ) ⊑ᵂ⟨ W₀ ⟩ (＇ Yᵒ)) : Set where
  constructor target-reemit
  field
    Wᵈ : World Δᴸ Δᴿ Δ
    γᵈ : CtxImp Wᵈ
    qᵈ : (＇ Xᵒ) ⊑ᵂ⟨ Wᵈ ⟩ (＇ Y′)
    resume :
      Wᵈ ∣ γᵈ ⊢² P ↓ seal Xᵒ ★ ⊑ U ∶ qᵈ
      → W₀ ∣ γ₀ ⊢² P ↓ seal Xᵒ ★
          ⊑ U ↓ seal Yᵒ (＇ Y′) ∶ qᵒ

data TargetSealDescentResult {Δᴸ Δᴿ Δ}
    {W₀ : World Δᴸ Δᴿ Δ} {γ₀ : CtxImp W₀}
    {P : Term Δᴸ} {U : Term Δᴿ}
    (Xᵒ : TyVar Δᴸ) (Yᵒ : TyVar Δᴿ)
    (qᵒ : (＇ Xᵒ) ⊑ᵂ⟨ W₀ ⟩ (＇ Yᵒ))
    : Ty Δᴿ → Set where
  target-seal★ :
    TargetSealTerminal W₀ γ₀ P U Xᵒ Yᵒ
    → TargetSealDescentResult Xᵒ Yᵒ qᵒ ★

  target-seal＇ : ∀ {Y′}
    → TargetSealReemit W₀ γ₀ P U Xᵒ Yᵒ Y′ qᵒ
    → TargetSealDescentResult Xᵒ Yᵒ qᵒ (＇ Y′)

TargetSealDescent : Set
TargetSealDescent =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
    {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Inert c
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ S
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂
  → TargetSealDescentResult {W₀ = W} {γ₀ = γ} {P = V ⟨ c ⟩}
      {U = U} Xᴸ Y q S

TargetTagSealWalk : Set
TargetTagSealWalk =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {R : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p₀ : R ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ R
  → targetStoreʷ W ∋ Y ⦂ S
  → W′ ∣ γ′ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p₀
  → W ∣ γ ⊢² V ↓ seal Xᴸ R ⊑ U ↓ seal Y S ∶ q
