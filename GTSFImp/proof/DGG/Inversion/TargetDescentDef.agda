module proof.DGG.Inversion.TargetDescentDef where

-- File Charter:
--   * States the checked terminal target-star descent package used by
--     right-injection inversion.
--   * Distinguishes stripped and paired terminal payloads without exposing
--     an active target-only re-emission continuation.
--   * Keeps the statement independent of OpenStrata, ParkedWorld, and
--     SealChain so M4 can reuse the same package directly.

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms using (Term; Value; _⟨_⟩; _↓_)
open import Imprecision
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTI2 using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_;
   sourceStoreʷ;
   targetStoreʷ)
open CTIR using (_∣_⊢²_⊑_∶_)

data TargetSealTerminalPayload {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (Xᵒ : TyVar Δᴸ) (Yᵒ : TyVar Δᴿ) : Set where
  terminal-stripped :
    Wᵒ ∣ γᵒ ⊢² P ⊑ U ∶ ★⊑★
    → TargetSealTerminalPayload Wᵒ γᵒ P U Xᵒ Yᵒ

  terminal-paired : ∀ {V : Term Δᴸ} {ν : Env∼ Δᴸ}
      {c : ν ⊢ (＇ Xᵒ) ∼ ★}
      {qᵖ : (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Yᵒ)}
    → P ≡ V ⟨ c ⟩
    → Wᵒ ∣ γᵒ ⊢² V ⊑ U ↓ seal Yᵒ ★ ∶ qᵖ
    → TargetSealTerminalPayload Wᵒ γᵒ P U Xᵒ Yᵒ

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
    payloadᵒ : TargetSealTerminalPayload Wᵒ γᵒ P U Xᵒ Yᵒ

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
