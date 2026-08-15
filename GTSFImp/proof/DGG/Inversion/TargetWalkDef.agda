module proof.DGG.Inversion.TargetWalkDef where

-- File Charter:
--   * States the target walk and source-star chain surfaces used by the
--     v2 right-injection inversion proof.
--   * Keeps the walk/chain statements as Set-level definitions so the
--     right-injection proof can be checked against supplied inhabitants.
--   * Contains no proof scripts and depends only on the cast-imprecision
--     and spine-value public surfaces.

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

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

data TargetSourceStarAtResult {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (V : Term Δᴸ) (U : Term Δᴿ)
    (X : TyVar Δᴸ) (Y : TyVar Δᴿ) :
    (S : Ty Δᴿ) →
    {ν : Env∼ Δᴸ} (c : ν ⊢ (＇ X) ∼ ★) →
    (q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)) → Set where
  target-source-star-final : ∀ {S ν}
      {c : ν ⊢ (＇ X) ∼ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → W ∣ γ ⊢² (V ⟨ c ⟩) ↓ seal X ★
        ⊑ U ↓ seal Y S ∶ q
    → TargetSourceStarAtResult W γ V U X Y S c q

  target-source-star-residual : ∀ {P ν}
      {c : ν ⊢ (＇ X) ∼ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → V ≡ P ↓ seal X ★
    → sourceStoreʷ W ∋ X ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ ★
    → RebaseAt W W X Y
    → W ∣ γ ⊢² P ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
    → TargetSourceStarAtResult W γ V U X Y ★ c q

  target-source-star-var-residual : ∀ {P Y′ ν}
      {c : ν ⊢ (＇ X) ∼ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → V ≡ P ↓ seal X ★
    → sourceStoreʷ W ∋ X ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ (＇ Y′)
    → RebaseAt W W X Y
    → W ∣ γ ⊢² P ↓ seal X ★ ⊑ U ↓ seal Y (＇ Y′) ∶ q
    → TargetSourceStarAtResult W γ V U X Y (＇ Y′) c q

  target-source-star-paired : ∀ {P Wᵖ γᵖ ν}
      {c : ν ⊢ (＇ X) ∼ ★}
      {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → V ≡ P ↓ seal X ★
    → CTI2.ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W X Y
    → CTI2.SameCtx γ γᵖ
    → sourceStoreʷ W ∋ X ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ ★
    → CTI2.MatchedConcealPartnerOK Wᵖ P (seal X ★) (just Y) U
    → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★
    → TargetSourceStarAtResult W γ V U X Y ★ c q

  target-source-star-payload : ∀ {P Wᵖ γᵖ ν}
      {c : ν ⊢ (＇ X) ∼ ★}
      {pᵖ : (＇ X) ⊑ᵂ⟨ Wᵖ ⟩ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → V ≡ P ↓ seal X ★
    → CTI2.ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W X Y
    → CTI2.SameCtx γ γᵖ
    → sourceStoreʷ W ∋ X ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ ★
    → Wᵖ ∣ γᵖ ⊢² P ↓ seal X ★ ⊑ U ∶ pᵖ
    → TargetSourceStarAtResult W γ V U X Y ★ c q

TargetSourceStarAt : Set
TargetSourceStarAt =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Inert c
  → Value U
  → sourceStoreʷ W ∋ X ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ S
  → W ∣ γ ⊢² V ⊑ U ↓ seal Y S ∶ q
  → TargetSourceStarAtResult W γ V U X Y S c q

TargetSourceStarChain : Set
TargetSourceStarChain =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
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
  → targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y (＇ Y₂) ∶ p₂
  → W ∣ γ ⊢²
      (V ⟨ c ⟩) ↓ seal Xᴸ ★
      ⊑ U ↓ seal Y (＇ Y₂) ∶ q
