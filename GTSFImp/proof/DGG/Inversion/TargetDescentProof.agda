module proof.DGG.Inversion.TargetDescentProof where

-- File Charter:
--   * Proves the checked terminal target-star descent used by M3.
--   * Reuses SealTransferCore for the actual target-star peel and composes
--     same-pivot rebases using the frozen target side.
--   * Leaves the variable-payload stack branch at the Def boundary for the
--     right-injection proof to consume directly.

import Data.Fin as Fin
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms using (Term; Value; Inert; inj; _⟨_⟩; _↓_)
open import Imprecision
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.SealTransferCore as STC
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; variable-obligation-aligns)
open import proof.DGG.Inversion.TargetWalkSupport using
  (rebase-source-membership)
open import proof.DGG.Inversion.TargetDescentDef using
  (TargetSealDescentResult; TargetSealReemit; TargetSealTerminal;
   TargetSealTerminalPayload; terminal-paired; terminal-stripped;
   reemit-paired; reemit-stripped; target-reemit; target-terminal;
   target-seal★)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   ηᴸʷ; ηᴿʷ; sourceStoreʷ; targetStoreʷ)

sameCtx-∘ : ∀ {Δᴸ Δᴿ Δ₁ Δ₂ Δ₃}
    {W₁ : World Δᴸ Δᴿ Δ₁} {W₂ : World Δᴸ Δᴿ Δ₂}
    {W₃ : World Δᴸ Δᴿ Δ₃}
    {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂} {γ₃ : CtxImp W₃}
  → CTI2.SameCtx γ₁ γ₂
  → CTI2.SameCtx γ₂ γ₃
  → CTI2.SameCtx γ₁ γ₃
sameCtx-∘ CTI2.same-[] CTI2.same-[] = CTI2.same-[]
sameCtx-∘ (CTI2.same-∷ sc₁) (CTI2.same-∷ sc₂) =
  CTI2.same-∷ (sameCtx-∘ sc₁ sc₂)

impEnvMono-∘ : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
  → CTI2.ImpEnvMono W₁ W₂
  → CTI2.ImpEnvMono W₂ W₃
  → CTI2.ImpEnvMono W₁ W₃
impEnvMono-∘ mono₁ mono₂ Z eq = mono₂ Z (mono₁ Z eq)

inner-source-pivot-eqᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt W′ W Xᴸ Y
  → (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)
  → X₂ ≡ Xᴸ
inner-source-pivot-eqᴿ {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} rb p
    with Fin._≟_ X₂ Xᴸ
inner-source-pivot-eqᴿ rb p | yes refl = refl
inner-source-pivot-eqᴿ {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} rb p | no X₂≢Xᴸ =
  ⊥-elim (X₂≢Xᴸ
    (toRenameᵗ-injective (ηᴸʷ W) same-center))
  where
  same-center :
    toRenameᵗ (ηᴸʷ W) X₂ ≡ toRenameᵗ (ηᴸʷ W) Xᴸ
  same-center =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot rb X₂≢Xᴸ)
      (trans (variable-obligation-aligns {W = W′} {X = X₂} {Y = Y} p)
        (trans (sym (CTI2.RebaseAt.ηᴿ-frozen rb Y))
          (sym (CTI2.RebaseAt.pivotAligned rb))))

composeSamePivotRebase : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt W′ W X Y
  → RebaseAt W₂ W′ X Y
  → RebaseAt W₂ W X Y
composeSamePivotRebase {W = W} {W′ = W′} {W₂ = W₂}
    {X = X} {Y = Y} rb₁ rb₂ =
  CTI2.rebase-at
    (CTI2.same-runtime
      (trans (CTI2.SameRuntime.sourceStore-same
        (CTI2.RebaseAt.sameRuntime rb₁))
        (CTI2.SameRuntime.sourceStore-same
          (CTI2.RebaseAt.sameRuntime rb₂)))
      (trans (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb₁))
        (CTI2.SameRuntime.targetStore-same
          (CTI2.RebaseAt.sameRuntime rb₂))))
    source-off target-frozen (CTI2.RebaseAt.pivotAligned rb₁)
    (CTI2.RebaseAt.storeRepresentations rb₁)
  where
  source-off : ∀ {Z} → Z ≢ X
    → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
  source-off Z≢X =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
      (CTI2.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

  target-frozen : ∀ Z
    → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
  target-frozen Z =
    trans (CTI2.RebaseAt.ηᴿ-frozen rb₁ Z)
      (CTI2.RebaseAt.ηᴿ-frozen rb₂ Z)

target-seal★-descent : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
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
  → targetStoreʷ W ∋ Y ⦂ ★
  → (∀ {W₂ : World Δᴸ Δᴿ Δ} {γ₂ : CtxImp W₂}
      → RebaseAt W₂ W′ X₂ Y
      → CTI2.ImpEnvMono W′ W₂
      → CTI2.SameCtx γ′ γ₂
      → (q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★)
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
      → CTI2.MatchedConcealPartnerOK W₂
          (V ⟨ c ⟩) (seal X₂ ★) (just Y) U)
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y ★ ∶ p₂
  → TargetSealDescentResult {W₀ = W} {γ₀ = γ} {P = V ⟨ c ⟩}
      {U = U} Xᴸ Y q ★
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c} {p₂ = p₂}
    sv inert vU mono rb sc X∈ Y∈ makePartner D
    with inner-source-pivot-eqᴿ rb p₂
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {c = c}
    sv inert vU mono rb sc X∈ Y∈ makePartner D
    | refl
    with STC.seal-transfer sv vU (rebase-source-membership rb X∈) D
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {c = c}
    sv inert vU mono rb sc X∈ Y∈ makePartner D
    | refl
    | STC.seal-transfer-stripped {W₂ = W₂} {γ₂ = γ₂}
        {q₂ = q₂} link mono₂ sc₂ D₂ =
  target-seal★
    (target-terminal W₂ γ₂
      (composeSamePivotRebase rb link)
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = W₂} mono mono₂)
      (sameCtx-∘ sc sc₂)
      (terminal-stripped (CTI2.cast⊑² c D₂ ★⊑★))
      (makePartner link mono₂ sc₂ q₂ D₂))
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {c = c}
    sv inert vU mono rb sc X∈ Y∈ makePartner D
    | refl
    | STC.seal-transfer-paired {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        {P = P} monoᵖ rbᵖ scᵖ source⊢ target⊢
        (CTI2.matched-seal-star-partner partner) prem
    with inert
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y}
    sv inert vU mono rb sc X∈ Y∈ makePartner D
    | refl
    | STC.seal-transfer-paired {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        {P = P} monoᵖ rbᵖ scᵖ source⊢ target⊢
        (CTI2.matched-seal-star-partner partner) prem
    | inj ⦃ Gᵍ = ＇ .Xᴸ ⦄ =
  target-seal★
    (target-terminal W′ _ rb mono sc
      (terminal-paired refl D)
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-round-trip
          (STC.transport-rep★-partner-ok rbᵖ partner))))

target-seal★-extract : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → (t : TargetSealTerminal W γ P U X Y)
  → sourceStoreʷ W ∋ X ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ ★
  → (q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y))
  → TargetSealTerminalPayload
      (TargetSealTerminal.Wᵒ t) (TargetSealTerminal.γᵒ t) P U X Y
target-seal★-extract
    (target-terminal Wᵒ γᵒ rb mono sc payload ok)
    X∈ Y∈ q =
  payload

target-seal＇-reemit : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W X Y
  → CTI2.SameCtx γ γ′
  → targetStoreʷ W ∋ Y ⦂ (＇ Y′)
  → (q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y))
  → (q′ : (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y′))
  → TargetSealReemit W γ P U X Y Y′ q
target-seal＇-reemit mono rb sc Y∈ q q′ =
  target-reemit _ _ q′
    λ where
      (reemit-stripped D) →
        CTI2.⊑conceal² mono (CTI2.rebase-varᴿ rb) sc
          (Conv.⊢↓-sealˣ Y∈) D q
      (reemit-paired D) → D
