module proof.DGG.Inversion.TargetDescentProof where

-- File Charter:
--   * Proves the checked terminal target-star descent used by M3.
--   * Reuses SealTransferCore for the actual target-star peel and composes
--     same-pivot rebases using the frozen target side.
--   * Does not re-emit active target-only seals: the live CTI relation makes
--     those branches impossible by generator position.

import Data.Fin as Fin
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
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
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.SealTransferCore as STC
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; variable-obligation-aligns)
open import proof.DGG.Inversion.TargetWalkSupport using
  (rebase-source-membership)
open import proof.DGG.Inversion.TargetDescentDef using
  (TargetSealTerminal; TargetSealTerminalPayload; terminal-paired;
   terminal-stripped; target-terminal)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTX using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_;
   ηᴸʷ;
   ηᴿʷ;
   sourceStoreʷ;
   targetStoreʷ)
open CTI2 using (_∣_⊢²_⊑_∶_)

sameCtx-∘ : ∀ {Δᴸ Δᴿ Δ₁ Δ₂ Δ₃}
    {W₁ : World Δᴸ Δᴿ Δ₁} {W₂ : World Δᴸ Δᴿ Δ₂}
    {W₃ : World Δᴸ Δᴿ Δ₃}
    {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂} {γ₃ : CtxImp W₃}
  → CTX.SameCtx γ₁ γ₂
  → CTX.SameCtx γ₂ γ₃
  → CTX.SameCtx γ₁ γ₃
sameCtx-∘ CTX.same-[] CTX.same-[] = CTX.same-[]
sameCtx-∘ (CTX.same-∷ sc₁) (CTX.same-∷ sc₂) =
  CTX.same-∷ (sameCtx-∘ sc₁ sc₂)

impEnvMono-∘ : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
  → CTX.ImpEnvMono W₁ W₂
  → CTX.ImpEnvMono W₂ W₃
  → CTX.ImpEnvMono W₁ W₃
impEnvMono-∘ = CTX.impEnvMono-trans

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
    trans (CTX.RebaseAt.ηᴸ-off-pivot rb X₂≢Xᴸ)
      (trans (variable-obligation-aligns {W = W′} {X = X₂} {Y = Y} p)
        (trans (sym (CTX.RebaseAt.ηᴿ-frozen rb Y))
          (sym (CTX.RebaseAt.pivotAligned rb))))

composeSamePivotRebase : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt W′ W X Y
  → RebaseAt W₂ W′ X Y
  → RebaseAt W₂ W X Y
composeSamePivotRebase {W = W} {W′ = W′} {W₂ = W₂}
    {X = X} {Y = Y} rb₁ rb₂ =
  CTX.rebase-at
    (CTX.same-runtime
      (trans (CTX.SameRuntime.sourceStore-same
        (CTX.RebaseAt.sameRuntime rb₁))
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb₂)))
      (trans (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime rb₁))
        (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime rb₂))))
    source-off target-frozen (CTX.RebaseAt.pivotAligned rb₁)
    (CTX.RebaseAt.storeRepresentations rb₁)
  where
  source-off : ∀ {Z} → Z ≢ X
    → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
  source-off Z≢X =
    trans (CTX.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
      (CTX.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

  target-frozen : ∀ Z
    → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
  target-frozen Z =
    trans (CTX.RebaseAt.ηᴿ-frozen rb₁ Z)
      (CTX.RebaseAt.ηᴿ-frozen rb₂ Z)

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
  → CTX.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTX.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ ★
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y ★ ∶ p₂
  → TargetSealTerminal W γ (V ⟨ c ⟩) U Xᴸ Y
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c} {p₂ = p₂}
    sv inert vU mono rb sc X∈ Y∈ D
    with inner-source-pivot-eqᴿ rb p₂
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {c = c}
    sv inert vU mono rb sc X∈ Y∈ D
    | refl
    with STC.seal-transfer sv vU (rebase-source-membership rb X∈) D
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {c = c}
    sv inert vU mono rb sc X∈ Y∈ D
    | refl
    | STC.seal-transfer-stripped {W₂ = W₂} {γ₂ = γ₂}
        {q₂ = q₂} link mono₂ sc₂ D₂ =
  target-terminal W₂ γ₂
    (composeSamePivotRebase rb link)
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = W₂} mono mono₂)
    (sameCtx-∘ sc sc₂)
    (terminal-stripped (CTI2.cast⊑² c D₂ ★⊑★))
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y} {c = c}
    sv inert vU mono rb sc X∈ Y∈ D
    | refl
    | STC.seal-transfer-paired {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        {P = P} monoᵖ rbᵖ scᵖ source⊢ target⊢ prem
    with inert
target-seal★-descent {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y = Y}
    sv inert vU mono rb sc X∈ Y∈ D
    | refl
    | STC.seal-transfer-paired {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        {P = P} monoᵖ rbᵖ scᵖ source⊢ target⊢ prem
    | inj ⦃ Gᵍ = ＇ .Xᴸ ⦄ =
  target-terminal W′ _ rb mono sc (terminal-paired refl D)

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
    (target-terminal Wᵒ γᵒ rb mono sc payload)
    X∈ Y∈ q =
  payload
