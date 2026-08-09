module proof.DGG.Inversion.SourceStripWorkerProof where

-- File Charter:
--   * Provides the source-column and source-spine strip members.
--   * Keeps the public `SourceStripProof` module free of local proof scripts.
--   * The two statements are exactly the frozen worker goals from
--     `SourceStripDef`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms using (Term; Value; _⦂∀_[_]; _↓_; _⟨_⟩)
open import Imprecision
open import Primitives using (κℕ; κ𝔹)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.SealTransferCore as STC
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCoreBranch;
   SourceColumnStripBranch; SourcePairedBranch; SourceSpineStripBranch;
   column-paired;
   column-sealed; column-tagged; core-paired; core-sealed;
   core-terminus; core-terminus-nonstar; spine-paired; spine-sealed;
   spine-tagged)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal; sv-reveal-fun;
   sv-conceal-fun; sv-reveal-all; sv-conceal-all; varv-seal;
   var-value-view; variable-obligation-aligns; seal-rebase-target)
open import proof.DGG.Inversion.TargetChainLemma using
  (target-source-star-chain)
open import proof.DGG.Inversion.TargetWalkSupport using
  (impEnvMono-∘; inner-source-pivot-eq; rebase-source-membership;
   rebase-source-membership-back; rebase-target-membership;
   rebase-pivot-obligation;
   sealed-source-name-tagged; sealed-source-partner-view;
   sealed-source-rep★; sealed-source-untagged; sameCtx-∘;
   target-seal-rebase-source;
   tagged-target-nonvar-nonstar-spine-⊥; seal-target-nonstar-⊥;
   target-source-var-chain; var-source-nonstar-⊥)

open CTI2 using
  (World; CtxImp; RebaseAt; RebaseAtᴸ; TagRebaseAtᴸ; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ)

private
  rebase-target-membership-forward : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Z : TyVar Δᴿ} {S : Ty Δᴿ}
    → RebaseAt W′ W X Y
    → targetStoreʷ W ∋ Z ⦂ S
    → targetStoreʷ W′ ∋ Z ⦂ S
  rebase-target-membership-forward rb Z∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb)) Z∈

  rebase-source-membership-forward : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X Z : TyVar Δᴸ} {Y : TyVar Δᴿ} {R : Ty Δᴸ}
    → RebaseAt W′ W X Y
    → sourceStoreʷ W ∋ Z ⦂ R
    → sourceStoreʷ W′ ∋ Z ⦂ R
  rebase-source-membership-forward rb Z∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (CTI2.SameRuntime.sourceStore-same
        (CTI2.RebaseAt.sameRuntime rb)) Z∈

  composeOuterRebase : ∀ {Δᴸ Δᴿ Δ}
      {W W′ W₂ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
    → RebaseAt W′ W X Y
    → RebaseAt W₂ W′ X Y′
    → RebaseAt W₂ W X Y
  composeOuterRebase {W = W} {W′ = W′} {W₂ = W₂}
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
      → toRenameᵗ (CTI2.ηᴸʷ W) Z
          ≡ toRenameᵗ (CTI2.ηᴸʷ W₂) Z
    source-off Z≢X =
      trans (CTI2.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
        (CTI2.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

    target-frozen : ∀ Z
      → toRenameᵗ (CTI2.ηᴿʷ W) Z
          ≡ toRenameᵗ (CTI2.ηᴿʷ W₂) Z
    target-frozen Z =
      trans (CTI2.RebaseAt.ηᴿ-frozen rb₁ Z)
        (CTI2.RebaseAt.ηᴿ-frozen rb₂ Z)

  composeTagRebaseOuter : ∀ {Δᴸ Δᴿ Δ}
      {W W′ W₂ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {Y′?}
    → RebaseAt W′ W X Y
    → TagRebaseAtᴸ W₂ W′ (just X) Y′?
    → RebaseAt W₂ W X Y
  composeTagRebaseOuter rb (CTI2.tag-rebase-varᴸ link) =
    composeOuterRebase rb link
  composeTagRebaseOuter rb
      (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
    rb

  composeTagRebaseTagOuter : ∀ {Δᴸ Δᴿ Δ}
      {W W′ W₂ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {Y′?}
    → RebaseAt W′ W X Y
    → TagRebaseAtᴸ W₂ W′ (just X) Y′?
    → Σ[ Z? ∈ _ ] TagRebaseAtᴸ W₂ W (just X) Z?
  composeTagRebaseTagOuter rb (CTI2.tag-rebase-varᴸ link) =
    _ , CTI2.tag-rebase-varᴸ (composeOuterRebase rb link)
  composeTagRebaseTagOuter rb
      (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
    _ , CTI2.tag-rebase-varᴸ rb

  impEnvMono-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    → CTI2.ImpEnvMono W W
  impEnvMono-refl Z eq = eq

  sameCtx-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
    → CTI2.SameCtx γ γ
  sameCtx-refl {γ = []} = CTI2.same-[]
  sameCtx-refl {γ = CTI2.ctx-imp A B p ∷ γ} =
    CTI2.same-∷ sameCtx-refl

  self-column-sealed : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
      {V : Term Δᴸ} {U : Term Δᴿ} {S : Ty Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → RebaseAt W′ W X Y
    → targetStoreʷ W ∋ Y ⦂ S
    → SpineValue V
    → W ∣ γ ⊢² V ⊑ U ↓ seal Y S ∶ q
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceColumnStripBranch W γ V U X Y S cY q
             Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  self-column-sealed {W = W} {γ = γ} {V = V} {U = U}
      {S = S} {X = X} {Y = Y} {q = q} rb target∈ sv final =
    V , ＇ X , X , W , γ , q , sv ,
      column-sealed
        V (＇ X) sv
        (W , γ , q , impEnvMono-refl {W = W} ,
          sameCtx-refl {γ = γ} ,
          CTI2.rebase-varᴸ
            (CTI2.sameWorldRebaseAt
              (variable-obligation-aligns {W = W} {X = X} {Y = Y} q)
              (CTI2.RebaseAt.storeRepresentations rb)) ,
          target∈ , final)
        (λ _ → final)

  self-spine-sealed : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
      {V : Term Δᴸ} {U : Term Δᴿ} {R : Ty Δᴸ} {S : Ty Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → RebaseAt W′ W X Y
    → targetStoreʷ W ∋ Y ⦂ S
    → SpineValue (V ↓ seal X R)
    → W ∣ γ ⊢² V ↓ seal X R ⊑ U ↓ seal Y S ∶ q
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ V R U X Y S cY q
             Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  self-spine-sealed {W = W} {γ = γ} {V = V} {U = U}
      {R = R} {S = S} {X = X} {Y = Y} {q = q}
      rb target∈ sv final =
    V ↓ seal X R , ＇ X , X , W , γ , q , sv ,
      spine-sealed
        (V ↓ seal X R) (＇ X) sv
        (W , γ , q , impEnvMono-refl {W = W} ,
          sameCtx-refl {γ = γ} ,
          CTI2.rebase-varᴸ
            (CTI2.sameWorldRebaseAt
              (variable-obligation-aligns {W = W} {X = X} {Y = Y} q)
              (CTI2.RebaseAt.storeRepresentations rb)) ,
          target∈ , final)
        (λ _ → final)

  source-column-untagged-final : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {R : Ty Δᴸ} {S : Ty Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {r : (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W X Y
    → CTI2.SameCtx γ γ′
    → targetStoreʷ W ∋ Y ⦂ S
    → W′ ∣ γ′ ⊢² V ↓ seal X R ⊑ U ↓ seal Y S ∶ r
    → W ∣ γ ⊢² V ↓ seal X R ⊑ U ↓ seal Y S ∶ q
  source-column-untagged-final {W = W} {W′ = W′} mono rb sc target∈
      (CTI2.conceal⊑² {W′ = Wᵖ} {p = pᵖ}
        ok monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈) prem r)
      with composeTagRebaseTagOuter rb rbᵖ
  source-column-untagged-final {W = W} {W′ = W′} {q = q}
      mono rb sc target∈
      (CTI2.conceal⊑² {W′ = Wᵖ} {p = pᵖ}
        ok monoᵖ rbᵖ scᵖ (CTI2.⊢↓-sealˣ X∈) prem r)
      | Z? , rbᶠ =
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↓))
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵖ}
        mono monoᵖ)
      rbᶠ (sameCtx-∘ sc scᵖ)
      (CTI2.⊢↓-sealˣ (rebase-source-membership-back rb X∈))
      prem q
  source-column-untagged-final {W = W} {W′ = W′} {q = q}
      mono rb sc target∈
      (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = pᵖ}
        monoᵖ rbᵖ scᵖ
        (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ target∈′)
        prem r) =
    CTI2.conceal⊑conceal²
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵖ}
        mono monoᵖ)
      (composeOuterRebase rb rbᵖ) (sameCtx-∘ sc scᵖ)
      (CTI2.⊢↓-sealˣ (rebase-source-membership-back rb X∈))
      (CTI2.⊢↓-sealˣ target∈) prem q
  source-column-untagged-final {W = W} {W′ = W′} {q = q}
      mono rb sc target∈
      (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ}
        monoᵈ rbᴿ scᵈ
        (CTI2.⊢↓-sealˣ target∈′) prem r)
      with target-seal-rebase-source rbᴿ r
  source-column-untagged-final {W = W} {W′ = W′} {q = q}
      mono rb sc target∈
      (CTI2.⊑conceal² {W′ = Wᵈ} {p = pᵈ}
        monoᵈ rbᴿ scᵈ
        (CTI2.⊢↓-sealˣ target∈′) prem r)
      | link =
    CTI2.⊑conceal²
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵈ}
        mono monoᵈ)
      (CTI2.rebase-varᴿ (composeOuterRebase rb link))
      (sameCtx-∘ sc scᵈ) (CTI2.⊢↓-sealˣ target∈) prem q

  tag-rebase-from-left : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    → RebaseAtᴸ W′ W (just X)
    → Σ[ Xᴿ? ∈ _ ] TagRebaseAtᴸ W′ W (just X) Xᴿ?
  tag-rebase-from-left (CTI2.rebase-varᴸ rb) =
    _ , CTI2.tag-rebase-varᴸ rb
  tag-rebase-from-left
      (CTI2.rebase-onlyᴸ to-star disaligned represented) =
    nothing , CTI2.tag-rebase-onlyᴸ to-star disaligned represented

  spine-value→Value : ∀ {Δ} {V : Term Δ}
    → SpineValue V
    → Value V
  spine-value→Value (sv-ƛ N) = Value.ƛ N
  spine-value→Value (sv-Λ sv) = Value.Λ (spine-value→Value sv)
  spine-value→Value (sv-$ κ) = Value.$ κ
  spine-value→Value (sv-cast sv inert) =
    spine-value→Value sv Value.《 inert 》
  spine-value→Value (sv-seal sv) =
    spine-value→Value sv Value.↓ CastTerms.seal
  spine-value→Value (sv-reveal-fun sv) =
    spine-value→Value sv Value.↑ CastTerms.fun
  spine-value→Value (sv-conceal-fun sv) =
    spine-value→Value sv Value.↓ CastTerms.fun
  spine-value→Value (sv-reveal-all sv) =
    spine-value→Value sv Value.↑ CastTerms.all
  spine-value→Value (sv-conceal-all sv) =
    spine-value→Value sv Value.↓ CastTerms.all

  value→spine : ∀ {Δ} {V : Term Δ}
    → Value V
    → SpineValue V
  value→spine (Value.ƛ N) = sv-ƛ N
  value→spine (Value.Λ vV) = sv-Λ (value→spine vV)
  value→spine (Value.$ κ) = sv-$ κ
  value→spine (vV Value.《 inert 》) = sv-cast (value→spine vV) inert
  value→spine (vV Value.↑ CastTerms.fun) =
    sv-reveal-fun (value→spine vV)
  value→spine (vV Value.↑ CastTerms.all) =
    sv-reveal-all (value→spine vV)
  value→spine (vV Value.↓ CastTerms.seal) =
    sv-seal (value→spine vV)
  value→spine (vV Value.↓ CastTerms.fun) =
    sv-conceal-fun (value→spine vV)
  value→spine (vV Value.↓ CastTerms.all) =
    sv-conceal-all (value→spine vV)

  rebase-only-star-rep-no-var-target : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → TagRebaseAtᴸ W W (just X) nothing
    → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
    → ⊥
  rebase-only-star-rep-no-var-target {W = W} {X = X} {Y = Y}
      (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) q =
    disaligned Y
      (sym (variable-obligation-aligns {W = W} {X = X} {Y = Y} q))

  tag-rebase-target : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {Xᴿ?}
    → TagRebaseAtᴸ W′ W (just X) Xᴿ?
    → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
    → RebaseAt W′ W X Y
  tag-rebase-target (CTI2.tag-rebase-varᴸ rb) q =
    seal-rebase-target (CTI2.rebase-varᴸ rb) q
  tag-rebase-target rb@(CTI2.tag-rebase-onlyᴸ _ _ _) q =
    ⊥-elim (rebase-only-star-rep-no-var-target rb q)

  plain-star-rep-premise : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {p : ★ ⊑ᵂ⟨ W′ ⟩ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
    → CTI2.ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) Xᴿ?
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ X ⦂ ★
    → W′ ∣ γ′ ⊢² V ⊑ U ∶ p
    → W ∣ γ ⊢² V ↓ seal X ★ ⊑ U ∶ q
  plain-star-rep-premise mono rb sc X∈ prem =
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.star-rep-target)
      mono rb sc (CTI2.⊢↓-sealˣ X∈) prem _

  injected-star-rep-premise : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
      {p : ★ ⊑ᵂ⟨ W′ ⟩ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
    → CTI2.ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) Xᴿ?
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ X ⦂ ★
    → CastTerms.Inert c
    → W′ ∣ γ′ ⊢² V ⊑ U ∶ p
    → W ∣ γ ⊢² (V ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★
  injected-star-rep-premise {c = c} {q = q} mono rb sc X∈ inert prem =
    CTI2.cast⊑² {p = q} c
      (plain-star-rep-premise mono rb sc X∈ prem) ★⊑★

  wrap-star-cast-final : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {S : Ty Δᴿ} {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
      {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ S
    → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂
    → W ∣ γ ⊢² (V ⟨ c ⟩) ↓ seal Xᴸ ★
        ⊑ U ↓ seal Y S ∶ q
  wrap-star-cast-final {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
      {c = c} {p₂ = p₂} {q = q}
      sv inert vU mono rb sc source∈ target∈ final
      with inner-source-pivot-eq rb q p₂
  wrap-star-cast-final {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
      {c = c} {q = q}
      sv inert vU mono rb sc source∈ target∈ final
      | refl
      with STC.seal-transfer sv vU
        (rebase-source-membership rb source∈) final
  wrap-star-cast-final {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
      {c = c} {q = q}
      sv inert vU mono rb sc source∈ target∈ final
      | refl | W₂ , γ₂ , link , mono₂ , sc₂ , q₂ , D₂ =
    CTI2.conceal⊑conceal²
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = W₂}
        mono mono₂)
      (composeOuterRebase rb link)
      (sameCtx-∘ sc sc₂)
      (CTI2.⊢↓-sealˣ source∈)
      (CTI2.⊢↓-sealˣ target∈)
      (CTI2.cast⊑² c D₂ ★⊑★)
      q
  wrap-star-cast-final {S = ＇ Y₂}
      sv inert vU mono rb sc source∈ target∈ final =
    target-source-star-chain sv inert vU mono rb sc source∈
      target∈ final
  wrap-star-cast-final {S = ‵ ι}
      sv inert vU mono rb sc source∈ target∈ final =
    ⊥-elim
      (seal-target-nonstar-⊥ source∈ rb target∈ nonvar-base nonstar-ι)
  wrap-star-cast-final {S = A ⇒ B}
      sv inert vU mono rb sc source∈ target∈ final =
    ⊥-elim
      (seal-target-nonstar-⊥ source∈ rb target∈ nonvar-fun nonstar-⇒)
  wrap-star-cast-final {S = `∀ A}
      sv inert vU mono rb sc source∈ target∈ final =
    ⊥-elim
      (seal-target-nonstar-⊥ source∈ rb target∈ nonvar-all nonstar-∀)

  star-rep-cast-final : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {S : Ty Δᴿ} {X X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
      {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) Xᴿ?
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ X ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ S
    → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂
    → W ∣ γ ⊢² (V ⟨ c ⟩) ↓ seal X ★
        ⊑ U ↓ seal Y S ∶ q
  star-rep-cast-final {q = q} sv inert vU mono rb sc source∈
      target∈ final =
    wrap-star-cast-final sv inert vU mono
      (tag-rebase-target rb q) sc source∈ target∈ final

postulate
  source-column-strip-worker : SourceColumnStrip
  source-spine-strip-worker : SourceSpineStrip
