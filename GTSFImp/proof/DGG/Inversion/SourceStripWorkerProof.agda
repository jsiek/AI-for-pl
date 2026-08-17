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
open import CastTerms using
  (Ctx; Term; Value; _⊢_⦂_; ⊢conceal; _⦂∀_[_]; _↓_; _⟨_⟩)
open import Imprecision
open import Primitives using (κℕ; κ𝔹)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCoreBranch;
   SourceColumnStripWorker; SourceSpineStripWorker;
   SourceColumnStripBranch; SourcePairedBranch; SourceSpineStripBranch;
   column-paired;
   column-sealed; column-tagged; core-paired; core-sealed;
   core-terminus; core-terminus-nonstar; spine-paired; spine-sealed;
   spine-tagged)
open import proof.DGG.Inversion.SourceStripColumnView using
  (SourceColumnSealDCase; column-seal-source-case;
   column-seal-target-cast-case; source-column-seal-D-case)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal; sv-reveal-fun;
   sv-conceal-fun; sv-reveal-all; sv-conceal-all; varv-seal;
   var-value-view; variable-obligation-aligns; seal-rebase-target)
open import proof.DGG.Inversion.TargetChainLemma using
  (target-source-star-at; target-source-star-chain)
open import proof.DGG.Inversion.TargetWalkDef using
  (TargetSourceStarAt; target-source-star-final;
   target-source-star-residual; target-source-star-var-residual;
   target-source-star-paired; target-source-star-payload;
   target-source-star-chain-final; target-source-star-chain-residual;
   target-source-star-chain-paired; target-source-star-chain-payload)
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
  source-seal-pivot-eq : ∀ {Γ} {M X Y R}
    → Γ ⊢ M ↓ seal X R ⦂ (＇ Y)
    → X ≡ Y
  source-seal-pivot-eq (⊢conceal _ _) = refl

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

  abstract
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
        ok monoᵖ rbᵖ scᵖ
        (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ target∈′)
        prem r) =
    CTI2.conceal⊑conceal²
      ok
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵖ}
        mono monoᵖ)
      (composeOuterRebase rb rbᵖ) (sameCtx-∘ sc scᵖ)
      (CTI2.⊢↓-sealˣ (rebase-source-membership-back rb X∈))
      (CTI2.⊢↓-sealˣ target∈) prem q
  source-column-untagged-final {W = W} {W′ = W′} {q = q}
      mono rb sc target∈
      (CTI2.packaged-seal-star² {Wᵖ = Wᵖ}
        ok monoᵖ rbᵖ scᵖ
        (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ target∈′)
        prem sourcePrem r) =
    CTI2.packaged-seal-star²
      ok
      (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = Wᵖ}
        mono monoᵖ)
      (composeOuterRebase rb rbᵖ) (sameCtx-∘ sc scᵖ)
      (CTI2.⊢↓-sealˣ (rebase-source-membership-back rb X∈))
      (CTI2.⊢↓-sealˣ target∈) prem sourcePrem q
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

  abstract
    target-source-star-at-opaque : TargetSourceStarAt
    target-source-star-at-opaque = target-source-star-at

  data WrapStarCastFinalInput {Δᴸ Δᴿ Δ}
      (W W′ : World Δᴸ Δᴿ Δ)
      (γ : CtxImp W) (γ′ : CtxImp W′)
      (V : Term Δᴸ) (U : Term Δᴿ)
      (Xᴸ X₂ : TyVar Δᴸ) (Y : TyVar Δᴿ) :
      (S : Ty Δᴿ)
      → {ν : Env∼ Δᴸ}
      → (c : ν ⊢ (＇ X₂) ∼ ★)
      → (p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y))
      → (q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y))
      → Set where
    wrap-final-at : ∀ {ν}
        {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      →
        X₂ ≡ Xᴸ
      →
        W′ ∣ γ′ ⊢² (V ⟨ c ⟩) ↓ seal Xᴸ ★
          ⊑ U ↓ seal Y ★ ∶ p₂
      → WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂ Y ★ c p₂ q

    wrap-final-chain : ∀ {Y₂ ν}
        {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → W ∣ γ ⊢² (V ⟨ c ⟩) ↓ seal Xᴸ ★
          ⊑ U ↓ seal Y (＇ Y₂) ∶ q
      → WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂
          Y (＇ Y₂) c p₂ q

    wrap-final-base : ∀ {ι ν}
        {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂
          Y (‵ ι) c p₂ q

    wrap-final-fun : ∀ {A B ν}
        {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂
          Y (A ⇒ B) c p₂ q

    wrap-final-all : ∀ {A ν}
        {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂
          Y (`∀ A) c p₂ q

  data WrapStarCastFinalView {Δᴸ Δᴿ Δ}
      (W W′ : World Δᴸ Δᴿ Δ)
      (γ : CtxImp W) (γ′ : CtxImp W′)
      (V : Term Δᴸ) (U : Term Δᴿ)
      (Xᴸ X₂ : TyVar Δᴸ) (Y : TyVar Δᴿ) :
      (S : Ty Δᴿ)
      → {ν : Env∼ Δᴸ}
      → (c : ν ⊢ (＇ X₂) ∼ ★)
      → (p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y))
      → (q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y))
      → Set where
    wrap-star-cast-final-ready : ∀ {S ν}
      {c : ν ⊢ (＇ X₂) ∼ ★}
      {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      →
      WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q
      → WrapStarCastFinalView W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q

    wrap-star-cast-nonfinal : ∀ {S ν}
      {c : ν ⊢ (＇ X₂) ∼ ★}
      {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      →
      WrapStarCastFinalView W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q

  wrap-star-cast-final-view : ∀ {Δᴸ Δᴿ Δ}
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
    → WrapStarCastFinalView W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q
  wrap-star-cast-final-view {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′} {V = V} {U = U} {S = ★}
      {Xᴸ = Xᴸ} {Y = Y} {c = c} {p₂ = p₂} {q = q}
      sv inert vU mono rb sc source∈ target∈ final
      with inner-source-pivot-eq rb q p₂
  wrap-star-cast-final-view {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′} {V = V} {U = U} {S = ★}
      {Xᴸ = Xᴸ} {Y = Y} {c = c} {p₂ = p₂} {q = q}
      sv inert vU mono rb sc source∈ target∈ final
      | refl
      with target-source-star-at-opaque
        {W = W′} {γ = γ′} {V = V} {U = U}
        {X = Xᴸ} {Y = Y} {S = ★} {c = c} {q = p₂}
        sv inert vU
        (rebase-source-membership rb source∈)
        (rebase-target-membership-forward rb target∈)
        final
  wrap-star-cast-final-view {S = ★} sv inert vU mono rb sc
      source∈ target∈ final | refl
      | target-source-star-final sourcePrem =
    wrap-star-cast-final-ready (wrap-final-at refl sourcePrem)
  wrap-star-cast-final-view {S = ★} sv inert vU mono rb sc
      source∈ target∈ final | refl
      | target-source-star-residual _ _ _ _ _ =
    wrap-star-cast-nonfinal
  wrap-star-cast-final-view {S = ★} sv inert vU mono rb sc
      source∈ target∈ final | refl
      | target-source-star-paired _ _ _ _ _ _ _ _ =
    wrap-star-cast-nonfinal
  wrap-star-cast-final-view {S = ★} sv inert vU mono rb sc
      source∈ target∈ final | refl
      | target-source-star-payload _ _ _ _ _ _ _ =
    wrap-star-cast-nonfinal
  wrap-star-cast-final-view {S = ＇ Y₂} sv inert vU mono rb sc
      source∈ target∈ final
      with target-source-star-chain sv inert vU mono rb sc source∈
        target∈ final
  wrap-star-cast-final-view {S = ＇ Y₂} sv inert vU mono rb sc
      source∈ target∈ final
      | target-source-star-chain-final chain =
    wrap-star-cast-final-ready (wrap-final-chain chain)
  wrap-star-cast-final-view {S = ＇ Y₂} sv inert vU mono rb sc
      source∈ target∈ final
      | target-source-star-chain-residual _ _ _ _ _ =
    wrap-star-cast-nonfinal
  wrap-star-cast-final-view {S = ＇ Y₂} sv inert vU mono rb sc
      source∈ target∈ final
      | target-source-star-chain-paired _ _ _ _ _ _ _ _ _ _ =
    wrap-star-cast-nonfinal
  wrap-star-cast-final-view {S = ＇ Y₂} sv inert vU mono rb sc
      source∈ target∈ final
      | target-source-star-chain-payload _ _ _ _ _ _ _ _ _ =
    wrap-star-cast-nonfinal
  wrap-star-cast-final-view {S = ‵ ι}
      sv inert vU mono rb sc source∈ target∈ final =
    wrap-star-cast-final-ready wrap-final-base
  wrap-star-cast-final-view {S = A ⇒ B}
      sv inert vU mono rb sc source∈ target∈ final =
    wrap-star-cast-final-ready wrap-final-fun
  wrap-star-cast-final-view {S = `∀ A}
      sv inert vU mono rb sc source∈ target∈ final =
    wrap-star-cast-final-ready wrap-final-all

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
    → WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q
    → W ∣ γ ⊢² (V ⟨ c ⟩) ↓ seal Xᴸ ★
        ⊑ U ↓ seal Y S ∶ q
  wrap-star-cast-final {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
      {c = c} {p₂ = p₂} {q = q}
      sv inert vU mono rb sc source∈ target∈
      (wrap-final-at refl sourcePrem) =
    source-column-untagged-final mono rb sc target∈
      sourcePrem
  wrap-star-cast-final {S = ＇ Y₂}
      sv inert vU mono rb sc source∈ target∈
      (wrap-final-chain chain) =
    chain
  wrap-star-cast-final {S = ‵ ι}
      sv inert vU mono rb sc source∈ target∈ wrap-final-base =
    ⊥-elim
      (seal-target-nonstar-⊥ source∈ rb target∈ nonvar-base nonstar-ι)
  wrap-star-cast-final {S = A ⇒ B}
      sv inert vU mono rb sc source∈ target∈ wrap-final-fun =
    ⊥-elim
      (seal-target-nonstar-⊥ source∈ rb target∈ nonvar-fun nonstar-⇒)
  wrap-star-cast-final {S = `∀ A}
      sv inert vU mono rb sc source∈ target∈ wrap-final-all =
    ⊥-elim
      (seal-target-nonstar-⊥ source∈ rb target∈ nonvar-all nonstar-∀)

  abstract
    source-cast-seal-final : ∀ {Δᴸ Δᴿ Δ}
        {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
        {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
        {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
        {pᵢ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
        {p₂ : (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → SpineValue V
      → CastTerms.Inert c
      → Value U
      → CTI2.ImpEnvMono W W′
      → RebaseAt W′ W Xᴸ Y
      → CTI2.SameCtx γ γ′
      → sourceStoreʷ W ∋ Xᴸ ⦂ ★
      → targetStoreʷ W ∋ Y ⦂ S
      → CTI2.ImpEnvMono W′ Wᵢ
      → (link : RebaseAt Wᵢ W′ X Y)
      → CTI2.SameCtx γ′ γᵢ
      → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
      → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵢ
      → WrapStarCastFinalInput W W′ γ γ′ (V ↓ seal X Rᵢ) U
          Xᴸ X Y S c p₂ q
      → W ∣ γ ⊢² ((V ↓ seal X Rᵢ) ⟨ c ⟩) ↓ seal Xᴸ ★
          ⊑ U ↓ seal Y S ∶ q
    source-cast-seal-final {W = W} {W′ = W′} {γ = γ}
        {γ′ = γ′} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
        {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {p₂ = p₂}
        {q = q} sv inert vU mono rb sc source∈ target∈
        monoᵢ link scᵢ X∈ prem finalInput =
      wrap-star-cast-final
        {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
        {V = V ↓ seal X Rᵢ} {U = U} {S = S}
        {Xᴸ = Xᴸ} {X₂ = X} {Y = Y} {c = c}
        {p₂ = p₂} {q = q}
        (sv-seal sv) inert vU mono rb sc source∈ target∈
        finalInput

  source-seal-cast-final : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {S : Ty Δᴿ} {X Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
      {pᵢ : (＇ X₂) ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X)
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → (link : RebaseAt Wᵢ W′ X Y)
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ ★
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵢ
    → WrapStarCastFinalInput W′ Wᵢ γ′ γᵢ V U X X₂ Y S c pᵢ
        (rebase-pivot-obligation link)
    → W ∣ γ ⊢² ((V ⟨ c ⟩) ↓ seal X ★) ↓ seal Xᴸ (＇ X)
        ⊑ U ↓ seal Y S ∶ q
  source-seal-cast-final {W = W} {W′ = W′} {Wᵢ = Wᵢ}
      {γ = γ} {γ′ = γ′} {V = V} {U = U} {S = S}
      {X = X} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
      {pᵢ = pᵢ} {q = q} sv inert vU mono rb sc source∈
      target∈ monoᵢ link scᵢ X∈ prem finalInput =
    target-source-var-chain (sv-seal (sv-cast sv inert)) vU mono
      rb sc source∈ target∈
      (wrap-star-cast-final
        {W = W′} {W′ = Wᵢ} {γ = γ′} {V = V} {U = U}
        {S = S} {Xᴸ = X} {X₂ = X₂} {Y = Y} {c = c}
        {p₂ = pᵢ} {q = rebase-pivot-obligation link}
        sv inert vU monoᵢ link scᵢ X∈
        (rebase-target-membership-forward rb target∈) finalInput)

  source-seal-final : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {pᵢ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X)
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → (link : RebaseAt Wᵢ W′ X Y)
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵢ
    → W ∣ γ ⊢² (V ↓ seal X Rᵢ) ↓ seal Xᴸ (＇ X)
        ⊑ U ↓ seal Y S ∶ q
  source-seal-final sv vU mono rb sc source∈ target∈
      monoᵢ link scᵢ X∈ prem =
    target-source-var-chain (sv-seal sv) vU mono rb sc source∈
      target∈
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↓))
        monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
        (CTI2.⊢↓-sealˣ X∈) prem
        (rebase-pivot-obligation link))

  source-column-seal-final : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {R : Ty Δᴸ} {S : Ty Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {pᵤ : R ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W X Y
    → CTI2.SameCtx γ γ′
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → (link : RebaseAt Wᵢ W′ X Y)
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ R
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵤ
    → W ∣ γ ⊢² V ↓ seal X R ⊑ U ↓ seal Y S ∶ q
  source-column-seal-final mono rb sc target∈ monoᵢ link scᵢ
      X∈ prem =
    source-column-untagged-final mono rb sc target∈
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↓))
        monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
        (CTI2.⊢↓-sealˣ X∈) prem
        (rebase-pivot-obligation link))

  source-column-direct-branch : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {R : Ty Δᴸ} {S : Ty Δᴿ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {pᵤ : (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W X Y
    → CTI2.SameCtx γ γ′
    → targetStoreʷ W ∋ Y ⦂ S
    → W′ ∣ γ′ ⊢² V ↓ seal X R ⊑ U ↓ seal Y S ∶ pᵤ
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceColumnStripBranch W γ (V ↓ seal X R) U X Y S cY q
             Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  source-column-direct-branch sv mono rb sc target∈ prem =
    self-column-sealed rb target∈ (sv-seal sv)
      (source-column-untagged-final mono rb sc target∈ prem)

  source-column-target-cast-branch : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {R : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {pᵤ : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → targetStoreʷ W ∋ Y ⦂ S
    → W′ ∣ γ′ ⊢² V ↓ seal X R ⊑ U ↓ seal Y S ∶ pᵤ
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceColumnStripBranch W γ (V ↓ seal X R) U Xᴸ Y S cY q
             Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  source-column-target-cast-branch {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′} {V = V} {U = U} {R = R} {S = S}
      {X = X} {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {pᵤ = pᵤ}
      {q = q} sv mono rb sc target∈ prem
      with source-seal-pivot-eq (CTI2T.source-typing² prem)
  source-column-target-cast-branch {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′} {V = V} {U = U} {R = R} {S = S}
      {X = .Xᴸ} {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {pᵤ = pᵤ}
      {q = q} sv mono rb sc target∈ prem
      | refl =
    source-column-direct-branch
      {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {R = R} {S = S}
      {X = Xᴸ} {Y = Y} {cY = cY} {pᵤ = pᵤ} {q = q}
      sv mono rb sc target∈ prem

  source-cast-seal-branch : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {νᴸ : Env∼ Δᴸ} {c : νᴸ ⊢ (＇ X) ∼ ★}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {pᵢ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {p₂ : (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → (link : RebaseAt Wᵢ W′ X Y)
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵢ
    → WrapStarCastFinalInput W W′ γ γ′ (V ↓ seal X Rᵢ) U
        Xᴸ X Y S c p₂ q
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ ((V ↓ seal X Rᵢ) ⟨ c ⟩) ★
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  source-cast-seal-branch {W = W} {W′ = W′} {Wᵢ = Wᵢ}
      {γ = γ} {γ′ = γ′} {γᵢ = γᵢ}
      {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
      {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c}
      {pᵢ = pᵢ} {p₂ = p₂} {q = q} sv inert vU mono rb sc
      source∈ target∈ monoᵢ link scᵢ X∈ prem finalInput =
    self-spine-sealed rb target∈
      (sv-seal (sv-cast (sv-seal sv) inert))
      (source-cast-seal-final
        {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
        {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
        {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵢ = pᵢ}
        {p₂ = p₂} {q = q} sv inert vU mono rb sc source∈ target∈
        monoᵢ link scᵢ X∈ prem finalInput)

  source-wrap-star-cast-branch : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {S : Ty Δᴿ} {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {νᴸ : Env∼ Δᴸ} {c : νᴸ ⊢ (＇ X₂) ∼ ★}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
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
    → WrapStarCastFinalInput W W′ γ γ′ V U Xᴸ X₂ Y S c p₂ q
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ (V ⟨ c ⟩) ★ U Xᴸ Y S cY
             q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  source-wrap-star-cast-branch {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′} {V = V ↓ seal X Rᵢ}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y}
      {c = c} {p₂ = p₂} {q = q}
      (sv-seal {V = V} {X = X} {R = Rᵢ} sv) inert vU
      mono rb sc source∈ target∈
      prem@(CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
        ok monoᵢ rbᵢ scᵢ (CTI2.⊢↓-sealˣ X∈) premᵢ .p₂)
      finalInput
      with source-seal-pivot-eq (CTI2T.source-typing² prem)
  source-wrap-star-cast-branch {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′} {V = V ↓ seal .X₂ Rᵢ}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y}
      {c = c} {p₂ = p₂} {q = q}
      (sv-seal {V = V} {X = .X₂} {R = Rᵢ} sv) inert vU
      mono rb sc source∈ target∈
      prem@(CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
        ok monoᵢ rbᵢ scᵢ (CTI2.⊢↓-sealˣ X∈) premᵢ .p₂)
      finalInput
      | refl =
    source-cast-seal-branch
      {W = W} {W′ = W′} {Wᵢ = Wᵢ}
      {γ = γ} {γ′ = γ′} {γᵢ = γᵢ}
      {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
      {X = X₂} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵢ = _}
      {p₂ = p₂} {q = q} sv inert vU mono rb sc source∈ target∈
      monoᵢ (tag-rebase-target rbᵢ p₂) scᵢ X∈ premᵢ
      finalInput
  source-wrap-star-cast-branch {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′} {V = V} {U = U} {S = S}
      {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
      {p₂ = p₂} {q = q} sv inert vU mono rb sc source∈
      target∈ prem finalInput =
    self-spine-sealed rb target∈ (sv-seal (sv-cast sv inert))
      (wrap-star-cast-final
        {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
        {V = V} {U = U} {S = S}
        {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
        {p₂ = p₂} {q = q}
        sv inert vU mono rb sc source∈ target∈ finalInput)

  source-seal-cast-branch : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {S : Ty Δᴿ} {X Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {νᴸ : Env∼ Δᴸ} {c : νᴸ ⊢ (＇ X₂) ∼ ★}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {pᵢ : (＇ X₂) ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X)
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → (link : RebaseAt Wᵢ W′ X Y)
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ ★
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵢ
    → WrapStarCastFinalInput W′ Wᵢ γ′ γᵢ V U X X₂ Y S c pᵢ
        (rebase-pivot-obligation link)
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ ((V ⟨ c ⟩) ↓ seal X ★)
             (＇ X) U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  source-seal-cast-branch {W = W} {W′ = W′} {Wᵢ = Wᵢ}
      {γ = γ} {γ′ = γ′} {γᵢ = γᵢ}
      {V = V} {U = U} {S = S}
      {X = X} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
      {pᵢ = pᵢ} {q = q} sv inert vU mono rb sc source∈
      target∈ monoᵢ link scᵢ X∈ prem finalInput =
    self-spine-sealed rb target∈
      (sv-seal (sv-seal (sv-cast sv inert)))
      (source-seal-cast-final
        {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
        {γᵢ = γᵢ} {V = V} {U = U} {S = S}
        {X = X} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
        {pᵢ = pᵢ} {q = q} sv inert vU mono rb sc source∈
        target∈ monoᵢ link scᵢ X∈ prem finalInput)

  source-seal-branch : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {pᵢ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X)
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → RebaseAt Wᵢ W′ X Y
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵢ
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ (V ↓ seal X Rᵢ) (＇ X)
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  source-seal-branch {W = W} {W′ = W′} {Wᵢ = Wᵢ}
      {γ = γ} {γ′ = γ′} {γᵢ = γᵢ}
      {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
      {X = X} {Xᴸ = Xᴸ} {Y = Y}
      {pᵢ = pᵢ} {q = q} sv vU mono rb sc source∈ target∈
      monoᵢ link scᵢ X∈ prem =
    self-spine-sealed rb target∈ (sv-seal (sv-seal sv))
      (source-seal-final
        {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
        {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
        {X = X} {Xᴸ = Xᴸ} {Y = Y} {pᵢ = pᵢ} {q = q}
        sv vU mono rb sc source∈ target∈ monoᵢ link scᵢ X∈ prem)

source-spine-direct-cast : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {R : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : R ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ R
  → targetStoreʷ W ∋ Y ⦂ S
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p
  → Σ[ Core ∈ Term Δᴸ ]
    Σ[ CoreTy ∈ Ty Δᴸ ]
    Σ[ Xᵒ ∈ TyVar Δᴸ ]
    Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ γᵒ ∈ CtxImp Wᵒ ]
    Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
      (SpineValue Core
       × SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
           Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
source-spine-direct-cast {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {R = R} {S = S} {Xᴸ = Xᴸ} {Y = Y}
    {q = q} sv vU mono rb sc source∈ target∈
    prem =
  self-spine-sealed rb target∈ (sv-seal sv)
    (CTI2.conceal⊑²
      (CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↓))
      mono (CTI2.tag-rebase-varᴸ rb) sc
      (CTI2.⊢↓-sealˣ source∈) prem q)

source-spine-strip-worker-ƛ : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-ƛ (sv-ƛ N) vU mono rb sc source∈
    target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-ƛ N) vU mono rb sc source∈
    target∈ prem

source-spine-strip-worker-Λ : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-Λ (sv-Λ sv) vU mono rb sc source∈
    target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-Λ sv) vU mono rb sc source∈
    target∈ prem
source-spine-strip-worker-Λ (sv-Λ sv) vU mono rb sc source∈
    target∈ D@(CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ (sv-Λ sv)
      nonvar-all nonstar-∀ D)

source-spine-strip-worker-$ : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-$ (sv-$ κ) vU mono rb sc source∈
    target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-$ κ) vU mono rb sc source∈
    target∈ prem

source-spine-strip-worker-cast-cast : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-cast-cast {W′ = W′} {Y = Y}
    (sv-cast {A = ‵ ι} sv CastTerms.inj) vU mono rb sc
    source∈ target∈
    (CTI2.cast⊑cast² {p = p₀} c cY prem p)
    with SPT.right-var-obligation-view {W = W′} {R = ‵ ι}
      {Y = Y} p₀
source-spine-strip-worker-cast-cast {W′ = W′} {Y = Y}
    (sv-cast {A = ‵ ι} sv CastTerms.inj) vU mono rb sc
    source∈ target∈
    (CTI2.cast⊑cast² {p = p₀} c cY prem p)
    | ()
source-spine-strip-worker-cast-cast {W′ = W′} {Y = Y}
    (sv-cast {A = A ⇒ B} sv CastTerms.inj) vU mono rb sc
    source∈ target∈
    (CTI2.cast⊑cast² {p = p₀} c cY prem p)
    with SPT.right-var-obligation-view {W = W′} {R = A ⇒ B}
      {Y = Y} p₀
source-spine-strip-worker-cast-cast {W′ = W′} {Y = Y}
    (sv-cast {A = A ⇒ B} sv CastTerms.inj) vU mono rb sc
    source∈ target∈
    (CTI2.cast⊑cast² {p = p₀} c cY prem p)
    | ()
source-spine-strip-worker-cast-cast {W′ = W′} {Y = Y}
    (sv-cast {A = `∀ A} sv CastTerms.inj) vU mono rb sc
    source∈ target∈
    (CTI2.cast⊑cast² {p = p₀} c cY prem p)
    with SPT.right-var-obligation-view {W = W′} {R = `∀ A}
      {Y = Y} p₀
source-spine-strip-worker-cast-cast {W′ = W′} {Y = Y}
    (sv-cast {A = `∀ A} sv CastTerms.inj) vU mono rb sc
    source∈ target∈
    (CTI2.cast⊑cast² {p = p₀} c cY prem p)
    | ()
source-spine-strip-worker-cast-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V ⟨ c ⟩} {U = U} {R = ★} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj)
    vU mono rb sc source∈ target∈
    (CTI2.cast⊑cast² .c cY prem p)
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {S = S}
      {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c} {q = q}
      sv inert vU mono rb sc source∈ target∈ prem
source-spine-strip-worker-cast-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V ⟨ c ⟩} {U = U} {R = ★} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj)
    vU mono rb sc source∈ target∈
    (CTI2.cast⊑cast² .c cY prem p)
    | wrap-star-cast-final-ready finalInput =
  source-wrap-star-cast-branch
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {S = S}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
    {q = q} sv inert vU mono rb sc source∈ target∈ prem
    finalInput
source-spine-strip-worker-cast-cast (sv-cast sv inert@CastTerms.fun) vU
    mono rb sc source∈ target∈
    D@(CTI2.cast⊑cast² c cY prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ (sv-cast sv inert)
      nonvar-fun nonstar-⇒ D)
source-spine-strip-worker-cast-cast (sv-cast sv inert@CastTerms.all) vU
    mono rb sc source∈ target∈
    D@(CTI2.cast⊑cast² c cY prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ (sv-cast sv inert)
      nonvar-all nonstar-∀ D)
source-spine-strip-worker-cast-cast
    (sv-cast sv inert@(CastTerms.genᵥ A≢★ safe)) vU mono rb sc
    source∈ target∈ D@(CTI2.cast⊑cast² c cY prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ (sv-cast sv inert)
      nonvar-all nonstar-∀ D)

source-spine-strip-worker-cast-step-nonvar : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-cast-step-nonvar
    (sv-cast {V = M ⦂∀ C [ A ]} () CastTerms.inj)
    vU mono rb sc source∈ target∈ D
source-spine-strip-worker-cast-step-nonvar
    (sv-cast {A = ＇ X₂} (sv-cast sv inert₁) CastTerms.inj)
    vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem p)
    with var-value-view (spine-value→Value (sv-cast sv inert₁))
      (CTI2T.source-typing² prem)
source-spine-strip-worker-cast-step-nonvar
    (sv-cast {A = ＇ X₂} (sv-cast sv inert₁) CastTerms.inj)
    vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem p)
    | varv-seal vW X∈′ ()
source-spine-strip-worker-cast-step-nonvar
    (sv-cast
      {V = (M ⦂∀ C [ A ]) ↓ seal X Rᵢ}
      (sv-seal {V = M ⦂∀ C [ A ]} ())
      CastTerms.inj)
    vU mono rb sc source∈ target∈ D
source-spine-strip-worker-cast-step-nonvar
    (sv-cast sv CastTerms.fun) vU mono rb sc
    source∈ target∈ (CTI2.cast⊑² c prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-fun
      nonstar-⇒ prem)
source-spine-strip-worker-cast-step-nonvar
    (sv-cast {A = ‵ ι} sv CastTerms.inj)
    vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-base
      nonstar-ι prem)
source-spine-strip-worker-cast-step-nonvar
    (sv-cast {A = A ⇒ B} sv CastTerms.inj)
    vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-fun
      nonstar-⇒ prem)
source-spine-strip-worker-cast-step-nonvar
    (sv-cast {A = `∀ A} sv CastTerms.inj)
    vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-all
      nonstar-∀ prem)
source-spine-strip-worker-cast-step-nonvar
    (sv-cast sv CastTerms.all) vU mono rb sc
    source∈ target∈ (CTI2.cast⊑² c prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-all
      nonstar-∀ prem)
source-spine-strip-worker-cast-step-nonvar
    (sv-cast sv inert@(CastTerms.genᵥ A≢★ safe)) vU mono rb sc
    source∈ target∈ D@(CTI2.cast⊑² c prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ (sv-cast sv inert)
      nonvar-all nonstar-∀ D)

source-spine-strip-worker-cast-step-over-seal-star
  : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {νᴸ : Env∼ Δᴸ} {c : νᴸ ⊢ (＇ X) ∼ ★}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {Yᵍ : TyVar Δᴿ} {cVar : νᴿ ⊢ (＇ Y) ∼ (＇ Yᵍ)}
      {pᵤ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → RebaseAt Wᵢ W′ X Yᵍ
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵤ
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ ((V ↓ seal X Rᵢ) ⟨ c ⟩) ★
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
{-# NON_COVERING #-}
source-spine-strip-worker-cast-step-over-seal-star
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c}
    {cVar = cVar} {pᵤ = pᵤ} {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem
    with SPT.var-consistency-view cVar
source-spine-strip-worker-cast-step-over-seal-star
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵤ = pᵤ}
    {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem
    | inj₁ refl
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V ↓ seal X Rᵢ} {U = U} {S = S}
      {Xᴸ = Xᴸ} {X₂ = X} {Y = Y} {c = c}
      {p₂ = rebase-pivot-obligation link} {q = q}
      (sv-seal sv) inert vU mono rb sc source∈ target∈
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↓))
        monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
        (CTI2.⊢↓-sealˣ X∈) prem
        (rebase-pivot-obligation link))
source-spine-strip-worker-cast-step-over-seal-star
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵤ = pᵤ}
    {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem
    | inj₁ refl | wrap-star-cast-final-ready finalInput =
  source-cast-seal-branch
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵢ = pᵤ}
    {p₂ = rebase-pivot-obligation link} {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem finalInput
source-spine-strip-worker-cast-step-over-seal-star
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵤ = pᵤ}
    {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem
    | inj₂ ()

source-spine-strip-worker-cast-step-over-seal-name
  : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {νᴸ : Env∼ Δᴸ} {c : νᴸ ⊢ (＇ X) ∼ ★}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {pᵤ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → RebaseAt Wᵢ W′ X Y
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵤ
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ ((V ↓ seal X Rᵢ) ⟨ c ⟩) ★
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
{-# NON_COVERING #-}
source-spine-strip-worker-cast-step-over-seal-name
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵤ = pᵤ}
    {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V ↓ seal X Rᵢ} {U = U} {S = S}
      {Xᴸ = Xᴸ} {X₂ = X} {Y = Y} {c = c}
      {p₂ = rebase-pivot-obligation link} {q = q}
      (sv-seal sv) inert vU mono rb sc source∈ target∈
      (CTI2.conceal⊑²
        (CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↓))
        monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
        (CTI2.⊢↓-sealˣ X∈) prem
        (rebase-pivot-obligation link))
source-spine-strip-worker-cast-step-over-seal-name
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵤ = pᵤ}
    {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem
    | wrap-star-cast-final-ready finalInput =
  source-cast-seal-branch
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {pᵢ = pᵤ}
    {p₂ = rebase-pivot-obligation link} {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem finalInput

source-spine-strip-worker-cast-step-over-seal
  : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {νᴸ : Env∼ Δᴸ} {c : νᴸ ⊢ (＇ X) ∼ ★}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {p★ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ ★}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ ★
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → TagRebaseAtᴸ Wᵢ W′ (just X) Xᴿ?
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
    → CTI2.SourceConcealPartnerOK Wᵢ V (seal X Rᵢ)
        Xᴿ? ((U ↓ seal Y S) ⟨ cY ⟩)
    → Wᵢ ∣ γᵢ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p★
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ ((V ↓ seal X Rᵢ) ⟨ c ⟩) ★
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
{-# NON_COVERING #-}
source-spine-strip-worker-cast-step-over-seal
    {V = M ⦂∀ C [ A ]}
    () inert vU mono rb sc source∈ target∈
    monoᵢ rbᵢ scᵢ X∈ ok prem
source-spine-strip-worker-cast-step-over-seal
    sv inert vU mono rb sc source∈ target∈
    monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ X∈
    (CTI2.seal-partner-ok
      (CTI2.star-rep-target
        _
        (CTI2.rep★-var-tag {c = cVar} aligned)))
    (CTI2.⊑cast² {p = pᵤ} cY prem p★) =
  source-spine-strip-worker-cast-step-over-seal-star
    {cVar = cVar}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem
source-spine-strip-worker-cast-step-over-seal
    sv inert vU mono rb sc source∈ target∈
    monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ X∈
    (CTI2.seal-partner-ok CTI2.name-protected-target)
    (CTI2.⊑cast² {p = pᵤ} cY prem p★) =
  source-spine-strip-worker-cast-step-over-seal-name
    sv inert vU mono rb sc source∈ target∈
    monoᵢ link scᵢ X∈ prem

source-spine-strip-worker-cast-step-wrap : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-cast-step-wrap
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V ⟨ c ⟩} {U = U} {R = ★} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj)
    vU mono rb sc source∈ target∈
    (CTI2.cast⊑² .c (CTI2.⊑cast² {p = p₂} cY prem p★) p)
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {S = S}
      {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
      {p₂ = p₂} {q = q}
      sv inert vU mono rb sc source∈ target∈ prem
source-spine-strip-worker-cast-step-wrap
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V ⟨ c ⟩} {U = U} {R = ★} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj)
    vU mono rb sc source∈ target∈
    (CTI2.cast⊑² .c (CTI2.⊑cast² {p = p₂} cY prem p★) p)
    | wrap-star-cast-final-ready finalInput =
  source-wrap-star-cast-branch
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {S = S}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
    {p₂ = p₂} {q = q} sv inert vU mono rb sc source∈ target∈
    prem finalInput

source-spine-strip-worker-cast-step
  : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {A B : Ty Δᴸ} {S : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {νᴸ : Env∼ Δᴸ} {c : νᴸ ⊢ A ∼ B}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {p₁ : A ⊑ᵂ⟨ W′ ⟩ ★}
      {p₀ : B ⊑ᵂ⟨ W′ ⟩ ★}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → CastTerms.Inert c
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ B
    → targetStoreʷ W ∋ Y ⦂ S
    → W′ ∣ γ′ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p₁
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ (V ⟨ c ⟩) B U Xᴸ Y S cY
             q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
{-# NON_COVERING #-}
source-spine-strip-worker-cast-step
    {V = M ⦂∀ C [ A₀ ]}
    () inert vU mono rb sc source∈ target∈ prem
source-spine-strip-worker-cast-step
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V ↓ seal X Rᵢ} {U = U} {B = ★} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {c = c} {q = q}
    (sv-seal {V = V} {X = X} {R = Rᵢ} sv) inert@CastTerms.inj
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      ok monoᵢ rbᵢ scᵢ (CTI2.⊢↓-sealˣ X∈) prem pᵢ) =
  source-spine-strip-worker-cast-step-over-seal
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {c = c} {q = q}
    sv inert vU mono rb sc source∈ target∈
    monoᵢ rbᵢ scᵢ X∈ ok prem
source-spine-strip-worker-cast-step
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {A = ＇ X₂} {B = ★} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {c = c} {q = q}
    sv inert@CastTerms.inj
    vU mono rb sc source∈ target∈
    (CTI2.⊑cast² {p = p₂} cY prem p★)
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
      {V = V} {U = U} {S = S}
      {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
      {p₂ = p₂} {q = q}
      sv inert vU mono rb sc source∈ target∈ prem
source-spine-strip-worker-cast-step
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {A = ＇ X₂} {B = ★} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {c = c} {q = q}
    sv inert@CastTerms.inj
    vU mono rb sc source∈ target∈
    (CTI2.⊑cast² {p = p₂} cY prem p★)
    | wrap-star-cast-final-ready finalInput =
  source-wrap-star-cast-branch
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {S = S}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
    {p₂ = p₂} {q = q} sv inert vU mono rb sc source∈ target∈
    prem finalInput
source-spine-strip-worker-cast-step {c = c} {p₀ = p₀}
    sv inert vU mono rb sc source∈ target∈ prem =
  source-spine-strip-worker-cast-step-nonvar (sv-cast sv inert)
    vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem p₀)

source-spine-strip-worker-cast : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-cast (sv-cast sv inert) vU mono rb sc
    source∈ target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-cast sv inert) vU mono rb sc
    source∈ target∈ prem
source-spine-strip-worker-cast (sv-cast sv inert) vU mono
    rb sc source∈ target∈
    D@(CTI2.cast⊑cast² c cY prem p) =
  source-spine-strip-worker-cast-cast (sv-cast sv inert) vU
    mono rb sc source∈ target∈ D
source-spine-strip-worker-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V ⟨ c ⟩} {U = U} {R = R} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-cast {V = V} sv inert) vU mono rb sc source∈ target∈
    (CTI2.cast⊑² .c prem p) =
  source-spine-strip-worker-cast-step
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {B = R} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {c = c} {p₀ = p} {q = q}
    sv inert vU mono rb sc source∈ target∈ prem

source-spine-strip-worker-seal-nonvar : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-seal-nonvar (sv-seal {V = M ⦂∀ C [ A ]} ())
    vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-nonvar
    (sv-seal
      (sv-cast {V = M ⦂∀ C [ A ]} () CastTerms.inj))
    vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-Λ sv)) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ rbᵢ scᵢ c⊢
      D@(CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem p) q) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ (sv-Λ sv)
      nonvar-all nonstar-∀ D)
source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-reveal-fun sv)) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ rbᵢ scᵢ c⊢
      (CTI2.reveal⊑² monoᵣ rbᵣ scᵣ c⊢ᵣ prem p) q) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-fun
      nonstar-⇒ prem)
source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-conceal-fun sv)) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ rbᵢ scᵢ c⊢
      (CTI2.conceal⊑² ok monoᵣ rbᵣ scᵣ c⊢ᵣ prem p) q) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-fun
      nonstar-⇒ prem)
source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-reveal-all sv)) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ rbᵢ scᵢ c⊢
      (CTI2.reveal⊑² monoᵣ rbᵣ scᵣ c⊢ᵣ prem p) q) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-all
      nonstar-∀ prem)
source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-conceal-all sv)) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ rbᵢ scᵢ c⊢
      (CTI2.conceal⊑² ok monoᵣ rbᵣ scᵣ c⊢ᵣ prem p) q) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-all
      nonstar-∀ prem)

source-spine-strip-worker-seal-cast : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-seal-cast
    (sv-seal
      (sv-cast {V = M ⦂∀ C [ A ]} () CastTerms.inj))
    vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok
        (CTI2.star-rep-target
          _
          (CTI2.rep★-var-tag {c = cVar} aligned)))
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑cast² {p = pᵤ} .c cY prem pᵢ) p)
    with SPT.var-consistency-view cVar
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok
        (CTI2.star-rep-target
          _
          (CTI2.rep★-var-tag {c = cVar} aligned)))
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑cast² {p = pᵤ} .c cY prem pᵢ) p)
    | inj₁ refl
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W′} {W′ = Wᵢ} {γ = γ′} {γ′ = γᵢ}
      {V = V} {U = U} {S = S}
      {Xᴸ = X} {X₂ = X₂} {Y = Y} {c = c}
      {p₂ = pᵤ} {q = rebase-pivot-obligation link}
      sv inert vU monoᵢ link scᵢ X∈
      (rebase-target-membership-forward rb target∈) prem
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok
        (CTI2.star-rep-target
          _
          (CTI2.rep★-var-tag {c = cVar} aligned)))
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑cast² {p = pᵤ} .c cY prem pᵢ) p)
    | inj₁ refl | wrap-star-cast-final-ready finalInput =
  source-seal-cast-branch
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {S = S}
    {X = X} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
    {pᵢ = pᵤ} {q = q} sv inert vU mono rb sc source∈
    target∈ monoᵢ link scᵢ X∈ prem finalInput
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok
        (CTI2.star-rep-target
          _
          (CTI2.rep★-var-tag {c = cVar} aligned)))
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑cast² {p = pᵤ} .c cY prem pᵢ) p)
    | inj₂ ()
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑cast² {p = pᵤ} .c cY prem pᵢ) p)
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W′} {W′ = Wᵢ} {γ = γ′} {γ′ = γᵢ}
      {V = V} {U = U} {S = S}
      {Xᴸ = X} {X₂ = X₂} {Y = Y} {c = c}
      {p₂ = pᵤ} {q = rebase-pivot-obligation link}
      sv inert vU monoᵢ link scᵢ X∈
      (rebase-target-membership-forward rb target∈) prem
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑cast² {p = pᵤ} .c cY prem pᵢ) p)
    | wrap-star-cast-final-ready finalInput =
  source-seal-cast-branch
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {S = S}
    {X = X} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
    {pᵢ = pᵤ} {q = q} sv inert vU mono rb sc source∈
    target∈ monoᵢ link scᵢ X∈ prem finalInput
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑² .c (CTI2.⊑cast² {p = pᵤ} cY prem pᵢ) p₀) p)
    -- OPTION-A DEBT (2026-08-16): non-final chain alternatives are
    -- swallowed by this function's legacy NON_COVERING pragma; real
    -- handling is part of the scheduled repair (see TODO.md and
    -- notes/lg1h-legacy-noncovering-inventory.md).
    with wrap-star-cast-final-view
      {W = W′} {W′ = Wᵢ} {γ = γ′} {γ′ = γᵢ}
      {V = V} {U = U} {S = S}
      {Xᴸ = X} {X₂ = X₂} {Y = Y} {c = c}
      {p₂ = pᵤ} {q = rebase-pivot-obligation link}
      sv inert vU monoᵢ link scᵢ X∈
      (rebase-target-membership-forward rb target∈) prem
source-spine-strip-worker-seal-cast
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = (V ⟨ c ⟩) ↓ seal X ★} {U = U} {R = ＇ X}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    (sv-seal {V = V ⟨ c ⟩} {X = X} {R = ★}
      (sv-cast {V = V} {A = ＇ X₂} sv inert@CastTerms.inj))
    vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵢ} {γ′ = γᵢ}
      (CTI2.seal-partner-ok CTI2.name-protected-target)
      monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ
      (CTI2.⊢↓-sealˣ X∈)
      (CTI2.cast⊑² .c (CTI2.⊑cast² {p = pᵤ} cY prem pᵢ) p₀) p)
    | wrap-star-cast-final-ready finalInput =
  source-seal-cast-branch
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {S = S}
    {X = X} {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} {c = c}
    {pᵢ = pᵤ} {q = q} sv inert vU mono rb sc source∈
    target∈ monoᵢ link scᵢ X∈ prem finalInput

source-spine-strip-worker-seal-source
  : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵢ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵢ : CtxImp Wᵢ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {νᴿ : Env∼ Δᴿ} {cY : νᴿ ⊢ (＇ Y) ∼ ★}
      {p★ : Rᵢ ⊑ᵂ⟨ Wᵢ ⟩ ★}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X)
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵢ
    → TagRebaseAtᴸ Wᵢ W′ (just X) Xᴿ?
    → CTI2.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ X ⦂ Rᵢ
    → CTI2.SourceConcealPartnerOK Wᵢ V (seal X Rᵢ)
        Xᴿ? ((U ↓ seal Y S) ⟨ cY ⟩)
    → Wᵢ ∣ γᵢ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p★
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ (V ↓ seal X Rᵢ) (＇ X)
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
{-# NON_COVERING #-}
source-spine-strip-worker-seal-source
    {V = M ⦂∀ C [ A ]}
    () vU mono rb sc source∈ target∈
    monoᵢ rbᵢ scᵢ X∈ ok prem
source-spine-strip-worker-seal-source
    sv vU mono rb sc source∈ target∈
    monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ X∈
    (CTI2.seal-partner-ok
      (CTI2.star-rep-target
        _
        (CTI2.rep★-var-tag {c = cVar} aligned)))
    (CTI2.⊑cast² {p = pᵤ} cY prem p★)
    with SPT.var-consistency-view cVar
source-spine-strip-worker-seal-source
    {W = W} {W′ = W′} {Wᵢ = Wᵢ}
    {γ = γ} {γ′ = γ′} {γᵢ = γᵢ}
    {V = V} {U = U} {Rᵢ = Rᵢ}
    {S = S} {X = X} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    sv vU mono rb sc source∈ target∈
    monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ X∈
    (CTI2.seal-partner-ok
      (CTI2.star-rep-target
        _
        (CTI2.rep★-var-tag {c = cVar} aligned)))
    (CTI2.⊑cast² {p = pᵤ} cY prem p★)
    | inj₁ refl =
  source-seal-branch
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {pᵢ = pᵤ} {q = q}
    sv vU mono rb sc source∈ target∈ monoᵢ link scᵢ X∈ prem
source-spine-strip-worker-seal-source
    {W = W} {W′ = W′} {Wᵢ = Wᵢ}
    {γ = γ} {γ′ = γ′} {γᵢ = γᵢ}
    {V = V} {U = U} {Rᵢ = Rᵢ}
    {S = S} {X = X} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    sv vU mono rb sc source∈ target∈
    monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ X∈
    (CTI2.seal-partner-ok
      (CTI2.star-rep-target
        _
        (CTI2.rep★-var-tag {c = cVar} aligned)))
    (CTI2.⊑cast² {p = pᵤ} cY prem p★)
    | inj₂ ()
source-spine-strip-worker-seal-source
    {W = W} {W′ = W′} {Wᵢ = Wᵢ}
    {γ = γ} {γ′ = γ′} {γᵢ = γᵢ}
    {V = V} {U = U} {Rᵢ = Rᵢ}
    {S = S} {X = X} {Xᴸ = Xᴸ} {Y = Y} {q = q}
    sv vU mono rb sc source∈ target∈
    monoᵢ (CTI2.tag-rebase-varᴸ link) scᵢ X∈
    (CTI2.seal-partner-ok CTI2.name-protected-target)
    (CTI2.⊑cast² {p = pᵤ} cY prem p★) =
  source-seal-branch
    {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
    {γᵢ = γᵢ} {V = V} {U = U} {Rᵢ = Rᵢ} {S = S}
    {X = X} {Xᴸ = Xᴸ} {Y = Y} {pᵢ = pᵤ} {q = q}
    sv vU mono rb sc source∈ target∈ monoᵢ link scᵢ X∈ prem

source-spine-strip-worker-seal-D
  : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {Rᵢ R : Ty Δᴸ} {S : Ty Δᴿ}
      {X Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {p₀ : R ⊑ᵂ⟨ W′ ⟩ ★}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → W′ ∣ γ′ ⊢² V ↓ seal X Rᵢ
        ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p₀
    → SpineValue V
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ R
    → targetStoreʷ W ∋ Y ⦂ S
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ (V ↓ seal X Rᵢ) R
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
{-# NON_COVERING #-}
source-spine-strip-worker-seal-D D@(CTI2.⊑cast² cY prem p)
    sv vU mono rb sc source∈ target∈ =
  source-spine-direct-cast (sv-seal sv) vU mono rb sc
    source∈ target∈ prem
source-spine-strip-worker-seal-D
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.cast⊑cast² c cY prem pᵢ) p)
    sv vU mono rb sc source∈ target∈ =
  source-spine-strip-worker-seal-cast
    (sv-seal sv) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-D
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.cast⊑² c prem pᵢ) p)
    sv vU mono rb sc source∈ target∈ =
  source-spine-strip-worker-seal-cast
    (sv-seal sv) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-D
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem pᵢ) p)
    sv vU mono rb sc source∈ target∈ =
  source-spine-strip-worker-seal-nonvar (sv-seal sv) vU mono rb sc
    source∈ target∈ D
source-spine-strip-worker-seal-D
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.reveal⊑² monoᵣ rbᵣ scᵣ c⊢ᵣ prem pᵢ) p)
    sv vU mono rb sc source∈ target∈ =
  source-spine-strip-worker-seal-nonvar (sv-seal sv) vU mono rb sc
    source∈ target∈ D
source-spine-strip-worker-seal-D
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.conceal⊑² okᵣ monoᵣ rbᵣ scᵣ c⊢ᵣ prem pᵢ) p)
    sv vU mono rb sc source∈ target∈ =
  source-spine-strip-worker-seal-nonvar (sv-seal sv) vU mono rb sc
    source∈ target∈ D
source-spine-strip-worker-seal-D
    (CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ
      (CTI2.⊢↓-sealˣ X∈) prem p)
    sv vU mono rb sc source∈ target∈ =
  source-spine-strip-worker-seal-source sv vU mono
    rb sc source∈ target∈ monoᵢ rbᵢ scᵢ X∈ ok prem

source-spine-strip-worker-seal : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-seal (sv-seal sv) vU mono rb sc
    source∈ target∈ D =
  source-spine-strip-worker-seal-D D sv vU mono rb sc
    source∈ target∈

source-spine-strip-worker-reveal-fun : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-reveal-fun (sv-reveal-fun sv) vU mono
    rb sc source∈ target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-reveal-fun sv) vU mono rb sc
    source∈ target∈ prem
source-spine-strip-worker-reveal-fun (sv-reveal-fun sv) vU mono
    rb sc source∈ target∈
    (CTI2.reveal⊑² monoᵢ rbᵢ scᵢ c⊢ prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-fun
      nonstar-⇒ prem)

source-spine-strip-worker-conceal-fun : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-conceal-fun (sv-conceal-fun sv) vU mono
    rb sc source∈ target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-conceal-fun sv) vU mono rb sc
    source∈ target∈ prem
source-spine-strip-worker-conceal-fun (sv-conceal-fun sv) vU mono
    rb sc source∈ target∈
    (CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢ prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-fun
      nonstar-⇒ prem)

source-spine-strip-worker-reveal-all : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-reveal-all (sv-reveal-all sv) vU mono
    rb sc source∈ target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-reveal-all sv) vU mono rb sc
    source∈ target∈ prem
source-spine-strip-worker-reveal-all (sv-reveal-all sv) vU mono
    rb sc source∈ target∈
    (CTI2.reveal⊑² monoᵢ rbᵢ scᵢ c⊢ prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-all
      nonstar-∀ prem)

source-spine-strip-worker-conceal-all : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-conceal-all (sv-conceal-all sv) vU mono
    rb sc source∈ target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-conceal-all sv) vU mono rb sc
    source∈ target∈ prem
source-spine-strip-worker-conceal-all (sv-conceal-all sv) vU mono
    rb sc source∈ target∈
    (CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢ prem p) =
  ⊥-elim
    (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-all
      nonstar-∀ prem)

source-spine-strip-worker : SourceSpineStripWorker
{-# NON_COVERING #-}
source-spine-strip-worker (sv-ƛ N) vU mono rb sc source∈
    target∈ D =
  source-spine-strip-worker-ƛ (sv-ƛ N) vU mono rb sc source∈
    target∈ D
source-spine-strip-worker (sv-Λ sv) vU mono rb sc source∈
    target∈ D =
  source-spine-strip-worker-Λ (sv-Λ sv) vU mono rb sc source∈
    target∈ D
source-spine-strip-worker (sv-$ κ) vU mono rb sc source∈
    target∈ D =
  source-spine-strip-worker-$ (sv-$ κ) vU mono rb sc source∈
    target∈ D
source-spine-strip-worker (sv-cast sv inert) vU mono rb sc
    source∈ target∈ D =
  source-spine-strip-worker-cast (sv-cast sv inert) vU mono rb sc
    source∈ target∈ D
source-spine-strip-worker (sv-seal sv) vU mono rb sc source∈
    target∈ D =
  source-spine-strip-worker-seal (sv-seal sv) vU mono rb sc source∈
    target∈ D
source-spine-strip-worker (sv-reveal-fun sv) vU mono rb sc
    source∈ target∈ D =
  source-spine-strip-worker-reveal-fun (sv-reveal-fun sv) vU mono
    rb sc source∈ target∈ D
source-spine-strip-worker (sv-conceal-fun sv) vU mono rb sc
    source∈ target∈ D =
  source-spine-strip-worker-conceal-fun (sv-conceal-fun sv) vU mono
    rb sc source∈ target∈ D
source-spine-strip-worker (sv-reveal-all sv) vU mono rb sc
    source∈ target∈ D =
  source-spine-strip-worker-reveal-all (sv-reveal-all sv) vU mono
    rb sc source∈ target∈ D
source-spine-strip-worker (sv-conceal-all sv) vU mono rb sc
    source∈ target∈ D =
  source-spine-strip-worker-conceal-all (sv-conceal-all sv) vU mono
    rb sc source∈ target∈ D

source-column-strip-worker-D : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → W′ ∣ γ′ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → targetStoreʷ W ∋ Y ⦂ S
  → Σ[ Core ∈ Term Δᴸ ]
    Σ[ CoreTy ∈ Ty Δᴸ ]
    Σ[ Xᵒ ∈ TyVar Δᴸ ]
    Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ γᵒ ∈ CtxImp Wᵒ ]
    Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
      (SpineValue Core
       × SourceColumnStripBranch W γ V U Xᴸ Y S cY q
           Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
source-column-strip-worker-seal-D : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {R : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → W′ ∣ γ′ ⊢² V ↓ seal Xᴸ R
      ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → targetStoreʷ W ∋ Y ⦂ S
  → Σ[ Core ∈ Term Δᴸ ]
    Σ[ CoreTy ∈ Ty Δᴸ ]
    Σ[ Xᵒ ∈ TyVar Δᴸ ]
    Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ γᵒ ∈ CtxImp Wᵒ ]
    Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
      (SpineValue Core
       × SourceColumnStripBranch W γ (V ↓ seal Xᴸ R) U Xᴸ Y S cY q
           Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
source-column-strip-worker-seal-D {W = W} {W′ = W′} {γ = γ}
    {γ′ = γ′} {V = V} {U = U} {R = R} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {q = q}
    D sv vU mono rb sc target∈
    with source-column-seal-D-case D
source-column-strip-worker-seal-D {W = W} {W′ = W′} {γ = γ}
    {γ′ = γ′} {V = V} {U = U} {R = R} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {q = q}
    D sv vU mono rb sc target∈
    | column-seal-target-cast-case {pᵤ = pᵤ} prem =
  source-column-direct-branch
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V} {U = U} {R = R} {S = S}
    {X = Xᴸ} {Y = Y} {cY = cY} {pᵤ = pᵤ} {q = q}
    sv mono rb sc target∈ prem
source-column-strip-worker-seal-D {W = W} {W′ = W′} {γ = γ}
    {γ′ = γ′} {V = V} {U = U} {R = R} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {q = q}
    D sv vU mono rb sc target∈
    | column-seal-source-case {Wᵢ = Wᵢ} {γᵢ = γᵢ}
        {pᵤ = pᵤ} monoᵢ link scᵢ X∈ prem =
  self-column-sealed rb target∈ (sv-seal sv)
    (source-column-seal-final
      {W = W} {W′ = W′} {Wᵢ = Wᵢ} {γ = γ} {γ′ = γ′}
      {γᵢ = γᵢ} {V = V} {U = U} {R = R} {S = S}
      {X = Xᴸ} {Y = Y} {pᵤ = pᵤ} {q = q}
      mono rb sc target∈ monoᵢ link scᵢ X∈ prem)

source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-ƛ N) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-ƛ N))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-ƛ N) vU mono rb sc target∈
    | varv-seal vW X∈ ()
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-Λ sv) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-Λ sv))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-Λ sv) vU mono rb sc target∈
    | varv-seal vW X∈ ()
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-$ κ) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-$ κ))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-$ κ) vU mono rb sc target∈
    | varv-seal vW X∈ ()
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-cast sv inert) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-cast sv inert))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-cast sv inert) vU mono rb sc target∈
    | varv-seal vW X∈ ()
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    {γ′ = γ′} {V = V ↓ seal X R} {U = U} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {q = q}
    D (sv-seal sv) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-seal sv))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    {γ′ = γ′} {V = .(V₀ ↓ seal Xᴸ R)} {U = U} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {q = q}
    D (sv-seal sv) vU mono rb sc target∈
    | varv-seal {W = V₀} {R = R} vV X∈ refl =
  source-column-strip-worker-seal-D
    {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {V = V₀} {U = U} {R = R} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {q = q}
    D (value→spine vV) vU mono rb sc target∈
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-reveal-fun sv) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-reveal-fun sv))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-reveal-fun sv) vU mono rb sc target∈
    | varv-seal vW X∈ ()
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-conceal-fun sv) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-conceal-fun sv))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-conceal-fun sv) vU mono rb sc target∈
    | varv-seal vW X∈ ()
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-reveal-all sv) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-reveal-all sv))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-reveal-all sv) vU mono rb sc target∈
    | varv-seal vW X∈ ()
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-conceal-all sv) vU mono rb sc target∈
    with var-value-view (spine-value→Value (sv-conceal-all sv))
      (CTI2T.source-typing² D)
source-column-strip-worker-D {W = W} {W′ = W′} {γ = γ}
    D (sv-conceal-all sv) vU mono rb sc target∈
    | varv-seal vW X∈ ()

source-column-strip-worker : SourceColumnStripWorker
source-column-strip-worker sv vU mono rb sc target∈ D =
  source-column-strip-worker-D D sv vU mono rb sc target∈
