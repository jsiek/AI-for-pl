module proof.DGG.WorldDecay where

-- File Charter:
--   * Defines monotonic decay of local-world imprecision marks toward X⊑★.
--   * Transports type and context imprecision obligations across decay.
--   * Blends premise worlds with decayed conclusion-world marks.
--   * Honestifies worlds by dynamizing centers without a target alignment.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Types
open import Consistency using (toRenameᵗ)
open import Imprecision
import proof.DGG.CtxImp as CTI2
open CTI2 using
  (World;
   _⊑ᵂ⟨_⟩_;
   CtxImp;
   ctx-imp;
   _∋ʷ_⦂_;
   Zʷ;
   Sʷ;
   SameCtx;
   same-[];
   same-∷)

------------------------------------------------------------------------
-- Type-level environment monotonicity
------------------------------------------------------------------------

⊑-env-mono : ∀ {Δ} {μ μᵈ : ImpEnv Δ} {A B : Ty Δ}
  → (∀ Z → μ Z ≡ X⊑★ → μᵈ Z ≡ X⊑★)
  → μ ⊢ A ⊑ B
  → μᵈ ⊢ A ⊑ B
⊑-env-mono cond ★⊑★ = ★⊑★
⊑-env-mono cond ι⊑ι = ι⊑ι
⊑-env-mono cond X⊑X = X⊑X
⊑-env-mono cond (⇒⊑⇒ A⊑A′ B⊑B′) =
  ⇒⊑⇒ (⊑-env-mono cond A⊑A′) (⊑-env-mono cond B⊑B′)
⊑-env-mono cond (∀⊑∀ A⊑B) =
  ∀⊑∀ (⊑-env-mono lift-cond A⊑B)
  where
  lift-cond : ∀ Z
    → extᵐ _ Z ≡ X⊑★
    → extᵐ _ Z ≡ X⊑★
  lift-cond Fin.zero eq = eq
  lift-cond (Fin.suc Z) eq = cond Z eq
⊑-env-mono cond (⇒⊑★ A⊑★ B⊑★) =
  ⇒⊑★ (⊑-env-mono cond A⊑★) (⊑-env-mono cond B⊑★)
⊑-env-mono cond ι⊑★ = ι⊑★
⊑-env-mono cond (X⊑★ eq) = X⊑★ (cond _ eq)
⊑-env-mono cond (∀⊑ Anv z∈A A⊑B) =
  ∀⊑ Anv z∈A (⊑-env-mono lift-cond A⊑B)
  where
  lift-cond : ∀ Z
    → instᵐ _ Z ≡ X⊑★
    → instᵐ _ Z ≡ X⊑★
  lift-cond Fin.zero eq = eq
  lift-cond (Fin.suc Z) eq = cond Z eq
⊑-env-mono cond ∀★⊑★ = ∀★⊑★
⊑-env-mono cond (∀⊑★ Ans A⊑★) =
  ∀⊑★ Ans (⊑-env-mono lift-cond A⊑★)
  where
  lift-cond : ∀ Z
    → extᵐ _ Z ≡ X⊑★
    → extᵐ _ Z ≡ X⊑★
  lift-cond Fin.zero eq = eq
  lift-cond (Fin.suc Z) eq = cond Z eq
⊑-env-mono cond bot-elim = bot-elim
⊑-env-mono cond bot⊑★ = bot⊑★

------------------------------------------------------------------------
-- Environment decay between worlds
------------------------------------------------------------------------

record EnvDecay {Δᴸ Δᴿ Δ} (W Wᵈ : World Δᴸ Δᴿ Δ) : Set where
  constructor env-decay
  field
    ηᴸ-same : CTI2.ηᴸʷ Wᵈ ≡ CTI2.ηᴸʷ W
    ηᴿ-same : CTI2.ηᴿʷ Wᵈ ≡ CTI2.ηᴿʷ W
    sourceStore-same :
      CTI2.sourceStoreʷ Wᵈ ≡ CTI2.sourceStoreʷ W
    targetStore-same :
      CTI2.targetStoreʷ Wᵈ ≡ CTI2.targetStoreʷ W
    env-mono : CTI2.ImpEnvMono W Wᵈ

open EnvDecay public

decay⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → EnvDecay W Wᵈ
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ Wᵈ ⟩ B
decay⊑ᵂ {W = W} {Wᵈ = Wᵈ} {A = A} {B = B} dec p =
  CTI2.imprecision-cong
    (sym (cong (λ η → renameᵗ (toRenameᵗ η) A) (ηᴸ-same dec)))
    (sym (cong (λ η → renameᵗ (toRenameᵗ η) B) (ηᴿ-same dec)))
    (⊑-env-mono (CTI2.dynamic-preserved (env-mono dec)) p)

decay-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → EnvDecay W W
decay-refl =
  env-decay refl refl refl refl CTI2.impEnvMono-refl

decay-dynamic-reflect : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : World Δᴸ Δᴿ Δ}
  → EnvDecay W Wᵈ
  → ∀ Z
  → CTI2.impEnvʷ Wᵈ Z ≡ X⊑★
  → CTI2.impEnvʷ W Z ≡ X⊑★
decay-dynamic-reflect dec =
  CTI2.impEnvMono-reflect-dynamic (env-mono dec)

reflect⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → EnvDecay W Wᵈ
  → A ⊑ᵂ⟨ Wᵈ ⟩ B
  → A ⊑ᵂ⟨ W ⟩ B
reflect⊑ᵂ {A = A} {B = B} dec p =
  CTI2.imprecision-cong
    (cong (λ η → renameᵗ (toRenameᵗ η) A) (ηᴸ-same dec))
    (cong (λ η → renameᵗ (toRenameᵗ η) B) (ηᴿ-same dec))
    (⊑-env-mono (decay-dynamic-reflect dec) p)

------------------------------------------------------------------------
-- Context decay
------------------------------------------------------------------------

decayCtx : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : World Δᴸ Δᴿ Δ}
  → (dec : EnvDecay W Wᵈ)
  → CtxImp W
  → CtxImp Wᵈ
decayCtx dec [] = []
decayCtx dec (ctx-imp A B p ∷ γ) =
  ctx-imp A B (decay⊑ᵂ dec p) ∷ decayCtx dec γ

decay∋ʷ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → γ ∋ʷ x ⦂ ctx-imp A B p
  → decayCtx dec γ ∋ʷ x ⦂ ctx-imp A B (decay⊑ᵂ dec p)
decay∋ʷ dec Zʷ = Zʷ
decay∋ʷ dec (Sʷ x∈) = Sʷ (decay∋ʷ dec x∈)

decaySameCtx : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W Wᵈ : World Δᴸ Δᴿ Δ}
    {W′ W′ᵈ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CtxImp W′}
  → (dec : EnvDecay W Wᵈ)
  → (dec′ : EnvDecay W′ W′ᵈ)
  → SameCtx γ γ′
  → SameCtx (decayCtx dec γ) (decayCtx dec′ γ′)
decaySameCtx dec dec′ same-[] = same-[]
decaySameCtx dec dec′ (same-∷ same) =
  same-∷ (decaySameCtx dec dec′ same)

------------------------------------------------------------------------
-- Blending premise-world marks with a decayed conclusion world
------------------------------------------------------------------------

blendVar : VarImp → VarImp → VarImp
blendVar X⊑★ v = X⊑★
blendVar X⊑X v = v

blendWorld : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
blendWorld W′ Wᵈ = W′

private
  blend-left-mono : ∀ {v vᵈ}
    → v ≡ X⊑★
    → blendVar v vᵈ ≡ X⊑★
  blend-left-mono refl = refl

blend-decay : ∀ {Δᴸ Δᴿ Δ}
    {W′ Wᵈ : World Δᴸ Δᴿ Δ}
  → EnvDecay W′ (blendWorld W′ Wᵈ)
blend-decay = decay-refl

blend-mono : ∀ {Δᴸ Δᴿ Δ}
    {W W′ Wᵈ : World Δᴸ Δᴿ Δ}
  → EnvDecay W Wᵈ
  → CTI2.ImpEnvMono W W′
  → CTI2.ImpEnvMono Wᵈ (blendWorld W′ Wᵈ)
blend-mono dec mono =
  CTI2.impEnvMono-trans (CTI2.impEnvMono-sym (env-mono dec)) mono

------------------------------------------------------------------------
-- Honest worlds
------------------------------------------------------------------------

honestify : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
honestify = CTI2.honestifyʷ

honestify-decay : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → EnvDecay W (honestify W)
honestify-decay {W = W} =
  env-decay refl refl refl refl
    (CTI2.imp-env-mono
      (CTI2.honestEnv-mono (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W))
      precise)
  where
  precise : ∀ Z
    → CTI2.impEnvʷ W Z ≡ X⊑X
    → CTI2.impEnvʷ (honestify W) Z ≡ X⊑X
  precise Z mark with CTI2.precise-center-has-source W Z mark
  precise Z mark | Xᴸ , aligned
      with CTI2.preciseMarksAligned (CTI2.invariantsʷ W) Xᴸ
        (trans (cong (CTI2.impEnvʷ W) aligned) mark)
  precise Z mark | Xᴸ , aligned | Xᴿ , target-aligned =
    trans
      (CTI2.honestEnv-aligned (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W) Z
        (Xᴿ , trans target-aligned aligned))
      mark

honestify-mark : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
    (Z : TyVar Δ)
  → (∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ ≢ Z)
  → CTI2.impEnvʷ (honestify W) Z ≡ X⊑★
honestify-mark W Z no-target =
  CTI2.honestEnv-unaligned (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W) Z no-target

honestify-WF : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
  → ∀ Xᴸ
  → CTI2.impEnvʷ (honestify W)
      (toRenameᵗ (CTI2.ηᴸʷ (honestify W)) Xᴸ) ≡ X⊑X
  → Σ[ Xᴿ ∈ TyVar Δᴿ ]
      toRenameᵗ (CTI2.ηᴿʷ (honestify W)) Xᴿ
        ≡ toRenameᵗ (CTI2.ηᴸʷ (honestify W)) Xᴸ
honestify-WF W =
  CTI2.preciseMarksAligned (CTI2.invariantsʷ (honestify W))
