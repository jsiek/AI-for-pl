module proof.DGG.WorldDecay where

-- File Charter:
--   * Defines monotonic decay of local-world imprecision marks toward X⊑★.
--   * Transports type and context imprecision obligations across decay.
--   * Blends premise worlds with decayed conclusion-world marks.
--   * Honestifies worlds by dynamizing centers without a target alignment.

open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
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
decay⊑ᵂ
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    (env-decay refl refl refl refl mono) p =
  ⊑-env-mono mono p

decay-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → EnvDecay W W
decay-refl = env-decay refl refl refl refl (λ Z eq → eq)

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
blendWorld W′ Wᵈ =
  CTI2.world (CTI2.ηᴸʷ W′) (CTI2.ηᴿʷ W′)
    (λ Z → blendVar (CTI2.impEnvʷ W′ Z) (CTI2.impEnvʷ Wᵈ Z))
    (CTI2.sourceStoreʷ W′) (CTI2.targetStoreʷ W′)

private
  blend-left-mono : ∀ {v vᵈ}
    → v ≡ X⊑★
    → blendVar v vᵈ ≡ X⊑★
  blend-left-mono refl = refl

blend-decay : ∀ {Δᴸ Δᴿ Δ}
    {W′ Wᵈ : World Δᴸ Δᴿ Δ}
  → EnvDecay W′ (blendWorld W′ Wᵈ)
blend-decay =
  env-decay refl refl refl refl (λ Z eq → blend-left-mono eq)

blend-mono : ∀ {Δᴸ Δᴿ Δ}
    {W′ Wᵈ : World Δᴸ Δᴿ Δ}
  → CTI2.ImpEnvMono Wᵈ (blendWorld W′ Wᵈ)
blend-mono {W′ = W′} {Wᵈ = Wᵈ} Z eq
    with CTI2.impEnvʷ W′ Z
blend-mono {W′ = W′} {Wᵈ = Wᵈ} Z eq | X⊑★ = refl
blend-mono {W′ = W′} {Wᵈ = Wᵈ} Z eq | X⊑X = eq

------------------------------------------------------------------------
-- Honest worlds
------------------------------------------------------------------------

private
  fin-suc-injective : ∀ {n} {X Y : Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

alignedᴿ? : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ) (Z : TyVar Δ)
  → Dec (Σ[ Xᴿ ∈ TyVar Δᴿ ] toRenameᵗ ηᴿ Xᴿ ≡ Z)
alignedᴿ? empty Z = no λ { (() , eq) }
alignedᴿ? (keep ηᴿ) Fin.zero = yes (Fin.zero , refl)
alignedᴿ? (keep ηᴿ) (Fin.suc Z) with alignedᴿ? ηᴿ Z
alignedᴿ? (keep ηᴿ) (Fin.suc Z) | yes (Xᴿ , eq) =
  yes (Fin.suc Xᴿ , cong Fin.suc eq)
alignedᴿ? (keep ηᴿ) (Fin.suc Z) | no unaligned =
  no λ
    { (Fin.zero , ())
    ; (Fin.suc Xᴿ , eq) → unaligned (Xᴿ , fin-suc-injective eq)
    }
alignedᴿ? (skip ηᴿ) Fin.zero = no λ { (Xᴿ , ()) }
alignedᴿ? (skip ηᴿ) (Fin.suc Z) with alignedᴿ? ηᴿ Z
alignedᴿ? (skip ηᴿ) (Fin.suc Z) | yes (Xᴿ , eq) =
  yes (Xᴿ , cong Fin.suc eq)
alignedᴿ? (skip ηᴿ) (Fin.suc Z) | no unaligned =
  no λ { (Xᴿ , eq) → unaligned (Xᴿ , fin-suc-injective eq) }

honestEnv : ∀ {Δᴿ Δ} → (Δᴿ ↪ᵗ Δ) → ImpEnv Δ → ImpEnv Δ
honestEnv ηᴿ μ Z with alignedᴿ? ηᴿ Z
honestEnv ηᴿ μ Z | yes aligned = μ Z
honestEnv ηᴿ μ Z | no unaligned = X⊑★

honestify : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
honestify W =
  CTI2.world (CTI2.ηᴸʷ W) (CTI2.ηᴿʷ W)
    (honestEnv (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W))
    (CTI2.sourceStoreʷ W) (CTI2.targetStoreʷ W)

private
  honestEnv-mono : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ)
      (μ : ImpEnv Δ) (Z : TyVar Δ)
    → μ Z ≡ X⊑★
    → honestEnv ηᴿ μ Z ≡ X⊑★
  honestEnv-mono ηᴿ μ Z eq with alignedᴿ? ηᴿ Z
  honestEnv-mono ηᴿ μ Z eq | yes aligned = eq
  honestEnv-mono ηᴿ μ Z eq | no unaligned = refl

honestify-decay : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → EnvDecay W (honestify W)
honestify-decay {W = W} =
  env-decay refl refl refl refl
    (honestEnv-mono (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W))

honestify-WF : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
  → CTI2.WFWorld (honestify W)
honestify-WF W Xᴸ precise
    with alignedᴿ? (CTI2.ηᴿʷ W)
           (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
honestify-WF W Xᴸ precise | yes (Xᴿ , aligned) = Xᴿ , aligned
honestify-WF W Xᴸ () | no unaligned
