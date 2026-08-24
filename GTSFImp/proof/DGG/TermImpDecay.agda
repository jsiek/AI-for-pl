module proof.DGG.TermImpDecay where

-- File Charter:
--   * Transports version-2 cast-term imprecision across world decay.
--   * Lifts decay through type binders and term-context lifting.
--   * Decays pivot-local rebasing and wrapper-rule premise worlds.
--   * Exports obligation-insensitive transport via proof irrelevance.

open import Data.List using ([]; _∷_)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (store-lift; _∋_⦂_)
open import Consistency using (keep; skip; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
open import Imprecision
import proof.DGG.CastTermImprecision as CTI2
open import proof.DGG.ConversionPivotAlignment using
  (GeneratorPosition; generator-absent; revealGeneratorPosition;
   concealGeneratorPosition; revealGeneratorPosition-store-transport;
   concealGeneratorPosition-store-transport)
import proof.DGG.CtxImp as CTX
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.WorldDecay
import proof.DGG.WorldDecay as WD
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using (subst-⊑)

------------------------------------------------------------------------
-- Decay under type binders
------------------------------------------------------------------------

liftDecayBoth : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → EnvDecay W Wᵈ
  → EnvDecay (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v Wᵈ)
liftDecayBoth {W = W} {Wᵈ = Wᵈ} v dec =
  env-decay
    (cong keep (ηᴸ-same dec))
    (cong keep (ηᴿ-same dec))
    (cong store-lift (sourceStore-same dec))
    (cong store-lift (targetStore-same dec))
    (CTX.imp-env-mono lift-dynamic lift-precise)
  where
  lift-dynamic : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldBoth v W) Z ≡ X⊑★
    → CTX.impEnvʷ (CTX.liftWorldBoth v Wᵈ) Z ≡ X⊑★
  lift-dynamic Fin.zero eq = eq
  lift-dynamic (Fin.suc Z) eq =
    CTX.dynamic-preserved (env-mono dec) Z eq

  lift-precise : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldBoth v W) Z ≡ X⊑X
    → CTX.impEnvʷ (CTX.liftWorldBoth v Wᵈ) Z ≡ X⊑X
  lift-precise Fin.zero eq = eq
  lift-precise (Fin.suc Z) eq =
    CTX.precise-preserved (env-mono dec) Z eq

liftDecayLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → EnvDecay W Wᵈ
  → EnvDecay (CTX.liftWorldLeft W) (CTX.liftWorldLeft Wᵈ)
liftDecayLeft {W = W} {Wᵈ = Wᵈ} v dec =
  env-decay
    (cong keep (ηᴸ-same dec))
    (cong skip (ηᴿ-same dec))
    (cong store-lift (sourceStore-same dec))
    (targetStore-same dec)
    (CTX.imp-env-mono lift-dynamic lift-precise)
  where
  lift-dynamic : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft W) Z ≡ X⊑★
    → CTX.impEnvʷ (CTX.liftWorldLeft Wᵈ) Z ≡ X⊑★
  lift-dynamic Fin.zero eq = eq
  lift-dynamic (Fin.suc Z) eq =
    CTX.dynamic-preserved (env-mono dec) Z eq

  lift-precise : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft W) Z ≡ X⊑X
    → CTX.impEnvʷ (CTX.liftWorldLeft Wᵈ) Z ≡ X⊑X
  lift-precise Fin.zero ()
  lift-precise (Fin.suc Z) eq =
    CTX.precise-preserved (env-mono dec) Z eq

decayLiftCtx : ∀ {Δᴸ Δᴿ Δ} {v} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {γ′ : CTX.CtxImp (CTX.liftWorldBoth v W)}
  → (dec : EnvDecay W Wᵈ)
  → CTX.LiftCtx v γ γ′
  → CTX.LiftCtx v (decayCtx dec γ)
      (decayCtx (liftDecayBoth v dec) γ′)
decayLiftCtx dec CTX.lift-[] = CTX.lift-[]
decayLiftCtx dec (CTX.lift-∷ liftγ) =
  CTX.lift-∷ (decayLiftCtx dec liftγ)

decayLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ} {v} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {γ′ : CTX.CtxImp (CTX.liftWorldLeft W)}
  → (dec : EnvDecay W Wᵈ)
  → CTX.LiftCtxᴸ v γ γ′
  → CTX.LiftCtxᴸ v (decayCtx dec γ)
      (decayCtx (liftDecayLeft v dec) γ′)
decayLiftCtxᴸ dec CTX.liftᴸ-[] = CTX.liftᴸ-[]
decayLiftCtxᴸ dec (CTX.liftᴸ-∷ liftγ) =
  CTX.liftᴸ-∷ (decayLiftCtxᴸ dec liftγ)

decaySmartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ Wᵐᵈ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTX.CtxImp W} {γᵐ : CTX.CtxImp Wᵐ}
  → (dec : EnvDecay W Wᵈ)
  → (decᵐ : EnvDecay Wᵐ Wᵐᵈ)
  → CTX.SmartLiftCtxᴸ γ γᵐ
  → CTX.SmartLiftCtxᴸ (decayCtx dec γ) (decayCtx decᵐ γᵐ)
decaySmartLiftCtxᴸ dec decᵐ CTX.smart-lift-[] = CTX.smart-lift-[]
decaySmartLiftCtxᴸ dec decᵐ (CTX.smart-lift-∷ liftγ) =
  CTX.smart-lift-∷ (decaySmartLiftCtxᴸ dec decᵐ liftγ)

rename-as-subst : ∀ {Δ Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (A : Ty Δ)
  → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
rename-as-subst ρ (＇ X) = refl
rename-as-subst ρ (‵ ι) = refl
rename-as-subst ρ ★ = refl
rename-as-subst ρ (A ⇒ B)
    rewrite rename-as-subst ρ A | rename-as-subst ρ B =
  refl
rename-as-subst ρ (`∀ A) =
  cong `∀
    (trans (substᵗ-cong A exts-eq)
      (rename-as-subst (extᵗ ρ) A))
  where
  exts-eq : ∀ X
    → extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
  exts-eq Fin.zero = refl
  exts-eq (Fin.suc X) = refl

transport⊑ᵂ-by-subst : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (σ : Δ ⇒ˢ Δ′)
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑★
      → CTX.impEnvʷ W′ ⊢ σ Z ⊑ ★)
  → (∀ C → substᵗ σ (CTX.embedᴸ W C) ≡ CTX.embedᴸ W′ C)
  → (∀ C → substᵗ σ (CTX.embedᴿ W C) ≡ CTX.embedᴿ W′ C)
  → A CTX.⊑ᵂ⟨ W ⟩ B
  → A CTX.⊑ᵂ⟨ W′ ⟩ B
transport⊑ᵂ-by-subst {W = W} {W′ = W′} {A = A} {B = B}
    σ star-map source-eq target-eq p =
  subst≡
    (λ L → CTX.impEnvʷ W′ ⊢ L ⊑ CTX.embedᴿ W′ B)
    (source-eq A)
    (subst≡
      (λ R → CTX.impEnvʷ W′ ⊢ substᵗ σ (CTX.embedᴸ W A) ⊑ R)
      (target-eq B)
      (subst-⊑ star-map p))

decaySmartFreshBehindGuard : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartFreshBehindGuard W Wᵐ
  → CTX.SmartFreshBehindGuard Wᵈ (WD.honestify Wᵐ)
decaySmartFreshBehindGuard
    {W = W} {Wᵈ = Wᵈ} {Wᵐ = Wᵐ}
    dec guard =
  CTX.smart-fresh-behind-guard
    old
    (trans (CTX.SmartFreshBehindGuard.sourceStore-lifted guard)
      (cong store-lift (sym (sourceStore-same dec))))
    (trans (CTX.SmartFreshBehindGuard.targetStore-same guard)
      (sym (targetStore-same dec)))
    transport
    old-mark
    target-frozen
    old-source-frozen
    (CTX.SmartFreshBehindGuard.fresh-not-target guard)
    fresh-mark
    target-mark
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard

  old-mark : ∀ Z
    → CTX.impEnvʷ Wᵈ Z ≡ X⊑★
    → CTX.impEnvʷ (WD.honestify Wᵐ)
        (toRenameᵗ old Z) ≡ X⊑★
  old-mark Z star =
    CTX.honestEnv-mono (CTX.ηᴿʷ Wᵐ) (CTX.impEnvʷ Wᵐ)
      (toRenameᵗ old Z)
      (CTX.SmartFreshBehindGuard.old-mark-mono guard Z
        (WD.decay-dynamic-reflect dec Z star))

  target-image : ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ ≡ toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
  target-image Xᴿ =
    cong (λ η → toRenameᵗ η Xᴿ) (ηᴿ-same dec)

  source-image : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ Wᵈ) Xᴸ ≡ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ
  source-image Xᴸ =
    cong (λ η → toRenameᵗ η Xᴸ) (ηᴸ-same dec)

  target-frozen : ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ
      ≡ toRenameᵗ old (toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ)
  target-frozen Xᴿ =
    trans (CTX.SmartFreshBehindGuard.target-frozen guard Xᴿ)
      (cong (toRenameᵗ old) (sym (target-image Xᴿ)))

  old-source-frozen : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
      ≡ toRenameᵗ old (toRenameᵗ (CTX.ηᴸʷ Wᵈ) Xᴸ)
  old-source-frozen Xᴸ =
    trans (CTX.SmartFreshBehindGuard.old-source-frozen guard Xᴸ)
      (cong (toRenameᵗ old) (sym (source-image Xᴸ)))

  fresh-mark : CTX.impEnvʷ (WD.honestify Wᵐ)
      (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero) ≡ X⊑★
  fresh-mark = WD.honestify-mark Wᵐ
    (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero)
    (CTX.SmartFreshBehindGuard.fresh-not-target guard)

  target-mark : ∀ Xᴿ
    → CTX.impEnvʷ Wᵈ (toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ) ≡ X⊑★
    → CTX.impEnvʷ (WD.honestify Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★
  target-mark Xᴿ star =
    CTX.honestEnv-mono (CTX.ηᴿʷ Wᵐ) (CTX.impEnvʷ Wᵐ)
      (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ)
      (CTX.SmartFreshBehindGuard.target-mark-mono guard Xᴿ
        (trans (sym (cong (CTX.impEnvʷ W) (target-image Xᴿ)))
          (WD.decay-dynamic-reflect dec
            (toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ) star)))

  transport : ∀ {A B}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft Wᵈ ⟩ B
    → A CTX.⊑ᵂ⟨ WD.honestify Wᵐ ⟩ B
  transport p = WD.decay⊑ᵂ (WD.honestify-decay {W = Wᵐ})
    (CTX.SmartFreshBehindGuard.transport⊑ᵂ guard
      (WD.reflect⊑ᵂ (liftDecayLeft X⊑★ dec) p))

decaySmartAliasMergeGuard : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δ}
    {β α : TyVar Δᴿ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → CTX.SmartAliasMergeGuard Wᵈ (WD.honestify Wᵐ) β α
decaySmartAliasMergeGuard
    {W = W} {Wᵈ = Wᵈ} {Wᵐ = Wᵐ} {β = β} {α = α}
    dec guard =
  CTX.smart-alias-merge-guard
    (subst≡ (λ Σ → Σ ∋ β ⦂ ＇ α) (sym (targetStore-same dec))
      (CTX.SmartAliasMergeGuard.β:=＇α guard))
    (subst≡ (λ Σ → Σ ∋ α ⦂ ★) (sym (targetStore-same dec))
      (CTX.SmartAliasMergeGuard.α:=★ guard))
    (trans (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)
      (cong store-lift (sym (sourceStore-same dec))))
    (trans (CTX.SmartAliasMergeGuard.targetStore-same guard)
      (sym (targetStore-same dec)))
    transport
    old-mark
    target-frozen
    pending-at-alias
    old-source-frozen
    no-old-source-at-alias
    alias-mark
    name-mark
    target-mark
  where
  old-mark : ∀ Z
    → CTX.impEnvʷ Wᵈ Z ≡ X⊑★
    → CTX.impEnvʷ (WD.honestify Wᵐ) Z ≡ X⊑★
  old-mark Z star =
    CTX.honestEnv-mono (CTX.ηᴿʷ Wᵐ) (CTX.impEnvʷ Wᵐ) Z
      (CTX.SmartAliasMergeGuard.old-mark-mono guard Z
        (WD.decay-dynamic-reflect dec Z star))

  target-image : ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ ≡ toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
  target-image Xᴿ =
    cong (λ η → toRenameᵗ η Xᴿ) (ηᴿ-same dec)

  source-image : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ Wᵈ) Xᴸ ≡ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ
  source-image Xᴸ =
    cong (λ η → toRenameᵗ η Xᴸ) (ηᴸ-same dec)

  target-frozen : ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ
      ≡ toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ
  target-frozen Xᴿ =
    trans (CTX.SmartAliasMergeGuard.target-frozen guard Xᴿ)
      (sym (target-image Xᴿ))

  pending-at-alias :
    toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero
      ≡ toRenameᵗ (CTX.ηᴿʷ Wᵈ) β
  pending-at-alias =
    trans (CTX.SmartAliasMergeGuard.pending-at-alias guard)
      (sym (target-image β))

  old-source-frozen : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
      ≡ toRenameᵗ (CTX.ηᴸʷ Wᵈ) Xᴸ
  old-source-frozen Xᴸ =
    trans (CTX.SmartAliasMergeGuard.old-source-frozen guard Xᴸ)
      (sym (source-image Xᴸ))

  no-old-source-at-alias : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ Wᵈ) Xᴸ
      ≢ toRenameᵗ (CTX.ηᴿʷ Wᵈ) β
  no-old-source-at-alias Xᴸ aligned =
    CTX.SmartAliasMergeGuard.no-old-source-at-alias guard Xᴸ
      (trans (sym (source-image Xᴸ))
        (trans aligned (target-image β)))

  alias-mark : CTX.impEnvʷ (WD.honestify Wᵐ)
      (toRenameᵗ (CTX.ηᴿʷ Wᵈ) β) ≡ X⊑★
  alias-mark =
    trans (cong (CTX.impEnvʷ (WD.honestify Wᵐ)) (target-image β))
      (CTX.honestEnv-mono (CTX.ηᴿʷ Wᵐ) (CTX.impEnvʷ Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ W) β)
        (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard))

  name-mark : CTX.impEnvʷ (WD.honestify Wᵐ)
      (toRenameᵗ (CTX.ηᴿʷ Wᵈ) α) ≡ X⊑★
  name-mark =
    trans (cong (CTX.impEnvʷ (WD.honestify Wᵐ)) (target-image α))
      (CTX.honestEnv-mono (CTX.ηᴿʷ Wᵐ) (CTX.impEnvʷ Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ W) α)
        (CTX.SmartAliasMergeGuard.name-mark-dynamic guard))

  target-mark : ∀ Xᴿ
    → Xᴿ ≢ β
    → Xᴿ ≢ α
    → CTX.impEnvʷ Wᵈ (toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ) ≡ X⊑★
    → CTX.impEnvʷ (WD.honestify Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★
  target-mark Xᴿ Xᴿ≢β Xᴿ≢α star =
    CTX.honestEnv-mono (CTX.ηᴿʷ Wᵐ) (CTX.impEnvʷ Wᵐ)
      (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ)
      (CTX.SmartAliasMergeGuard.target-mark-off-footprint guard Xᴿ
        Xᴿ≢β Xᴿ≢α
        (trans (sym (cong (CTX.impEnvʷ W) (target-image Xᴿ)))
          (WD.decay-dynamic-reflect dec
            (toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ) star)))

  transport : ∀ {A B}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft Wᵈ ⟩ B
    → A CTX.⊑ᵂ⟨ WD.honestify Wᵐ ⟩ B
  transport p = WD.decay⊑ᵂ (WD.honestify-decay {W = Wᵐ})
    (CTX.SmartAliasMergeGuard.transport⊑ᵂ guard
      (WD.reflect⊑ᵂ (liftDecayLeft X⊑★ dec) p))

decaySmartCommaLiftᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartCommaLiftᴸ W Wᵐ
  → CTX.SmartCommaLiftᴸ Wᵈ (WD.honestify Wᵐ)
decaySmartCommaLiftᴸ dec (CTX.smart-fresh-behind guard) =
  CTX.smart-fresh-behind (decaySmartFreshBehindGuard dec guard)
decaySmartCommaLiftᴸ dec (CTX.smart-merge-alias guard) =
  CTX.smart-merge-alias (decaySmartAliasMergeGuard dec guard)

decayCtx-tgt : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (dec : EnvDecay W Wᵈ)
  → (γ : CTX.CtxImp W)
  → CTX.tgtCtxʷ (decayCtx dec γ) ≡ CTX.tgtCtxʷ γ
decayCtx-tgt dec [] = refl
decayCtx-tgt dec (CTX.ctx-imp A B p ∷ γ) =
  cong (_ ∷_) (decayCtx-tgt dec γ)

decay-target-typing : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴿ} {B : Ty Δᴿ}
  → (dec : EnvDecay W Wᵈ)
  → ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ , CTX.targetStoreʷ Wᵈ ,
      CTX.tgtCtxʷ (decayCtx dec γ) ⟩ ⊢ M ⦂ B
decay-target-typing {W = W} {Wᵈ = Wᵈ} {γ = γ} dec M⊢ =
  subst≡
    (λ Σ → ⟨ _ , Σ , CTX.tgtCtxʷ (decayCtx dec γ) ⟩ ⊢ _ ⦂ _)
    (sym (targetStore-same dec))
    (subst≡ (λ Γ → ⟨ _ , CTX.targetStoreʷ W , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec γ)) M⊢)

decay-source-⊢↑ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {A B Rᴸ} {Xᴸ : TyVar Δᴸ} {c : Conv↑ Δᴸ A B}
  → EnvDecay W Wᵈ
  → CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c
  → CTX.sourceStoreʷ Wᵈ ⊢↑[ Xᴸ ⦂ Rᴸ ] c
decay-source-⊢↑ dec c⊢ =
  subst≡ (λ Σ → Σ ⊢↑[ _ ⦂ _ ] _) (sym (sourceStore-same dec)) c⊢

decay-source-⊢↓ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {A B Rᴸ} {Xᴸ : TyVar Δᴸ} {c : Conv↓ Δᴸ A B}
  → EnvDecay W Wᵈ
  → CTX.sourceStoreʷ W ⊢↓[ Xᴸ ⦂ Rᴸ ] c
  → CTX.sourceStoreʷ Wᵈ ⊢↓[ Xᴸ ⦂ Rᴸ ] c
decay-source-⊢↓ dec c⊢ =
  subst≡ (λ Σ → Σ ⊢↓[ _ ⦂ _ ] _) (sym (sourceStore-same dec)) c⊢

decay-target-⊢↑ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {A B Rᴿ} {Xᴿ : TyVar Δᴿ} {c : Conv↑ Δᴿ A B}
  → EnvDecay W Wᵈ
  → CTX.targetStoreʷ W ⊢↑[ Xᴿ ⦂ Rᴿ ] c
  → CTX.targetStoreʷ Wᵈ ⊢↑[ Xᴿ ⦂ Rᴿ ] c
decay-target-⊢↑ dec c⊢ =
  subst≡ (λ Σ → Σ ⊢↑[ _ ⦂ _ ] _) (sym (targetStore-same dec)) c⊢

decay-target-⊢↓ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {A B Rᴿ} {Xᴿ : TyVar Δᴿ} {c : Conv↓ Δᴿ A B}
  → EnvDecay W Wᵈ
  → CTX.targetStoreʷ W ⊢↓[ Xᴿ ⦂ Rᴿ ] c
  → CTX.targetStoreʷ Wᵈ ⊢↓[ Xᴿ ⦂ Rᴿ ] c
decay-target-⊢↓ dec c⊢ =
  subst≡ (λ Σ → Σ ⊢↓[ _ ⦂ _ ] _) (sym (targetStore-same dec)) c⊢

decay-source-reveal-position : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {A B Rᴸ}
    {Xᴸ : TyVar Δᴸ} {c : Conv↑ Δᴸ A B}
  → (dec : EnvDecay W Wᵈ)
  → (c⊢ : CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → (P : GeneratorPosition)
  → revealGeneratorPosition c⊢ ≡ P
  → revealGeneratorPosition (decay-source-⊢↑ dec c⊢) ≡ P
decay-source-reveal-position dec c⊢ P eq =
  trans
    (revealGeneratorPosition-store-transport
      (sym (sourceStore-same dec)) c⊢) eq

decay-source-conceal-position : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {A B Rᴸ}
    {Xᴸ : TyVar Δᴸ} {c : Conv↓ Δᴸ A B}
  → (dec : EnvDecay W Wᵈ)
  → (c⊢ : CTX.sourceStoreʷ W ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
  → (P : GeneratorPosition)
  → concealGeneratorPosition c⊢ ≡ P
  → concealGeneratorPosition (decay-source-⊢↓ dec c⊢) ≡ P
decay-source-conceal-position dec c⊢ P eq =
  trans
    (concealGeneratorPosition-store-transport
      (sym (sourceStore-same dec)) c⊢) eq

decay-target-reveal-position : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {A B Rᴿ}
    {Xᴿ : TyVar Δᴿ} {c : Conv↑ Δᴿ A B}
  → (dec : EnvDecay W Wᵈ)
  → (c⊢ : CTX.targetStoreʷ W ⊢↑[ Xᴿ ⦂ Rᴿ ] c)
  → (P : GeneratorPosition)
  → revealGeneratorPosition c⊢ ≡ P
  → revealGeneratorPosition (decay-target-⊢↑ dec c⊢) ≡ P
decay-target-reveal-position dec c⊢ P eq =
  trans
    (revealGeneratorPosition-store-transport
      (sym (targetStore-same dec)) c⊢) eq

decay-target-conceal-position : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {A B Rᴿ}
    {Xᴿ : TyVar Δᴿ} {c : Conv↓ Δᴿ A B}
  → (dec : EnvDecay W Wᵈ)
  → (c⊢ : CTX.targetStoreʷ W ⊢↓[ Xᴿ ⦂ Rᴿ ] c)
  → (P : GeneratorPosition)
  → concealGeneratorPosition c⊢ ≡ P
  → concealGeneratorPosition (decay-target-⊢↓ dec c⊢) ≡ P
decay-target-conceal-position dec c⊢ P eq =
  trans
    (concealGeneratorPosition-store-transport
      (sym (targetStore-same dec)) c⊢) eq

------------------------------------------------------------------------
-- Decay of pivot-local rebasing
------------------------------------------------------------------------

decayRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₁ᵈ W₂ W₂ᵈ : CTX.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (dec₁ : EnvDecay W₁ W₁ᵈ)
  → (dec₂ : EnvDecay W₂ W₂ᵈ)
  → CTX.RebaseAt W₁ W₂ Xᴸ Xᴿ
  → CTX.RebaseAt W₁ᵈ W₂ᵈ Xᴸ Xᴿ
decayRebaseAt
    {W₁ = W₁} {W₁ᵈ = W₁ᵈ} {W₂ = W₂} {W₂ᵈ = W₂ᵈ}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} dec₁ dec₂
    (CTX.rebase-at (CTX.same-runtime source-eq target-eq)
      offL frozenR aligned (CTX.store-rep-imp represented)) =
  CTX.rebase-at (CTX.same-runtime source-eqᵈ target-eqᵈ)
    offLᵈ frozenRᵈ alignedᵈ
    (CTX.store-rep-imp
      (subst≡
        (λ A → A CTX.⊑ᵂ⟨ W₂ᵈ ⟩
          CTX.resolveVar (CTX.targetStoreʷ W₂ᵈ) Xᴿ)
        (sym source-rep-eq)
        (subst≡
          (λ B → CTX.resolveVar (CTX.sourceStoreʷ W₂) Xᴸ
            CTX.⊑ᵂ⟨ W₂ᵈ ⟩ B)
          (sym target-rep-eq)
          (decay⊑ᵂ dec₂ represented))))
  where
  source-rep-eq : CTX.resolveVar (CTX.sourceStoreʷ W₂ᵈ) Xᴸ
    ≡ CTX.resolveVar (CTX.sourceStoreʷ W₂) Xᴸ
  source-rep-eq = cong (λ Σ → CTX.resolveVar Σ Xᴸ)
    (sourceStore-same dec₂)

  target-rep-eq : CTX.resolveVar (CTX.targetStoreʷ W₂ᵈ) Xᴿ
    ≡ CTX.resolveVar (CTX.targetStoreʷ W₂) Xᴿ
  target-rep-eq = cong (λ Σ → CTX.resolveVar Σ Xᴿ)
    (targetStore-same dec₂)

  source-eqᵈ = trans (sourceStore-same dec₂)
    (trans source-eq (sym (sourceStore-same dec₁)))

  target-eqᵈ = trans (targetStore-same dec₂)
    (trans target-eq (sym (targetStore-same dec₁)))

  source-image₁ : ∀ Y
    → toRenameᵗ (CTX.ηᴸʷ W₁ᵈ) Y ≡ toRenameᵗ (CTX.ηᴸʷ W₁) Y
  source-image₁ Y = cong (λ η → toRenameᵗ η Y) (ηᴸ-same dec₁)

  source-image₂ : ∀ Y
    → toRenameᵗ (CTX.ηᴸʷ W₂ᵈ) Y ≡ toRenameᵗ (CTX.ηᴸʷ W₂) Y
  source-image₂ Y = cong (λ η → toRenameᵗ η Y) (ηᴸ-same dec₂)

  target-image₁ : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ W₁ᵈ) Y ≡ toRenameᵗ (CTX.ηᴿʷ W₁) Y
  target-image₁ Y = cong (λ η → toRenameᵗ η Y) (ηᴿ-same dec₁)

  target-image₂ : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ W₂ᵈ) Y ≡ toRenameᵗ (CTX.ηᴿʷ W₂) Y
  target-image₂ Y = cong (λ η → toRenameᵗ η Y) (ηᴿ-same dec₂)

  offLᵈ : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ W₂ᵈ) Y ≡ toRenameᵗ (CTX.ηᴸʷ W₁ᵈ) Y
  offLᵈ {Y} Y≢X = trans (source-image₂ Y)
    (trans (offL Y≢X) (sym (source-image₁ Y)))

  frozenRᵈ : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ W₂ᵈ) Y ≡ toRenameᵗ (CTX.ηᴿʷ W₁ᵈ) Y
  frozenRᵈ Y = trans (target-image₂ Y)
    (trans (frozenR Y) (sym (target-image₁ Y)))

  alignedᵈ : toRenameᵗ (CTX.ηᴸʷ W₂ᵈ) Xᴸ
    ≡ toRenameᵗ (CTX.ηᴿʷ W₂ᵈ) Xᴿ
  alignedᵈ = trans (source-image₂ Xᴸ)
    (trans aligned (sym (target-image₂ Xᴿ)))

------------------------------------------------------------------------
-- Term-imprecision decay
------------------------------------------------------------------------

reindex-⊢² : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p q : A CTX.⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
reindex-⊢² {W = W} {γ = γ} {M = M} {M′ = M′} {p = p} {q = q} rel =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ M′ ∶ r) (PI.⊑-unique p q) rel

decay-source-dynamic : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) X) ≡ X⊑★
  → CTX.impEnvʷ Wᵈ (toRenameᵗ (CTX.ηᴸʷ Wᵈ) X) ≡ X⊑★
decay-source-dynamic {Wᵈ = Wᵈ} {X = X} dec dynamic =
  trans (cong (CTX.impEnvʷ Wᵈ)
      (cong (λ η → toRenameᵗ η X) (ηᴸ-same dec)))
    (CTX.dynamic-preserved (env-mono dec) _ dynamic)

decay-source-no-target : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → (dec : EnvDecay W Wᵈ)
  → (∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ W) X)
  → ∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ Wᵈ) X
decay-source-no-target {X = X} dec no-target Xᴿ aligned =
  no-target Xᴿ
    (trans (sym (cong (λ η → toRenameᵗ η Xᴿ) (ηᴿ-same dec)))
      (trans aligned
        (cong (λ η → toRenameᵗ η X) (ηᴸ-same dec))))

decay-source-represented-star : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.resolveVar (CTX.sourceStoreʷ W) X CTX.⊑ᵂ⟨ W ⟩ ★
  → CTX.resolveVar (CTX.sourceStoreʷ Wᵈ) X CTX.⊑ᵂ⟨ Wᵈ ⟩ ★
decay-source-represented-star {W = W} {Wᵈ = Wᵈ} {X = X}
    dec represented =
  subst≡ (λ R → R CTX.⊑ᵂ⟨ Wᵈ ⟩ ★) (sym rep-eq)
    (decay⊑ᵂ dec represented)
  where
  rep-eq : CTX.resolveVar (CTX.sourceStoreʷ Wᵈ) X
    ≡ CTX.resolveVar (CTX.sourceStoreʷ W) X
  rep-eq = cong (λ Σ → CTX.resolveVar Σ X) (sourceStore-same dec)

⊢²-decay : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ decay⊑ᵂ dec p
⊢²-decay
    dec
    (CTI2.x⊑x² x∈) =
  CTI2.x⊑x² (decay∋ʷ dec x∈)
⊢²-decay
    dec
    (CTI2.ƛ⊑ƛ² M⊑M′) =
  reindex-⊢² (CTI2.ƛ⊑ƛ² (⊢²-decay dec M⊑M′))
⊢²-decay
    dec
    (CTI2.·⊑·² {pA = pA} {pB = pB} L⊑L′ M⊑M′) =
  reindex-⊢²
    (CTI2.·⊑·²
      (reindex-⊢²
        {q = ⇒⊑⇒ (decay⊑ᵂ dec pA) (decay⊑ᵂ dec pB)}
        (⊢²-decay dec L⊑L′))
      (⊢²-decay dec M⊑M′))
⊢²-decay
    dec
    (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
  CTI2.Λ⊑Λ² (decayLiftCtx dec liftγ) vV vV′
    (⊢²-decay (liftDecayBoth X⊑X dec) V⊑V′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {γ = γ}
    dec
    (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑² Anv zero∈A (decayLiftCtxᴸ dec liftγ) vV
    (decay-target-typing dec M′⊢)
    (⊢²-decay (liftDecayLeft X⊑★ dec) V⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {γ = γ}
    dec
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} Anv zero∈A liftW
      liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (decaySmartCommaLiftᴸ dec liftW)
    (decaySmartLiftCtxᴸ dec (WD.honestify-decay {W = Wᵐ}) liftγ) vV
    (decay-target-typing dec M′⊢)
    (⊢²-decay (WD.honestify-decay {W = Wᵐ}) V⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.•⊑•² p∀ M⊑M′ q r) =
  CTI2.•⊑•² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    dec
    (CTI2.•⊑² p∀ M⊑M′ q r) =
  CTI2.•⊑² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    dec
    (CTI2.κ⊑κ² κ p) =
  CTI2.κ⊑κ² κ (decay⊑ᵂ dec p)
⊢²-decay
    dec
    (CTI2.cast⊑cast² c c′ M⊑M′ q) =
  CTI2.cast⊑cast² c c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.⊑cast² c′ M⊑M′ q) =
  CTI2.⊑cast² c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.cast⊑² c M⊑M′ q) =
  CTI2.cast⊑² c (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.⊑reveal² c′⊢ position≡absent M⊑M′ q) =
  CTI2.⊑reveal² (decay-target-⊢↑ dec c′⊢)
    (decay-target-reveal-position dec c′⊢ generator-absent
      position≡absent)
    (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.⊑conceal² c′⊢ position≡absent M⊑M′ q) =
  CTI2.⊑conceal² (decay-target-⊢↓ dec c′⊢)
    (decay-target-conceal-position dec c′⊢ generator-absent
      position≡absent)
    (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.reveal⊑-identity c⊢ position≡absent M⊑M′ q) =
  CTI2.reveal⊑-identity (decay-source-⊢↑ dec c⊢)
    (decay-source-reveal-position dec c⊢ generator-absent
      position≡absent)
    (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {Wᵈ = Wᵈ}
    dec
    (CTI2.reveal⊑² {W′ = W′} c⊢ position≢absent Xᴿ∈ represented
      rule-mono rb sc M⊑M′ q) =
  CTI2.reveal⊑² (decay-source-⊢↑ dec c⊢)
    (λ position≡absent → position≢absent
      (trans
        (sym (decay-source-reveal-position dec c⊢
          (revealGeneratorPosition c⊢) refl)) position≡absent))
    (subst≡ (λ Σ → Σ ∋ _ ⦂ _) (sym (targetStore-same dec)) Xᴿ∈)
    (decay⊑ᵂ (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) represented)
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ} dec rule-mono)
    (decayRebaseAt dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) rb)
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.reveal⊑-only² c⊢ position≢absent dynamic no-target represented
      M⊑M′ q) =
  CTI2.reveal⊑-only² (decay-source-⊢↑ dec c⊢)
    (λ position≡absent → position≢absent
      (trans
        (sym (decay-source-reveal-position dec c⊢
          (revealGeneratorPosition c⊢) refl)) position≡absent))
    (decay-source-dynamic dec dynamic)
    (decay-source-no-target dec no-target)
    (decay⊑ᵂ dec represented)
    (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.conceal⊑² c⊢ position≢absent dynamic no-target represented
      M⊑M′ q) =
  CTI2.conceal⊑² (decay-source-⊢↓ dec c⊢)
    (λ position≡absent → position≢absent
      (trans
        (sym (decay-source-conceal-position dec c⊢
          (concealGeneratorPosition c⊢) refl)) position≡absent))
    (decay-source-dynamic dec dynamic)
    (decay-source-no-target dec no-target)
    (decay⊑ᵂ dec represented)
    (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.conceal⊑-identity c⊢ position≡absent M⊑M′ q) =
  CTI2.conceal⊑-identity (decay-source-⊢↓ dec c⊢)
    (decay-source-conceal-position dec c⊢ generator-absent
      position≡absent)
    (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {Wᵈ = Wᵈ}
    dec
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} c⊢ c′⊢ positions-equal
      position≢absent
      represented rule-mono rb sc M⊑M′ q) =
  CTI2.reveal⊑reveal² (decay-source-⊢↑ dec c⊢)
    (decay-target-⊢↑ dec c′⊢)
    (trans
      (decay-source-reveal-position dec c⊢
        (revealGeneratorPosition c⊢) refl)
      (trans positions-equal
        (sym (decay-target-reveal-position dec c′⊢
          (revealGeneratorPosition c′⊢) refl))))
    (λ position≡absent → position≢absent
      (trans
        (sym (decay-source-reveal-position dec c⊢
          (revealGeneratorPosition c⊢) refl)) position≡absent))
    (decay⊑ᵂ (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) represented)
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ} dec rule-mono)
    (decayRebaseAt dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sc)
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {Wᵈ = Wᵈ}
    dec
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} c⊢ c′⊢ positions-equal
      position≢absent
      represented rule-mono rb sc M⊑M′ q) =
  CTI2.conceal⊑conceal² (decay-source-⊢↓ dec c⊢)
    (decay-target-⊢↓ dec c′⊢)
    (trans
      (decay-source-conceal-position dec c⊢
        (concealGeneratorPosition c⊢) refl)
      (trans positions-equal
        (sym (decay-target-conceal-position dec c′⊢
          (concealGeneratorPosition c′⊢) refl))))
    (λ position≡absent → position≢absent
      (trans
        (sym (decay-source-conceal-position dec c⊢
          (concealGeneratorPosition c⊢) refl)) position≡absent))
    (decay⊑ᵂ (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) represented)
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ} dec rule-mono)
    (decayRebaseAt
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) dec rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sc)
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    dec
    (CTI2.blame⊑² M′⊢ p) =
  CTI2.blame⊑²
    (decay-target-typing dec M′⊢)
    (decay⊑ᵂ dec p)
⊢²-decay
    dec
    (CTI2.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
  CTI2.⊕⊑⊕² op (⊢²-decay dec L⊑L′) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec r)

⊢²-decay-at : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → (pᵈ : A CTX.⊑ᵂ⟨ Wᵈ ⟩ B)
  → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ pᵈ
⊢²-decay-at {Wᵈ = Wᵈ} {γ = γ} {M = M} {M′ = M′} {p = p}
    dec M⊑M′ pᵈ =
  subst≡ (λ q → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ q)
    (PI.⊑-unique (decay⊑ᵂ dec p) pᵈ) (⊢²-decay dec M⊑M′)
