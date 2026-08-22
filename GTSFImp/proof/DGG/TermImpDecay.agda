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
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import Consistency using (keep; skip; toRenameᵗ)
open import Conversion using (Conv↓)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
open import Imprecision
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.WorldDecay
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using (subst-⊑)

------------------------------------------------------------------------
-- Decay under type binders
------------------------------------------------------------------------

liftDecayBoth : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → EnvDecay W Wᵈ
  → EnvDecay (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v Wᵈ)
liftDecayBoth
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    v
    (env-decay refl refl refl refl mono) =
  env-decay refl refl refl refl lift-mono
  where
  lift-mono : ∀ Z
    → extendᵐ v μ Z ≡ X⊑★
    → extendᵐ v μᵈ Z ≡ X⊑★
  lift-mono Fin.zero eq = eq
  lift-mono (Fin.suc Z) eq = mono Z eq

liftBothBinderDecay : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
  → EnvDecay
      (CTX.liftWorldBoth X⊑X W)
      (CTX.liftWorldBoth X⊑★ W)
liftBothBinderDecay = env-decay refl refl refl refl lift-mono
  where
  lift-mono : ∀ {Δ} {μ : ImpEnv Δ}
    → (Z : Fin.Fin (suc Δ))
    → extendᵐ X⊑X μ Z ≡ X⊑★
    → extendᵐ X⊑★ μ Z ≡ X⊑★
  lift-mono Fin.zero eq = refl
  lift-mono (Fin.suc Z) eq = eq

liftDecayLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → EnvDecay W Wᵈ
  → EnvDecay (CTX.liftWorldLeft v W) (CTX.liftWorldLeft v Wᵈ)
liftDecayLeft
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    v
    (env-decay refl refl refl refl mono) =
  env-decay refl refl refl refl lift-mono
  where
  lift-mono : ∀ Z
    → extendᵐ v μ Z ≡ X⊑★
    → extendᵐ v μᵈ Z ≡ X⊑★
  lift-mono Fin.zero eq = eq
  lift-mono (Fin.suc Z) eq = mono Z eq

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
    {γ′ : CTX.CtxImp (CTX.liftWorldLeft v W)}
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
  → CTX.SmartFreshBehindGuard Wᵈ (SPT.dynWorld Wᵐ)
decaySmartFreshBehindGuard
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Δ = Δ} {Δᵐ = Δᵐ}
    {W = W} {Wᵈ = Wᵈ} {Wᵐ = Wᵐ}
    (env-decay refl refl refl refl mono) guard =
  CTX.smart-fresh-behind-guard
    (CTX.SmartFreshBehindGuard.oldCenters guard)
    (CTX.SmartFreshBehindGuard.sourceStore-lifted guard)
    (CTX.SmartFreshBehindGuard.targetStore-same guard)
    transport′
    (λ Z star → refl)
    (CTX.SmartFreshBehindGuard.target-frozen guard)
    (CTX.SmartFreshBehindGuard.old-source-frozen guard)
    (CTX.SmartFreshBehindGuard.fresh-not-target guard)
    refl
    (λ Xᴿ star → refl)
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard

  smartSubst : suc Δ ⇒ˢ Δᵐ
  smartSubst Fin.zero =
    ＇ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero)
  smartSubst (Fin.suc Z) = ＇ (toRenameᵗ old Z)

  smartStar : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ Wᵈ) Z ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) ⊢ smartSubst Z ⊑ ★
  smartStar Fin.zero star = X⊑★ refl
  smartStar (Fin.suc Z) star = X⊑★ refl

  source-point : ∀ X
    → smartSubst (toRenameᵗ (keep (CTX.ηᴸʷ W)) X)
      ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) X)
  source-point Fin.zero = refl
  source-point (Fin.suc X) =
    cong ＇_ (sym (CTX.SmartFreshBehindGuard.old-source-frozen guard X))

  target-point : ∀ Y
    → smartSubst (toRenameᵗ (skip (CTX.ηᴿʷ W)) Y)
      ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
  target-point Y =
    cong ＇_ (sym (CTX.SmartFreshBehindGuard.target-frozen guard Y))

  source-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴸ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴸ (SPT.dynWorld Wᵐ) C
  source-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (keep (CTX.ηᴸʷ W))) C)
      (trans (substᵗ-cong C source-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴸʷ Wᵐ)) C))

  target-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴿ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴿ (SPT.dynWorld Wᵐ) C
  target-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (skip (CTX.ηᴿʷ W))) C)
      (trans (substᵗ-cong C target-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴿʷ Wᵐ)) C))

  transport′ : ∀ {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ Wᵈ ⟩ B
    → A CTX.⊑ᵂ⟨ SPT.dynWorld Wᵐ ⟩ B
  transport′ =
    transport⊑ᵂ-by-subst
      {W = CTX.liftWorldLeft X⊑★ Wᵈ}
      {W′ = SPT.dynWorld Wᵐ}
      smartSubst smartStar source-eq target-eq

decaySmartAliasMergeGuard : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δ}
    {β α : TyVar Δᴿ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → CTX.SmartAliasMergeGuard Wᵈ (SPT.dynWorld Wᵐ) β α
decaySmartAliasMergeGuard
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Δ = Δ}
    {W = W} {Wᵈ = Wᵈ} {Wᵐ = Wᵐ} {β = β}
    (env-decay refl refl refl refl mono) guard =
  CTX.smart-alias-merge-guard
    (CTX.SmartAliasMergeGuard.β:=＇α guard)
    (CTX.SmartAliasMergeGuard.α:=★ guard)
    (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)
    (CTX.SmartAliasMergeGuard.targetStore-same guard)
    transport′
    (λ Z star → refl)
    (CTX.SmartAliasMergeGuard.target-frozen guard)
    (CTX.SmartAliasMergeGuard.pending-at-alias guard)
    (CTX.SmartAliasMergeGuard.old-source-frozen guard)
    (CTX.SmartAliasMergeGuard.no-old-source-at-alias guard)
    refl
    refl
    (λ Xᴿ Xᴿ≢β Xᴿ≢α star → refl)
  where
  smartSubst : suc Δ ⇒ˢ Δ
  smartSubst Fin.zero = ＇ (toRenameᵗ (CTX.ηᴿʷ W) β)
  smartSubst (Fin.suc Z) = ＇ Z

  smartStar : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ Wᵈ) Z ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) ⊢ smartSubst Z ⊑ ★
  smartStar Fin.zero star = X⊑★ refl
  smartStar (Fin.suc Z) star = X⊑★ refl

  source-point : ∀ X
    → smartSubst (toRenameᵗ (keep (CTX.ηᴸʷ W)) X)
      ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) X)
  source-point Fin.zero =
    cong ＇_ (sym (CTX.SmartAliasMergeGuard.pending-at-alias guard))
  source-point (Fin.suc X) =
    cong ＇_ (sym (CTX.SmartAliasMergeGuard.old-source-frozen guard X))

  target-point : ∀ Y
    → smartSubst (toRenameᵗ (skip (CTX.ηᴿʷ W)) Y)
      ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
  target-point Y =
    cong ＇_ (sym (CTX.SmartAliasMergeGuard.target-frozen guard Y))

  source-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴸ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴸ (SPT.dynWorld Wᵐ) C
  source-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (keep (CTX.ηᴸʷ W))) C)
      (trans (substᵗ-cong C source-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴸʷ Wᵐ)) C))

  target-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴿ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴿ (SPT.dynWorld Wᵐ) C
  target-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (skip (CTX.ηᴿʷ W))) C)
      (trans (substᵗ-cong C target-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴿʷ Wᵐ)) C))

  transport′ : ∀ {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ Wᵈ ⟩ B
    → A CTX.⊑ᵂ⟨ SPT.dynWorld Wᵐ ⟩ B
  transport′ =
    transport⊑ᵂ-by-subst
      {W = CTX.liftWorldLeft X⊑★ Wᵈ}
      {W′ = SPT.dynWorld Wᵐ}
      smartSubst smartStar source-eq target-eq

decaySmartCommaLiftᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartCommaLiftᴸ W Wᵐ
  → CTX.SmartCommaLiftᴸ Wᵈ (SPT.dynWorld Wᵐ)
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
    {W₁ = CTX.world ηL₁ ηR₁ μ₁ ΣL₁ ΣR₁}
    {W₁ᵈ = CTX.world ηL₁′ ηR₁′ μ₁ᵈ ΣL₁′ ΣR₁′}
    {W₂ = CTX.world ηL₂ ηR₂ μ₂ ΣL₂ ΣR₂}
    {W₂ᵈ = CTX.world ηL₂′ ηR₂′ μ₂ᵈ ΣL₂′ ΣR₂′}
    (env-decay refl refl refl refl mono₁)
    dec₂@(env-decay refl refl refl refl mono₂)
    (CTX.rebase-at (CTX.same-runtime source-eq target-eq)
      offL frozenR aligned (CTX.store-rep-imp represented)) =
  CTX.rebase-at (CTX.same-runtime source-eq target-eq)
    offL frozenR aligned
    (CTX.store-rep-imp (decay⊑ᵂ dec₂ represented))

------------------------------------------------------------------------
-- Term-imprecision decay
------------------------------------------------------------------------

private
  decayRep★PartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {P Xᴿ? M′}
    → EnvDecay W Wᵈ
    → CTX.Rep★PartnerOK W X P Xᴿ? M′
    → CTX.Rep★PartnerOK Wᵈ X P Xᴿ? M′
  decayRep★PartnerOK (env-decay refl refl refl refl mono)
      (CTX.rep★-untagged nt) =
    CTX.rep★-untagged nt
  decayRep★PartnerOK (env-decay refl refl refl refl mono)
      (CTX.rep★-nonvar-tag Gnv) =
    CTX.rep★-nonvar-tag Gnv
  decayRep★PartnerOK (env-decay refl refl refl refl mono)
      (CTX.rep★-var-tag aligned) =
    CTX.rep★-var-tag aligned
  decayRep★PartnerOK (env-decay refl refl refl refl mono)
      (CTX.rep★-matched-inner-tags X₂≢X aligned) =
    CTX.rep★-matched-inner-tags X₂≢X aligned
  decayRep★PartnerOK dec (CTX.rep★-round-trip ok) =
    CTX.rep★-round-trip (decayRep★PartnerOK dec ok)

  decayNoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ}
    → EnvDecay W Wᵈ
    → CTX.NoTargetOccupantAtSource W X
    → CTX.NoTargetOccupantAtSource Wᵈ X
  decayNoTargetOccupantAtSource
      (env-decay refl refl refl refl mono) no-target =
    no-target

  decaySourceConcealOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
    → EnvDecay W Wᵈ
    → CTX.SourceConcealOK W M c Xᴿ? M′
    → CTX.SourceConcealOK Wᵈ M c Xᴿ? M′
  decaySourceConcealOK dec
      (CTX.seal-nonstar-unmatched-ok {X = X} Rns no-target) =
    CTX.seal-nonstar-unmatched-ok Rns
      (decayNoTargetOccupantAtSource {X = X} dec no-target)
  decaySourceConcealOK (env-decay refl refl refl refl mono)
      (CTX.seal-nonstar-name-protected-ok Rns aligned) =
    CTX.seal-nonstar-name-protected-ok Rns aligned
  decaySourceConcealOK dec CTX.fun-conceal-ok =
    CTX.fun-conceal-ok
  decaySourceConcealOK dec CTX.all-conceal-ok =
    CTX.all-conceal-ok
  decaySourceConcealOK dec CTX.id-conceal-ok =
    CTX.id-conceal-ok

  decayMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Y M′}
    → EnvDecay W Wᵈ
    → CTX.MatchedConcealPartnerOK W M c Y M′
    → CTX.MatchedConcealPartnerOK Wᵈ M c Y M′
  decayMatchedConcealPartnerOK dec
      (CTX.matched-seal-star-partner ok) =
    CTX.matched-seal-star-partner (decayRep★PartnerOK dec ok)
  decayMatchedConcealPartnerOK dec (CTX.matched-seal-nonstar Rns) =
    CTX.matched-seal-nonstar Rns
  decayMatchedConcealPartnerOK dec CTX.matched-fun-conceal-target =
    CTX.matched-fun-conceal-target
  decayMatchedConcealPartnerOK dec CTX.matched-all-conceal-target =
    CTX.matched-all-conceal-target
  decayMatchedConcealPartnerOK dec CTX.matched-id-conceal-target =
    CTX.matched-id-conceal-target

⊢²-decay : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ decay⊑ᵂ dec p
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.x⊑x² x∈) =
  CTI2.x⊑x² (decay∋ʷ dec x∈)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.ƛ⊑ƛ² M⊑M′) =
  CTI2.ƛ⊑ƛ² (⊢²-decay dec M⊑M′)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.·⊑·² L⊑L′ M⊑M′) =
  CTI2.·⊑·² (⊢²-decay dec L⊑L′) (⊢²-decay dec M⊑M′)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
  CTI2.Λ⊑Λ² (decayLiftCtx dec liftγ) vV vV′
    (⊢²-decay (liftDecayBoth X⊑X dec) V⊑V′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    {γ = γ}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑² Anv zero∈A (decayLiftCtxᴸ dec liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec γ)) M′⊢)
    (⊢²-decay (liftDecayLeft X⊑★ dec) V⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    {γ = γ}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} Anv zero∈A liftW
      liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (decaySmartCommaLiftᴸ dec liftW)
    (decaySmartLiftCtxᴸ dec (SPT.dynWorld-decay Wᵐ) liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec γ)) M′⊢)
    (⊢²-decay (SPT.dynWorld-decay Wᵐ) V⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.•⊑•² p∀ M⊑M′ q r) =
  CTI2.•⊑•² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.•⊑² p∀ M⊑M′ q r) =
  CTI2.•⊑² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.κ⊑κ² κ p) =
  CTI2.κ⊑κ² κ (decay⊑ᵂ dec p)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.cast⊑cast² c c′ M⊑M′ q) =
  CTI2.cast⊑cast² c c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑cast² c′ M⊑M′ q) =
  CTI2.⊑cast² c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.cast⊑² c M⊑M′ q) =
  CTI2.cast⊑² c (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑reveal² rule-mono CTX.rebase-idᴿ sc
      c′⊢ M⊑M′ q) =
  CTI2.⊑reveal² (λ _ eq → eq) CTX.rebase-idᴿ
    (decaySameCtx dec dec sc) c′⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑reveal² {W′ = W′} rule-mono
      (CTX.rebase-varᴿ rb) sc c′⊢ M⊑M′ q) =
  CTI2.⊑reveal²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTX.rebase-varᴿ
      (decayRebaseAt dec
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c′⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑conceal² rule-mono CTX.rebase-idᴿ sc
      c′⊢ M⊑M′ q) =
  CTI2.⊑conceal² (λ _ eq → eq) CTX.rebase-idᴿ
    (decaySameCtx dec dec sc) c′⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.⊑conceal² {W′ = W′} rule-mono
      (CTX.rebase-varᴿ rb) sc c′⊢ M⊑M′ q) =
  CTI2.⊑conceal²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTX.rebase-varᴿ
      (decayRebaseAt
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) dec rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c′⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑² rule-mono CTX.rebase-idᴸ sc
      c⊢ M⊑M′ q) =
  CTI2.reveal⊑² (λ _ eq → eq) CTX.rebase-idᴸ
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑² {W′ = W′} rule-mono
      (CTX.rebase-varᴸ rb) sc c⊢ M⊑M′ q) =
  CTI2.reveal⊑²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTX.rebase-varᴸ
      (decayRebaseAt dec
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑² rule-mono
      (CTX.rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.reveal⊑² (λ _ eq → eq)
    (CTX.rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑²-seal-star-open no-target rule-mono
      (CTX.tag-rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-seal-star-open
    (decayNoTargetOccupantAtSource dec no-target)
    (λ _ eq → eq)
    (CTX.tag-rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑²-source-ok ok rule-mono CTX.tag-rebase-idᴸ
      sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-source-ok (decaySourceConcealOK dec ok)
    (λ _ eq → eq) CTX.tag-rebase-idᴸ
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑²-source-ok {W′ = W′} ok rule-mono
      (CTX.tag-rebase-varᴸ rb) sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-source-ok
    (decaySourceConcealOK
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) ok)
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ})
    (CTX.tag-rebase-varᴸ
      (decayRebaseAt
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) dec rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) sc)
    c⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑²-source-ok ok rule-mono
      (CTX.tag-rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-source-ok (decaySourceConcealOK dec ok)
    (λ _ eq → eq)
    (CTX.tag-rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} rule-mono rb sc
      c⊢ c′⊢ M⊑M′ q) =
  CTI2.reveal⊑reveal²
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ})
    (decayRebaseAt dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} ok rule-mono rb sc
      c⊢ c′⊢ M⊑M′ q) =
  CTI2.conceal⊑conceal²
    (decayMatchedConcealPartnerOK
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) ok)
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ})
    (decayRebaseAt
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) dec rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ} ok rule-mono rb sc
      c⊢ c′⊢ M⊑M′ sourcePrem q) =
  CTI2.packaged-seal-star²
    (decayMatchedConcealPartnerOK
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) ok)
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ})
    (decayRebaseAt
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) dec rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) M⊑M′)
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ}) sourcePrem)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
    (CTI2.blame⊑² M′⊢ p) =
  CTI2.blame⊑²
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec _)) M′⊢)
    (decay⊑ᵂ dec p)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono)
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
