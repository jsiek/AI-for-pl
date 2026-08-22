module proof.DGG.CastTermImprecision2Typing where

-- File Charter:
--   * Projects source and target typing derivations from the version-2
--     cast-term imprecision relation.
--   * Provides the target projection needed by canonical-value inversion in
--     ExtraCastRight2, transporting typing across SameCtx and pivot-local
--     rebases whose runtime stores are unchanged.
--   * Erases optional-pivot conversion typing to ordinary store validity.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-lift)
import TermCtx as T
open import Conversion using
  (Conv↑; Conv↓; _⊢↑_; _⊢↓_;
   ⊢↑-unseal; ⊢↑-⇒; ⊢↑-∀; ⊢↑-id;
   ⊢↓-seal; ⊢↓-⇒; ⊢↓-∀; ⊢↓-id)
open import CastTerms
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   sourceStoreʷ;
   targetStoreʷ;
   CtxImp;
   ctx-imp;
   srcTyʷ;
   tgtTyʷ;
   srcCtxʷ;
   tgtCtxʷ;
   _∋ʷ_⦂_;
   Zʷ;
   Sʷ;
   SameCtx;
   same-[];
   same-∷;
   LiftCtx;
   lift-[];
   lift-∷;
   LiftCtxᴸ;
   liftᴸ-[];
   liftᴸ-∷;
   SmartLiftCtxᴸ;
   smart-lift-[];
   smart-lift-∷;
   SmartCommaLiftᴸ;
   smart-fresh-behind;
   smart-merge-alias;
   RebaseAt;
   RebaseAtᴸ;
   RebaseAtᴿ)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Context projections
------------------------------------------------------------------------

lookup-source : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {x e}
  → γ ∋ʷ x ⦂ e
  → srcCtxʷ γ T.∋ x ⦂ srcTyʷ e
lookup-source Zʷ = T.Z
lookup-source (Sʷ x∈) = T.S (lookup-source x∈)

lookup-target : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {x e}
  → γ ∋ʷ x ⦂ e
  → tgtCtxʷ γ T.∋ x ⦂ tgtTyʷ e
lookup-target Zʷ = T.Z
lookup-target (Sʷ x∈) = T.S (lookup-target x∈)

sameCtx-source : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CtxImp W′}
  → SameCtx γ γ′
  → srcCtxʷ γ ≡ srcCtxʷ γ′
sameCtx-source same-[] = refl
sameCtx-source (same-∷ sc) = cong (_ ∷_) (sameCtx-source sc)

sameCtx-target : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CtxImp W′}
  → SameCtx γ γ′
  → tgtCtxʷ γ ≡ tgtCtxʷ γ′
sameCtx-target same-[] = refl
sameCtx-target (same-∷ sc) = cong (_ ∷_) (sameCtx-target sc)

liftCtx-source : ∀ {Δᴸ Δᴿ Δ} {v} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp (CTX.liftWorldBoth v W)}
  → LiftCtx v γ γ′
  → srcCtxʷ γ′ ≡ T.⇑ᶜ (srcCtxʷ γ)
liftCtx-source lift-[] = refl
liftCtx-source (lift-∷ liftγ) = cong (_ ∷_) (liftCtx-source liftγ)

liftCtx-target : ∀ {Δᴸ Δᴿ Δ} {v} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp (CTX.liftWorldBoth v W)}
  → LiftCtx v γ γ′
  → tgtCtxʷ γ′ ≡ T.⇑ᶜ (tgtCtxʷ γ)
liftCtx-target lift-[] = refl
liftCtx-target (lift-∷ liftγ) = cong (_ ∷_) (liftCtx-target liftγ)

liftCtxᴸ-source : ∀ {Δᴸ Δᴿ Δ} {v} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp (CTX.liftWorldLeft v W)}
  → LiftCtxᴸ v γ γ′
  → srcCtxʷ γ′ ≡ T.⇑ᶜ (srcCtxʷ γ)
liftCtxᴸ-source liftᴸ-[] = refl
liftCtxᴸ-source (liftᴸ-∷ liftγ) = cong (_ ∷_) (liftCtxᴸ-source liftγ)

smartLiftCtxᴸ-source : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ} {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CtxImp W} {γᵐ : CtxImp Wᵐ}
  → SmartLiftCtxᴸ γ γᵐ
  → srcCtxʷ γᵐ ≡ T.⇑ᶜ (srcCtxʷ γ)
smartLiftCtxᴸ-source smart-lift-[] = refl
smartLiftCtxᴸ-source (smart-lift-∷ liftγ) =
  cong (_ ∷_) (smartLiftCtxᴸ-source liftγ)

smartLift-source-store : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ} {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
  → SmartCommaLiftᴸ W Wᵐ
  → sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)
smartLift-source-store (smart-fresh-behind guard) =
  CTX.SmartFreshBehindGuard.sourceStore-lifted guard
smartLift-source-store (smart-merge-alias guard) =
  CTX.SmartAliasMergeGuard.sourceStore-lifted guard

------------------------------------------------------------------------
-- Indexed conversion typing erases to ordinary validity
------------------------------------------------------------------------

mutual
  erase-⊢↑ : ∀ {Δ} {Σ : TyStore Δ} {X? A B} {c : Conv↑ Δ A B}
    → Σ Conv.⊢↑[ X? ] c
    → Σ ⊢↑ c
  erase-⊢↑ (Conv.⊢↑-unsealˣ X∈) = ⊢↑-unseal X∈
  erase-⊢↑ (Conv.⊢↑-⇒ˣ join ⊢c ⊢d) =
    ⊢↑-⇒ (erase-⊢↓ ⊢c) (erase-⊢↑ ⊢d)
  erase-⊢↑ (Conv.⊢↑-∀ˣ ⊢c) = ⊢↑-∀ (erase-⊢↑ ⊢c)
  erase-⊢↑ (Conv.⊢↑-∀-idˣ ⊢c) = ⊢↑-∀ (erase-⊢↑ ⊢c)
  erase-⊢↑ Conv.⊢↑-idˣ = ⊢↑-id

  erase-⊢↓ : ∀ {Δ} {Σ : TyStore Δ} {X? A B} {c : Conv↓ Δ A B}
    → Σ Conv.⊢↓[ X? ] c
    → Σ ⊢↓ c
  erase-⊢↓ (Conv.⊢↓-sealˣ X∈) = ⊢↓-seal X∈
  erase-⊢↓ (Conv.⊢↓-⇒ˣ join ⊢c ⊢d) =
    ⊢↓-⇒ (erase-⊢↑ ⊢c) (erase-⊢↓ ⊢d)
  erase-⊢↓ (Conv.⊢↓-∀ˣ ⊢c) = ⊢↓-∀ (erase-⊢↓ ⊢c)
  erase-⊢↓ (Conv.⊢↓-∀-idˣ ⊢c) = ⊢↓-∀ (erase-⊢↓ ⊢c)
  erase-⊢↓ Conv.⊢↓-idˣ = ⊢↓-id

------------------------------------------------------------------------
-- Runtime-store equalities carried by rebasing
------------------------------------------------------------------------

rebase-source-store : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ Xᴿ}
  → RebaseAt W W′ Xᴸ Xᴿ
  → sourceStoreʷ W′ ≡ sourceStoreʷ W
rebase-source-store rb =
  CTX.SameRuntime.sourceStore-same (CTX.RebaseAt.sameRuntime rb)

rebase-target-store : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ Xᴿ}
  → RebaseAt W W′ Xᴸ Xᴿ
  → targetStoreʷ W′ ≡ targetStoreʷ W
rebase-target-store rb =
  CTX.SameRuntime.targetStore-same (CTX.RebaseAt.sameRuntime rb)

rebaseᴸ-source-store : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {X?}
  → RebaseAtᴸ W W′ X?
  → sourceStoreʷ W′ ≡ sourceStoreʷ W
rebaseᴸ-source-store CTX.rebase-idᴸ = refl
rebaseᴸ-source-store (CTX.rebase-varᴸ rb) = rebase-source-store rb
rebaseᴸ-source-store (CTX.rebase-onlyᴸ to-star disaligned represented) = refl

rebaseᴸ-target-store : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {X?}
  → RebaseAtᴸ W W′ X?
  → targetStoreʷ W′ ≡ targetStoreʷ W
rebaseᴸ-target-store CTX.rebase-idᴸ = refl
rebaseᴸ-target-store (CTX.rebase-varᴸ rb) = rebase-target-store rb
rebaseᴸ-target-store (CTX.rebase-onlyᴸ to-star disaligned represented) = refl

rebaseᴿ-source-store : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {X?}
  → RebaseAtᴿ W W′ X?
  → sourceStoreʷ W′ ≡ sourceStoreʷ W
rebaseᴿ-source-store CTX.rebase-idᴿ = refl
rebaseᴿ-source-store (CTX.rebase-varᴿ rb) = rebase-source-store rb

rebaseᴿ-target-store : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {X?}
  → RebaseAtᴿ W W′ X?
  → targetStoreʷ W′ ≡ targetStoreʷ W
rebaseᴿ-target-store CTX.rebase-idᴿ = refl
rebaseᴿ-target-store (CTX.rebase-varᴿ rb) = rebase-target-store rb

------------------------------------------------------------------------
-- Typing transport at a wrapper boundary
------------------------------------------------------------------------

transport-source : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CtxImp W′} {M A}
  → sourceStoreʷ W′ ≡ sourceStoreʷ W
  → SameCtx γ γ′
  → ⟨ Δᴸ , sourceStoreʷ W′ , srcCtxʷ γ′ ⟩ ⊢ M ⦂ A
  → ⟨ Δᴸ , sourceStoreʷ W , srcCtxʷ γ ⟩ ⊢ M ⦂ A
transport-source {Δᴸ = Δᴸ} {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {M = M} {A = A} store-eq sc M⊢ =
  subst≡ (λ Σ → ⟨ Δᴸ , Σ , srcCtxʷ γ ⟩ ⊢ M ⦂ A)
    store-eq
    (subst≡ (λ Γ → ⟨ Δᴸ , sourceStoreʷ W′ , Γ ⟩ ⊢ M ⦂ A)
      (sym (sameCtx-source sc)) M⊢)

transport-target : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CtxImp W′} {M A}
  → targetStoreʷ W′ ≡ targetStoreʷ W
  → SameCtx γ γ′
  → ⟨ Δᴿ , targetStoreʷ W′ , tgtCtxʷ γ′ ⟩ ⊢ M ⦂ A
  → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ A
transport-target {Δᴿ = Δᴿ} {W = W} {W′ = W′} {γ = γ} {γ′ = γ′}
    {M = M} {A = A} store-eq sc M⊢ =
  subst≡ (λ Σ → ⟨ Δᴿ , Σ , tgtCtxʷ γ ⟩ ⊢ M ⦂ A)
    store-eq
    (subst≡ (λ Γ → ⟨ Δᴿ , targetStoreʷ W′ , Γ ⟩ ⊢ M ⦂ A)
      (sym (sameCtx-target sc)) M⊢)

------------------------------------------------------------------------
-- Typing projections
------------------------------------------------------------------------

mutual
  source-typing² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {M M′ A B} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → ⟨ Δᴸ , sourceStoreʷ W , srcCtxʷ γ ⟩ ⊢ M ⦂ A

  target-typing² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {M M′ A B} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M′ ⦂ B

  source-typing² (CTI2.x⊑x² x∈) = ⊢` (lookup-source x∈)
  source-typing² (CTI2.ƛ⊑ƛ² M⊑M′) = ⊢ƛ (source-typing² M⊑M′)
  source-typing² (CTI2.·⊑·² L⊑L′ M⊑M′) =
    ⊢· (source-typing² L⊑L′) (source-typing² M⊑M′)
  source-typing² (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
    ⊢Λ vV
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (liftCtx-source liftγ) (source-typing² V⊑V′))
  source-typing² (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
    ⊢Λ vV
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (liftCtxᴸ-source liftγ) (source-typing² V⊑M′))
  source-typing²
      (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV M′⊢
        V⊑M′ q) =
    ⊢Λ vV
      (subst≡ (λ Σ → ⟨ _ , Σ , T.⇑ᶜ (srcCtxʷ _) ⟩ ⊢ _ ⦂ _)
        (smartLift-source-store liftW)
        (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
          (smartLiftCtxᴸ-source liftγ) (source-typing² V⊑M′)))
  source-typing² (CTI2.•⊑•² p∀ M⊑M′ q r) = ⊢• (source-typing² M⊑M′)
  source-typing² (CTI2.•⊑² p∀ M⊑M′ q r) = ⊢• (source-typing² M⊑M′)
  source-typing² (CTI2.κ⊑κ² κ p) = ⊢$ κ
  source-typing² (CTI2.cast⊑cast² c c′ M⊑M′ q) =
    ⊢⟨⟩ (source-typing² M⊑M′) c
  source-typing² (CTI2.⊑cast² c′ M⊑M′ q) = source-typing² M⊑M′
  source-typing² (CTI2.⊑reveal² mono rb sc c′⊢ M⊑M′ q) =
    transport-source (rebaseᴿ-source-store rb) sc (source-typing² M⊑M′)
  source-typing² (CTI2.⊑conceal² mono rb sc c′⊢ M⊑M′ q) =
    transport-source (sym (rebaseᴿ-source-store rb)) sc
      (source-typing² M⊑M′)
  source-typing² (CTI2.cast⊑² c M⊑M′ q) = ⊢⟨⟩ (source-typing² M⊑M′) c
  source-typing² (CTI2.reveal⊑² mono rb sc c⊢ M⊑M′ q) =
    ⊢reveal (erase-⊢↑ c⊢)
      (transport-source (rebaseᴸ-source-store rb) sc (source-typing² M⊑M′))
  source-typing²
      (CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢
        M⊑M′ q) =
    ⊢conceal (erase-⊢↓ c⊢)
      (transport-source (sym
        (rebaseᴸ-source-store (CTX.forgetTagRebaseᴸ rb))) sc
        (source-typing² M⊑M′))
  source-typing²
      (CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ M⊑M′ q) =
    ⊢conceal (erase-⊢↓ c⊢)
      (transport-source (sym
        (rebaseᴸ-source-store (CTX.forgetTagRebaseᴸ rb))) sc
        (source-typing² M⊑M′))
  source-typing² (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ M⊑M′ q) =
    ⊢reveal (erase-⊢↑ c⊢)
      (transport-source (rebase-source-store rb) sc (source-typing² M⊑M′))
  source-typing²
      (CTI2.conceal⊑conceal² ok mono rb sc c⊢ c′⊢ M⊑M′ q) =
    ⊢conceal (erase-⊢↓ c⊢)
      (transport-source (sym (rebase-source-store rb)) sc
        (source-typing² M⊑M′))
  source-typing²
      (CTI2.packaged-seal-star² ok mono rb sc c⊢ c′⊢
        M⊑M′ sourcePrem q) =
    transport-source (sym (rebase-source-store rb)) sc
      (source-typing² sourcePrem)
  source-typing² (CTI2.blame⊑² M′⊢ p) = ⊢blame
  source-typing² (CTI2.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
    ⊢⊕ op (source-typing² L⊑L′) (source-typing² M⊑M′)

  target-typing² (CTI2.x⊑x² x∈) = ⊢` (lookup-target x∈)
  target-typing² (CTI2.ƛ⊑ƛ² M⊑M′) = ⊢ƛ (target-typing² M⊑M′)
  target-typing² (CTI2.·⊑·² L⊑L′ M⊑M′) =
    ⊢· (target-typing² L⊑L′) (target-typing² M⊑M′)
  target-typing² (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
    ⊢Λ vV′
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (liftCtx-target liftγ) (target-typing² V⊑V′))
  target-typing² (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) = M′⊢
  target-typing²
      (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV M′⊢
        V⊑M′ q) = M′⊢
  target-typing² (CTI2.•⊑•² p∀ M⊑M′ q r) = ⊢• (target-typing² M⊑M′)
  target-typing² (CTI2.•⊑² p∀ M⊑M′ q r) = target-typing² M⊑M′
  target-typing² (CTI2.κ⊑κ² κ p) = ⊢$ κ
  target-typing² (CTI2.cast⊑cast² c c′ M⊑M′ q) =
    ⊢⟨⟩ (target-typing² M⊑M′) c′
  target-typing² (CTI2.⊑cast² c′ M⊑M′ q) = ⊢⟨⟩ (target-typing² M⊑M′) c′
  target-typing² (CTI2.⊑reveal² mono rb sc c′⊢ M⊑M′ q) =
    ⊢reveal (erase-⊢↑ c′⊢)
      (transport-target (rebaseᴿ-target-store rb) sc (target-typing² M⊑M′))
  target-typing² (CTI2.⊑conceal² mono rb sc c′⊢ M⊑M′ q) =
    ⊢conceal (erase-⊢↓ c′⊢)
      (transport-target (sym (rebaseᴿ-target-store rb)) sc
        (target-typing² M⊑M′))
  target-typing² (CTI2.cast⊑² c M⊑M′ q) = target-typing² M⊑M′
  target-typing² (CTI2.reveal⊑² mono rb sc c⊢ M⊑M′ q) =
    transport-target (rebaseᴸ-target-store rb) sc (target-typing² M⊑M′)
  target-typing²
      (CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢
        M⊑M′ q) =
    transport-target (sym
      (rebaseᴸ-target-store (CTX.forgetTagRebaseᴸ rb))) sc
      (target-typing² M⊑M′)
  target-typing²
      (CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ M⊑M′ q) =
    transport-target (sym
      (rebaseᴸ-target-store (CTX.forgetTagRebaseᴸ rb))) sc
      (target-typing² M⊑M′)
  target-typing² (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ M⊑M′ q) =
    ⊢reveal (erase-⊢↑ c′⊢)
      (transport-target (rebase-target-store rb) sc (target-typing² M⊑M′))
  target-typing²
      (CTI2.conceal⊑conceal² ok mono rb sc c⊢ c′⊢ M⊑M′ q) =
    ⊢conceal (erase-⊢↓ c′⊢)
      (transport-target (sym (rebase-target-store rb)) sc
        (target-typing² M⊑M′))
  target-typing²
      (CTI2.packaged-seal-star² ok mono rb sc c⊢ c′⊢
        M⊑M′ sourcePrem q) =
    ⊢conceal (erase-⊢↓ c′⊢)
      (transport-target (sym (rebase-target-store rb)) sc
        (target-typing² M⊑M′))
  target-typing² (CTI2.blame⊑² M′⊢ p) = M′⊢
  target-typing² (CTI2.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
    ⊢⊕ op (target-typing² L⊑L′) (target-typing² M⊑M′)
