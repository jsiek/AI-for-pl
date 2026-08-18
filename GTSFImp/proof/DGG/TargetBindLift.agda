module proof.DGG.TargetBindLift where

-- File Charter:
--   * Converts the post-Λ body world from an abstract lifted target binder
--     to the fresh store-bound target binder used by the instantiation
--     reduct.
--   * Reuses center renaming for the fresh center slot, then transports only
--     target-store bookkeeping from `store-lift` to the corresponding
--     `store-bind`.
--   * Exports the two-bind tower world and the derivation transport consumed
--     by the M5 instantiation-inversion Λ case.

open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using (TyStore; store-lift; store-bind; _∋_⦂_; S-lift∋)
open import Imprecision using
  (VarImp; ImpEnv; X⊑★; X⊑X; ⇒⊑⇒; instᵐ; extendᵐ; _⊢_⊑_)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ; wk↪ᵗ)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_)
import TermCtx as T
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.SealPeelToolkit as SPT
open import proof.TypeInTermSubst using
  (StoreTransport; StoreTransport-lift; StoreTransport-lift-bind;
   typing-store-transport)
open import proof.ImprecisionConsistency using
  (imp-env-weaken; toRenameᵗ-injective)

open CTI2 using
  (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_; PivotJoin;
   _⊢↑[_]_; _⊢↓[_]_)

------------------------------------------------------------------------
-- Small center-renaming normalizers
------------------------------------------------------------------------

∘↪-idˡ : ∀ {Δ Δ′}
  → (η : Δ ↪ᵗ Δ′)
  → (id↪ᵗ CR.∘↪ η) ≡ η
∘↪-idˡ empty = refl
∘↪-idˡ (keep η) = cong keep (∘↪-idˡ η)
∘↪-idˡ (skip η) = cong skip (∘↪-idˡ η)

renameEnv-id : ∀ {Δ}
  → (μ : ImpEnv Δ)
  → ∀ X
  → CR.renameEnv id↪ᵗ μ X ≡ μ X
renameEnv-id {zero} μ ()
renameEnv-id {suc Δ} μ Fin.zero = refl
renameEnv-id {suc Δ} μ (Fin.suc X) =
  renameEnv-id (λ Y → μ (Fin.suc Y)) X

------------------------------------------------------------------------
-- The fresh target bind tower
------------------------------------------------------------------------

ΛLiftToBindFreshWorld : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ)))
ΛLiftToBindFreshWorld v W =
  CTI2.world
    (skip (keep (skip (CTI2.ηᴸʷ W))))
    (skip (keep (keep (CTI2.ηᴿʷ W))))
    (instᵐ (extendᵐ v (instᵐ (CTI2.impEnvʷ W))))
    (store-lift (CTI2.sourceStoreʷ W))
    (store-bind (store-bind (CTI2.targetStoreʷ W) ★) (＇ Fin.zero))


ΛLiftToBindFreshWorldᴸ : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (suc (suc Δᴸ)) (suc (suc Δᴿ))
      (suc (suc (suc (suc Δ))))
ΛLiftToBindFreshWorldᴸ v W =
  CTI2.world
    (skip (keep (keep (skip (CTI2.ηᴸʷ W)))))
    (skip (keep (skip (keep (CTI2.ηᴿʷ W)))))
    (instᵐ (extendᵐ v (extendᵐ X⊑★
      (instᵐ (CTI2.impEnvʷ W)))))
    (store-lift (store-lift (CTI2.sourceStoreʷ W)))
    (store-bind (store-bind (CTI2.targetStoreʷ W) ★) (＇ Fin.zero))

------------------------------------------------------------------------
-- Indexed conversion typing under store transport
------------------------------------------------------------------------

mutual
  revealˣ-store-transport : ∀ {Δ} {Σ Σ′ : TyStore Δ} {X? A B}
      {c : Conv↑ Δ A B}
    → StoreTransport Σ Σ′
    → Σ CTI2.⊢↑[ X? ] c
    → Σ′ CTI2.⊢↑[ X? ] c
  revealˣ-store-transport hΣ (CTI2.⊢↑-unsealˣ X∈) =
    CTI2.⊢↑-unsealˣ (hΣ X∈)
  revealˣ-store-transport hΣ (CTI2.⊢↑-⇒ˣ join c⊢ d⊢) =
    CTI2.⊢↑-⇒ˣ join (concealˣ-store-transport hΣ c⊢)
      (revealˣ-store-transport hΣ d⊢)
  revealˣ-store-transport hΣ (CTI2.⊢↑-∀ˣ c⊢) =
    CTI2.⊢↑-∀ˣ
      (revealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  revealˣ-store-transport hΣ (CTI2.⊢↑-∀-idˣ c⊢) =
    CTI2.⊢↑-∀-idˣ
      (revealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  revealˣ-store-transport hΣ CTI2.⊢↑-idˣ = CTI2.⊢↑-idˣ

  concealˣ-store-transport : ∀ {Δ} {Σ Σ′ : TyStore Δ} {X? A B}
      {c : Conv↓ Δ A B}
    → StoreTransport Σ Σ′
    → Σ CTI2.⊢↓[ X? ] c
    → Σ′ CTI2.⊢↓[ X? ] c
  concealˣ-store-transport hΣ (CTI2.⊢↓-sealˣ X∈) =
    CTI2.⊢↓-sealˣ (hΣ X∈)
  concealˣ-store-transport hΣ (CTI2.⊢↓-⇒ˣ join c⊢ d⊢) =
    CTI2.⊢↓-⇒ˣ join (revealˣ-store-transport hΣ c⊢)
      (concealˣ-store-transport hΣ d⊢)
  concealˣ-store-transport hΣ (CTI2.⊢↓-∀ˣ c⊢) =
    CTI2.⊢↓-∀ˣ
      (concealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  concealˣ-store-transport hΣ (CTI2.⊢↓-∀-idˣ c⊢) =
    CTI2.⊢↓-∀-idˣ
      (concealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  concealˣ-store-transport hΣ CTI2.⊢↓-idˣ = CTI2.⊢↓-idˣ

mutual
  revealˣ-pivot-store : ∀ {Δ} {Σ : TyStore Δ} {X A B}
      {c : Conv↑ Δ A B}
    → Σ CTI2.⊢↑[ just X ] c
    → Σ[ R ∈ Ty Δ ] Σ ∋ X ⦂ R
  revealˣ-pivot-store (CTI2.⊢↑-unsealˣ {R = R} X∈) = R , X∈
  revealˣ-pivot-store (CTI2.⊢↑-⇒ˣ CTI2.join-left c⊢ d⊢) =
    concealˣ-pivot-store c⊢
  revealˣ-pivot-store (CTI2.⊢↑-⇒ˣ CTI2.join-right c⊢ d⊢) =
    revealˣ-pivot-store d⊢
  revealˣ-pivot-store (CTI2.⊢↑-⇒ˣ CTI2.join-both c⊢ d⊢) =
    concealˣ-pivot-store c⊢
  revealˣ-pivot-store (CTI2.⊢↑-∀ˣ c⊢)
      with revealˣ-pivot-store c⊢
  revealˣ-pivot-store (CTI2.⊢↑-∀ˣ c⊢)
      | R , S-lift∋ {A = A} X∈ eq = A , X∈

  concealˣ-pivot-store : ∀ {Δ} {Σ : TyStore Δ} {X A B}
      {c : Conv↓ Δ A B}
    → Σ CTI2.⊢↓[ just X ] c
    → Σ[ R ∈ Ty Δ ] Σ ∋ X ⦂ R
  concealˣ-pivot-store (CTI2.⊢↓-sealˣ {R = R} X∈) = R , X∈
  concealˣ-pivot-store (CTI2.⊢↓-⇒ˣ CTI2.join-left c⊢ d⊢) =
    revealˣ-pivot-store c⊢
  concealˣ-pivot-store (CTI2.⊢↓-⇒ˣ CTI2.join-right c⊢ d⊢) =
    concealˣ-pivot-store d⊢
  concealˣ-pivot-store (CTI2.⊢↓-⇒ˣ CTI2.join-both c⊢ d⊢) =
    revealˣ-pivot-store c⊢
  concealˣ-pivot-store (CTI2.⊢↓-∀ˣ c⊢)
      with concealˣ-pivot-store c⊢
  concealˣ-pivot-store (CTI2.⊢↓-∀ˣ c⊢)
      | R , S-lift∋ {A = A} X∈ eq = A , X∈

------------------------------------------------------------------------
-- Target-store-only world movement
------------------------------------------------------------------------

record TargetStoreMove {Δᴸ Δᴿ Δ}
    (W Wᵗ : World Δᴸ Δᴿ Δ) : Set where
  constructor target-store-move
  field
    ηᴸ-same : CTI2.ηᴸʷ Wᵗ ≡ CTI2.ηᴸʷ W
    ηᴿ-same : CTI2.ηᴿʷ Wᵗ ≡ CTI2.ηᴿʷ W
    impEnv-same : ∀ X → CTI2.impEnvʷ Wᵗ X ≡ CTI2.impEnvʷ W X
    sourceStore-same : CTI2.sourceStoreʷ Wᵗ ≡ CTI2.sourceStoreʷ W
    targetStore-transport :
      StoreTransport (CTI2.targetStoreʷ W) (CTI2.targetStoreʷ Wᵗ)
    targetResolve-same : ∀ {X R}
      → CTI2.targetStoreʷ W ∋ X ⦂ R
      → CTI2.resolveVar (CTI2.targetStoreʷ Wᵗ) X
          ≡ CTI2.resolveVar (CTI2.targetStoreʷ W) X

open TargetStoreMove public

move⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → TargetStoreMove W Wᵗ
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ Wᵗ ⟩ B
move⊑ᵂ (target-store-move refl refl same refl hΣ resolve) p =
  imp-env-weaken (λ X dynamic → trans (same X) dynamic) p

move⊑ᵂ-back : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → TargetStoreMove W Wᵗ
  → A ⊑ᵂ⟨ Wᵗ ⟩ B
  → A ⊑ᵂ⟨ W ⟩ B
move⊑ᵂ-back (target-store-move refl refl same refl hΣ resolve) p =
  imp-env-weaken (λ X dynamic → trans (sym (same X)) dynamic) p

moveCtx : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → TargetStoreMove W Wᵗ
  → CtxImp W
  → CtxImp Wᵗ
moveCtx mv [] = []
moveCtx {W = W} mv (CTI2.ctx-imp A B p ∷ γ) =
  CTI2.ctx-imp A B (move⊑ᵂ mv p) ∷ moveCtx mv γ

move∋ʷ : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (mv : TargetStoreMove W Wᵗ)
  → γ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B p
  → moveCtx mv γ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B (move⊑ᵂ mv p)
move∋ʷ mv CTI2.Zʷ = CTI2.Zʷ
move∋ʷ mv (CTI2.Sʷ x∈) = CTI2.Sʷ (move∋ʷ mv x∈)

moveSameCtx : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W₁ W₁ᵗ : World Δᴸ Δᴿ Δ}
    {W₂ W₂ᵗ : World Δᴸ Δᴿ Δ′}
    {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂}
  → (mv₁ : TargetStoreMove W₁ W₁ᵗ)
  → (mv₂ : TargetStoreMove W₂ W₂ᵗ)
  → CTI2.SameCtx γ₁ γ₂
  → CTI2.SameCtx (moveCtx mv₁ γ₁) (moveCtx mv₂ γ₂)
moveSameCtx mv₁ mv₂ CTI2.same-[] = CTI2.same-[]
moveSameCtx mv₁ mv₂ (CTI2.same-∷ sc) =
  CTI2.same-∷ (moveSameCtx mv₁ mv₂ sc)

moveImpEnvMono : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₁ᵗ W₂ W₂ᵗ : World Δᴸ Δᴿ Δ}
  → TargetStoreMove W₁ W₁ᵗ
  → TargetStoreMove W₂ W₂ᵗ
  → CTI2.ImpEnvMono W₁ W₂
  → CTI2.ImpEnvMono W₁ᵗ W₂ᵗ
moveImpEnvMono
    (target-store-move refl refl same₁ refl hΣ₁ resolve₁)
    (target-store-move refl refl same₂ refl hΣ₂ resolve₂)
    mono X dynamic =
  trans (same₂ X) (mono X (trans (sym (same₁ X)) dynamic))

private
  moveRep★PartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {P Xᴿ? M′}
    → TargetStoreMove W Wᵗ
    → CTI2.Rep★PartnerOK W X P Xᴿ? M′
    → CTI2.Rep★PartnerOK Wᵗ X P Xᴿ? M′
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTI2.rep★-untagged nt) =
    CTI2.rep★-untagged nt
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTI2.rep★-nonvar-tag Gnv) =
    CTI2.rep★-nonvar-tag Gnv
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTI2.rep★-var-tag aligned) =
    CTI2.rep★-var-tag aligned
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
    CTI2.rep★-matched-inner-tags X₂≢X aligned
  moveRep★PartnerOK mv (CTI2.rep★-round-trip ok) =
    CTI2.rep★-round-trip (moveRep★PartnerOK mv ok)

  moveNoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ}
    → TargetStoreMove W Wᵗ
    → CTI2.NoTargetOccupantAtSource W X
    → CTI2.NoTargetOccupantAtSource Wᵗ X
  moveNoTargetOccupantAtSource
      (target-store-move refl refl same refl hΣ resolve) no-target =
    no-target

  moveSourceConcealOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
    → TargetStoreMove W Wᵗ
    → CTI2.SourceConcealOK W M c Xᴿ? M′
    → CTI2.SourceConcealOK Wᵗ M c Xᴿ? M′
  moveSourceConcealOK mv (CTI2.seal-nonstar-plain-ok Rns nt) =
    CTI2.seal-nonstar-plain-ok Rns nt
  moveSourceConcealOK (target-store-move refl refl same refl hΣ resolve)
      (CTI2.seal-nonstar-name-protected-ok Rns aligned) =
    CTI2.seal-nonstar-name-protected-ok Rns aligned
  moveSourceConcealOK mv CTI2.fun-conceal-ok =
    CTI2.fun-conceal-ok
  moveSourceConcealOK mv CTI2.all-conceal-ok =
    CTI2.all-conceal-ok
  moveSourceConcealOK mv CTI2.id-conceal-ok =
    CTI2.id-conceal-ok

  moveMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Y M′}
    → TargetStoreMove W Wᵗ
    → CTI2.MatchedConcealPartnerOK W M c Y M′
    → CTI2.MatchedConcealPartnerOK Wᵗ M c Y M′
  moveMatchedConcealPartnerOK mv
      (CTI2.matched-seal-star-partner ok) =
    CTI2.matched-seal-star-partner (moveRep★PartnerOK mv ok)
  moveMatchedConcealPartnerOK mv (CTI2.matched-seal-nonstar Rns) =
    CTI2.matched-seal-nonstar Rns
  moveMatchedConcealPartnerOK mv CTI2.matched-fun-conceal-target =
    CTI2.matched-fun-conceal-target
  moveMatchedConcealPartnerOK mv CTI2.matched-all-conceal-target =
    CTI2.matched-all-conceal-target
  moveMatchedConcealPartnerOK mv CTI2.matched-id-conceal-target =
    CTI2.matched-id-conceal-target

liftMoveBoth : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → TargetStoreMove W Wᵗ
  → TargetStoreMove (CTI2.liftWorldBoth v W) (CTI2.liftWorldBoth v Wᵗ)
liftMoveBoth v (target-store-move refl refl same refl hΣ resolve) =
  target-store-move refl refl same′ refl (StoreTransport-lift hΣ)
    resolve-lift
  where
  same′ : ∀ X → extendᵐ v _ X ≡ extendᵐ v _ X
  same′ Fin.zero = refl
  same′ (Fin.suc X) = same X

  resolve-lift : ∀ {X R}
    → store-lift _ ∋ X ⦂ R
    → CTI2.resolveVar (store-lift _) X ≡ CTI2.resolveVar (store-lift _) X
  resolve-lift (S-lift∋ X∈ eq) = cong ⇑ᵗ (resolve X∈)

liftMoveLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → TargetStoreMove W Wᵗ
  → TargetStoreMove (CTI2.liftWorldLeft v W) (CTI2.liftWorldLeft v Wᵗ)
liftMoveLeft v (target-store-move refl refl same refl hΣ resolve) =
  target-store-move refl refl same′ refl hΣ resolve
  where
  same′ : ∀ X → extendᵐ v _ X ≡ extendᵐ v _ X
  same′ Fin.zero = refl
  same′ (Fin.suc X) = same X

moveCtx-tgt : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (mv : TargetStoreMove W Wᵗ)
  → (γ : CtxImp W)
  → CTI2.tgtCtxʷ (moveCtx mv γ) ≡ CTI2.tgtCtxʷ γ
moveCtx-tgt mv [] = refl
moveCtx-tgt mv (CTI2.ctx-imp A B p ∷ γ) =
  cong (B ∷_) (moveCtx-tgt mv γ)

target-typing-move : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴿ} {B : Ty Δᴿ}
  → (mv : TargetStoreMove W Wᵗ)
  → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ , CTI2.targetStoreʷ Wᵗ ,
        CTI2.tgtCtxʷ (moveCtx mv γ) ⟩ ⊢ M ⦂ B
target-typing-move mv M⊢ =
  subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
    (sym (moveCtx-tgt mv _))
    (typing-store-transport (targetStore-transport mv) M⊢)

record TargetBindLiftMove {Δᴸ Δᴿ Δ}
    (W Wᵗ : World Δᴸ Δᴿ Δ) (Y : TyVar Δᴿ) : Set where
  constructor target-bind-lift-move
  field
    baseMove : TargetStoreMove W Wᵗ
    target-pivot-star :
      CTI2.impEnvʷ Wᵗ (toRenameᵗ (CTI2.ηᴿʷ Wᵗ) Y) ≡ X⊑★
    target-resolve-pivot-old :
      CTI2.resolveVar (CTI2.targetStoreʷ W) Y ≡ ＇ Y
    target-resolve-pivot :
      CTI2.resolveVar (CTI2.targetStoreʷ Wᵗ) Y ≡ ★
    target-resolve-other : ∀ Z
      → Z ≢ Y
      → CTI2.resolveVar (CTI2.targetStoreʷ Wᵗ) Z
          ≡ CTI2.resolveVar (CTI2.targetStoreʷ W) Z

open TargetBindLiftMove public

fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
  → Fin.suc X ≡ Fin.suc Y
  → X ≡ Y
fin-suc-injective refl = refl

target-bind-lift-move⊑ᵂ :
  ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → TargetBindLiftMove W Wᵗ Y
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ Wᵗ ⟩ B
target-bind-lift-move⊑ᵂ mv = move⊑ᵂ (baseMove mv)

moveLiftCtx : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {v} {γ : CtxImp W} {γ′ : CtxImp (CTI2.liftWorldBoth v W)}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.LiftCtx v γ γ′
  → CTI2.LiftCtx v (moveCtx mv γ)
      (moveCtx (liftMoveBoth v mv) γ′)
moveLiftCtx mv CTI2.lift-[] = CTI2.lift-[]
moveLiftCtx mv (CTI2.lift-∷ liftγ) =
  CTI2.lift-∷ (moveLiftCtx mv liftγ)

moveLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {v} {γ : CtxImp W} {γ′ : CtxImp (CTI2.liftWorldLeft v W)}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.LiftCtxᴸ v γ γ′
  → CTI2.LiftCtxᴸ v (moveCtx mv γ)
      (moveCtx (liftMoveLeft v mv) γ′)
moveLiftCtxᴸ mv CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
moveLiftCtxᴸ mv (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (moveLiftCtxᴸ mv liftγ)

liftTargetBindMoveBoth : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
  → (v : VarImp)
  → TargetBindLiftMove W Wᵗ Y
  → TargetBindLiftMove
      (CTI2.liftWorldBoth v W)
      (CTI2.liftWorldBoth v Wᵗ)
      (Fin.suc Y)
liftTargetBindMoveBoth {W = W} {Wᵗ = Wᵗ} {Y = Y} v
    (target-bind-lift-move mv pivot-star old-pivot pivot-res other) =
  target-bind-lift-move (liftMoveBoth v mv) pivot-star
    (cong ⇑ᵗ old-pivot) (cong ⇑ᵗ pivot-res) other′
  where
  other′ : ∀ Z
    → Z ≢ Fin.suc Y
    → CTI2.resolveVar
        (CTI2.targetStoreʷ (CTI2.liftWorldBoth v Wᵗ)) Z
        ≡ CTI2.resolveVar
            (CTI2.targetStoreʷ (CTI2.liftWorldBoth v W)) Z
  other′ Fin.zero neq = refl
  other′ (Fin.suc Z) neq = cong ⇑ᵗ (other Z (λ eq → neq (cong Fin.suc eq)))

liftTargetBindMoveLeft : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
  → (v : VarImp)
  → TargetBindLiftMove W Wᵗ Y
  → TargetBindLiftMove
      (CTI2.liftWorldLeft v W)
      (CTI2.liftWorldLeft v Wᵗ)
      Y
liftTargetBindMoveLeft v
    (target-bind-lift-move mv pivot-star old-pivot pivot-res other) =
  target-bind-lift-move (liftMoveLeft v mv) pivot-star old-pivot
    pivot-res other

targetStoreAs : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyStore Δᴿ
  → World Δᴸ Δᴿ Δ
targetStoreAs W Σᴿ =
  CTI2.world (CTI2.ηᴸʷ W) (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W)
    (CTI2.sourceStoreʷ W) Σᴿ

target-pivot-star-source : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
  → TargetBindLiftMove W Wᵗ Y
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴿʷ W) Y) ≡ X⊑★
target-pivot-star-source
    (target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other) =
  trans (sym (same _)) pivot-star

premiseMoveEqAny : ∀ {Δᴸ Δᴿ Δ Δᴸ′ Δ′}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ′ Δᴿ Δ′}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.targetStoreʷ W′ ≡ CTI2.targetStoreʷ W
  → TargetStoreMove W′ (targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ))
premiseMoveEqAny
    {Wᵗ = Wᵗ}
    {W′ = W′}
    (target-store-move refl refl same refl hΣ resolve)
    targetEq =
  target-store-move refl refl (λ X → refl) refl transport′ resolve′
  where
  transport′ :
    StoreTransport (CTI2.targetStoreʷ W′) (CTI2.targetStoreʷ Wᵗ)
  transport′ {X = X} {A = A} X∈ =
    hΣ (subst≡ (λ Σ → Σ ∋ X ⦂ A) targetEq X∈)

  resolve′ : ∀ {X R}
    → CTI2.targetStoreʷ W′ ∋ X ⦂ R
    → CTI2.resolveVar (CTI2.targetStoreʷ Wᵗ) X
        ≡ CTI2.resolveVar (CTI2.targetStoreʷ W′) X
  resolve′ {X = X} {R = R} X∈ =
    trans
      (resolve (subst≡ (λ Σ → Σ ∋ X ⦂ R) targetEq X∈))
      (cong (λ Σ → CTI2.resolveVar Σ X) (sym targetEq))

premiseMoveEq : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.targetStoreʷ W′ ≡ CTI2.targetStoreʷ W
  → TargetStoreMove W′ (targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ))
premiseMoveEq = premiseMoveEqAny

premiseTargetBindMove : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y}
  → TargetBindLiftMove W Wᵗ Y
  → CTI2.ImpEnvMono W W′
  → CTI2.targetStoreʷ W′ ≡ CTI2.targetStoreʷ W
  → toRenameᵗ (CTI2.ηᴿʷ W′) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y
  → TargetBindLiftMove W′ (targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ)) Y
premiseTargetBindMove
    {W = W} {Wᵗ = Wᵗ} {W′ = W′} {Y = Y}
    (target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono targetEq frozenY =
  target-bind-lift-move
    (premiseMoveEq
      {W = W} {Wᵗ = Wᵗ} {W′ = W′}
      (target-store-move refl refl same refl hΣ resolve) targetEq)
    pivot-star′ old-pivot′ pivot-res other′
  where
  pivot-star′ :
    CTI2.impEnvʷ W′ (toRenameᵗ (CTI2.ηᴿʷ W′) Y) ≡ X⊑★
  pivot-star′ =
    subst≡ (λ Z → CTI2.impEnvʷ W′ Z ≡ X⊑★)
      (sym frozenY)
      (mono (toRenameᵗ (CTI2.ηᴿʷ W) Y)
        (trans (sym (same _)) pivot-star))

  old-pivot′ : CTI2.resolveVar (CTI2.targetStoreʷ W′) Y ≡ ＇ Y
  old-pivot′ =
    trans (cong (λ Σ → CTI2.resolveVar Σ Y) targetEq) old-pivot

  other′ : ∀ Z
    → Z ≢ Y
    → CTI2.resolveVar (CTI2.targetStoreʷ Wᵗ) Z
        ≡ CTI2.resolveVar (CTI2.targetStoreʷ W′) Z
  other′ Z Z≢Y =
    trans (other Z Z≢Y)
      (cong (λ Σ → CTI2.resolveVar Σ Z) (sym targetEq))

smartAliasPivotStar : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ} {Y β α}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.SmartAliasMergeGuard W Wᵐ β α
  → CTI2.impEnvʷ Wᵐ (toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Y) ≡ X⊑★
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = Y} {β = β} {α = α}
    mv guard with FinP._≟_ Y β
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = .β} {β = β}
    mv guard | yes refl =
  subst≡
    (λ C → CTI2.impEnvʷ Wᵐ C ≡ X⊑★)
    (sym (CTI2.SmartAliasMergeGuard.target-frozen guard β))
    (CTI2.SmartAliasMergeGuard.alias-mark-dynamic guard)
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = Y} {β = β} {α = α}
    mv guard | no Y≢β with FinP._≟_ Y α
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = .α} {β = β} {α = α}
    mv guard | no Y≢β | yes refl =
  subst≡
    (λ C → CTI2.impEnvʷ Wᵐ C ≡ X⊑★)
    (sym (CTI2.SmartAliasMergeGuard.target-frozen guard α))
    (CTI2.SmartAliasMergeGuard.name-mark-dynamic guard)
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = Y} {β = β} {α = α}
    mv guard | no Y≢β | no Y≢α =
  CTI2.SmartAliasMergeGuard.target-mark-off-footprint guard Y
    Y≢β Y≢α (target-pivot-star-source mv)

smartFreshPivotStar : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.SmartFreshBehindGuard W Wᵐ
  → CTI2.impEnvʷ Wᵐ (toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Y) ≡ X⊑★
smartFreshPivotStar mv guard =
  CTI2.SmartFreshBehindGuard.target-mark-mono guard _
    (target-pivot-star-source mv)

smartAliasTargetBindMove : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ} {Y β α}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → TargetBindLiftMove Wᵐ
      (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ)) Y
smartAliasTargetBindMove {Wᵗ = Wᵗ} {Wᵐ = Wᵐ} {Y = Y} mv guard =
  target-bind-lift-move
    (premiseMoveEqAny (baseMove mv)
      (CTI2.SmartAliasMergeGuard.targetStore-same guard))
    (smartAliasPivotStar mv guard)
    old-pivot′
    (target-resolve-pivot mv)
    other′
  where
  targetEq = CTI2.SmartAliasMergeGuard.targetStore-same guard

  old-pivot′ : CTI2.resolveVar (CTI2.targetStoreʷ Wᵐ) Y ≡ ＇ Y
  old-pivot′ =
    trans (cong (λ Σ → CTI2.resolveVar Σ Y) targetEq)
      (target-resolve-pivot-old mv)

  other′ : ∀ Z
    → Z ≢ Y
    → CTI2.resolveVar
        (CTI2.targetStoreʷ
          (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ))) Z
        ≡ CTI2.resolveVar (CTI2.targetStoreʷ Wᵐ) Z
  other′ Z Z≢Y =
    trans (target-resolve-other mv Z Z≢Y)
      (cong (λ Σ → CTI2.resolveVar Σ Z) (sym targetEq))

smartFreshTargetBindMove : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → TargetBindLiftMove Wᵐ
      (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ)) Y
smartFreshTargetBindMove {Wᵗ = Wᵗ} {Wᵐ = Wᵐ} {Y = Y} mv guard =
  target-bind-lift-move
    (premiseMoveEqAny (baseMove mv)
      (CTI2.SmartFreshBehindGuard.targetStore-same guard))
    (smartFreshPivotStar mv guard)
    old-pivot′
    (target-resolve-pivot mv)
    other′
  where
  targetEq = CTI2.SmartFreshBehindGuard.targetStore-same guard

  old-pivot′ : CTI2.resolveVar (CTI2.targetStoreʷ Wᵐ) Y ≡ ＇ Y
  old-pivot′ =
    trans (cong (λ Σ → CTI2.resolveVar Σ Y) targetEq)
      (target-resolve-pivot-old mv)

  other′ : ∀ Z
    → Z ≢ Y
    → CTI2.resolveVar
        (CTI2.targetStoreʷ
          (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ))) Z
        ≡ CTI2.resolveVar (CTI2.targetStoreʷ Wᵐ) Z
  other′ Z Z≢Y =
    trans (target-resolve-other mv Z Z≢Y)
      (cong (λ Σ → CTI2.resolveVar Σ Z) (sym targetEq))

moveSmartAliasMergeGuard : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ} {Y β α}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.SmartAliasMergeGuard W Wᵐ β α
  → CTI2.SmartAliasMergeGuard Wᵗ
      (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ)) β α
moveSmartAliasMergeGuard
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    guard =
  CTI2.smart-alias-merge-guard
    (hΣ (CTI2.SmartAliasMergeGuard.β:=＇α guard))
    (hΣ (CTI2.SmartAliasMergeGuard.α:=★ guard))
    (CTI2.SmartAliasMergeGuard.sourceStore-lifted guard)
    refl
    (λ p → CTI2.SmartAliasMergeGuard.transport⊑ᵂ guard
      (move⊑ᵂ-back (liftMoveLeft X⊑★ mv) p))
    (λ Z dynamic → CTI2.SmartAliasMergeGuard.old-mark-mono guard Z
      (trans (sym (same Z)) dynamic))
    (CTI2.SmartAliasMergeGuard.target-frozen guard)
    (CTI2.SmartAliasMergeGuard.pending-at-alias guard)
    (CTI2.SmartAliasMergeGuard.old-source-frozen guard)
    (CTI2.SmartAliasMergeGuard.no-old-source-at-alias guard)
    (CTI2.SmartAliasMergeGuard.alias-mark-dynamic guard)
    (CTI2.SmartAliasMergeGuard.name-mark-dynamic guard)
    (λ X X≢β X≢α dynamic →
      CTI2.SmartAliasMergeGuard.target-mark-off-footprint guard
        X X≢β X≢α (trans (sym (same _)) dynamic))

moveSmartFreshBehindGuard : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.SmartFreshBehindGuard W Wᵐ
  → CTI2.SmartFreshBehindGuard Wᵗ
      (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ))
moveSmartFreshBehindGuard
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    guard =
  CTI2.smart-fresh-behind-guard
    (CTI2.SmartFreshBehindGuard.oldCenters guard)
    (CTI2.SmartFreshBehindGuard.sourceStore-lifted guard)
    refl
    (λ p → CTI2.SmartFreshBehindGuard.transport⊑ᵂ guard
      (move⊑ᵂ-back (liftMoveLeft X⊑★ mv) p))
    (λ Z dynamic → CTI2.SmartFreshBehindGuard.old-mark-mono guard Z
      (trans (sym (same Z)) dynamic))
    (CTI2.SmartFreshBehindGuard.target-frozen guard)
    (CTI2.SmartFreshBehindGuard.old-source-frozen guard)
    (CTI2.SmartFreshBehindGuard.fresh-not-target guard)
    (CTI2.SmartFreshBehindGuard.fresh-mark-dynamic guard)
    (λ X dynamic → CTI2.SmartFreshBehindGuard.target-mark-mono guard X
      (trans (sym (same _)) dynamic))

moveSmartCommaLiftᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.SmartCommaLiftᴸ W Wᵐ
  → CTI2.SmartCommaLiftᴸ Wᵗ
      (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ))
moveSmartCommaLiftᴸ mv (CTI2.smart-fresh-behind guard) =
  CTI2.smart-fresh-behind (moveSmartFreshBehindGuard mv guard)
moveSmartCommaLiftᴸ mv (CTI2.smart-merge-alias guard) =
  CTI2.smart-merge-alias (moveSmartAliasMergeGuard mv guard)

moveSmartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CtxImp W} {γᵐ : CtxImp Wᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → (mvᵐ : TargetBindLiftMove Wᵐ
      (targetStoreAs Wᵐ (CTI2.targetStoreʷ Wᵗ)) Y)
  → CTI2.SmartLiftCtxᴸ γ γᵐ
  → CTI2.SmartLiftCtxᴸ (moveCtx (baseMove mv) γ)
      (moveCtx (baseMove mvᵐ) γᵐ)
moveSmartLiftCtxᴸ mv mvᵐ CTI2.smart-lift-[] = CTI2.smart-lift-[]
moveSmartLiftCtxᴸ mv mvᵐ (CTI2.smart-lift-∷ liftγ) =
  CTI2.smart-lift-∷ (moveSmartLiftCtxᴸ mv mvᵐ liftγ)

moveStoreRepBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y Xᴸ Xᴿ}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.StoreRepImp W Xᴸ Xᴿ
  → CTI2.StoreRepImp Wᵗ Xᴸ Xᴿ
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTI2.store-rep-imp represented)
    with FinP._≟_ Xᴿ Y
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = .Y}
    (target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTI2.store-rep-imp represented)
    | yes refl
    with SPT.right-var-obligation-view
      {W = W} {R = CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ}
      {Y = Y}
      (subst≡
        (λ B → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ
          ⊑ᵂ⟨ W ⟩ B)
        old-pivot
        represented)
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = .Y}
    (target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTI2.store-rep-imp represented)
    | yes refl | X₂ , source-eq , aligned =
  CTI2.store-rep-imp
    (subst≡
      (λ R → R ⊑ᵂ⟨ Wᵗ ⟩ CTI2.resolveVar (CTI2.targetStoreʷ Wᵗ) Y)
      (sym source-eq)
      (subst≡
        (λ B → ＇ X₂ ⊑ᵂ⟨ Wᵗ ⟩ B)
        (sym pivot-res)
        (subst≡
          (λ Z → CTI2.impEnvʷ Wᵗ ⊢ (＇ Z) ⊑ ★)
          (sym aligned)
          (X⊑★ pivot-star))))
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTI2.store-rep-imp represented)
    | no Xᴿ≢Y =
  CTI2.store-rep-imp
    (subst≡
      (λ B → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ
        ⊑ᵂ⟨ Wᵗ ⟩ B)
      (sym (other Xᴿ Xᴿ≢Y))
      (move⊑ᵂ mv represented))

moveRebaseAtForwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ Xᴿ}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.ImpEnvMono W W′
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTI2.RebaseAt Wᵗ W′ᵗ Xᴸ Xᴿ
moveRebaseAtForwardBindLift
    {W = W} {Wᵗ = Wᵗ} {W′ = W′} {Y = Y}
    mv@(target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTI2.rebase-at (CTI2.same-runtime sourceEq targetEq)
      off frozen aligned reps) =
  W′ᵗ , mv′ ,
  CTI2.rebase-at (CTI2.same-runtime sourceEq refl)
    off frozen aligned (moveStoreRepBindLift mv′ reps)
  where
  W′ᵗ = targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ)
  mv′ = premiseTargetBindMove mv mono targetEq (frozen Y)

moveRebaseAtBackwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ Xᴿ}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.ImpEnvMono W W′
  → CTI2.RebaseAt W′ W Xᴸ Xᴿ
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTI2.RebaseAt W′ᵗ Wᵗ Xᴸ Xᴿ
moveRebaseAtBackwardBindLift
    {W = W} {Wᵗ = Wᵗ} {W′ = W′} {Y = Y}
    mv@(target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTI2.rebase-at (CTI2.same-runtime sourceEq targetEq)
      off frozen aligned reps) =
  W′ᵗ , mv′ ,
  CTI2.rebase-at (CTI2.same-runtime sourceEq refl)
    off frozen aligned (moveStoreRepBindLift mv reps)
  where
  W′ᵗ = targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ)
  mv′ = premiseTargetBindMove mv mono (sym targetEq) (sym (frozen Y))

moveRebaseAtᴿForwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴿ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.ImpEnvMono W W′
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTI2.RebaseAtᴿ Wᵗ W′ᵗ Xᴿ?
moveRebaseAtᴿForwardBindLift mv mono CTI2.rebase-idᴿ =
  _ , mv , CTI2.rebase-idᴿ
moveRebaseAtᴿForwardBindLift mv mono (CTI2.rebase-varᴿ rb)
    with moveRebaseAtForwardBindLift mv mono rb
moveRebaseAtᴿForwardBindLift mv mono (CTI2.rebase-varᴿ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTI2.rebase-varᴿ rb′

moveRebaseAtᴿBackwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴿ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.ImpEnvMono W W′
  → CTI2.RebaseAtᴿ W′ W Xᴿ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTI2.RebaseAtᴿ W′ᵗ Wᵗ Xᴿ?
moveRebaseAtᴿBackwardBindLift mv mono CTI2.rebase-idᴿ =
  _ , mv , CTI2.rebase-idᴿ
moveRebaseAtᴿBackwardBindLift mv mono (CTI2.rebase-varᴿ rb)
    with moveRebaseAtBackwardBindLift mv mono rb
moveRebaseAtᴿBackwardBindLift mv mono (CTI2.rebase-varᴿ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTI2.rebase-varᴿ rb′

moveRebaseAtᴸForwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.ImpEnvMono W W′
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTI2.RebaseAtᴸ Wᵗ W′ᵗ Xᴸ?
moveRebaseAtᴸForwardBindLift mv mono CTI2.rebase-idᴸ =
  _ , mv , CTI2.rebase-idᴸ
moveRebaseAtᴸForwardBindLift mv mono (CTI2.rebase-varᴸ rb)
    with moveRebaseAtForwardBindLift mv mono rb
moveRebaseAtᴸForwardBindLift mv mono (CTI2.rebase-varᴸ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTI2.rebase-varᴸ rb′
moveRebaseAtᴸForwardBindLift
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTI2.rebase-onlyᴸ to-star disaligned represented) =
  _ ,
  target-bind-lift-move
    mv
    pivot-star old-pivot pivot-res other ,
  CTI2.rebase-onlyᴸ (trans (same _) to-star) disaligned
    (move⊑ᵂ mv represented)

moveTagRebaseAtᴸBackwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ? Xᴿ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTI2.ImpEnvMono W W′
  → CTI2.TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTI2.TagRebaseAtᴸ W′ᵗ Wᵗ Xᴸ? Xᴿ?
moveTagRebaseAtᴸBackwardBindLift mv mono CTI2.tag-rebase-idᴸ =
  _ , mv , CTI2.tag-rebase-idᴸ
moveTagRebaseAtᴸBackwardBindLift mv mono (CTI2.tag-rebase-varᴸ rb)
    with moveRebaseAtBackwardBindLift mv mono rb
moveTagRebaseAtᴸBackwardBindLift mv mono (CTI2.tag-rebase-varᴸ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTI2.tag-rebase-varᴸ rb′
moveTagRebaseAtᴸBackwardBindLift
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
  _ ,
  target-bind-lift-move
    mv
    pivot-star old-pivot pivot-res other ,
  CTI2.tag-rebase-onlyᴸ (trans (same _) to-star) disaligned
    (move⊑ᵂ mv represented)

moveStoreRepWithTarget∈ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ R}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.targetStoreʷ W ∋ Xᴿ ⦂ R
  → CTI2.StoreRepImp W Xᴸ Xᴿ
  → CTI2.StoreRepImp Wᵗ Xᴸ Xᴿ
moveStoreRepWithTarget∈
    {W = W}
    {Wᵗ = Wᵗ}
    {Xᴸ = Xᴸ}
    mv@(target-store-move refl refl same refl hΣ resolve)
    X∈
    (CTI2.store-rep-imp represented) =
  CTI2.store-rep-imp
    (subst≡
      (λ B → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ
        ⊑ᵂ⟨ Wᵗ ⟩ B)
      (sym (resolve X∈))
      (move⊑ᵂ mv represented))

moveRebaseAtForwardWithTarget∈ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ R}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.targetStoreʷ W ∋ Xᴿ ⦂ R
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetStoreMove W′ W′ᵗ ]
      CTI2.RebaseAt Wᵗ W′ᵗ Xᴸ Xᴿ
moveRebaseAtForwardWithTarget∈
    {Wᵗ = Wᵗ}
    {W′ = W′}
    {Xᴿ = Xᴿ}
    {R = R}
    mv@(target-store-move refl refl same refl hΣ resolve)
    (CTI2.rebase-at (CTI2.same-runtime sourceEq targetEq)
      off frozen aligned reps)
    X∈ =
  W′ᵗ , mv′ ,
  CTI2.rebase-at (CTI2.same-runtime sourceEq refl)
    off frozen aligned
    (moveStoreRepWithTarget∈ mv′ X∈′ reps)
  where
  W′ᵗ = targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ)
  mv′ = premiseMoveEq mv targetEq
  X∈′ = subst≡ (λ Σ → Σ ∋ Xᴿ ⦂ R) (sym targetEq) X∈

moveRebaseAtBackwardWithTarget∈ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ R}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.RebaseAt W′ W Xᴸ Xᴿ
  → CTI2.targetStoreʷ W ∋ Xᴿ ⦂ R
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetStoreMove W′ W′ᵗ ]
      CTI2.RebaseAt W′ᵗ Wᵗ Xᴸ Xᴿ
moveRebaseAtBackwardWithTarget∈
    {Wᵗ = Wᵗ}
    {W′ = W′}
    mv@(target-store-move refl refl same refl hΣ resolve)
    (CTI2.rebase-at (CTI2.same-runtime sourceEq targetEq)
      off frozen aligned reps)
    X∈ =
  W′ᵗ , mv′ ,
  CTI2.rebase-at (CTI2.same-runtime sourceEq refl)
    off frozen aligned
    (moveStoreRepWithTarget∈ mv X∈ reps)
  where
  W′ᵗ = targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ)
  mv′ = premiseMoveEq mv (sym targetEq)

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r) (PI.⊑-unique p q) d

source-reveal-move : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {X? A B}
    {c : Conv↑ Δᴸ A B}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.sourceStoreʷ W CTI2.⊢↑[ X? ] c
  → CTI2.sourceStoreʷ Wᵗ CTI2.⊢↑[ X? ] c
source-reveal-move
    (target-store-move refl refl same refl hΣ resolve) c⊢ = c⊢

source-conceal-move : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {X? A B}
    {c : Conv↓ Δᴸ A B}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ X? ] c
  → CTI2.sourceStoreʷ Wᵗ CTI2.⊢↓[ X? ] c
source-conceal-move
    (target-store-move refl refl same refl hΣ resolve) c⊢ = c⊢

⊢²-target-bind-lift-move : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
    {γ : CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Wᵗ ∣ moveCtx (baseMove mv) γ ⊢² M ⊑ M′ ∶
      move⊑ᵂ (baseMove mv) p
⊢²-target-bind-lift-move mv (CTI2.x⊑x² x∈) =
  CTI2.x⊑x² (move∋ʷ (baseMove mv) x∈)
⊢²-target-bind-lift-move mv (CTI2.ƛ⊑ƛ² M⊑M′) =
  ⊢²-retarget (CTI2.ƛ⊑ƛ² (⊢²-target-bind-lift-move mv M⊑M′))
⊢²-target-bind-lift-move {p = p} mv
    (CTI2.·⊑·² {pA = pA} {pB = pB} L⊑L′ M⊑M′) =
  ⊢²-retarget {q = move⊑ᵂ (baseMove mv) p}
    (CTI2.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒ (move⊑ᵂ (baseMove mv) pA)
          (move⊑ᵂ (baseMove mv) pB)}
        (⊢²-target-bind-lift-move mv L⊑L′))
      (⊢²-target-bind-lift-move mv M⊑M′))
⊢²-target-bind-lift-move mv
    (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
  CTI2.Λ⊑Λ² (moveLiftCtx (baseMove mv) liftγ) vV vV′
    (⊢²-target-bind-lift-move
      (liftTargetBindMoveBoth X⊑X mv) V⊑V′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑² Anv zero∈A (moveLiftCtxᴸ (baseMove mv) liftγ) vV
    (target-typing-move (baseMove mv) M′⊢)
    (⊢²-target-bind-lift-move
      (liftTargetBindMoveLeft X⊑★ mv) V⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.Λ⊑²-smart-comma
      Anv zero∈A (CTI2.smart-merge-alias guard) liftγ vV M′⊢
      V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTI2.smart-merge-alias (moveSmartAliasMergeGuard mv guard))
    (moveSmartLiftCtxᴸ mv mvᵐ liftγ) vV
    (target-typing-move (baseMove mv) M′⊢)
    (⊢²-target-bind-lift-move mvᵐ V⊑M′)
    (move⊑ᵂ (baseMove mv) q)
  where
  mvᵐ = smartAliasTargetBindMove mv guard
⊢²-target-bind-lift-move mv
    (CTI2.Λ⊑²-smart-comma
      Anv zero∈A (CTI2.smart-fresh-behind guard) liftγ vV M′⊢
      V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTI2.smart-fresh-behind (moveSmartFreshBehindGuard mv guard))
    (moveSmartLiftCtxᴸ mv mvᵐ liftγ) vV
    (target-typing-move (baseMove mv) M′⊢)
    (⊢²-target-bind-lift-move mvᵐ V⊑M′)
    (move⊑ᵂ (baseMove mv) q)
  where
  mvᵐ = smartFreshTargetBindMove mv guard
⊢²-target-bind-lift-move mv (CTI2.•⊑•² p∀ M⊑M′ q r) =
  CTI2.•⊑•² (move⊑ᵂ (baseMove mv) p∀)
    (⊢²-target-bind-lift-move mv M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
    (move⊑ᵂ (baseMove mv) r)
⊢²-target-bind-lift-move mv (CTI2.•⊑² p∀ M⊑M′ q r) =
  CTI2.•⊑² (move⊑ᵂ (baseMove mv) p∀)
    (⊢²-target-bind-lift-move mv M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
    (move⊑ᵂ (baseMove mv) r)
⊢²-target-bind-lift-move mv (CTI2.κ⊑κ² κ p) =
  CTI2.κ⊑κ² κ (move⊑ᵂ (baseMove mv) p)
⊢²-target-bind-lift-move mv
    (CTI2.cast⊑cast² c c′ M⊑M′ q) =
  CTI2.cast⊑cast² c c′
    (⊢²-target-bind-lift-move mv M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv (CTI2.⊑cast² c′ M⊑M′ q) =
  CTI2.⊑cast² c′ (⊢²-target-bind-lift-move mv M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv (CTI2.cast⊑² c M⊑M′ q) =
  CTI2.cast⊑² c (⊢²-target-bind-lift-move mv M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.⊑reveal² {W′ = W′} {p = p} mono rb sc c′⊢
      M⊑M′ q)
    with moveRebaseAtᴿForwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.⊑reveal² {W′ = W′} {p = p} mono rb sc c′⊢
      M⊑M′ q)
    | W′ᵗ , mv′ , rb′ =
  CTI2.⊑reveal²
    (moveImpEnvMono (baseMove mv) (baseMove mv′) mono)
    rb′
    (moveSameCtx (baseMove mv) (baseMove mv′) sc)
    (revealˣ-store-transport (targetStore-transport (baseMove mv)) c′⊢)
    (⊢²-target-bind-lift-move mv′ M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.⊑conceal² {W′ = W′} {p = p} mono rb sc c′⊢
      M⊑M′ q)
    with moveRebaseAtᴿBackwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.⊑conceal² {W′ = W′} {p = p} mono rb sc c′⊢
      M⊑M′ q)
    | W′ᵗ , mv′ , rb′ =
  CTI2.⊑conceal²
    (moveImpEnvMono (baseMove mv) (baseMove mv′) mono)
    rb′
    (moveSameCtx (baseMove mv) (baseMove mv′) sc)
    (concealˣ-store-transport (targetStore-transport (baseMove mv)) c′⊢)
    (⊢²-target-bind-lift-move mv′ M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.reveal⊑² {W′ = W′} {p = p} mono rb sc c⊢
      M⊑M′ q)
    with moveRebaseAtᴸForwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.reveal⊑² {W′ = W′} {p = p} mono rb sc c⊢
      M⊑M′ q)
    | W′ᵗ , mv′ , rb′ =
  CTI2.reveal⊑²
    (moveImpEnvMono (baseMove mv) (baseMove mv′) mono)
    rb′
    (moveSameCtx (baseMove mv) (baseMove mv′) sc)
    (source-reveal-move (baseMove mv) c⊢)
    (⊢²-target-bind-lift-move mv′ M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.conceal⊑²-seal-star-open {W′ = W′} {p = p}
      no-target mono rb sc c⊢ M⊑M′ q)
    with moveTagRebaseAtᴸBackwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.conceal⊑²-seal-star-open {W′ = W′} {p = p}
      no-target mono rb sc c⊢ M⊑M′ q)
    | W′ᵗ , mv′ , rb′ =
  CTI2.conceal⊑²-seal-star-open
    (moveNoTargetOccupantAtSource (baseMove mv′) no-target)
    (moveImpEnvMono (baseMove mv) (baseMove mv′) mono)
    rb′
    (moveSameCtx (baseMove mv) (baseMove mv′) sc)
    (source-conceal-move (baseMove mv) c⊢)
    (⊢²-target-bind-lift-move mv′ M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.conceal⊑²-source-ok {W′ = W′} {p = p}
      ok mono rb sc c⊢ M⊑M′ q)
    with moveTagRebaseAtᴸBackwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.conceal⊑²-source-ok {W′ = W′} {p = p}
      ok mono rb sc c⊢ M⊑M′ q)
    | W′ᵗ , mv′ , rb′ =
  CTI2.conceal⊑²-source-ok
    (moveSourceConcealOK (baseMove mv′) ok)
    (moveImpEnvMono (baseMove mv) (baseMove mv′) mono)
    rb′
    (moveSameCtx (baseMove mv) (baseMove mv′) sc)
    (source-conceal-move (baseMove mv) c⊢)
    (⊢²-target-bind-lift-move mv′ M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p} mono rb sc
      c⊢ c′⊢ M⊑M′ q)
    with moveRebaseAtForwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p} mono rb sc
      c⊢ c′⊢ M⊑M′ q)
    | Wᵖᵗ , mvᵖ , rbᵖ =
  CTI2.reveal⊑reveal²
    (moveImpEnvMono (baseMove mv) (baseMove mvᵖ) mono)
    rbᵖ
    (moveSameCtx (baseMove mv) (baseMove mvᵖ) sc)
    (source-reveal-move (baseMove mv) c⊢)
    (revealˣ-store-transport (targetStore-transport (baseMove mv)) c′⊢)
    (⊢²-target-bind-lift-move mvᵖ M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p} ok mono rb
      sc c⊢ c′⊢ M⊑M′ q)
    with moveRebaseAtBackwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p} ok mono rb
      sc c⊢ c′⊢ M⊑M′ q)
    | Wᵖᵗ , mvᵖ , rbᵖ =
  CTI2.conceal⊑conceal²
    (moveMatchedConcealPartnerOK (baseMove mvᵖ) ok)
    (moveImpEnvMono (baseMove mv) (baseMove mvᵖ) mono)
    rbᵖ
    (moveSameCtx (baseMove mv) (baseMove mvᵖ) sc)
    (source-conceal-move (baseMove mv) c⊢)
    (concealˣ-store-transport (targetStore-transport (baseMove mv)) c′⊢)
    (⊢²-target-bind-lift-move mvᵖ M⊑M′)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ} {p★ = p★}
      {qᵖ = qᵖ} ok mono rb sc c⊢ c′⊢ M⊑M′ sourcePrem q)
    with moveRebaseAtBackwardBindLift mv mono rb
⊢²-target-bind-lift-move mv
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ} {p★ = p★}
      {qᵖ = qᵖ} ok mono rb sc c⊢ c′⊢ M⊑M′ sourcePrem q)
    | Wᵖᵗ , mvᵖ , rbᵖ =
  CTI2.packaged-seal-star²
    (moveMatchedConcealPartnerOK (baseMove mvᵖ) ok)
    (moveImpEnvMono (baseMove mv) (baseMove mvᵖ) mono)
    rbᵖ
    (moveSameCtx (baseMove mv) (baseMove mvᵖ) sc)
    (source-conceal-move (baseMove mv) c⊢)
    (concealˣ-store-transport (targetStore-transport (baseMove mv)) c′⊢)
    (⊢²-target-bind-lift-move mvᵖ M⊑M′)
    (⊢²-target-bind-lift-move mvᵖ sourcePrem)
    (move⊑ᵂ (baseMove mv) q)
⊢²-target-bind-lift-move mv (CTI2.blame⊑² M′⊢ p) =
  CTI2.blame⊑² (target-typing-move (baseMove mv) M′⊢)
    (move⊑ᵂ (baseMove mv) p)
⊢²-target-bind-lift-move mv (CTI2.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
  CTI2.⊕⊑⊕² op
    (⊢²-target-bind-lift-move mv L⊑L′)
    (⊢²-target-bind-lift-move mv M⊑M′)
    (move⊑ᵂ (baseMove mv) r)

freshLiftToBindMove : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {v : VarImp}
  → TargetStoreMove
      (CR.renameWorld wk↪ᵗ
        (CTI2.liftWorldBoth v (CTI2.rightOnlyWorld W ★)))
      (ΛLiftToBindFreshWorld v W)
freshLiftToBindMove {W = W} {v = v} =
  target-store-move
    (cong skip
      (sym (∘↪-idˡ (keep (skip (CTI2.ηᴸʷ W))))))
    (cong skip
      (sym (∘↪-idˡ (keep (keep (CTI2.ηᴿʷ W))))))
    same
    refl
    StoreTransport-lift-bind
    resolve
  where
  same : ∀ X
    → extendᵐ X⊑★ (extendᵐ v (instᵐ (CTI2.impEnvʷ W))) X
      ≡ extendᵐ X⊑★
          (CR.renameEnv id↪ᵗ
            (extendᵐ v (instᵐ (CTI2.impEnvʷ W)))) X
  same Fin.zero = refl
  same (Fin.suc X) =
    sym (renameEnv-id (extendᵐ v (instᵐ (CTI2.impEnvʷ W))) X)

  resolve : ∀ {Δ} {Σ : TyStore (suc Δ)} {X R}
    → store-lift Σ ∋ X ⦂ R
    → CTI2.resolveVar (store-bind Σ (＇ Fin.zero)) X
        ≡ CTI2.resolveVar (store-lift Σ) X
  resolve (S-lift∋ X∈ eq) = refl

freshLiftToBindTargetMove★ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → TargetBindLiftMove
      (CR.renameWorld wk↪ᵗ
        (CTI2.liftWorldBoth X⊑★ (CTI2.rightOnlyWorld W ★)))
      (ΛLiftToBindFreshWorld X⊑★ W)
      Fin.zero
freshLiftToBindTargetMove★ {W = W} =
  target-bind-lift-move
    (freshLiftToBindMove {W = W} {v = X⊑★})
    refl
    refl
    refl
    other
  where
  other : ∀ Z
    → Z ≢ Fin.zero
    → CTI2.resolveVar
        (CTI2.targetStoreʷ (ΛLiftToBindFreshWorld X⊑★ W)) Z
        ≡ CTI2.resolveVar
            (CTI2.targetStoreʷ
              (CR.renameWorld wk↪ᵗ
                (CTI2.liftWorldBoth X⊑★
                  (CTI2.rightOnlyWorld W ★)))) Z
  other Fin.zero neq = ⊥-elim (neq refl)
  other (Fin.suc Z) neq = refl


freshLiftToBindTargetMoveAt : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ (suc Δᴿ) Δ}
    {Σ₂ : TyStore (suc (suc Δᴿ))}
  → StoreTransport (store-lift (CTI2.targetStoreʷ W)) Σ₂
  → CTI2.resolveVar Σ₂ Fin.zero ≡ ★
  → (∀ Z → Z ≢ Fin.zero
      → CTI2.resolveVar Σ₂ Z
          ≡ CTI2.resolveVar (store-lift (CTI2.targetStoreʷ W)) Z)
  → TargetBindLiftMove
      (CR.renameWorld wk↪ᵗ (CTI2.liftWorldBoth X⊑★ W))
      (targetStoreAs
        (CR.renameWorld wk↪ᵗ (CTI2.liftWorldBoth X⊑★ W)) Σ₂)
      Fin.zero
freshLiftToBindTargetMoveAt {W = W} {Σ₂ = Σ₂} hΣ pivot other =
  target-bind-lift-move
    (target-store-move refl refl (λ X → refl) refl hΣ resolve)
    refl refl pivot other
  where
  resolve : ∀ {X R}
    → store-lift (CTI2.targetStoreʷ W) ∋ X ⦂ R
    → CTI2.resolveVar Σ₂ X
        ≡ CTI2.resolveVar (store-lift (CTI2.targetStoreʷ W)) X
  resolve (S-lift∋ {X = X} X∈ eq) = other (Fin.suc X) (λ ())


freshLiftToBindTargetMoveAtκ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ (suc Δᴿ) Δ}
    (κ : suc Δ ↪ᵗ Δ′)
    {Σ₂ : TyStore (suc (suc Δᴿ))}
  → CTI2.impEnvʷ (CR.renameWorld κ (CTI2.liftWorldBoth X⊑★ W))
      (toRenameᵗ
        (CTI2.ηᴿʷ (CR.renameWorld κ (CTI2.liftWorldBoth X⊑★ W)))
        Fin.zero)
      ≡ X⊑★
  → StoreTransport (store-lift (CTI2.targetStoreʷ W)) Σ₂
  → CTI2.resolveVar Σ₂ Fin.zero ≡ ★
  → (∀ Z → Z ≢ Fin.zero
      → CTI2.resolveVar Σ₂ Z
          ≡ CTI2.resolveVar (store-lift (CTI2.targetStoreʷ W)) Z)
  → TargetBindLiftMove
      (CR.renameWorld κ (CTI2.liftWorldBoth X⊑★ W))
      (targetStoreAs (CR.renameWorld κ (CTI2.liftWorldBoth X⊑★ W)) Σ₂)
      Fin.zero
freshLiftToBindTargetMoveAtκ {W = W} κ {Σ₂ = Σ₂}
    pivot-star hΣ pivot other =
  target-bind-lift-move
    (target-store-move refl refl (λ X → refl) refl hΣ resolve)
    pivot-star refl pivot other
  where
  resolve : ∀ {X R}
    → store-lift (CTI2.targetStoreʷ W) ∋ X ⦂ R
    → CTI2.resolveVar Σ₂ X
        ≡ CTI2.resolveVar (store-lift (CTI2.targetStoreʷ W)) X
  resolve (S-lift∋ {X = X} X∈ eq) = other (Fin.suc X) (λ ())


freshLiftToBindTargetMoveAtκᴸ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ (suc Δᴿ) Δ}
    (κ : suc (suc Δ) ↪ᵗ Δ′)
    {Σ₂ : TyStore (suc (suc Δᴿ))}
  → CTI2.impEnvʷ
      (CR.renameWorld κ
        (CTI2.liftWorldBoth X⊑★
          (CTI2.liftWorldLeft X⊑★ W)))
      (toRenameᵗ
        (CTI2.ηᴿʷ
          (CR.renameWorld κ
            (CTI2.liftWorldBoth X⊑★
              (CTI2.liftWorldLeft X⊑★ W))))
        Fin.zero)
      ≡ X⊑★
  → StoreTransport (store-lift (CTI2.targetStoreʷ W)) Σ₂
  → CTI2.resolveVar Σ₂ Fin.zero ≡ ★
  → (∀ Z → Z ≢ Fin.zero
      → CTI2.resolveVar Σ₂ Z
          ≡ CTI2.resolveVar (store-lift (CTI2.targetStoreʷ W)) Z)
  → TargetBindLiftMove
      (CR.renameWorld κ
        (CTI2.liftWorldBoth X⊑★
          (CTI2.liftWorldLeft X⊑★ W)))
      (targetStoreAs
        (CR.renameWorld κ
          (CTI2.liftWorldBoth X⊑★
            (CTI2.liftWorldLeft X⊑★ W)))
        Σ₂)
      Fin.zero
freshLiftToBindTargetMoveAtκᴸ {W = W} κ {Σ₂ = Σ₂}
    pivot-star hΣ pivot other =
  target-bind-lift-move
    (target-store-move refl refl (λ X → refl) refl hΣ resolve)
    pivot-star refl pivot other
  where
  resolve : ∀ {X R}
    → store-lift (CTI2.targetStoreʷ W) ∋ X ⦂ R
    → CTI2.resolveVar Σ₂ X
        ≡ CTI2.resolveVar (store-lift (CTI2.targetStoreʷ W)) X
  resolve (S-lift∋ {X = X} X∈ eq) = other (Fin.suc X) (λ ())

freshLiftToBindMoveᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {v : VarImp}
  → TargetStoreMove
      (CR.renameWorld wk↪ᵗ
        (CTI2.liftWorldBoth v
          (CTI2.liftWorldLeft X⊑★ (CTI2.rightOnlyWorld W ★))))
      (ΛLiftToBindFreshWorldᴸ v W)
freshLiftToBindMoveᴸ {W = W} {v = v} =
  target-store-move
    (cong skip
      (sym (∘↪-idˡ (keep (keep (skip (CTI2.ηᴸʷ W)))))))
    (cong skip
      (sym (∘↪-idˡ (keep (skip (keep (CTI2.ηᴿʷ W)))))))
    same
    refl
    StoreTransport-lift-bind
    resolve
  where
  same : ∀ X
    → extendᵐ X⊑★
        (extendᵐ v (extendᵐ X⊑★
          (instᵐ (CTI2.impEnvʷ W)))) X
      ≡ extendᵐ X⊑★
          (CR.renameEnv id↪ᵗ
            (extendᵐ v (extendᵐ X⊑★
              (instᵐ (CTI2.impEnvʷ W))))) X
  same Fin.zero = refl
  same (Fin.suc X) =
    sym (renameEnv-id
      (extendᵐ v (extendᵐ X⊑★ (instᵐ (CTI2.impEnvʷ W)))) X)

  resolve : ∀ {Δ} {Σ : TyStore (suc Δ)} {X R}
    → store-lift Σ ∋ X ⦂ R
    → CTI2.resolveVar (store-bind Σ (＇ Fin.zero)) X
        ≡ CTI2.resolveVar (store-lift Σ) X
  resolve (S-lift∋ X∈ eq) = refl

freshLiftToBindTargetMove★ᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → TargetBindLiftMove
      (CR.renameWorld wk↪ᵗ
        (CTI2.liftWorldBoth X⊑★
          (CTI2.liftWorldLeft X⊑★ (CTI2.rightOnlyWorld W ★))))
      (ΛLiftToBindFreshWorldᴸ X⊑★ W)
      Fin.zero
freshLiftToBindTargetMove★ᴸ {W = W} =
  target-bind-lift-move
    (freshLiftToBindMoveᴸ {W = W} {v = X⊑★})
    refl
    refl
    refl
    other
  where
  other : ∀ Z
    → Z ≢ Fin.zero
    → CTI2.resolveVar
        (CTI2.targetStoreʷ (ΛLiftToBindFreshWorldᴸ X⊑★ W)) Z
        ≡ CTI2.resolveVar
            (CTI2.targetStoreʷ
              (CR.renameWorld wk↪ᵗ
                (CTI2.liftWorldBoth X⊑★
                  (CTI2.liftWorldLeft X⊑★
                    (CTI2.rightOnlyWorld W ★))))) Z
  other Fin.zero neq = ⊥-elim (neq refl)
  other (Fin.suc Z) neq = refl

ΛLiftToBindFreshTransport : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp (CTI2.liftWorldBoth X⊑★ (CTI2.rightOnlyWorld W ★))}
    {M : Term (suc Δᴸ)} {M′ : Term (suc (suc Δᴿ))}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
    {p : A ⊑ᵂ⟨ CTI2.liftWorldBoth X⊑★
      (CTI2.rightOnlyWorld W ★) ⟩ B}
  → CTI2.liftWorldBoth X⊑★ (CTI2.rightOnlyWorld W ★)
      ∣ γ ⊢² M ⊑ M′ ∶ p
  → Σ[ γᵇ ∈ CtxImp (ΛLiftToBindFreshWorld X⊑★ W) ]
    Σ[ pᵇ ∈ A ⊑ᵂ⟨ ΛLiftToBindFreshWorld X⊑★ W ⟩ B ]
      ΛLiftToBindFreshWorld X⊑★ W ∣ γᵇ ⊢² M ⊑ M′ ∶ pᵇ
ΛLiftToBindFreshTransport {W = W} {γ = γ} {p = p} rel =
  moveCtx (baseMove mv) (CR.renameCtx wk↪ᵗ γ) ,
  pᵇ ,
  ⊢²-target-bind-lift-move mv relʳ
  where
  Wʳ = CR.renameWorld wk↪ᵗ
    (CTI2.liftWorldBoth X⊑★ (CTI2.rightOnlyWorld W ★))

  pʳ : _ ⊑ᵂ⟨ Wʳ ⟩ _
  pʳ =
    CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth X⊑★ (CTI2.rightOnlyWorld W ★)}
      wk↪ᵗ p

  relʳ : Wʳ ∣ CR.renameCtx wk↪ᵗ γ ⊢² _ ⊑ _ ∶ pʳ
  relʳ = CR.⊢²-extend-center rel pʳ

  mv = freshLiftToBindTargetMove★ {W = W}

  pᵇ : _ ⊑ᵂ⟨ ΛLiftToBindFreshWorld X⊑★ W ⟩ _
  pᵇ = move⊑ᵂ (baseMove mv) pʳ
