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
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CenterRename as CR
import proof.DGG.SealPeelToolkit as SPT
open import proof.TypeInTermSubst using
  (StoreTransport; StoreTransport-lift; StoreTransport-lift-bind;
   typing-store-transport)
open import proof.ImprecisionConsistency using
  (imp-env-weaken; toRenameᵗ-injective)

open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

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
  CTX.world
    (skip (keep (skip (CTX.ηᴸʷ W))))
    (skip (keep (keep (CTX.ηᴿʷ W))))
    (instᵐ (extendᵐ v (instᵐ (CTX.impEnvʷ W))))
    (store-lift (CTX.sourceStoreʷ W))
    (store-bind (store-bind (CTX.targetStoreʷ W) ★) (＇ Fin.zero))


ΛLiftToBindFreshWorldᴸ : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (suc (suc Δᴸ)) (suc (suc Δᴿ))
      (suc (suc (suc (suc Δ))))
ΛLiftToBindFreshWorldᴸ v W =
  CTX.world
    (skip (keep (keep (skip (CTX.ηᴸʷ W)))))
    (skip (keep (skip (keep (CTX.ηᴿʷ W)))))
    (instᵐ (extendᵐ v (extendᵐ X⊑★
      (instᵐ (CTX.impEnvʷ W)))))
    (store-lift (store-lift (CTX.sourceStoreʷ W)))
    (store-bind (store-bind (CTX.targetStoreʷ W) ★) (＇ Fin.zero))

------------------------------------------------------------------------
-- Indexed conversion typing under store transport
------------------------------------------------------------------------

mutual
  revealˣ-store-transport : ∀ {Δ} {Σ Σ′ : TyStore Δ} {X? A B}
      {c : Conv↑ Δ A B}
    → StoreTransport Σ Σ′
    → Σ Conv.⊢↑[ X? ] c
    → Σ′ Conv.⊢↑[ X? ] c
  revealˣ-store-transport hΣ (Conv.⊢↑-unsealˣ X∈) =
    Conv.⊢↑-unsealˣ (hΣ X∈)
  revealˣ-store-transport hΣ (Conv.⊢↑-⇒ˣ join c⊢ d⊢) =
    Conv.⊢↑-⇒ˣ join (concealˣ-store-transport hΣ c⊢)
      (revealˣ-store-transport hΣ d⊢)
  revealˣ-store-transport hΣ (Conv.⊢↑-∀ˣ c⊢) =
    Conv.⊢↑-∀ˣ
      (revealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  revealˣ-store-transport hΣ (Conv.⊢↑-∀-idˣ c⊢) =
    Conv.⊢↑-∀-idˣ
      (revealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  revealˣ-store-transport hΣ Conv.⊢↑-idˣ = Conv.⊢↑-idˣ

  concealˣ-store-transport : ∀ {Δ} {Σ Σ′ : TyStore Δ} {X? A B}
      {c : Conv↓ Δ A B}
    → StoreTransport Σ Σ′
    → Σ Conv.⊢↓[ X? ] c
    → Σ′ Conv.⊢↓[ X? ] c
  concealˣ-store-transport hΣ (Conv.⊢↓-sealˣ X∈) =
    Conv.⊢↓-sealˣ (hΣ X∈)
  concealˣ-store-transport hΣ (Conv.⊢↓-⇒ˣ join c⊢ d⊢) =
    Conv.⊢↓-⇒ˣ join (revealˣ-store-transport hΣ c⊢)
      (concealˣ-store-transport hΣ d⊢)
  concealˣ-store-transport hΣ (Conv.⊢↓-∀ˣ c⊢) =
    Conv.⊢↓-∀ˣ
      (concealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  concealˣ-store-transport hΣ (Conv.⊢↓-∀-idˣ c⊢) =
    Conv.⊢↓-∀-idˣ
      (concealˣ-store-transport (StoreTransport-lift hΣ) c⊢)
  concealˣ-store-transport hΣ Conv.⊢↓-idˣ = Conv.⊢↓-idˣ

mutual
  revealˣ-pivot-store : ∀ {Δ} {Σ : TyStore Δ} {X A B}
      {c : Conv↑ Δ A B}
    → Σ Conv.⊢↑[ just X ] c
    → Σ[ R ∈ Ty Δ ] Σ ∋ X ⦂ R
  revealˣ-pivot-store (Conv.⊢↑-unsealˣ {R = R} X∈) = R , X∈
  revealˣ-pivot-store (Conv.⊢↑-⇒ˣ Conv.join-left c⊢ d⊢) =
    concealˣ-pivot-store c⊢
  revealˣ-pivot-store (Conv.⊢↑-⇒ˣ Conv.join-right c⊢ d⊢) =
    revealˣ-pivot-store d⊢
  revealˣ-pivot-store (Conv.⊢↑-⇒ˣ Conv.join-both c⊢ d⊢) =
    concealˣ-pivot-store c⊢
  revealˣ-pivot-store (Conv.⊢↑-∀ˣ c⊢)
      with revealˣ-pivot-store c⊢
  revealˣ-pivot-store (Conv.⊢↑-∀ˣ c⊢)
      | R , S-lift∋ {A = A} X∈ eq = A , X∈

  concealˣ-pivot-store : ∀ {Δ} {Σ : TyStore Δ} {X A B}
      {c : Conv↓ Δ A B}
    → Σ Conv.⊢↓[ just X ] c
    → Σ[ R ∈ Ty Δ ] Σ ∋ X ⦂ R
  concealˣ-pivot-store (Conv.⊢↓-sealˣ {R = R} X∈) = R , X∈
  concealˣ-pivot-store (Conv.⊢↓-⇒ˣ Conv.join-left c⊢ d⊢) =
    revealˣ-pivot-store c⊢
  concealˣ-pivot-store (Conv.⊢↓-⇒ˣ Conv.join-right c⊢ d⊢) =
    concealˣ-pivot-store d⊢
  concealˣ-pivot-store (Conv.⊢↓-⇒ˣ Conv.join-both c⊢ d⊢) =
    revealˣ-pivot-store c⊢
  concealˣ-pivot-store (Conv.⊢↓-∀ˣ c⊢)
      with concealˣ-pivot-store c⊢
  concealˣ-pivot-store (Conv.⊢↓-∀ˣ c⊢)
      | R , S-lift∋ {A = A} X∈ eq = A , X∈

------------------------------------------------------------------------
-- Target-store-only world movement
------------------------------------------------------------------------

record TargetStoreMove {Δᴸ Δᴿ Δ}
    (W Wᵗ : World Δᴸ Δᴿ Δ) : Set where
  constructor target-store-move
  field
    ηᴸ-same : CTX.ηᴸʷ Wᵗ ≡ CTX.ηᴸʷ W
    ηᴿ-same : CTX.ηᴿʷ Wᵗ ≡ CTX.ηᴿʷ W
    impEnv-same : ∀ X → CTX.impEnvʷ Wᵗ X ≡ CTX.impEnvʷ W X
    sourceStore-same : CTX.sourceStoreʷ Wᵗ ≡ CTX.sourceStoreʷ W
    targetStore-transport :
      StoreTransport (CTX.targetStoreʷ W) (CTX.targetStoreʷ Wᵗ)
    targetResolve-same : ∀ {X R}
      → CTX.targetStoreʷ W ∋ X ⦂ R
      → CTX.resolveVar (CTX.targetStoreʷ Wᵗ) X
          ≡ CTX.resolveVar (CTX.targetStoreʷ W) X

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
moveCtx {W = W} mv (CTX.ctx-imp A B p ∷ γ) =
  CTX.ctx-imp A B (move⊑ᵂ mv p) ∷ moveCtx mv γ

move∋ʷ : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (mv : TargetStoreMove W Wᵗ)
  → γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B p
  → moveCtx mv γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B (move⊑ᵂ mv p)
move∋ʷ mv CTX.Zʷ = CTX.Zʷ
move∋ʷ mv (CTX.Sʷ x∈) = CTX.Sʷ (move∋ʷ mv x∈)

moveSameCtx : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W₁ W₁ᵗ : World Δᴸ Δᴿ Δ}
    {W₂ W₂ᵗ : World Δᴸ Δᴿ Δ′}
    {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂}
  → (mv₁ : TargetStoreMove W₁ W₁ᵗ)
  → (mv₂ : TargetStoreMove W₂ W₂ᵗ)
  → CTX.SameCtx γ₁ γ₂
  → CTX.SameCtx (moveCtx mv₁ γ₁) (moveCtx mv₂ γ₂)
moveSameCtx mv₁ mv₂ CTX.same-[] = CTX.same-[]
moveSameCtx mv₁ mv₂ (CTX.same-∷ sc) =
  CTX.same-∷ (moveSameCtx mv₁ mv₂ sc)

moveImpEnvMono : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₁ᵗ W₂ W₂ᵗ : World Δᴸ Δᴿ Δ}
  → TargetStoreMove W₁ W₁ᵗ
  → TargetStoreMove W₂ W₂ᵗ
  → CTX.ImpEnvMono W₁ W₂
  → CTX.ImpEnvMono W₁ᵗ W₂ᵗ
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
    → CTX.Rep★PartnerOK W X P Xᴿ? M′
    → CTX.Rep★PartnerOK Wᵗ X P Xᴿ? M′
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTX.rep★-untagged nt) =
    CTX.rep★-untagged nt
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTX.rep★-nonvar-tag Gnv) =
    CTX.rep★-nonvar-tag Gnv
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTX.rep★-var-tag aligned) =
    CTX.rep★-var-tag aligned
  moveRep★PartnerOK (target-store-move refl refl same refl hΣ resolve)
      (CTX.rep★-matched-inner-tags X₂≢X aligned) =
    CTX.rep★-matched-inner-tags X₂≢X aligned
  moveRep★PartnerOK mv (CTX.rep★-round-trip ok) =
    CTX.rep★-round-trip (moveRep★PartnerOK mv ok)

  moveNoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ}
    → TargetStoreMove W Wᵗ
    → CTX.NoTargetOccupantAtSource W X
    → CTX.NoTargetOccupantAtSource Wᵗ X
  moveNoTargetOccupantAtSource
      (target-store-move refl refl same refl hΣ resolve) no-target =
    no-target

  moveSourceConcealOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
    → TargetStoreMove W Wᵗ
    → CTX.SourceConcealOK W M c Xᴿ? M′
    → CTX.SourceConcealOK Wᵗ M c Xᴿ? M′
  moveSourceConcealOK mv (CTX.seal-nonstar-plain-ok Rns nt) =
    CTX.seal-nonstar-plain-ok Rns nt
  moveSourceConcealOK (target-store-move refl refl same refl hΣ resolve)
      (CTX.seal-nonstar-name-protected-ok Rns aligned) =
    CTX.seal-nonstar-name-protected-ok Rns aligned
  moveSourceConcealOK mv CTX.fun-conceal-ok =
    CTX.fun-conceal-ok
  moveSourceConcealOK mv CTX.all-conceal-ok =
    CTX.all-conceal-ok
  moveSourceConcealOK mv CTX.id-conceal-ok =
    CTX.id-conceal-ok

  moveMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Y M′}
    → TargetStoreMove W Wᵗ
    → CTX.MatchedConcealPartnerOK W M c Y M′
    → CTX.MatchedConcealPartnerOK Wᵗ M c Y M′
  moveMatchedConcealPartnerOK mv
      (CTX.matched-seal-star-partner ok) =
    CTX.matched-seal-star-partner (moveRep★PartnerOK mv ok)
  moveMatchedConcealPartnerOK mv (CTX.matched-seal-nonstar Rns) =
    CTX.matched-seal-nonstar Rns
  moveMatchedConcealPartnerOK mv CTX.matched-fun-conceal-target =
    CTX.matched-fun-conceal-target
  moveMatchedConcealPartnerOK mv CTX.matched-all-conceal-target =
    CTX.matched-all-conceal-target
  moveMatchedConcealPartnerOK mv CTX.matched-id-conceal-target =
    CTX.matched-id-conceal-target

liftMoveBoth : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → TargetStoreMove W Wᵗ
  → TargetStoreMove (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v Wᵗ)
liftMoveBoth v (target-store-move refl refl same refl hΣ resolve) =
  target-store-move refl refl same′ refl (StoreTransport-lift hΣ)
    resolve-lift
  where
  same′ : ∀ X → extendᵐ v _ X ≡ extendᵐ v _ X
  same′ Fin.zero = refl
  same′ (Fin.suc X) = same X

  resolve-lift : ∀ {X R}
    → store-lift _ ∋ X ⦂ R
    → CTX.resolveVar (store-lift _) X ≡ CTX.resolveVar (store-lift _) X
  resolve-lift (S-lift∋ X∈ eq) = cong ⇑ᵗ (resolve X∈)

liftMoveLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → TargetStoreMove W Wᵗ
  → TargetStoreMove (CTX.liftWorldLeft v W) (CTX.liftWorldLeft v Wᵗ)
liftMoveLeft v (target-store-move refl refl same refl hΣ resolve) =
  target-store-move refl refl same′ refl hΣ resolve
  where
  same′ : ∀ X → extendᵐ v _ X ≡ extendᵐ v _ X
  same′ Fin.zero = refl
  same′ (Fin.suc X) = same X

moveCtx-tgt : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (mv : TargetStoreMove W Wᵗ)
  → (γ : CtxImp W)
  → CTX.tgtCtxʷ (moveCtx mv γ) ≡ CTX.tgtCtxʷ γ
moveCtx-tgt mv [] = refl
moveCtx-tgt mv (CTX.ctx-imp A B p ∷ γ) =
  cong (B ∷_) (moveCtx-tgt mv γ)

target-typing-move : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴿ} {B : Ty Δᴿ}
  → (mv : TargetStoreMove W Wᵗ)
  → ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ , CTX.targetStoreʷ Wᵗ ,
        CTX.tgtCtxʷ (moveCtx mv γ) ⟩ ⊢ M ⦂ B
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
      CTX.impEnvʷ Wᵗ (toRenameᵗ (CTX.ηᴿʷ Wᵗ) Y) ≡ X⊑★
    target-resolve-pivot-old :
      CTX.resolveVar (CTX.targetStoreʷ W) Y ≡ ＇ Y
    target-resolve-pivot :
      CTX.resolveVar (CTX.targetStoreʷ Wᵗ) Y ≡ ★
    target-resolve-other : ∀ Z
      → Z ≢ Y
      → CTX.resolveVar (CTX.targetStoreʷ Wᵗ) Z
          ≡ CTX.resolveVar (CTX.targetStoreʷ W) Z

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
    {v} {γ : CtxImp W} {γ′ : CtxImp (CTX.liftWorldBoth v W)}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.LiftCtx v γ γ′
  → CTX.LiftCtx v (moveCtx mv γ)
      (moveCtx (liftMoveBoth v mv) γ′)
moveLiftCtx mv CTX.lift-[] = CTX.lift-[]
moveLiftCtx mv (CTX.lift-∷ liftγ) =
  CTX.lift-∷ (moveLiftCtx mv liftγ)

moveLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {v} {γ : CtxImp W} {γ′ : CtxImp (CTX.liftWorldLeft v W)}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.LiftCtxᴸ v γ γ′
  → CTX.LiftCtxᴸ v (moveCtx mv γ)
      (moveCtx (liftMoveLeft v mv) γ′)
moveLiftCtxᴸ mv CTX.liftᴸ-[] = CTX.liftᴸ-[]
moveLiftCtxᴸ mv (CTX.liftᴸ-∷ liftγ) =
  CTX.liftᴸ-∷ (moveLiftCtxᴸ mv liftγ)

liftTargetBindMoveBoth : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
  → (v : VarImp)
  → TargetBindLiftMove W Wᵗ Y
  → TargetBindLiftMove
      (CTX.liftWorldBoth v W)
      (CTX.liftWorldBoth v Wᵗ)
      (Fin.suc Y)
liftTargetBindMoveBoth {W = W} {Wᵗ = Wᵗ} {Y = Y} v
    (target-bind-lift-move mv pivot-star old-pivot pivot-res other) =
  target-bind-lift-move (liftMoveBoth v mv) pivot-star
    (cong ⇑ᵗ old-pivot) (cong ⇑ᵗ pivot-res) other′
  where
  other′ : ∀ Z
    → Z ≢ Fin.suc Y
    → CTX.resolveVar
        (CTX.targetStoreʷ (CTX.liftWorldBoth v Wᵗ)) Z
        ≡ CTX.resolveVar
            (CTX.targetStoreʷ (CTX.liftWorldBoth v W)) Z
  other′ Fin.zero neq = refl
  other′ (Fin.suc Z) neq = cong ⇑ᵗ (other Z (λ eq → neq (cong Fin.suc eq)))

liftTargetBindMoveLeft : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
  → (v : VarImp)
  → TargetBindLiftMove W Wᵗ Y
  → TargetBindLiftMove
      (CTX.liftWorldLeft v W)
      (CTX.liftWorldLeft v Wᵗ)
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
  CTX.world (CTX.ηᴸʷ W) (CTX.ηᴿʷ W) (CTX.impEnvʷ W)
    (CTX.sourceStoreʷ W) Σᴿ

target-pivot-star-source : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y}
  → TargetBindLiftMove W Wᵗ Y
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴿʷ W) Y) ≡ X⊑★
target-pivot-star-source
    (target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other) =
  trans (sym (same _)) pivot-star

premiseMoveEqAny : ∀ {Δᴸ Δᴿ Δ Δᴸ′ Δ′}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ′ Δᴿ Δ′}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.targetStoreʷ W′ ≡ CTX.targetStoreʷ W
  → TargetStoreMove W′ (targetStoreAs W′ (CTX.targetStoreʷ Wᵗ))
premiseMoveEqAny
    {Wᵗ = Wᵗ}
    {W′ = W′}
    (target-store-move refl refl same refl hΣ resolve)
    targetEq =
  target-store-move refl refl (λ X → refl) refl transport′ resolve′
  where
  transport′ :
    StoreTransport (CTX.targetStoreʷ W′) (CTX.targetStoreʷ Wᵗ)
  transport′ {X = X} {A = A} X∈ =
    hΣ (subst≡ (λ Σ → Σ ∋ X ⦂ A) targetEq X∈)

  resolve′ : ∀ {X R}
    → CTX.targetStoreʷ W′ ∋ X ⦂ R
    → CTX.resolveVar (CTX.targetStoreʷ Wᵗ) X
        ≡ CTX.resolveVar (CTX.targetStoreʷ W′) X
  resolve′ {X = X} {R = R} X∈ =
    trans
      (resolve (subst≡ (λ Σ → Σ ∋ X ⦂ R) targetEq X∈))
      (cong (λ Σ → CTX.resolveVar Σ X) (sym targetEq))

premiseMoveEq : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.targetStoreʷ W′ ≡ CTX.targetStoreʷ W
  → TargetStoreMove W′ (targetStoreAs W′ (CTX.targetStoreʷ Wᵗ))
premiseMoveEq = premiseMoveEqAny

premiseTargetBindMove : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y}
  → TargetBindLiftMove W Wᵗ Y
  → CTX.ImpEnvMono W W′
  → CTX.targetStoreʷ W′ ≡ CTX.targetStoreʷ W
  → toRenameᵗ (CTX.ηᴿʷ W′) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ W) Y
  → TargetBindLiftMove W′ (targetStoreAs W′ (CTX.targetStoreʷ Wᵗ)) Y
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
    CTX.impEnvʷ W′ (toRenameᵗ (CTX.ηᴿʷ W′) Y) ≡ X⊑★
  pivot-star′ =
    subst≡ (λ Z → CTX.impEnvʷ W′ Z ≡ X⊑★)
      (sym frozenY)
      (mono (toRenameᵗ (CTX.ηᴿʷ W) Y)
        (trans (sym (same _)) pivot-star))

  old-pivot′ : CTX.resolveVar (CTX.targetStoreʷ W′) Y ≡ ＇ Y
  old-pivot′ =
    trans (cong (λ Σ → CTX.resolveVar Σ Y) targetEq) old-pivot

  other′ : ∀ Z
    → Z ≢ Y
    → CTX.resolveVar (CTX.targetStoreʷ Wᵗ) Z
        ≡ CTX.resolveVar (CTX.targetStoreʷ W′) Z
  other′ Z Z≢Y =
    trans (other Z Z≢Y)
      (cong (λ Σ → CTX.resolveVar Σ Z) (sym targetEq))

smartAliasPivotStar : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ} {Y β α}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → CTX.impEnvʷ Wᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y) ≡ X⊑★
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = Y} {β = β} {α = α}
    mv guard with FinP._≟_ Y β
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = .β} {β = β}
    mv guard | yes refl =
  subst≡
    (λ C → CTX.impEnvʷ Wᵐ C ≡ X⊑★)
    (sym (CTX.SmartAliasMergeGuard.target-frozen guard β))
    (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard)
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = Y} {β = β} {α = α}
    mv guard | no Y≢β with FinP._≟_ Y α
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = .α} {β = β} {α = α}
    mv guard | no Y≢β | yes refl =
  subst≡
    (λ C → CTX.impEnvʷ Wᵐ C ≡ X⊑★)
    (sym (CTX.SmartAliasMergeGuard.target-frozen guard α))
    (CTX.SmartAliasMergeGuard.name-mark-dynamic guard)
smartAliasPivotStar {W = W} {Wᵐ = Wᵐ} {Y = Y} {β = β} {α = α}
    mv guard | no Y≢β | no Y≢α =
  CTX.SmartAliasMergeGuard.target-mark-off-footprint guard Y
    Y≢β Y≢α (target-pivot-star-source mv)

smartFreshPivotStar : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.SmartFreshBehindGuard W Wᵐ
  → CTX.impEnvʷ Wᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y) ≡ X⊑★
smartFreshPivotStar mv guard =
  CTX.SmartFreshBehindGuard.target-mark-mono guard _
    (target-pivot-star-source mv)

smartAliasTargetBindMove : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ} {Y β α}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → TargetBindLiftMove Wᵐ
      (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ)) Y
smartAliasTargetBindMove {Wᵗ = Wᵗ} {Wᵐ = Wᵐ} {Y = Y} mv guard =
  target-bind-lift-move
    (premiseMoveEqAny (baseMove mv)
      (CTX.SmartAliasMergeGuard.targetStore-same guard))
    (smartAliasPivotStar mv guard)
    old-pivot′
    (target-resolve-pivot mv)
    other′
  where
  targetEq = CTX.SmartAliasMergeGuard.targetStore-same guard

  old-pivot′ : CTX.resolveVar (CTX.targetStoreʷ Wᵐ) Y ≡ ＇ Y
  old-pivot′ =
    trans (cong (λ Σ → CTX.resolveVar Σ Y) targetEq)
      (target-resolve-pivot-old mv)

  other′ : ∀ Z
    → Z ≢ Y
    → CTX.resolveVar
        (CTX.targetStoreʷ
          (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ))) Z
        ≡ CTX.resolveVar (CTX.targetStoreʷ Wᵐ) Z
  other′ Z Z≢Y =
    trans (target-resolve-other mv Z Z≢Y)
      (cong (λ Σ → CTX.resolveVar Σ Z) (sym targetEq))

smartFreshTargetBindMove : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetBindLiftMove Wᵐ
      (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ)) Y
smartFreshTargetBindMove {Wᵗ = Wᵗ} {Wᵐ = Wᵐ} {Y = Y} mv guard =
  target-bind-lift-move
    (premiseMoveEqAny (baseMove mv)
      (CTX.SmartFreshBehindGuard.targetStore-same guard))
    (smartFreshPivotStar mv guard)
    old-pivot′
    (target-resolve-pivot mv)
    other′
  where
  targetEq = CTX.SmartFreshBehindGuard.targetStore-same guard

  old-pivot′ : CTX.resolveVar (CTX.targetStoreʷ Wᵐ) Y ≡ ＇ Y
  old-pivot′ =
    trans (cong (λ Σ → CTX.resolveVar Σ Y) targetEq)
      (target-resolve-pivot-old mv)

  other′ : ∀ Z
    → Z ≢ Y
    → CTX.resolveVar
        (CTX.targetStoreʷ
          (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ))) Z
        ≡ CTX.resolveVar (CTX.targetStoreʷ Wᵐ) Z
  other′ Z Z≢Y =
    trans (target-resolve-other mv Z Z≢Y)
      (cong (λ Σ → CTX.resolveVar Σ Z) (sym targetEq))

moveSmartAliasMergeGuard : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δ} {Y β α}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → CTX.SmartAliasMergeGuard Wᵗ
      (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ)) β α
moveSmartAliasMergeGuard
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    guard =
  CTX.smart-alias-merge-guard
    (hΣ (CTX.SmartAliasMergeGuard.β:=＇α guard))
    (hΣ (CTX.SmartAliasMergeGuard.α:=★ guard))
    (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)
    refl
    (λ p → CTX.SmartAliasMergeGuard.transport⊑ᵂ guard
      (move⊑ᵂ-back (liftMoveLeft X⊑★ mv) p))
    (λ Z dynamic → CTX.SmartAliasMergeGuard.old-mark-mono guard Z
      (trans (sym (same Z)) dynamic))
    (CTX.SmartAliasMergeGuard.target-frozen guard)
    (CTX.SmartAliasMergeGuard.pending-at-alias guard)
    (CTX.SmartAliasMergeGuard.old-source-frozen guard)
    (CTX.SmartAliasMergeGuard.no-old-source-at-alias guard)
    (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard)
    (CTX.SmartAliasMergeGuard.name-mark-dynamic guard)
    (λ X X≢β X≢α dynamic →
      CTX.SmartAliasMergeGuard.target-mark-off-footprint guard
        X X≢β X≢α (trans (sym (same _)) dynamic))

moveSmartFreshBehindGuard : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.SmartFreshBehindGuard W Wᵐ
  → CTX.SmartFreshBehindGuard Wᵗ
      (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ))
moveSmartFreshBehindGuard
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    guard =
  CTX.smart-fresh-behind-guard
    (CTX.SmartFreshBehindGuard.oldCenters guard)
    (CTX.SmartFreshBehindGuard.sourceStore-lifted guard)
    refl
    (λ p → CTX.SmartFreshBehindGuard.transport⊑ᵂ guard
      (move⊑ᵂ-back (liftMoveLeft X⊑★ mv) p))
    (λ Z dynamic → CTX.SmartFreshBehindGuard.old-mark-mono guard Z
      (trans (sym (same Z)) dynamic))
    (CTX.SmartFreshBehindGuard.target-frozen guard)
    (CTX.SmartFreshBehindGuard.old-source-frozen guard)
    (CTX.SmartFreshBehindGuard.fresh-not-target guard)
    (CTX.SmartFreshBehindGuard.fresh-mark-dynamic guard)
    (λ X dynamic → CTX.SmartFreshBehindGuard.target-mark-mono guard X
      (trans (sym (same _)) dynamic))

moveSmartCommaLiftᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.SmartCommaLiftᴸ W Wᵐ
  → CTX.SmartCommaLiftᴸ Wᵗ
      (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ))
moveSmartCommaLiftᴸ mv (CTX.smart-fresh-behind guard) =
  CTX.smart-fresh-behind (moveSmartFreshBehindGuard mv guard)
moveSmartCommaLiftᴸ mv (CTX.smart-merge-alias guard) =
  CTX.smart-merge-alias (moveSmartAliasMergeGuard mv guard)

moveSmartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵗ : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CtxImp W} {γᵐ : CtxImp Wᵐ} {Y}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → (mvᵐ : TargetBindLiftMove Wᵐ
      (targetStoreAs Wᵐ (CTX.targetStoreʷ Wᵗ)) Y)
  → CTX.SmartLiftCtxᴸ γ γᵐ
  → CTX.SmartLiftCtxᴸ (moveCtx (baseMove mv) γ)
      (moveCtx (baseMove mvᵐ) γᵐ)
moveSmartLiftCtxᴸ mv mvᵐ CTX.smart-lift-[] = CTX.smart-lift-[]
moveSmartLiftCtxᴸ mv mvᵐ (CTX.smart-lift-∷ liftγ) =
  CTX.smart-lift-∷ (moveSmartLiftCtxᴸ mv mvᵐ liftγ)

moveStoreRepBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Y Xᴸ Xᴿ}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → CTX.StoreRepImp Wᵗ Xᴸ Xᴿ
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTX.store-rep-imp represented)
    with FinP._≟_ Xᴿ Y
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = .Y}
    (target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTX.store-rep-imp represented)
    | yes refl
    with SPT.right-var-obligation-view
      {W = W} {R = CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ}
      {Y = Y}
      (subst≡
        (λ B → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
          ⊑ᵂ⟨ W ⟩ B)
        old-pivot
        represented)
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = .Y}
    (target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTX.store-rep-imp represented)
    | yes refl | X₂ , source-eq , aligned =
  CTX.store-rep-imp
    (subst≡
      (λ R → R ⊑ᵂ⟨ Wᵗ ⟩ CTX.resolveVar (CTX.targetStoreʷ Wᵗ) Y)
      (sym source-eq)
      (subst≡
        (λ B → ＇ X₂ ⊑ᵂ⟨ Wᵗ ⟩ B)
        (sym pivot-res)
        (subst≡
          (λ Z → CTX.impEnvʷ Wᵗ ⊢ (＇ Z) ⊑ ★)
          (sym aligned)
          (X⊑★ pivot-star))))
moveStoreRepBindLift
    {W = W} {Wᵗ = Wᵗ} {Y = Y} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    (CTX.store-rep-imp represented)
    | no Xᴿ≢Y =
  CTX.store-rep-imp
    (subst≡
      (λ B → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
        ⊑ᵂ⟨ Wᵗ ⟩ B)
      (sym (other Xᴿ Xᴿ≢Y))
      (move⊑ᵂ mv represented))

moveRebaseAtForwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ Xᴿ}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.ImpEnvMono W W′
  → CTX.RebaseAt W W′ Xᴸ Xᴿ
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTX.RebaseAt Wᵗ W′ᵗ Xᴸ Xᴿ
moveRebaseAtForwardBindLift
    {W = W} {Wᵗ = Wᵗ} {W′ = W′} {Y = Y}
    mv@(target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTX.rebase-at (CTX.same-runtime sourceEq targetEq)
      off frozen aligned reps) =
  W′ᵗ , mv′ ,
  CTX.rebase-at (CTX.same-runtime sourceEq refl)
    off frozen aligned (moveStoreRepBindLift mv′ reps)
  where
  W′ᵗ = targetStoreAs W′ (CTX.targetStoreʷ Wᵗ)
  mv′ = premiseTargetBindMove mv mono targetEq (frozen Y)

moveRebaseAtBackwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ Xᴿ}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.ImpEnvMono W W′
  → CTX.RebaseAt W′ W Xᴸ Xᴿ
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTX.RebaseAt W′ᵗ Wᵗ Xᴸ Xᴿ
moveRebaseAtBackwardBindLift
    {W = W} {Wᵗ = Wᵗ} {W′ = W′} {Y = Y}
    mv@(target-bind-lift-move
      (target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTX.rebase-at (CTX.same-runtime sourceEq targetEq)
      off frozen aligned reps) =
  W′ᵗ , mv′ ,
  CTX.rebase-at (CTX.same-runtime sourceEq refl)
    off frozen aligned (moveStoreRepBindLift mv reps)
  where
  W′ᵗ = targetStoreAs W′ (CTX.targetStoreʷ Wᵗ)
  mv′ = premiseTargetBindMove mv mono (sym targetEq) (sym (frozen Y))

moveRebaseAtᴿForwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴿ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.ImpEnvMono W W′
  → CTX.RebaseAtᴿ W W′ Xᴿ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTX.RebaseAtᴿ Wᵗ W′ᵗ Xᴿ?
moveRebaseAtᴿForwardBindLift mv mono CTX.rebase-idᴿ =
  _ , mv , CTX.rebase-idᴿ
moveRebaseAtᴿForwardBindLift mv mono (CTX.rebase-varᴿ rb)
    with moveRebaseAtForwardBindLift mv mono rb
moveRebaseAtᴿForwardBindLift mv mono (CTX.rebase-varᴿ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTX.rebase-varᴿ rb′

moveRebaseAtᴿBackwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴿ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.ImpEnvMono W W′
  → CTX.RebaseAtᴿ W′ W Xᴿ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTX.RebaseAtᴿ W′ᵗ Wᵗ Xᴿ?
moveRebaseAtᴿBackwardBindLift mv mono CTX.rebase-idᴿ =
  _ , mv , CTX.rebase-idᴿ
moveRebaseAtᴿBackwardBindLift mv mono (CTX.rebase-varᴿ rb)
    with moveRebaseAtBackwardBindLift mv mono rb
moveRebaseAtᴿBackwardBindLift mv mono (CTX.rebase-varᴿ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTX.rebase-varᴿ rb′

moveRebaseAtᴸForwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.ImpEnvMono W W′
  → CTX.RebaseAtᴸ W W′ Xᴸ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTX.RebaseAtᴸ Wᵗ W′ᵗ Xᴸ?
moveRebaseAtᴸForwardBindLift mv mono CTX.rebase-idᴸ =
  _ , mv , CTX.rebase-idᴸ
moveRebaseAtᴸForwardBindLift mv mono (CTX.rebase-varᴸ rb)
    with moveRebaseAtForwardBindLift mv mono rb
moveRebaseAtᴸForwardBindLift mv mono (CTX.rebase-varᴸ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTX.rebase-varᴸ rb′
moveRebaseAtᴸForwardBindLift
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTX.rebase-onlyᴸ to-star disaligned represented) =
  _ ,
  target-bind-lift-move
    mv
    pivot-star old-pivot pivot-res other ,
  CTX.rebase-onlyᴸ (trans (same _) to-star) disaligned
    (move⊑ᵂ mv represented)

moveTagRebaseAtᴸBackwardBindLift : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Y Xᴸ? Xᴿ?}
  → (mv : TargetBindLiftMove W Wᵗ Y)
  → CTX.ImpEnvMono W W′
  → CTX.TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetBindLiftMove W′ W′ᵗ Y ]
      CTX.TagRebaseAtᴸ W′ᵗ Wᵗ Xᴸ? Xᴿ?
moveTagRebaseAtᴸBackwardBindLift mv mono CTX.tag-rebase-idᴸ =
  _ , mv , CTX.tag-rebase-idᴸ
moveTagRebaseAtᴸBackwardBindLift mv mono (CTX.tag-rebase-varᴸ rb)
    with moveRebaseAtBackwardBindLift mv mono rb
moveTagRebaseAtᴸBackwardBindLift mv mono (CTX.tag-rebase-varᴸ rb)
    | W′ᵗ , mv′ , rb′ =
  W′ᵗ , mv′ , CTX.tag-rebase-varᴸ rb′
moveTagRebaseAtᴸBackwardBindLift
    (target-bind-lift-move
      mv@(target-store-move refl refl same refl hΣ resolve)
      pivot-star old-pivot pivot-res other)
    mono
    (CTX.tag-rebase-onlyᴸ to-star disaligned represented) =
  _ ,
  target-bind-lift-move
    mv
    pivot-star old-pivot pivot-res other ,
  CTX.tag-rebase-onlyᴸ (trans (same _) to-star) disaligned
    (move⊑ᵂ mv represented)

moveStoreRepWithTarget∈ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ R}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.targetStoreʷ W ∋ Xᴿ ⦂ R
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → CTX.StoreRepImp Wᵗ Xᴸ Xᴿ
moveStoreRepWithTarget∈
    {W = W}
    {Wᵗ = Wᵗ}
    {Xᴸ = Xᴸ}
    mv@(target-store-move refl refl same refl hΣ resolve)
    X∈
    (CTX.store-rep-imp represented) =
  CTX.store-rep-imp
    (subst≡
      (λ B → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
        ⊑ᵂ⟨ Wᵗ ⟩ B)
      (sym (resolve X∈))
      (move⊑ᵂ mv represented))

moveRebaseAtForwardWithTarget∈ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ R}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.RebaseAt W W′ Xᴸ Xᴿ
  → CTX.targetStoreʷ W ∋ Xᴿ ⦂ R
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetStoreMove W′ W′ᵗ ]
      CTX.RebaseAt Wᵗ W′ᵗ Xᴸ Xᴿ
moveRebaseAtForwardWithTarget∈
    {Wᵗ = Wᵗ}
    {W′ = W′}
    {Xᴿ = Xᴿ}
    {R = R}
    mv@(target-store-move refl refl same refl hΣ resolve)
    (CTX.rebase-at (CTX.same-runtime sourceEq targetEq)
      off frozen aligned reps)
    X∈ =
  W′ᵗ , mv′ ,
  CTX.rebase-at (CTX.same-runtime sourceEq refl)
    off frozen aligned
    (moveStoreRepWithTarget∈ mv′ X∈′ reps)
  where
  W′ᵗ = targetStoreAs W′ (CTX.targetStoreʷ Wᵗ)
  mv′ = premiseMoveEq mv targetEq
  X∈′ = subst≡ (λ Σ → Σ ∋ Xᴿ ⦂ R) (sym targetEq) X∈

moveRebaseAtBackwardWithTarget∈ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ R}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.RebaseAt W′ W Xᴸ Xᴿ
  → CTX.targetStoreʷ W ∋ Xᴿ ⦂ R
  → Σ[ W′ᵗ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ mv′ ∈ TargetStoreMove W′ W′ᵗ ]
      CTX.RebaseAt W′ᵗ Wᵗ Xᴸ Xᴿ
moveRebaseAtBackwardWithTarget∈
    {Wᵗ = Wᵗ}
    {W′ = W′}
    mv@(target-store-move refl refl same refl hΣ resolve)
    (CTX.rebase-at (CTX.same-runtime sourceEq targetEq)
      off frozen aligned reps)
    X∈ =
  W′ᵗ , mv′ ,
  CTX.rebase-at (CTX.same-runtime sourceEq refl)
    off frozen aligned
    (moveStoreRepWithTarget∈ mv X∈ reps)
  where
  W′ᵗ = targetStoreAs W′ (CTX.targetStoreʷ Wᵗ)
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
  → CTX.sourceStoreʷ W Conv.⊢↑[ X? ] c
  → CTX.sourceStoreʷ Wᵗ Conv.⊢↑[ X? ] c
source-reveal-move
    (target-store-move refl refl same refl hΣ resolve) c⊢ = c⊢

source-conceal-move : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {X? A B}
    {c : Conv↓ Δᴸ A B}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.sourceStoreʷ W Conv.⊢↓[ X? ] c
  → CTX.sourceStoreʷ Wᵗ Conv.⊢↓[ X? ] c
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
      Anv zero∈A (CTX.smart-merge-alias guard) liftγ vV M′⊢
      V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTX.smart-merge-alias (moveSmartAliasMergeGuard mv guard))
    (moveSmartLiftCtxᴸ mv mvᵐ liftγ) vV
    (target-typing-move (baseMove mv) M′⊢)
    (⊢²-target-bind-lift-move mvᵐ V⊑M′)
    (move⊑ᵂ (baseMove mv) q)
  where
  mvᵐ = smartAliasTargetBindMove mv guard
⊢²-target-bind-lift-move mv
    (CTI2.Λ⊑²-smart-comma
      Anv zero∈A (CTX.smart-fresh-behind guard) liftγ vV M′⊢
      V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTX.smart-fresh-behind (moveSmartFreshBehindGuard mv guard))
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
        (CTX.liftWorldBoth v (CTX.rightOnlyWorld W ★)))
      (ΛLiftToBindFreshWorld v W)
freshLiftToBindMove {W = W} {v = v} =
  target-store-move
    (cong skip
      (sym (∘↪-idˡ (keep (skip (CTX.ηᴸʷ W))))))
    (cong skip
      (sym (∘↪-idˡ (keep (keep (CTX.ηᴿʷ W))))))
    same
    refl
    StoreTransport-lift-bind
    resolve
  where
  same : ∀ X
    → extendᵐ X⊑★ (extendᵐ v (instᵐ (CTX.impEnvʷ W))) X
      ≡ extendᵐ X⊑★
          (CR.renameEnv id↪ᵗ
            (extendᵐ v (instᵐ (CTX.impEnvʷ W)))) X
  same Fin.zero = refl
  same (Fin.suc X) =
    sym (renameEnv-id (extendᵐ v (instᵐ (CTX.impEnvʷ W))) X)

  resolve : ∀ {Δ} {Σ : TyStore (suc Δ)} {X R}
    → store-lift Σ ∋ X ⦂ R
    → CTX.resolveVar (store-bind Σ (＇ Fin.zero)) X
        ≡ CTX.resolveVar (store-lift Σ) X
  resolve (S-lift∋ X∈ eq) = refl

freshLiftToBindTargetMove★ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → TargetBindLiftMove
      (CR.renameWorld wk↪ᵗ
        (CTX.liftWorldBoth X⊑★ (CTX.rightOnlyWorld W ★)))
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
    → CTX.resolveVar
        (CTX.targetStoreʷ (ΛLiftToBindFreshWorld X⊑★ W)) Z
        ≡ CTX.resolveVar
            (CTX.targetStoreʷ
              (CR.renameWorld wk↪ᵗ
                (CTX.liftWorldBoth X⊑★
                  (CTX.rightOnlyWorld W ★)))) Z
  other Fin.zero neq = ⊥-elim (neq refl)
  other (Fin.suc Z) neq = refl


freshLiftToBindTargetMoveAt : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ (suc Δᴿ) Δ}
    {Σ₂ : TyStore (suc (suc Δᴿ))}
  → StoreTransport (store-lift (CTX.targetStoreʷ W)) Σ₂
  → CTX.resolveVar Σ₂ Fin.zero ≡ ★
  → (∀ Z → Z ≢ Fin.zero
      → CTX.resolveVar Σ₂ Z
          ≡ CTX.resolveVar (store-lift (CTX.targetStoreʷ W)) Z)
  → TargetBindLiftMove
      (CR.renameWorld wk↪ᵗ (CTX.liftWorldBoth X⊑★ W))
      (targetStoreAs
        (CR.renameWorld wk↪ᵗ (CTX.liftWorldBoth X⊑★ W)) Σ₂)
      Fin.zero
freshLiftToBindTargetMoveAt {W = W} {Σ₂ = Σ₂} hΣ pivot other =
  target-bind-lift-move
    (target-store-move refl refl (λ X → refl) refl hΣ resolve)
    refl refl pivot other
  where
  resolve : ∀ {X R}
    → store-lift (CTX.targetStoreʷ W) ∋ X ⦂ R
    → CTX.resolveVar Σ₂ X
        ≡ CTX.resolveVar (store-lift (CTX.targetStoreʷ W)) X
  resolve (S-lift∋ {X = X} X∈ eq) = other (Fin.suc X) (λ ())


freshLiftToBindTargetMoveAtκ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ (suc Δᴿ) Δ}
    (κ : suc Δ ↪ᵗ Δ′)
    {Σ₂ : TyStore (suc (suc Δᴿ))}
  → CTX.impEnvʷ (CR.renameWorld κ (CTX.liftWorldBoth X⊑★ W))
      (toRenameᵗ
        (CTX.ηᴿʷ (CR.renameWorld κ (CTX.liftWorldBoth X⊑★ W)))
        Fin.zero)
      ≡ X⊑★
  → StoreTransport (store-lift (CTX.targetStoreʷ W)) Σ₂
  → CTX.resolveVar Σ₂ Fin.zero ≡ ★
  → (∀ Z → Z ≢ Fin.zero
      → CTX.resolveVar Σ₂ Z
          ≡ CTX.resolveVar (store-lift (CTX.targetStoreʷ W)) Z)
  → TargetBindLiftMove
      (CR.renameWorld κ (CTX.liftWorldBoth X⊑★ W))
      (targetStoreAs (CR.renameWorld κ (CTX.liftWorldBoth X⊑★ W)) Σ₂)
      Fin.zero
freshLiftToBindTargetMoveAtκ {W = W} κ {Σ₂ = Σ₂}
    pivot-star hΣ pivot other =
  target-bind-lift-move
    (target-store-move refl refl (λ X → refl) refl hΣ resolve)
    pivot-star refl pivot other
  where
  resolve : ∀ {X R}
    → store-lift (CTX.targetStoreʷ W) ∋ X ⦂ R
    → CTX.resolveVar Σ₂ X
        ≡ CTX.resolveVar (store-lift (CTX.targetStoreʷ W)) X
  resolve (S-lift∋ {X = X} X∈ eq) = other (Fin.suc X) (λ ())


freshLiftToBindTargetMoveAtκᴸ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ (suc Δᴿ) Δ}
    (κ : suc (suc Δ) ↪ᵗ Δ′)
    {Σ₂ : TyStore (suc (suc Δᴿ))}
  → CTX.impEnvʷ
      (CR.renameWorld κ
        (CTX.liftWorldBoth X⊑★
          (CTX.liftWorldLeft X⊑★ W)))
      (toRenameᵗ
        (CTX.ηᴿʷ
          (CR.renameWorld κ
            (CTX.liftWorldBoth X⊑★
              (CTX.liftWorldLeft X⊑★ W))))
        Fin.zero)
      ≡ X⊑★
  → StoreTransport (store-lift (CTX.targetStoreʷ W)) Σ₂
  → CTX.resolveVar Σ₂ Fin.zero ≡ ★
  → (∀ Z → Z ≢ Fin.zero
      → CTX.resolveVar Σ₂ Z
          ≡ CTX.resolveVar (store-lift (CTX.targetStoreʷ W)) Z)
  → TargetBindLiftMove
      (CR.renameWorld κ
        (CTX.liftWorldBoth X⊑★
          (CTX.liftWorldLeft X⊑★ W)))
      (targetStoreAs
        (CR.renameWorld κ
          (CTX.liftWorldBoth X⊑★
            (CTX.liftWorldLeft X⊑★ W)))
        Σ₂)
      Fin.zero
freshLiftToBindTargetMoveAtκᴸ {W = W} κ {Σ₂ = Σ₂}
    pivot-star hΣ pivot other =
  target-bind-lift-move
    (target-store-move refl refl (λ X → refl) refl hΣ resolve)
    pivot-star refl pivot other
  where
  resolve : ∀ {X R}
    → store-lift (CTX.targetStoreʷ W) ∋ X ⦂ R
    → CTX.resolveVar Σ₂ X
        ≡ CTX.resolveVar (store-lift (CTX.targetStoreʷ W)) X
  resolve (S-lift∋ {X = X} X∈ eq) = other (Fin.suc X) (λ ())

freshLiftToBindMoveᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {v : VarImp}
  → TargetStoreMove
      (CR.renameWorld wk↪ᵗ
        (CTX.liftWorldBoth v
          (CTX.liftWorldLeft X⊑★ (CTX.rightOnlyWorld W ★))))
      (ΛLiftToBindFreshWorldᴸ v W)
freshLiftToBindMoveᴸ {W = W} {v = v} =
  target-store-move
    (cong skip
      (sym (∘↪-idˡ (keep (keep (skip (CTX.ηᴸʷ W)))))))
    (cong skip
      (sym (∘↪-idˡ (keep (skip (keep (CTX.ηᴿʷ W)))))))
    same
    refl
    StoreTransport-lift-bind
    resolve
  where
  same : ∀ X
    → extendᵐ X⊑★
        (extendᵐ v (extendᵐ X⊑★
          (instᵐ (CTX.impEnvʷ W)))) X
      ≡ extendᵐ X⊑★
          (CR.renameEnv id↪ᵗ
            (extendᵐ v (extendᵐ X⊑★
              (instᵐ (CTX.impEnvʷ W))))) X
  same Fin.zero = refl
  same (Fin.suc X) =
    sym (renameEnv-id
      (extendᵐ v (extendᵐ X⊑★ (instᵐ (CTX.impEnvʷ W)))) X)

  resolve : ∀ {Δ} {Σ : TyStore (suc Δ)} {X R}
    → store-lift Σ ∋ X ⦂ R
    → CTX.resolveVar (store-bind Σ (＇ Fin.zero)) X
        ≡ CTX.resolveVar (store-lift Σ) X
  resolve (S-lift∋ X∈ eq) = refl

freshLiftToBindTargetMove★ᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → TargetBindLiftMove
      (CR.renameWorld wk↪ᵗ
        (CTX.liftWorldBoth X⊑★
          (CTX.liftWorldLeft X⊑★ (CTX.rightOnlyWorld W ★))))
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
    → CTX.resolveVar
        (CTX.targetStoreʷ (ΛLiftToBindFreshWorldᴸ X⊑★ W)) Z
        ≡ CTX.resolveVar
            (CTX.targetStoreʷ
              (CR.renameWorld wk↪ᵗ
                (CTX.liftWorldBoth X⊑★
                  (CTX.liftWorldLeft X⊑★
                    (CTX.rightOnlyWorld W ★))))) Z
  other Fin.zero neq = ⊥-elim (neq refl)
  other (Fin.suc Z) neq = refl

ΛLiftToBindFreshTransport : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp (CTX.liftWorldBoth X⊑★ (CTX.rightOnlyWorld W ★))}
    {M : Term (suc Δᴸ)} {M′ : Term (suc (suc Δᴿ))}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
    {p : A ⊑ᵂ⟨ CTX.liftWorldBoth X⊑★
      (CTX.rightOnlyWorld W ★) ⟩ B}
  → CTX.liftWorldBoth X⊑★ (CTX.rightOnlyWorld W ★)
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
    (CTX.liftWorldBoth X⊑★ (CTX.rightOnlyWorld W ★))

  pʳ : _ ⊑ᵂ⟨ Wʳ ⟩ _
  pʳ =
    CR.rename-⊑ᵂ
      {W = CTX.liftWorldBoth X⊑★ (CTX.rightOnlyWorld W ★)}
      wk↪ᵗ p

  relʳ : Wʳ ∣ CR.renameCtx wk↪ᵗ γ ⊢² _ ⊑ _ ∶ pʳ
  relʳ = CR.⊢²-extend-center rel pʳ

  mv = freshLiftToBindTargetMove★ {W = W}

  pᵇ : _ ⊑ᵂ⟨ ΛLiftToBindFreshWorld X⊑★ W ⟩ _
  pᵇ = move⊑ᵂ (baseMove mv) pʳ
