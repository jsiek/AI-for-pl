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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Data.Fin as Fin
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-lift; store-bind; _∋_⦂_; S-lift∋)
open import Imprecision using (VarImp; ImpEnv; X⊑★; X⊑X; instᵐ; extendᵐ)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ; wk↪ᵗ)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_)
open import FunExt using (funext)
import TermCtx as T
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CenterRename as CR
open import proof.TypeInTermSubst using
  (StoreTransport; StoreTransport-lift; StoreTransport-lift-bind;
   typing-store-transport)

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
  → CR.renameEnv id↪ᵗ μ ≡ μ
renameEnv-id {zero} μ = funext λ ()
renameEnv-id {suc Δ} μ =
  funext λ
    { Fin.zero → refl
    ; (Fin.suc X) →
        cong (λ ν → ν X)
          (renameEnv-id (λ Y → μ (Fin.suc Y)))
    }

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
    impEnv-same : CTI2.impEnvʷ Wᵗ ≡ CTI2.impEnvʷ W
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
move⊑ᵂ (target-store-move refl refl refl refl hΣ resolve) p = p

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
    (target-store-move refl refl refl refl hΣ₁ resolve₁)
    (target-store-move refl refl refl refl hΣ₂ resolve₂)
    mono =
  mono

private
  moveRep★PartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {P Xᴿ? M′}
    → TargetStoreMove W Wᵗ
    → CTI2.Rep★PartnerOK W X P Xᴿ? M′
    → CTI2.Rep★PartnerOK Wᵗ X P Xᴿ? M′
  moveRep★PartnerOK (target-store-move refl refl refl refl hΣ resolve)
      (CTI2.rep★-untagged nt) =
    CTI2.rep★-untagged nt
  moveRep★PartnerOK (target-store-move refl refl refl refl hΣ resolve)
      (CTI2.rep★-nonvar-tag Gnv) =
    CTI2.rep★-nonvar-tag Gnv
  moveRep★PartnerOK (target-store-move refl refl refl refl hΣ resolve)
      (CTI2.rep★-var-tag aligned) =
    CTI2.rep★-var-tag aligned
  moveRep★PartnerOK (target-store-move refl refl refl refl hΣ resolve)
      (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
    CTI2.rep★-matched-inner-tags X₂≢X aligned
  moveRep★PartnerOK mv (CTI2.rep★-round-trip ok) =
    CTI2.rep★-round-trip (moveRep★PartnerOK mv ok)

  moveSealPartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {P R Xᴿ? M′}
    → TargetStoreMove W Wᵗ
    → CTI2.SealPartnerOK W X P R Xᴿ? M′
    → CTI2.SealPartnerOK Wᵗ X P R Xᴿ? M′
  moveSealPartnerOK mv (CTI2.star-rep-target ok) =
    CTI2.star-rep-target (moveRep★PartnerOK mv ok)
  moveSealPartnerOK mv (CTI2.plain-target nt) =
    CTI2.plain-target nt
  moveSealPartnerOK mv CTI2.name-protected-target =
    CTI2.name-protected-target

  moveSourceConcealPartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵗ : World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
    → TargetStoreMove W Wᵗ
    → CTI2.SourceConcealPartnerOK W M c Xᴿ? M′
    → CTI2.SourceConcealPartnerOK Wᵗ M c Xᴿ? M′
  moveSourceConcealPartnerOK mv (CTI2.seal-partner-ok ok) =
    CTI2.seal-partner-ok (moveSealPartnerOK mv ok)
  moveSourceConcealPartnerOK mv CTI2.fun-conceal-target =
    CTI2.fun-conceal-target
  moveSourceConcealPartnerOK mv CTI2.all-conceal-target =
    CTI2.all-conceal-target
  moveSourceConcealPartnerOK mv CTI2.id-conceal-target =
    CTI2.id-conceal-target

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
liftMoveBoth v (target-store-move refl refl refl refl hΣ resolve) =
  target-store-move refl refl refl refl (StoreTransport-lift hΣ)
    resolve-lift
  where
  resolve-lift : ∀ {X R}
    → store-lift _ ∋ X ⦂ R
    → CTI2.resolveVar (store-lift _) X ≡ CTI2.resolveVar (store-lift _) X
  resolve-lift (S-lift∋ X∈ eq) = cong ⇑ᵗ (resolve X∈)

liftMoveLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → TargetStoreMove W Wᵗ
  → TargetStoreMove (CTI2.liftWorldLeft v W) (CTI2.liftWorldLeft v Wᵗ)
liftMoveLeft v (target-store-move refl refl refl refl hΣ resolve) =
  target-store-move refl refl refl refl hΣ resolve

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

targetStoreAs : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyStore Δᴿ
  → World Δᴸ Δᴿ Δ
targetStoreAs W Σᴿ =
  CTI2.world (CTI2.ηᴸʷ W) (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W)
    (CTI2.sourceStoreʷ W) Σᴿ

premiseMoveEq : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ W′ : World Δᴸ Δᴿ Δ}
  → (mv : TargetStoreMove W Wᵗ)
  → CTI2.targetStoreʷ W′ ≡ CTI2.targetStoreʷ W
  → TargetStoreMove W′ (targetStoreAs W′ (CTI2.targetStoreʷ Wᵗ))
premiseMoveEq
    {Wᵗ = Wᵗ}
    {W′ = W′}
    (target-store-move refl refl refl refl hΣ resolve)
    targetEq =
  target-store-move refl refl refl refl transport′ resolve′
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
    (target-store-move refl refl refl refl hΣ resolve)
    X∈
    (CTI2.store-rep-imp represented) =
  CTI2.store-rep-imp
    (subst≡
      (λ B → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ
        ⊑ᵂ⟨ Wᵗ ⟩ B)
      (sym (resolve X∈))
      represented)

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
    mv@(target-store-move refl refl refl refl hΣ resolve)
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
    mv@(target-store-move refl refl refl refl hΣ resolve)
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
    (sym (cong (extendᵐ X⊑★)
      (renameEnv-id (extendᵐ v (instᵐ (CTI2.impEnvʷ W))))))
    refl
    StoreTransport-lift-bind
    resolve
  where
  resolve : ∀ {Δ} {Σ : TyStore (suc Δ)} {X R}
    → store-lift Σ ∋ X ⦂ R
    → CTI2.resolveVar (store-bind Σ (＇ Fin.zero)) X
        ≡ CTI2.resolveVar (store-lift Σ) X
  resolve (S-lift∋ X∈ eq) = refl
