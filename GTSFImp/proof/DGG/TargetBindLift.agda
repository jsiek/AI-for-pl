module proof.DGG.TargetBindLift where

-- File Charter:
--   * Constructs the canonical two-bind worlds used after a target-side
--     instantiation step.
--   * Relates two already-constructed inductive worlds when their embeddings,
--     imprecision environment, and source store agree and the target store
--     has a direct transport.
--   * Lifts that evidence through binders and transports world imprecision,
--     contexts, membership, and target typing.
--   * Does not synthesize a world by replacing a target store; callers must
--     provide both genuine inductive worlds.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (store-lift; _∋_⦂_; S-lift∋)
open import Imprecision using (VarImp; X⊑★)
open import Consistency using (keep; skip; toRenameᵗ)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import proof.DGG.CtxImp as CTX
open import proof.TypeInTermSubst using
  (StoreTransport; StoreTransport-lift; typing-store-transport)
open import proof.ImprecisionConsistency using (imp-env-weaken)

open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)

------------------------------------------------------------------------
-- The fresh target bind tower
------------------------------------------------------------------------

ΛLiftToBindFreshWorld : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ)))
ΛLiftToBindFreshWorld v W =
  CTX.liftWorldLeft
    (CTX.rightOnlyWorld
      (CTX.rightOnlyWorld W ★ (inj₁ refl))
      (＇ Fin.zero)
      (inj₂ (Fin.suc Fin.zero , refl , (λ Xᴸ ()))))


ΛLiftToBindFreshWorldᴸ : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (suc (suc Δᴸ)) (suc (suc Δᴿ))
      (suc (suc (suc (suc Δ))))
ΛLiftToBindFreshWorldᴸ v W =
  CTX.liftWorldLeft
    (CTX.liftWorldLeft
      (CTX.rightOnlyWorld
        (CTX.rightOnlyWorld W ★ (inj₁ refl))
        (＇ Fin.zero)
        (inj₂ (Fin.suc Fin.zero , refl , (λ Xᴸ ())))))

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

moveSourceMember : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵗ : World Δᴸ Δᴿ Δ} {X R}
  → (mv : TargetStoreMove W Wᵗ)
  → CTX.sourceStoreʷ W ∋ X ⦂ R
  → CTX.sourceStoreʷ Wᵗ ∋ X ⦂ R
moveSourceMember {X = X} {R = R} mv member =
  subst≡ (λ Σ → Σ ∋ X ⦂ R) (sym (sourceStore-same mv)) member

move⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → TargetStoreMove W Wᵗ
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ Wᵗ ⟩ B
move⊑ᵂ {A = A} {B = B} mv p =
  CTX.imprecision-cong
    (cong (λ η → renameᵗ (toRenameᵗ η) A) (sym (ηᴸ-same mv)))
    (cong (λ η → renameᵗ (toRenameᵗ η) B) (sym (ηᴿ-same mv)))
    (imp-env-weaken
      (λ X dynamic → trans (impEnv-same mv X) dynamic) p)

move⊑ᵂ-back : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → TargetStoreMove W Wᵗ
  → A ⊑ᵂ⟨ Wᵗ ⟩ B
  → A ⊑ᵂ⟨ W ⟩ B
move⊑ᵂ-back {A = A} {B = B} mv p =
  CTX.imprecision-cong
    (cong (λ η → renameᵗ (toRenameᵗ η) A) (ηᴸ-same mv))
    (cong (λ η → renameᵗ (toRenameᵗ η) B) (ηᴿ-same mv))
    (imp-env-weaken
      (λ X dynamic → trans (sym (impEnv-same mv X)) dynamic) p)

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
moveImpEnvMono mv₁ mv₂ mono =
  CTX.imp-env-mono
    (λ X dynamic → trans (impEnv-same mv₂ X)
      (CTX.dynamic-preserved mono X
        (trans (sym (impEnv-same mv₁ X)) dynamic)))
    (λ X precise → trans (impEnv-same mv₂ X)
      (CTX.precise-preserved mono X
        (trans (sym (impEnv-same mv₁ X)) precise)))

liftMoveBoth : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → TargetStoreMove W Wᵗ
  → TargetStoreMove (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v Wᵗ)
liftMoveBoth {W = W} {Wᵗ = Wᵗ} v mv =
  target-store-move
    (cong keep (ηᴸ-same mv))
    (cong keep (ηᴿ-same mv))
    same′
    (cong store-lift (sourceStore-same mv))
    (StoreTransport-lift (targetStore-transport mv))
    resolve-lift
  where
  same′ : ∀ X
    → CTX.impEnvʷ (CTX.liftWorldBoth v Wᵗ) X
      ≡ CTX.impEnvʷ (CTX.liftWorldBoth v W) X
  same′ Fin.zero = refl
  same′ (Fin.suc X) = impEnv-same mv X

  resolve-lift : ∀ {X R}
    → CTX.targetStoreʷ (CTX.liftWorldBoth v W) ∋ X ⦂ R
    → CTX.resolveVar (CTX.targetStoreʷ (CTX.liftWorldBoth v Wᵗ)) X
      ≡ CTX.resolveVar (CTX.targetStoreʷ (CTX.liftWorldBoth v W)) X
  resolve-lift (S-lift∋ X∈ eq) =
    cong ⇑ᵗ (targetResolve-same mv X∈)

liftMoveLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵗ : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → TargetStoreMove W Wᵗ
  → TargetStoreMove (CTX.liftWorldLeft W) (CTX.liftWorldLeft Wᵗ)
liftMoveLeft {W = W} {Wᵗ = Wᵗ} v mv =
  target-store-move
    (cong keep (ηᴸ-same mv))
    (cong skip (ηᴿ-same mv))
    same′
    (cong store-lift (sourceStore-same mv))
    (targetStore-transport mv)
    (targetResolve-same mv)
  where
  same′ : ∀ X
    → CTX.impEnvʷ (CTX.liftWorldLeft Wᵗ) X
      ≡ CTX.impEnvʷ (CTX.liftWorldLeft W) X
  same′ Fin.zero = refl
  same′ (Fin.suc X) = impEnv-same mv X

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
    {v} {γ : CtxImp W} {γ′ : CtxImp (CTX.liftWorldLeft W)}
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
      (CTX.liftWorldLeft W)
      (CTX.liftWorldLeft Wᵗ)
      Y
liftTargetBindMoveLeft v
    (target-bind-lift-move mv pivot-star old-pivot pivot-res other) =
  target-bind-lift-move (liftMoveLeft v mv) pivot-star old-pivot
    pivot-res other
