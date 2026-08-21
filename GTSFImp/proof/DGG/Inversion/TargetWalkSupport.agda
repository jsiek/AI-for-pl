module proof.DGG.Inversion.TargetWalkSupport where

-- File Charter:
--   * Houses the proven store, alignment, and rebase helpers shared by the
--     target walk, source-star chain, and higher-order right-injection proof.
--   * Records the pinned occupied non-star source-seal row left invalid by
--     D17(c); the legacy workers consume that residual explicitly.
--   * Contains no inhabitant of the target walk itself.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using
  (TyStore; store-lift; store-bind; _∋_⦂_; Z∋; S-lift∋;
   S-bind∋)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; keep; skip; toRenameᵗ;
   id; _!; ∀ᶜ_; gen_; inst_)
import Consistency as C
open import Conversion using
  (Conv↑; Conv↓; _⊢↓_; `∀↑_; `∀↓_; _↦↑_; _↦↓_;
   ⊢↓-seal)
open import Imprecision
open import Primitives using (Const; κℕ; κ𝔹)
open import CastTerms
open import Reduction
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.WorldDecay as WD
import proof.DGG.TermImpDecay as TD
import proof.DGG.TagTransport as TT
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.SealTransferCore as STC
open import proof.DGG.ConvImp using
  (pivot-id-endpoints↑; pivot-id-endpoints↓)
open CTX using
  (World;
   ηᴸʷ;
   ηᴿʷ;
   impEnvʷ;
   sourceStoreʷ;
   targetStoreʷ;
   embedᴿ;
   _⊑ᵂ⟨_⟩_;
   CtxImp;
   ctx-imp)
open CTI2 using (_∣_⊢²_⊑_∶_)
open SVD using
  (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all;
   varv-seal; var-value-view; right-tag-variable-view;
   variable-obligation-aligns; seal-rebase-target)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; source-occurs-target; rename-occurs;
   ext-injective; toRenameᵗ-injective; nonstar-from-≢★; rename-⊑;
   fin-suc-injective; nonvar-occurs-nonstar; unshift-⊑)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using (toRename-keep-eq)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

renameᵗ-skip-eq : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (skip η)) B
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) B)
renameᵗ-skip-eq η B =
  trans (renameᵗ-cong B (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc B))

-- The ∀⊑ view of a world obligation for `∀ A against B is exactly a
-- premise for the left-only lifted world: the instᵐ environment is the
-- lifted world's environment, and B's embedding gains one shift.

liftWorldLeft-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
  → instᵐ (impEnvʷ W)
      ⊢ renameᵗ (extᵗ (toRenameᵗ (ηᴸʷ W))) A
        ⊑ ⇑ᵗ (embedᴿ W B)
  → A ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ B
liftWorldLeft-⊑ᵂ {W = W} {A = A} {B = B} body =
  subst≡
    (λ T → extendᵐ X⊑★ (impEnvʷ W) ⊢
       T ⊑ renameᵗ (toRenameᵗ (skip (ηᴿʷ W))) B)
    (sym (renameᵗ-cong A (toRename-keep-eq (ηᴸʷ W))))
    (subst≡
      (λ T → extendᵐ X⊑★ (impEnvʷ W) ⊢
         renameᵗ (extᵗ (toRenameᵗ (ηᴸʷ W))) A ⊑ T)
      (sym (renameᵗ-skip-eq (ηᴿʷ W) B))
      body)

lowerWorldLeft-shift-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ B
  → A ⊑ᵂ⟨ W ⟩ B
lowerWorldLeft-shift-⊑ᵂ {W = W} {A = A} {B = B} p =
  unshift-⊑
    (subst≡
      (λ R → instᵐ (impEnvʷ W) ⊢ ⇑ᵗ (CTX.embedᴸ W A) ⊑ R)
      (renameᵗ-skip-eq (ηᴿʷ W) B)
      (subst≡
        (λ L → instᵐ (impEnvʷ W) ⊢ L ⊑
          renameᵗ (toRenameᵗ (skip (ηᴿʷ W))) B)
        (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq (ηᴸʷ W)))
          (renameᵗ-shift (toRenameᵗ (ηᴸʷ W)) A))
        p))

liftWorldBoth-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {v : VarImp}
  → A ⊑ᵂ⟨ W ⟩ B
  → ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldBoth v W ⟩ ⇑ᵗ B
liftWorldBoth-⊑ᵂ {W = W} {A = A} {B = B} {v = v} p =
  subst≡
    (λ L → impEnvʷ (CTX.liftWorldBoth v W) ⊢ L ⊑
      embedᴿ (CTX.liftWorldBoth v W) (⇑ᵗ B))
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq (ηᴸʷ W)))
                (renameᵗ-shift (toRenameᵗ (ηᴸʷ W)) A)))
    (subst≡
      (λ R → impEnvʷ (CTX.liftWorldBoth v W) ⊢
        ⇑ᵗ (CTX.embedᴸ W A) ⊑ R)
      (sym (trans (renameᵗ-cong (⇑ᵗ B) (toRename-keep-eq (ηᴿʷ W)))
                  (renameᵗ-shift (toRenameᵗ (ηᴿʷ W)) B)))
      (rename-⊑ Fin.suc fin-suc-injective (λ _ eq → eq) p))

-- Rebasing is stable under a binder introduced on both sides.  This is
-- the world-level counterpart of the shifted-pivot conversion rules.

liftRebaseAt : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {v : VarImp}
  → CTX.RebaseAt W W′ Xᴸ Xᴿ
  → CTX.RebaseAt (CTX.liftWorldBoth v W)
      (CTX.liftWorldBoth v W′) (Fin.suc Xᴸ) (Fin.suc Xᴿ)
liftRebaseAt {Δᴸ = Δᴸ} {W = W} {W′ = W′} {Xᴸ = Xᴸ}
    {Xᴿ = Xᴿ} {v = v} rb =
  CTX.rebase-at
    (CTX.same-runtime
      (cong store-lift
        (CTX.SameRuntime.sourceStore-same (CTX.RebaseAt.sameRuntime rb)))
      (cong store-lift
        (CTX.SameRuntime.targetStore-same (CTX.RebaseAt.sameRuntime rb))))
    source-off target-off
    (cong Fin.suc (CTX.RebaseAt.pivotAligned rb))
    (CTX.store-rep-imp lift-represented)
  where
  old-represented =
    CTX.StoreRepImp.represented
      (CTX.RebaseAt.storeRepresentations rb)

  renamed-represented =
    rename-⊑ Fin.suc fin-suc-injective (λ _ eq → eq) old-represented

  lift-represented :
    CTX.resolveVar
        (sourceStoreʷ (CTX.liftWorldBoth v W′)) (Fin.suc Xᴸ)
      ⊑ᵂ⟨ CTX.liftWorldBoth v W′ ⟩
    CTX.resolveVar
        (targetStoreʷ (CTX.liftWorldBoth v W′)) (Fin.suc Xᴿ)
  lift-represented =
    subst≡
      (λ L → impEnvʷ (CTX.liftWorldBoth v W′) ⊢ L ⊑
        embedᴿ (CTX.liftWorldBoth v W′)
          (⇑ᵗ (CTX.resolveVar (targetStoreʷ W′) Xᴿ)))
      (sym (trans
        (renameᵗ-cong (⇑ᵗ (CTX.resolveVar (sourceStoreʷ W′) Xᴸ))
          (toRename-keep-eq (ηᴸʷ W′)))
        (renameᵗ-shift (toRenameᵗ (ηᴸʷ W′))
          (CTX.resolveVar (sourceStoreʷ W′) Xᴸ))))
      (subst≡
        (λ R → impEnvʷ (CTX.liftWorldBoth v W′) ⊢
          ⇑ᵗ (CTX.embedᴸ W′
            (CTX.resolveVar (sourceStoreʷ W′) Xᴸ)) ⊑ R)
        (sym (trans
          (renameᵗ-cong (⇑ᵗ (CTX.resolveVar (targetStoreʷ W′) Xᴿ))
            (toRename-keep-eq (ηᴿʷ W′)))
          (renameᵗ-shift (toRenameᵗ (ηᴿʷ W′))
            (CTX.resolveVar (targetStoreʷ W′) Xᴿ))))
        renamed-represented)

  source-off : ∀ {Y}
    → Y ≢ Fin.suc Xᴸ
    → toRenameᵗ (ηᴸʷ (CTX.liftWorldBoth v W′)) Y
        ≡ toRenameᵗ (ηᴸʷ (CTX.liftWorldBoth v W)) Y
  source-off {Fin.zero} Y≢ = refl
  source-off {Fin.suc Y} Y≢ =
    cong Fin.suc
      (CTX.RebaseAt.ηᴸ-off-pivot rb
        (λ eq → Y≢ (cong Fin.suc eq)))

  target-off : ∀ Y
    → toRenameᵗ (ηᴿʷ (CTX.liftWorldBoth v W′)) Y
        ≡ toRenameᵗ (ηᴿʷ (CTX.liftWorldBoth v W)) Y
  target-off Fin.zero = refl
  target-off (Fin.suc Y) =
    cong Fin.suc (CTX.RebaseAt.ηᴿ-frozen rb Y)


liftPivot : ∀ {Δ} → Maybe (TyVar Δ) → Maybe (TyVar (suc Δ))
liftPivot nothing = nothing
liftPivot (just X) = just (Fin.suc X)

liftRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {v : VarImp}
  → CTX.RebaseAtᴸ W W′ Xᴸ?
  → CTX.RebaseAtᴸ (CTX.liftWorldBoth v W)
      (CTX.liftWorldBoth v W′) (liftPivot Xᴸ?)
liftRebaseAtᴸ CTX.rebase-idᴸ = CTX.rebase-idᴸ
liftRebaseAtᴸ (CTX.rebase-varᴸ rb) =
  CTX.rebase-varᴸ (liftRebaseAt rb)
liftRebaseAtᴸ {Δᴿ = Δᴿ} {W = W} {v = v}
    (CTX.rebase-onlyᴸ {Xᴸ = Xᴸ} to-star disaligned represented) =
  CTX.rebase-onlyᴸ to-star lifted-disaligned
    (liftWorldBoth-⊑ᵂ
      {W = W} {A = CTX.resolveVar (sourceStoreʷ W) Xᴸ}
      {B = ★} {v = v}
      represented)
  where
  lifted-disaligned : ∀ (Xᴿ : TyVar (suc Δᴿ))
    → toRenameᵗ (ηᴿʷ (CTX.liftWorldBoth v W)) Xᴿ
        ≢ toRenameᵗ (ηᴸʷ (CTX.liftWorldBoth v W)) (Fin.suc Xᴸ)
  lifted-disaligned Fin.zero ()
  lifted-disaligned (Fin.suc Xᴿ) eq =
    disaligned Xᴿ (fin-suc-injective eq)

------------------------------------------------------------------------
-- Stage 2: right-injection inversion for spine values
------------------------------------------------------------------------

-- Threading mark-honesty and decay through the inversion.  The
-- inversion's recursion may enter a wrapper's premise world, which
-- the input derivation does not constrain to be mark-honest; the
-- var-rebased wrapper cases therefore decay their premises into the
-- honestified premise world before recursing.

impEnvMono-∘ : ∀ {Δᴸ Δᴿ Δ} {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
  → CTX.ImpEnvMono W₁ W₂
  → CTX.ImpEnvMono W₂ W₃
  → CTX.ImpEnvMono W₁ W₃
impEnvMono-∘ = CTX.impEnvMono-trans

sameCtx-∘ : ∀ {Δᴸ Δᴿ Δ₁ Δ₂ Δ₃}
    {W₁ : World Δᴸ Δᴿ Δ₁} {W₂ : World Δᴸ Δᴿ Δ₂}
    {W₃ : World Δᴸ Δᴿ Δ₃}
    {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂} {γ₃ : CtxImp W₃}
  → CTX.SameCtx γ₁ γ₂
  → CTX.SameCtx γ₂ γ₃
  → CTX.SameCtx γ₁ γ₃
sameCtx-∘ CTX.same-[] CTX.same-[] = CTX.same-[]
sameCtx-∘ (CTX.same-∷ sc₁) (CTX.same-∷ sc₂) =
  CTX.same-∷ (sameCtx-∘ sc₁ sc₂)

rebase-target-membership : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
  → CTX.RebaseAt W′ W X Y
  → targetStoreʷ W′ ∋ Y ⦂ S
  → targetStoreʷ W ∋ Y ⦂ S
rebase-target-membership ra Y∈ =
  subst≡ (λ Σ → Σ ∋ _ ⦂ _)
    (sym (CTX.SameRuntime.targetStore-same
      (CTX.RebaseAt.sameRuntime ra))) Y∈

rebase-source-membership : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {R : Ty Δᴸ}
  → CTX.RebaseAt W′ W X Y
  → sourceStoreʷ W ∋ X ⦂ R
  → sourceStoreʷ W′ ∋ X ⦂ R
rebase-source-membership ra X∈ =
  subst≡ (λ Σ → Σ ∋ _ ⦂ _)
    (CTX.SameRuntime.sourceStore-same
      (CTX.RebaseAt.sameRuntime ra)) X∈

rebase-source-membership-back : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ}
    {X Z : TyVar Δᴸ} {Y : TyVar Δᴿ} {R : Ty Δᴸ}
  → CTX.RebaseAt W′ W X Y
  → sourceStoreʷ W′ ∋ Z ⦂ R
  → sourceStoreʷ W ∋ Z ⦂ R
rebase-source-membership-back ra Z∈ =
  subst≡ (λ Σ → Σ ∋ _ ⦂ _)
    (sym (CTX.SameRuntime.sourceStore-same
      (CTX.RebaseAt.sameRuntime ra))) Z∈

store-variable-distinct : ∀ {Δ} {Σ : TyStore Δ}
    {Z Z₃ : TyVar Δ}
  → Σ ∋ Z ⦂ (＇ Z₃)
  → Z₃ ≢ Z
store-variable-distinct (Z∋ {A = ＇ X} refl) ()
store-variable-distinct (Z∋ {A = ‵ ι} ())
store-variable-distinct (Z∋ {A = ★} ())
store-variable-distinct (Z∋ {A = A ⇒ B} ())
store-variable-distinct (Z∋ {A = `∀ A} ())
store-variable-distinct (S-lift∋ {A = ＇ X} X∈ refl) refl =
  store-variable-distinct X∈ refl
store-variable-distinct (S-lift∋ {A = ‵ ι} X∈ ())
store-variable-distinct (S-lift∋ {A = ★} X∈ ())
store-variable-distinct (S-lift∋ {A = A ⇒ B} X∈ ())
store-variable-distinct (S-lift∋ {A = `∀ A} X∈ ())
store-variable-distinct (S-bind∋ {A = ＇ X} X∈ refl) refl =
  store-variable-distinct X∈ refl
store-variable-distinct (S-bind∋ {A = ‵ ι} X∈ ())
store-variable-distinct (S-bind∋ {A = ★} X∈ ())
store-variable-distinct (S-bind∋ {A = A ⇒ B} X∈ ())
store-variable-distinct (S-bind∋ {A = `∀ A} X∈ ())

store-lookup-unique : ∀ {Δ} {Σ : TyStore Δ} {X A B}
  → Σ ∋ X ⦂ A
  → Σ ∋ X ⦂ B
  → A ≡ B
store-lookup-unique (Z∋ eq) (Z∋ eq′) = trans eq (sym eq′)
store-lookup-unique (S-lift∋ X∈ eq) (S-lift∋ X∈′ eq′) =
  trans eq (trans (cong ⇑ᵗ (store-lookup-unique X∈ X∈′)) (sym eq′))
store-lookup-unique (S-bind∋ X∈ eq) (S-bind∋ X∈′ eq′) =
  trans eq (trans (cong ⇑ᵗ (store-lookup-unique X∈ X∈′)) (sym eq′))

store-lookup-resolve-star : ∀ {Δ} {Σ : TyStore Δ} {X}
  → Σ ∋ X ⦂ ★
  → CTX.resolveVar Σ X ≡ ★
store-lookup-resolve-star (Z∋ {A = ＇ X} ())
store-lookup-resolve-star (Z∋ {A = ‵ ι} ())
store-lookup-resolve-star (Z∋ {A = ★} refl) = refl
store-lookup-resolve-star (Z∋ {A = A ⇒ B} ())
store-lookup-resolve-star (Z∋ {A = `∀ A} ())
store-lookup-resolve-star (S-lift∋ {A = ＇ X} X∈ ())
store-lookup-resolve-star (S-lift∋ {A = ‵ ι} X∈ ())
store-lookup-resolve-star (S-lift∋ {A = ★} X∈ refl) =
  cong ⇑ᵗ (store-lookup-resolve-star X∈)
store-lookup-resolve-star (S-lift∋ {A = A ⇒ B} X∈ ())
store-lookup-resolve-star (S-lift∋ {A = `∀ A} X∈ ())
store-lookup-resolve-star (S-bind∋ {A = ＇ X} X∈ ())
store-lookup-resolve-star (S-bind∋ {A = ‵ ι} X∈ ())
store-lookup-resolve-star (S-bind∋ {A = ★} X∈ refl) =
  cong ⇑ᵗ (store-lookup-resolve-star X∈)
store-lookup-resolve-star (S-bind∋ {A = A ⇒ B} X∈ ())
store-lookup-resolve-star (S-bind∋ {A = `∀ A} X∈ ())

star-store-rep : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → sourceStoreʷ W ∋ X ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ ★
  → CTX.StoreRepImp W X Y
star-store-rep {W = W} {X = X} {Y = Y} X∈ Y∈ =
  CTX.store-rep-imp
    (subst≡ (λ L → L ⊑ᵂ⟨ W ⟩ CTX.resolveVar (targetStoreʷ W) Y)
      (sym (store-lookup-resolve-star X∈))
      (subst≡ (λ R → ★ ⊑ᵂ⟨ W ⟩ R)
        (sym (store-lookup-resolve-star Y∈))
        ★⊑★))

data StoreChain {Δ} (Σ : TyStore Δ) :
    TyVar Δ → TyVar Δ → Set where
  chain-one : ∀ {X Y}
    → Σ ∋ X ⦂ (＇ Y)
    → StoreChain Σ X Y

  chain-step : ∀ {X Y Z}
    → Σ ∋ X ⦂ (＇ Y)
    → StoreChain Σ Y Z
    → StoreChain Σ X Z

store-chain-extend : ∀ {Δ} {Σ : TyStore Δ} {X Y Z}
  → StoreChain Σ X Y
  → Σ ∋ Y ⦂ (＇ Z)
  → StoreChain Σ X Z
store-chain-extend (chain-one X∈) Y∈ =
  chain-step X∈ (chain-one Y∈)
store-chain-extend (chain-step X∈ chain) Y∈ =
  chain-step X∈ (store-chain-extend chain Y∈)

store-chain-lift-inv : ∀ {Δ} {Σ : TyStore Δ} {X Z}
  → StoreChain (store-lift Σ) (Fin.suc X) Z
  → Σ[ Z₀ ∈ TyVar Δ ]
      (Z ≡ Fin.suc Z₀ × StoreChain Σ X Z₀)
store-chain-lift-inv
    (chain-one (S-lift∋ {A = ＇ Z₀} X∈ refl)) =
  Z₀ , refl , chain-one X∈
store-chain-lift-inv
    (chain-one (S-lift∋ {A = ‵ ι} X∈ ()))
store-chain-lift-inv
    (chain-one (S-lift∋ {A = ★} X∈ ()))
store-chain-lift-inv
    (chain-one (S-lift∋ {A = A ⇒ B} X∈ ()))
store-chain-lift-inv
    (chain-one (S-lift∋ {A = `∀ A} X∈ ()))
store-chain-lift-inv
    (chain-step (S-lift∋ {A = ＇ Y₀} X∈ refl) chain)
    with store-chain-lift-inv chain
store-chain-lift-inv
    (chain-step (S-lift∋ {A = ＇ Y₀} X∈ refl) chain)
    | Z₀ , refl , chain₀ =
  Z₀ , refl , chain-step X∈ chain₀
store-chain-lift-inv
    (chain-step (S-lift∋ {A = ‵ ι} X∈ ()) chain)
store-chain-lift-inv
    (chain-step (S-lift∋ {A = ★} X∈ ()) chain)
store-chain-lift-inv
    (chain-step (S-lift∋ {A = A ⇒ B} X∈ ()) chain)
store-chain-lift-inv
    (chain-step (S-lift∋ {A = `∀ A} X∈ ()) chain)

store-chain-bind-suc-inv : ∀ {Δ} {Σ : TyStore Δ} {C X Z}
  → StoreChain (store-bind Σ C) (Fin.suc X) Z
  → Σ[ Z₀ ∈ TyVar Δ ]
      (Z ≡ Fin.suc Z₀ × StoreChain Σ X Z₀)
store-chain-bind-suc-inv
    (chain-one (S-bind∋ {A = ＇ Z₀} X∈ refl)) =
  Z₀ , refl , chain-one X∈
store-chain-bind-suc-inv
    (chain-one (S-bind∋ {A = ‵ ι} X∈ ()))
store-chain-bind-suc-inv
    (chain-one (S-bind∋ {A = ★} X∈ ()))
store-chain-bind-suc-inv
    (chain-one (S-bind∋ {A = A ⇒ B} X∈ ()))
store-chain-bind-suc-inv
    (chain-one (S-bind∋ {A = `∀ A} X∈ ()))
store-chain-bind-suc-inv
    (chain-step (S-bind∋ {A = ＇ Y₀} X∈ refl) chain)
    with store-chain-bind-suc-inv chain
store-chain-bind-suc-inv
    (chain-step (S-bind∋ {A = ＇ Y₀} X∈ refl) chain)
    | Z₀ , refl , chain₀ =
  Z₀ , refl , chain-step X∈ chain₀
store-chain-bind-suc-inv
    (chain-step (S-bind∋ {A = ‵ ι} X∈ ()) chain)
store-chain-bind-suc-inv
    (chain-step (S-bind∋ {A = ★} X∈ ()) chain)
store-chain-bind-suc-inv
    (chain-step (S-bind∋ {A = A ⇒ B} X∈ ()) chain)
store-chain-bind-suc-inv
    (chain-step (S-bind∋ {A = `∀ A} X∈ ()) chain)

store-chain-bind-zero-not-zero : ∀ {Δ} {Σ : TyStore Δ} {C Z}
  → StoreChain (store-bind Σ C) Fin.zero Z
  → Z ≢ Fin.zero
store-chain-bind-zero-not-zero
    (chain-one (Z∋ {A = ＇ Z₀} refl)) ()
store-chain-bind-zero-not-zero
    (chain-one (Z∋ {A = ‵ ι} ()))
store-chain-bind-zero-not-zero
    (chain-one (Z∋ {A = ★} ()))
store-chain-bind-zero-not-zero
    (chain-one (Z∋ {A = A ⇒ B} ()))
store-chain-bind-zero-not-zero
    (chain-one (Z∋ {A = `∀ A} ()))
store-chain-bind-zero-not-zero
    (chain-step (Z∋ {A = ＇ Y₀} refl) chain) Z≡zero
    with store-chain-bind-suc-inv chain
store-chain-bind-zero-not-zero
    (chain-step (Z∋ {A = ＇ Y₀} refl) chain) ()
    | Z₀ , refl , chain₀
store-chain-bind-zero-not-zero
    (chain-step (Z∋ {A = ‵ ι} ()) chain) Z≡zero
store-chain-bind-zero-not-zero
    (chain-step (Z∋ {A = ★} ()) chain) Z≡zero
store-chain-bind-zero-not-zero
    (chain-step (Z∋ {A = A ⇒ B} ()) chain) Z≡zero
store-chain-bind-zero-not-zero
    (chain-step (Z∋ {A = `∀ A} ()) chain) Z≡zero

store-chain-distinct : ∀ {Δ} {Σ : TyStore Δ} {X Z}
  → StoreChain Σ X Z
  → Z ≢ X
store-chain-distinct {Σ = store-lift Σ} {X = Fin.zero}
    (chain-one ())
store-chain-distinct {Σ = store-lift Σ} {X = Fin.zero}
    (chain-step () chain)
store-chain-distinct {Σ = store-lift Σ} {X = Fin.suc X} chain eq
    with store-chain-lift-inv chain
store-chain-distinct {Σ = store-lift Σ} {X = Fin.suc X} chain eq
    | Z₀ , refl , chain₀ =
  store-chain-distinct chain₀ (fin-suc-injective eq)
store-chain-distinct {Σ = store-bind Σ C} {X = Fin.zero} chain eq =
  store-chain-bind-zero-not-zero chain eq
store-chain-distinct {Σ = store-bind Σ C} {X = Fin.suc X} chain eq
    with store-chain-bind-suc-inv chain
store-chain-distinct {Σ = store-bind Σ C} {X = Fin.suc X} chain eq
    | Z₀ , refl , chain₀ =
  store-chain-distinct chain₀ (fin-suc-injective eq)

store-chain-unaligned : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {X₀ X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → StoreChain (sourceStoreʷ W) X₀ X
  → toRenameᵗ (ηᴸʷ W) X₀ ≡ toRenameᵗ (ηᴿʷ W) Y
  → toRenameᵗ (ηᴸʷ W) X
      ≢ toRenameᵗ (ηᴿʷ W) Y
store-chain-unaligned {W = W} {X₀ = X₀} chain root-aligned aligned =
  store-chain-distinct chain
    (toRenameᵗ-injective (ηᴸʷ W)
      (trans aligned (sym root-aligned)))

source-chain-target-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ Wᵖ : World Δᴸ Δᴿ Δ}
    {Xᴸ X X₂ : TyVar Δᴸ} {Y Y₁ : TyVar Δᴿ}
  → CTX.RebaseAt W′ W Xᴸ Y
  → CTX.RebaseAt Wᵖ W′ X Y₁
  → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X)
  → sourceStoreʷ W′ ∋ X ⦂ (＇ X₂)
  → (＇ X₂) ⊑ᵂ⟨ Wᵖ ⟩ (＇ Y)
  → (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → ⊥
source-chain-target-⊥ {W = W} {W′ = W′} {Wᵖ = Wᵖ}
    {Xᴸ = Xᴸ} {X = X} {X₂ = X₂} {Y = Y} ra rb X∈ X∈′ p q =
  store-chain-unaligned {W = W} chain
    (variable-obligation-aligns {W = W} {X = Xᴸ} {Y = Y} q)
    aligned-end
  where
  X∈′W : sourceStoreʷ W ∋ X ⦂ (＇ X₂)
  X∈′W = rebase-source-membership-back ra X∈′

  chain : StoreChain (sourceStoreʷ W) Xᴸ X₂
  chain = chain-step X∈ (chain-one X∈′W)

  X₂≢Xᴸ : X₂ ≢ Xᴸ
  X₂≢Xᴸ = store-chain-distinct chain

  X₂≢X : X₂ ≢ X
  X₂≢X = store-variable-distinct X∈′

  aligned-end :
    toRenameᵗ (ηᴸʷ W) X₂ ≡ toRenameᵗ (ηᴿʷ W) Y
  aligned-end =
    trans (CTX.RebaseAt.ηᴸ-off-pivot ra X₂≢Xᴸ)
      (trans (CTX.RebaseAt.ηᴸ-off-pivot rb X₂≢X)
        (trans (variable-obligation-aligns
          {W = Wᵖ} {X = X₂} {Y = Y} p)
          (trans (sym (CTX.RebaseAt.ηᴿ-frozen rb Y))
            (sym (CTX.RebaseAt.ηᴿ-frozen ra Y)))))

source-chain-frozen-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTX.RebaseAt W′ W Xᴸ Y
  → CTX.RebaseAt W₂ W′ X₂ Y
  → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X₂)
  → toRenameᵗ (ηᴸʷ W₂) X₂
      ≢ toRenameᵗ (ηᴸʷ W′) X₂
  → ⊥
source-chain-frozen-⊥ {W = W} {W′ = W′} {W₂ = W₂}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} ra′ link X∈ moved =
  store-variable-distinct X∈
    (toRenameᵗ-injective (ηᴸʷ W) same-center)
  where
  X₂≢Xᴸ : X₂ ≢ Xᴸ
  X₂≢Xᴸ = store-variable-distinct X∈

  same-center :
    toRenameᵗ (ηᴸʷ W) X₂ ≡ toRenameᵗ (ηᴸʷ W) Xᴸ
  same-center =
    trans (CTX.RebaseAt.ηᴸ-off-pivot ra′ X₂≢Xᴸ)
      (trans (CTX.RebaseAt.pivotAligned link)
        (trans (sym (CTX.RebaseAt.ηᴿ-frozen ra′ Y))
          (sym (CTX.RebaseAt.pivotAligned ra′))))

target-seal-rebase-source : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTX.RebaseAtᴿ W′ W (just Y)
  → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → CTX.RebaseAt W′ W X Y
target-seal-rebase-source {W = W} {X = X} {Y = Y}
    (CTX.rebase-varᴿ rb) q
    with toRenameᵗ-injective (ηᴸʷ W)
      (trans (CTX.RebaseAt.pivotAligned rb)
        (sym (variable-obligation-aligns {W = W} {X = X} {Y = Y} q)))
target-seal-rebase-source (CTX.rebase-varᴿ rb) q | refl = rb

rebase-pivot-obligation : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTX.RebaseAt W W′ X Y
  → (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y)
rebase-pivot-obligation {W′ = W′} {X = X} rb =
  subst≡
    (λ Z → impEnvʷ W′
      ⊢ ＇ (toRenameᵗ (ηᴸʷ W′) X) ⊑ ＇ Z)
    (CTX.RebaseAt.pivotAligned rb)
    X⊑X

aligned-functional : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
  → CTX.CenterAligned W X Y
  → CTX.CenterAligned W X Y′
  → Y ≡ Y′
aligned-functional {W = W} aligned aligned′ =
  toRenameᵗ-injective (ηᴿʷ W) (trans (sym aligned) aligned′)

rebase-target-functional : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
  → CTX.RebaseAt Wᵖ W X Y
  → CTX.RebaseAt Wᵖ W X Y′
  → Y ≡ Y′
rebase-target-functional {W = W} {X = X} rb rb′ =
  aligned-functional {W = W} {X = X}
    (CTX.RebaseAt.pivotAligned rb)
    (CTX.RebaseAt.pivotAligned rb′)

target-pedigree-unique : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y Yᵖ : TyVar Δᴿ}
  → CTX.RebaseAt Wᵖ W X Y
  → CTX.RebaseAt Wᵖ W X Yᵖ
  → Yᵖ ≡ Y
target-pedigree-unique rb rbᵖ =
  sym (rebase-target-functional rb rbᵖ)

tag-target-pedigree-unique : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y Yᵖ : TyVar Δᴿ}
  → CTX.RebaseAt Wᵖ W X Y
  → CTX.TagRebaseAtᴸ Wᵖ W (just X) (just Yᵖ)
  → Yᵖ ≡ Y
tag-target-pedigree-unique rb (CTX.tag-rebase-varᴸ rbᵖ) =
  target-pedigree-unique rb rbᵖ

star-source-nonstar-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {S : Ty Δᴿ}
  → ★ ⊑ᵂ⟨ W ⟩ S
  → NonStar S
  → ⊥
star-source-nonstar-⊥ {S = ＇ Y} () nonstar-X
star-source-nonstar-⊥ {S = ‵ ι} () nonstar-ι
star-source-nonstar-⊥ {S = A ⇒ B} () nonstar-⇒
star-source-nonstar-⊥ {S = `∀ A} () nonstar-∀

var-source-nonstar-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {S : Ty Δᴿ}
  → (＇ X) ⊑ᵂ⟨ W ⟩ S
  → NonVar S
  → NonStar S
  → ⊥
var-source-nonstar-⊥ {S = ＇ Y} q () nonstar-X
var-source-nonstar-⊥ {S = ‵ ι} () nonvar-base nonstar-ι
var-source-nonstar-⊥ {S = A ⇒ B} () nonvar-fun nonstar-⇒
var-source-nonstar-⊥ {S = `∀ A} () nonvar-all nonstar-∀

seal-target-nonstar-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
  → sourceStoreʷ W ∋ X ⦂ ★
  → CTX.RebaseAt W′ W X Y
  → targetStoreʷ W ∋ Y ⦂ S
  → NonVar S
  → NonStar S
  → ⊥
seal-target-nonstar-⊥ {W = W} {X = X} {Y = Y} {S = S}
    X∈ ra Y∈ Snv Sns =
  star-source-nonstar-⊥ {W = W} {S = S}
    (subst≡ (λ T → ★ ⊑ᵂ⟨ W ⟩ T)
      (SPT.resolveVar-nonvar Y∈ Snv)
      (subst≡
        (λ T → T ⊑ᵂ⟨ W ⟩ CTX.resolveVar (targetStoreʷ W) Y)
        (SPT.resolveVar-nonvar X∈ nonvar-star)
        (CTX.StoreRepImp.represented
          (CTX.RebaseAt.storeRepresentations ra))))
    Sns

-- Compose the outer seal rebase with an inner seal-transfer link when
-- the inner source pivot did not move.  The anchor reconstruction is
-- exactly the unmoved branch isolated by MovedLinkProbe.
composeSealRebase : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTX.RebaseAt W′ W Xᴸ Y
  → CTX.RebaseAt W₂ W′ X₂ Y
  → toRenameᵗ (ηᴸʷ W₂) X₂ ≡ toRenameᵗ (ηᴸʷ W′) X₂
  → CTX.RebaseAt W₂ W Xᴸ Y
composeSealRebase {Δᴸ = Δᴸ} {W = W} {W′ = W′} {W₂ = W₂}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} ra′ link agrees =
  CTX.rebase-at
    (CTX.same-runtime
      (trans (CTX.SameRuntime.sourceStore-same
        (CTX.RebaseAt.sameRuntime ra′))
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime link)))
      (trans (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime ra′))
        (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime link))))
    source-off target-frozen (CTX.RebaseAt.pivotAligned ra′)
    (CTX.RebaseAt.storeRepresentations ra′)
  where
  source-off : ∀ {Z} → Z ≢ Xᴸ
    → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
  source-off {Z} Z≠Xᴸ with Fin._≟_ Z X₂
  source-off {.X₂} X₂≠Xᴸ | yes refl =
    trans (CTX.RebaseAt.ηᴸ-off-pivot ra′ X₂≠Xᴸ) (sym agrees)
  source-off {Z} Z≠Xᴸ | no Z≠X₂ =
    trans (CTX.RebaseAt.ηᴸ-off-pivot ra′ Z≠Xᴸ)
      (CTX.RebaseAt.ηᴸ-off-pivot link Z≠X₂)

  target-frozen : ∀ Z
    → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
  target-frozen Z =
    trans (CTX.RebaseAt.ηᴿ-frozen ra′ Z)
      (CTX.RebaseAt.ηᴿ-frozen link Z)

inner-source-pivot-eq : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTX.RebaseAt W′ W Xᴸ Y
  → (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)
  → X₂ ≡ Xᴸ
inner-source-pivot-eq {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} rb q p
    with Fin._≟_ X₂ Xᴸ
inner-source-pivot-eq rb q p | yes refl = refl
inner-source-pivot-eq {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} rb q p | no X₂≢Xᴸ =
  ⊥-elim (X₂≢Xᴸ
    (toRenameᵗ-injective (ηᴸʷ W) same-center))
  where
  same-center :
    toRenameᵗ (ηᴸʷ W) X₂ ≡ toRenameᵗ (ηᴸʷ W) Xᴸ
  same-center =
    trans (CTX.RebaseAt.ηᴸ-off-pivot rb X₂≢Xᴸ)
      (trans (variable-obligation-aligns {W = W′} {X = X₂} {Y = Y} p)
        (trans (sym (CTX.RebaseAt.ηᴿ-frozen rb Y))
          (sym (variable-obligation-aligns
            {W = W} {X = Xᴸ} {Y = Y} q))))

composeSamePivotRebase : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTX.RebaseAt W′ W X Y
  → CTX.RebaseAt W₂ W′ X Y
  → CTX.RebaseAt W₂ W X Y
composeSamePivotRebase {W = W} {W′ = W′} {W₂ = W₂}
    {X = X} {Y = Y} rb₁ rb₂ =
  CTX.rebase-at
    (CTX.same-runtime
      (trans (CTX.SameRuntime.sourceStore-same
        (CTX.RebaseAt.sameRuntime rb₁))
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb₂)))
      (trans (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime rb₁))
        (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime rb₂))))
    source-off target-frozen (CTX.RebaseAt.pivotAligned rb₁)
    (CTX.RebaseAt.storeRepresentations rb₁)
  where
  source-off : ∀ {Z} → Z ≢ X
    → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
  source-off Z≢X =
    trans (CTX.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
      (CTX.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

  target-frozen : ∀ Z
    → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
  target-frozen Z =
    trans (CTX.RebaseAt.ηᴿ-frozen rb₁ Z)
      (CTX.RebaseAt.ηᴿ-frozen rb₂ Z)

composeOuterRebase : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
  → CTX.RebaseAt W′ W X Y
  → CTX.RebaseAt W₂ W′ X Y′
  → CTX.RebaseAt W₂ W X Y
composeOuterRebase {W = W} {W′ = W′} {W₂ = W₂}
    {X = X} {Y = Y} rb₁ rb₂ =
  CTX.rebase-at
    (CTX.same-runtime
      (trans (CTX.SameRuntime.sourceStore-same
        (CTX.RebaseAt.sameRuntime rb₁))
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb₂)))
      (trans (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime rb₁))
        (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime rb₂))))
    source-off target-frozen (CTX.RebaseAt.pivotAligned rb₁)
    (CTX.RebaseAt.storeRepresentations rb₁)
  where
  source-off : ∀ {Z} → Z ≢ X
    → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
  source-off Z≢X =
    trans (CTX.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
      (CTX.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

  target-frozen : ∀ Z
    → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
  target-frozen Z =
    trans (CTX.RebaseAt.ηᴿ-frozen rb₁ Z)
      (CTX.RebaseAt.ηᴿ-frozen rb₂ Z)

record OccupiedNonStarSourceSealResidual : Set₁ where
  field
    target-source-var-chain : ∀ {Δᴸ Δᴿ Δ}
        {W W′ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → SpineValue V
      → Value U
      → CTX.ImpEnvMono W W′
      → CTX.RebaseAt W′ W Xᴸ Y
      → CTX.SameCtx γ γ′
      → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X₂)
      → targetStoreʷ W ∋ Y ⦂ S
      → W′ ∣ γ′ ⊢² V ⊑ U ↓ Conversion.seal Y S ∶ p₂
      → W ∣ γ ⊢² V ↓ Conversion.seal Xᴸ (＇ X₂)
        ⊑ U ↓ Conversion.seal Y S ∶ q

tagged-target-nonvar-nonstar-spine-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ W ⟩ ★}
  → SpineValue V
  → NonVar A
  → NonStar A
  → W ∣ γ ⊢² V ⊑ (U ↓ Conversion.seal Y S) ⟨ cY ⟩ ∶ p
  → ⊥

open OccupiedNonStarSourceSealResidual public

tagged-target-nonvar-nonstar-spine-⊥ {W = W} {A = A} {Y = Y}
    sv Anv Ans (CTI2.⊑cast² {p = p} cY prem q)
    with SPT.right-var-obligation-view {W = W} {R = A} {Y = Y} p
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {A = A} {Y = Y}
    sv Anv Ans (CTI2.⊑cast² {p = p} cY prem q)
    | X₂ , refl , aligned
    with Anv
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {A = .(＇ X₂)}
    {Y = Y} sv Anv Ans
    (CTI2.⊑cast² {p = p} cY prem q)
    | X₂ , refl , aligned | ()
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {Y = Y}
    (sv-cast sv₀ inert) Anv Ans
    (CTI2.cast⊑cast² {p = p} c c′ prem q)
    with SPT.right-var-obligation-view {W = W} {Y = Y} p
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {Y = Y}
    (sv-cast sv₀ inert) Anv Ans
    (CTI2.cast⊑cast² {p = p} c c′ prem q)
    | X₂ , refl , aligned
    with SPT.var-consistency-view c
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {Y = Y}
    (sv-cast sv₀ inert) Anv Ans
    (CTI2.cast⊑cast² {p = p} c c′ prem q)
    | X₂ , refl , aligned | inj₁ refl
    with Anv
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {Y = Y}
    (sv-cast sv₀ inert) Anv Ans
    (CTI2.cast⊑cast² {p = p} c c′ prem q)
    | X₂ , refl , aligned | inj₁ refl | ()
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {Y = Y}
    (sv-cast sv₀ inert) Anv Ans
    (CTI2.cast⊑cast² {p = p} c c′ prem q)
    | X₂ , refl , aligned | inj₂ refl
    with Ans
tagged-target-nonvar-nonstar-spine-⊥ {W = W} {Y = Y}
    (sv-cast sv₀ inert) Anv Ans
    (CTI2.cast⊑cast² {p = p} c c′ prem q)
    | X₂ , refl , aligned | inj₂ refl | ()
tagged-target-nonvar-nonstar-spine-⊥ (sv-Λ sv₀) Anv Ans
    (CTI2.Λ⊑² Anv₀ z∈A liftγ vV target⊢ prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ Anv₀
    (nonvar-occurs-nonstar Anv₀ z∈A) prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-Λ sv₀) Anv Ans
    (CTI2.Λ⊑²-smart-comma Anv₀ z∈A liftW liftγ vV target⊢ prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ Anv₀
    (nonvar-occurs-nonstar Anv₀ z∈A) prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-cast sv₀ inj)
    Anv () (CTI2.cast⊑² c prem q)
tagged-target-nonvar-nonstar-spine-⊥ (sv-cast sv₀ fun)
    Anv Ans (CTI2.cast⊑² c prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-cast sv₀ all)
    Anv Ans (CTI2.cast⊑² c prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
tagged-target-nonvar-nonstar-spine-⊥
    (sv-cast {A = ＇ X} sv₀ (genᵥ A≢★ safe))
    Anv Ans (CTI2.cast⊑² c prem q)
    with SPT.var-consistency-view c
tagged-target-nonvar-nonstar-spine-⊥
    (sv-cast {A = ＇ X} sv₀ (genᵥ A≢★ safe))
    Anv Ans (CTI2.cast⊑² c prem q) | inj₁ ()
tagged-target-nonvar-nonstar-spine-⊥
    (sv-cast {A = ＇ X} sv₀ (genᵥ A≢★ safe))
    Anv Ans (CTI2.cast⊑² c prem q) | inj₂ ()
tagged-target-nonvar-nonstar-spine-⊥
    (sv-cast {A = ‵ ι} sv₀ (genᵥ A≢★ safe))
    Anv Ans (CTI2.cast⊑² c prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-base
    nonstar-ι prem
tagged-target-nonvar-nonstar-spine-⊥
    (sv-cast {A = ★} sv₀ (genᵥ A≢★ safe))
    Anv Ans (CTI2.cast⊑² c prem q) =
  ⊥-elim (A≢★ refl)
tagged-target-nonvar-nonstar-spine-⊥
    (sv-cast {A = A ⇒ B} sv₀ (genᵥ A≢★ safe))
    Anv Ans (CTI2.cast⊑² c prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥
    (sv-cast {A = `∀ A} sv₀ (genᵥ A≢★ safe))
    Anv Ans (CTI2.cast⊑² c prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-reveal-fun sv₀)
    Anv Ans (CTI2.reveal⊑² mono rb sc c⊢ prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-reveal-all sv₀)
    Anv Ans (CTI2.reveal⊑² mono rb sc c⊢ prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-conceal-fun sv₀)
    Anv Ans (CTI2.conceal⊑² mono rb sc c⊢ prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-conceal-all sv₀)
    Anv Ans (CTI2.conceal⊑² mono rb sc c⊢ prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
