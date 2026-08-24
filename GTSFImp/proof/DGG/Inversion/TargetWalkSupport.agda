module proof.DGG.Inversion.TargetWalkSupport where

-- File Charter:
--   * Houses the proven store, world-lifting, and rebase helpers shared by
--     higher-order right-injection and target strip/descent proofs.
--   * Keeps only support with a live proof or checked-fixture consumer.
--   * Does not depend on the legacy source-strip, target-walk, or target-chain
--     proof surfaces.

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
  (Conv↑; Conv↓; `∀↑_; `∀↓_; _↦↑_; _↦↓_)
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

store-lookup-unique : ∀ {Δ} {Σ : TyStore Δ} {X A B}
  → Σ ∋ X ⦂ A
  → Σ ∋ X ⦂ B
  → A ≡ B
store-lookup-unique (Z∋ eq) (Z∋ eq′) = trans eq (sym eq′)
store-lookup-unique (S-lift∋ X∈ eq) (S-lift∋ X∈′ eq′) =
  trans eq (trans (cong ⇑ᵗ (store-lookup-unique X∈ X∈′)) (sym eq′))
store-lookup-unique (S-bind∋ X∈ eq) (S-bind∋ X∈′ eq′) =
  trans eq (trans (cong ⇑ᵗ (store-lookup-unique X∈ X∈′)) (sym eq′))

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

star-source-nonstar-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {S : Ty Δᴿ}
  → ★ ⊑ᵂ⟨ W ⟩ S
  → NonStar S
  → ⊥
star-source-nonstar-⊥ {S = ＇ Y} () nonstar-X
star-source-nonstar-⊥ {S = ‵ ι} () nonstar-ι
star-source-nonstar-⊥ {S = A ⇒ B} () nonstar-⇒
star-source-nonstar-⊥ {S = `∀ A} () nonstar-∀

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
    Anv Ans
    (CTI2.reveal⊑-identity c⊢ position≡absent prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-reveal-all sv₀)
    Anv Ans
    (CTI2.reveal⊑-identity c⊢ position≡absent prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-reveal-fun sv₀)
    Anv Ans
    (CTI2.reveal⊑-only² c⊢ position≢absent dynamic no-target
      represented prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-reveal-all sv₀)
    Anv Ans
    (CTI2.reveal⊑-only² c⊢ position≢absent dynamic no-target
      represented prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-reveal-fun sv₀)
    Anv Ans
    (CTI2.reveal⊑² c⊢ position≢absent target-member represented
      mono rb sc prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-reveal-all sv₀)
    Anv Ans
    (CTI2.reveal⊑² c⊢ position≢absent target-member represented
      mono rb sc prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-conceal-fun sv₀)
    Anv Ans
    (CTI2.conceal⊑-identity c⊢ position≡absent prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-conceal-all sv₀)
    Anv Ans
    (CTI2.conceal⊑-identity c⊢ position≡absent prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-conceal-fun sv₀)
    Anv Ans
    (CTI2.conceal⊑² c⊢ position≢absent dynamic no-target
      represented prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-fun
    nonstar-⇒ prem
tagged-target-nonvar-nonstar-spine-⊥ (sv-conceal-all sv₀)
    Anv Ans
    (CTI2.conceal⊑² c⊢ position≢absent dynamic no-target
      represented prem q) =
  tagged-target-nonvar-nonstar-spine-⊥ sv₀ nonvar-all
    nonstar-∀ prem
