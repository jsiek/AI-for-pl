module proof.DGG.ExtraCastRight2 where

-- File Charter:
--   * Ports the extra-cast-on-the-right development to the version-2
--     cast-term imprecision relation, in stages.
--   * Stage 1: the statements of extra-cast-right and its inst
--     catch-up companion as Set-level definitions, together with the
--     world-extension interface their conclusions need.  Compared with
--     version 1 the statement carries no transport function for the
--     source type: A : Ty Δᴸ is untouched by target-side allocation,
--     and only the world and the target types evolve.
--     The identity and inert-cast cases are proved directly with reusable
--     zero-change and one-keep world extensions.
--   * Stage 2: the right-injection inversion lemma, proved for spine
--     values: constants, lambdas, type abstractions, inert casts, and
--     function-shaped reveal/conceal wrappers.  Because obligations
--     are propositions (proof.Imprecision.⊑-unique), the free q of
--     the wrapper rules carries no information beyond its type, and
--     extending to ∀-shaped wrappers is a type-level inhabitation
--     question; see SpineValue for what remains.
--   * Binder-lifted world/rebase lemmas support the ∀-shaped frontier.
--     The identity-pivot universal reveal and conceal subcases are complete;
--     their conversion endpoints are equal and need no rebasing.
--     Bare seal is not reducible to obligation transport alone:
--     ExtraCastRight2Counterexample gives a checked configuration where
--     the input relation exists but every possible output relation after
--     target-tag cancellation is empty.  General bare-seal inversion needs
--     a stronger relation/world invariant or a restricted theorem domain.
--   * Version-2 pay-offs visible here: no renaming wrapper around the
--     relation, the Λ⊑² case recurses with the target data unchanged,
--     and the ground lemmas of proof.ImprecisionConsistency apply
--     directly to world-embedded obligations.

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-lift; _∋_⦂_)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; keep; skip; toRenameᵗ;
   id; _!; ∀ᶜ_; gen_; inst_)
import Consistency as C
open import Conversion using
  (Conv↑; Conv↓; _⊢↓_; `∀↑_; `∀↓_; _↦↑_; _↦↓_; ⊢↓-seal)
open import Imprecision
open import Primitives using (Const; κℕ; κ𝔹)
open import CastTerms
open import Reduction
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.ConvImp using
  (pivot-id-endpoints↑; pivot-id-endpoints↓)
open CTI2 using
  (World; ηᴸʷ; ηᴿʷ; impEnvʷ; sourceStoreʷ; targetStoreʷ; embedᴿ;
   _⊑ᵂ⟨_⟩_; CtxImp; ctx-imp; _∣_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; source-occurs-target; rename-occurs;
   ext-injective; toRenameᵗ-injective; nonstar-from-≢★; rename-⊑;
   fin-suc-injective)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using (toRename-keep-eq)

------------------------------------------------------------------------
-- Target polymorphic value views (for the inst catch-up statement)
------------------------------------------------------------------------

data AllValueView {Δ : TyCtx} (V : Term Δ) : Set where
  allv-Λ : ∀ {W}
    → Value W
    → V ≡ Λ W
    → AllValueView V

  allv-∀ : ∀ {μ : Env∼ Δ} {W} {A B : Ty (suc Δ)}
      {c : C.extᵐ μ ⊢ A ∼ B}
    → Value W
    → V ≡ W ⟨ ∀ᶜ c ⟩
    → AllValueView V

  allv-gen : ∀ {μ : Env∼ Δ} {W} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : C.genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    → Value W
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → V ≡ W ⟨ (gen c) A≢★ ⟩
    → AllValueView V

  allv-reveal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↑ (suc Δ) A B}
    → Value W
    → V ≡ W ↑ `∀↑ c
    → AllValueView V

  allv-conceal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↓ (suc Δ) A B}
    → Value W
    → V ≡ W ↓ `∀↓ c
    → AllValueView V

------------------------------------------------------------------------
-- Stage 1: statements
------------------------------------------------------------------------

-- A right-side world extension: the source store is untouched, the
-- target store follows the machine's store changes, and every type
-- obligation transports with the change.

record WorldExtendᴿ {Δᴸ Δᴿ Δᴿ′ Δ Δ′} (χs : StoreChanges Δᴿ Δᴿ′)
    (W : World Δᴸ Δᴿ Δ) (W′ : World Δᴸ Δᴿ′ Δ′) : Set where
  field
    sourceStore-kept : sourceStoreʷ W′ ≡ sourceStoreʷ W
    targetStore-follows : targetStoreʷ W′ ≡ (χs ▶ˢ targetStoreʷ W)
    transport⊑ᵂ : ∀ {A : Ty Δᴸ} {C : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ C
      → A ⊑ᵂ⟨ W′ ⟩ (χs ▶ᵗ C)

open WorldExtendᴿ public

sameWorldExtendᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → WorldExtendᴿ [] W W
sameWorldExtendᴿ = record
  { sourceStore-kept = refl
  ; targetStore-follows = refl
  ; transport⊑ᵂ = λ p → p
  }

sameWorldKeepExtendᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → WorldExtendᴿ (Reduction.keep ∷ []) W W
sameWorldKeepExtendᴿ = record
  { sourceStore-kept = refl
  ; targetStore-follows = refl
  ; transport⊑ᵂ = λ p → p
  }

mapCtxᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′} {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → WorldExtendᴿ χs W W′
  → CtxImp W
  → CtxImp W′
mapCtxᴿ ext [] = []
mapCtxᴿ {χs = χs} ext (ctx-imp A B p ∷ γ) =
  ctx-imp A (χs ▶ᵗ B) (transport⊑ᵂ ext p) ∷ mapCtxᴿ ext γ

mapCtxᴿ-same : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    (γ : CtxImp W)
  → mapCtxᴿ sameWorldExtendᴿ γ ≡ γ
mapCtxᴿ-same [] = refl
mapCtxᴿ-same (ctx-imp A B p ∷ γ) = cong (_ ∷_) (mapCtxᴿ-same γ)

mapCtxᴿ-keep : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    (γ : CtxImp W)
  → mapCtxᴿ sameWorldKeepExtendᴿ γ ≡ γ
mapCtxᴿ-keep [] = refl
mapCtxᴿ-keep (ctx-imp A B p ∷ γ) = cong (_ ∷_) (mapCtxᴿ-keep γ)

-- Extra cast on the right: if related values face an extra target
-- cast, the target alone reduces to a value in an extended world that
-- still relates them.

ExtraCastRight² : Set
ExtraCastRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))

-- The inst catch-up companion: instantiating a polymorphic target
-- value allocates on the right and reduces to a value related in the
-- extended world.

InstCatchupRight² : Set
InstCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : C.instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))

-- Inert target casts are already values, so this direct case of
-- extra-cast-right neither changes the target store nor the world.

inert-extra-cast-right² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → (vM′ : Value M′)
  → (c′ : ν ⊢ B ∼ B′)
  → Inert c′
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))
inert-extra-cast-right² {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ c′ inert q =
  Δᴿ , [] , Δ , W , sameWorldExtendᴿ , M′ ⟨ c′ ⟩ ,
  vM′ 《 inert 》 ,
  (M′ ⟨ c′ ⟩ ∎[]) ,
  subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q)
    (sym (mapCtxᴿ-same γ)) (CTI2.⊑cast² c′ M⊑M′ q)

-- An identity cast takes one pure keep step and leaves the original target
-- value.  The input and requested obligations coincide propositionally.

id-extra-cast-right² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → (vM′ : Value M′)
  → (a : Atom B)
  → (q : A ⊑ᵂ⟨ W ⟩ B)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ id {μ = ν} a ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))
id-extra-cast-right² {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M′ = M′} {p = p} M⊑M′ vM vM′ a q =
  Δᴿ , Reduction.keep ∷ [] , Δ , W , sameWorldKeepExtendᴿ , M′ ,
  vM′ ,
  (M′ ⟨ id a ⟩
    —→[ Reduction.keep ]⟨ pure-step (β-id vM′) ⟩
  M′ ∎[]) ,
  subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ M′ ∶ q)
    (sym (mapCtxᴿ-keep γ))
    (subst≡ (λ r → W ∣ γ ⊢² M ⊑ M′ ∶ r) (PI.⊑-unique p q) M⊑M′)

------------------------------------------------------------------------
-- Stage 2: helpers
------------------------------------------------------------------------

renameᵗ-skip-eq : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (skip η)) B ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) B)
renameᵗ-skip-eq η B =
  trans (renameᵗ-cong B (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc B))

-- The ∀⊑ view of a world obligation for `∀ A against B is exactly a
-- premise for the left-only lifted world: the instᵐ environment is the
-- lifted world's environment, and B's embedding gains one shift.

liftWorldLeft-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
  → instᵐ (impEnvʷ W)
      ⊢ renameᵗ (extᵗ (toRenameᵗ (ηᴸʷ W))) A ⊑ ⇑ᵗ (embedᴿ W B)
  → A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B
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

liftWorldBoth-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {v : VarImp}
  → A ⊑ᵂ⟨ W ⟩ B
  → ⇑ᵗ A ⊑ᵂ⟨ CTI2.liftWorldBoth v W ⟩ ⇑ᵗ B
liftWorldBoth-⊑ᵂ {W = W} {A = A} {B = B} {v = v} p =
  subst≡
    (λ L → impEnvʷ (CTI2.liftWorldBoth v W) ⊢ L ⊑
      embedᴿ (CTI2.liftWorldBoth v W) (⇑ᵗ B))
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq (ηᴸʷ W)))
                (renameᵗ-shift (toRenameᵗ (ηᴸʷ W)) A)))
    (subst≡
      (λ R → impEnvʷ (CTI2.liftWorldBoth v W) ⊢
        ⇑ᵗ (CTI2.embedᴸ W A) ⊑ R)
      (sym (trans (renameᵗ-cong (⇑ᵗ B) (toRename-keep-eq (ηᴿʷ W)))
                  (renameᵗ-shift (toRenameᵗ (ηᴿʷ W)) B)))
      (rename-⊑ Fin.suc fin-suc-injective (λ _ eq → eq) p))

-- Rebasing is stable under a binder introduced on both sides.  This is
-- the world-level counterpart of the shifted-pivot conversion rules.

liftRebaseAt : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {v : VarImp}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.RebaseAt (CTI2.liftWorldBoth v W)
      (CTI2.liftWorldBoth v W′) (Fin.suc Xᴸ) (Fin.suc Xᴿ)
liftRebaseAt {W = W} {W′ = W′} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} {v = v} rb =
  CTI2.rebase-at
    (CTI2.same-runtime
      (cong store-lift
        (CTI2.SameRuntime.sourceStore-same (CTI2.RebaseAt.sameRuntime rb)))
      (cong store-lift
        (CTI2.SameRuntime.targetStore-same (CTI2.RebaseAt.sameRuntime rb))))
    source-off target-off
    (cong Fin.suc (CTI2.RebaseAt.pivotAligned rb))
    (CTI2.store-rep-imp lift-represented)
  where
  old-represented =
    CTI2.StoreRepImp.represented
      (CTI2.RebaseAt.storeRepresentations rb)

  renamed-represented =
    rename-⊑ Fin.suc fin-suc-injective (λ _ eq → eq) old-represented

  lift-represented :
    CTI2.resolveVar
        (sourceStoreʷ (CTI2.liftWorldBoth v W′)) (Fin.suc Xᴸ)
      ⊑ᵂ⟨ CTI2.liftWorldBoth v W′ ⟩
    CTI2.resolveVar
        (targetStoreʷ (CTI2.liftWorldBoth v W′)) (Fin.suc Xᴿ)
  lift-represented =
    subst≡
      (λ L → impEnvʷ (CTI2.liftWorldBoth v W′) ⊢ L ⊑
        embedᴿ (CTI2.liftWorldBoth v W′)
          (⇑ᵗ (CTI2.resolveVar (targetStoreʷ W′) Xᴿ)))
      (sym (trans
        (renameᵗ-cong (⇑ᵗ (CTI2.resolveVar (sourceStoreʷ W′) Xᴸ))
          (toRename-keep-eq (ηᴸʷ W′)))
        (renameᵗ-shift (toRenameᵗ (ηᴸʷ W′))
          (CTI2.resolveVar (sourceStoreʷ W′) Xᴸ))))
      (subst≡
        (λ R → impEnvʷ (CTI2.liftWorldBoth v W′) ⊢
          ⇑ᵗ (CTI2.embedᴸ W′
            (CTI2.resolveVar (sourceStoreʷ W′) Xᴸ)) ⊑ R)
        (sym (trans
          (renameᵗ-cong (⇑ᵗ (CTI2.resolveVar (targetStoreʷ W′) Xᴿ))
            (toRename-keep-eq (ηᴿʷ W′)))
          (renameᵗ-shift (toRenameᵗ (ηᴿʷ W′))
            (CTI2.resolveVar (targetStoreʷ W′) Xᴿ))))
        renamed-represented)

  source-off : ∀ {Y}
    → Y ≢ Fin.suc Xᴸ
    → toRenameᵗ (ηᴸʷ (CTI2.liftWorldBoth v W′)) Y
        ≡ toRenameᵗ (ηᴸʷ (CTI2.liftWorldBoth v W)) Y
  source-off {Fin.zero} Y≢ = refl
  source-off {Fin.suc Y} Y≢ =
    cong Fin.suc
      (CTI2.RebaseAt.ηᴸ-off-pivot rb
        (λ eq → Y≢ (cong Fin.suc eq)))

  target-off : ∀ {Y}
    → Y ≢ Fin.suc Xᴿ
    → toRenameᵗ (ηᴿʷ (CTI2.liftWorldBoth v W′)) Y
        ≡ toRenameᵗ (ηᴿʷ (CTI2.liftWorldBoth v W)) Y
  target-off {Fin.zero} Y≢ = refl
  target-off {Fin.suc Y} Y≢ =
    cong Fin.suc
      (CTI2.RebaseAt.ηᴿ-off-pivot rb
        (λ eq → Y≢ (cong Fin.suc eq)))


liftPivot : ∀ {Δ} → Maybe (TyVar Δ) → Maybe (TyVar (suc Δ))
liftPivot nothing = nothing
liftPivot (just X) = just (Fin.suc X)

liftRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {v : VarImp}
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → CTI2.RebaseAtᴸ (CTI2.liftWorldBoth v W)
      (CTI2.liftWorldBoth v W′) (liftPivot Xᴸ?)
liftRebaseAtᴸ CTI2.rebase-idᴸ = CTI2.rebase-idᴸ
liftRebaseAtᴸ (CTI2.rebase-varᴸ rb) =
  CTI2.rebase-varᴸ (liftRebaseAt rb)
liftRebaseAtᴸ {Δᴿ = Δᴿ} {W = W} {v = v}
    (CTI2.rebase-onlyᴸ {Xᴸ = Xᴸ} to-star disaligned represented) =
  CTI2.rebase-onlyᴸ to-star lifted-disaligned
    (liftWorldBoth-⊑ᵂ
      {W = W} {A = CTI2.resolveVar (sourceStoreʷ W) Xᴸ}
      {B = ★} {v = v}
      represented)
  where
  lifted-disaligned : ∀ (Xᴿ : TyVar (suc Δᴿ))
    → toRenameᵗ (ηᴿʷ (CTI2.liftWorldBoth v W)) Xᴿ
        ≢ toRenameᵗ (ηᴸʷ (CTI2.liftWorldBoth v W)) (Fin.suc Xᴸ)
  lifted-disaligned Fin.zero ()
  lifted-disaligned (Fin.suc Xᴿ) eq =
    disaligned Xᴿ (fin-suc-injective eq)

------------------------------------------------------------------------
-- Canonical target values at an abstract variable
------------------------------------------------------------------------

data VarValueView {Δ : TyCtx} (Σ : TyStore Δ) (V : Term Δ)
    (X : TyVar Δ) : Set where
  varv-seal : ∀ {W R}
    → Value W
    → Σ ∋ X ⦂ R
    → V ≡ W ↓ Conversion.seal X R
    → VarValueView Σ V X

var-value-view : ∀ {Δ} {Σ : TyStore Δ} {Γ} {V : Term Δ} {X}
  → Value V
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ ＇ X
  → VarValueView Σ V X
var-value-view (ƛ N) ()
var-value-view (Λ vV) ()
var-value-view ($ (κℕ n)) ()
var-value-view ($ (κ𝔹 b)) ()
var-value-view (vV 《 inj 》) ()
var-value-view (vV 《 fun 》) ()
var-value-view (vV 《 all 》) ()
var-value-view (vV 《 genᵥ A≢★ safe 》) ()
var-value-view (vV ↑ fun) ()
var-value-view (vV ↑ all) ()
var-value-view (vV ↓ seal) (⊢conceal (⊢↓-seal X∈) V⊢) =
  varv-seal vV X∈ refl
var-value-view (vV ↓ fun) ()
var-value-view (vV ↓ all) ()

tag-inner-typing : ∀ {Δ} {Σ : TyStore Δ} {Γ} {N : Term Δ}
    {H : Ty Δ} {ν : Env∼ Δ}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
  → ⟨ Δ , Σ , Γ ⟩ ⊢
      N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ⦂ ★
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N ⦂ H
tag-inner-typing (⊢⟨⟩ N⊢ cH!) = N⊢

right-tag-variable-view : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ}
    {H∼★ : ν ⊢ (＇ Y) ∼★} {Hns : NonStar (＇ Y)}
    {cH : ν ⊢ (＇ Y) ∼ (＇ Y)} {p : A ⊑ᵂ⟨ W ⟩ ★}
  → Value N
  → W ∣ γ ⊢² M
      ⊑ N ⟨ _! ⦃ ＇ Y ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → VarValueView (targetStoreʷ W) N Y
right-tag-variable-view vN M⊑N! =
  var-value-view vN (tag-inner-typing (CTI2T.target-typing² M⊑N!))

variable-imprecision-aligns : ∀ {Δ} {μ : ImpEnv Δ} {X Y : TyVar Δ}
  → μ ⊢ ＇ X ⊑ ＇ Y
  → X ≡ Y
variable-imprecision-aligns X⊑X = refl

variable-obligation-aligns : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
  → toRenameᵗ (ηᴸʷ W) X ≡ toRenameᵗ (ηᴿʷ W) Y
variable-obligation-aligns q = variable-imprecision-aligns q

-- If a source seal's result is related to a target variable, a left rebase
-- cannot be the disaligned rebase-onlyᴸ case.  Its paired pivot is exactly
-- that target variable.

seal-rebase-target : ∀ {Δᴸ Δᴿ Δ} {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTI2.RebaseAtᴸ Wᵖ W (just X)
  → ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
  → CTI2.RebaseAt Wᵖ W X Y
seal-rebase-target {W = W} {X = X} {Y = Y}
    (CTI2.rebase-varᴸ {Xᴿ = Xᴿ} rb) q
    with toRenameᵗ-injective (ηᴿʷ W)
      (trans (sym (CTI2.RebaseAt.pivotAligned rb))
        (variable-obligation-aligns {W = W} {X = X} {Y = Y} q))
seal-rebase-target (CTI2.rebase-varᴸ rb) q | refl = rb
seal-rebase-target
    {W = W} {X = X} {Y = Y}
    (CTI2.rebase-onlyᴸ to-star disaligned represented) q =
  ⊥-elim
    (disaligned Y
      (sym (variable-obligation-aligns {W = W} {X = X} {Y = Y} q)))

-- A source seal related to a variable-tagged target determines both sides
-- of the matching outer boundary.  The target value must itself be sealed
-- at that variable, and the source's nominally one-sided rebase is the
-- corresponding paired rebase.

seal-tag-boundary-view² : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ} {R : Ty Δᴸ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ}
    {H∼★ : ν ⊢ (＇ Y) ∼★} {Hns : NonStar (＇ Y)}
    {cH : ν ⊢ (＇ Y) ∼ (＇ Y)} {p : ＇ X ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.RebaseAtᴸ Wᵖ W (just X)
  → Value N
  → W ∣ γ ⊢² M ↓ Conversion.seal X R
      ⊑ N ⟨ _! ⦃ ＇ Y ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y)
  → Σ[ U ∈ Term Δᴿ ] Σ[ S ∈ Ty Δᴿ ]
      (Value U
        × (targetStoreʷ W ∋ Y ⦂ S)
        × (N ≡ U ↓ Conversion.seal Y S)
        × CTI2.RebaseAt Wᵖ W X Y)
seal-tag-boundary-view² rb vN M↓X⊑N! q
    with right-tag-variable-view vN M↓X⊑N!
seal-tag-boundary-view² rb vN M↓X⊑N! q
    | varv-seal {W = U} {R = S} vU Y∈ refl =
  U , S , vU , Y∈ , refl , seal-rebase-target rb q

------------------------------------------------------------------------
-- Stage 2: right-injection inversion for spine values
------------------------------------------------------------------------

-- Values whose spine contains no ∀-shaped conversion wrapper and no
-- bare seal.  Function-shaped reveal and conceal wrappers are fine:
-- their pre-conversion tag obligation rebuilds from the ⇒⊑★ view of
-- the premise index, so no transport along the conversion is needed.
-- Since obligations are propositions (proof.Imprecision.⊑-unique),
-- extending to the remaining wrappers is a type-level inhabitation
-- question: an obligation-transport lemma along the pivot-indexed
-- conversion typing.  Its ∀-cases need occurrence transport along
-- conversions.  Until that lemma exists, ∀-shaped wrappers are open.
-- Bare seals are excluded for a stronger reason: the checked
-- ExtraCastRight2Counterexample refutes unrestricted relational inversion.

data SpineValue {Δ : TyCtx} : Term Δ → Set where
  sv-ƛ : (N : Term Δ) → SpineValue (ƛ N)

  sv-Λ : ∀ {V} → SpineValue V → SpineValue (Λ V)

  sv-$ : (κ : Const) → SpineValue ($ κ)

  sv-cast : ∀ {V} {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → SpineValue V → Inert c → SpineValue (V ⟨ c ⟩)

  sv-reveal-fun : ∀ {V} {A A′ B B′ : Ty Δ}
      {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
    → SpineValue V → SpineValue (V ↑ (c ↦↑ d))

  sv-conceal-fun : ∀ {V} {A A′ B B′ : Ty Δ}
      {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
    → SpineValue V → SpineValue (V ↓ (c ↦↓ d))

-- If a spine value is related to a tagged target value, the tag can be
-- peeled off the target at any obligation for the tag's ground type.

right-inj-inversion² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ} {A : Ty Δᴸ} {H : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
    {p : A ⊑ᵂ⟨ W ⟩ ★}
  → SpineValue M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : A ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² M ⊑ N ∶ q

-- Target-only cast: the premise already carries the tag obligation.
right-inj-inversion² sv vN (CTI2.⊑cast² {p = p₀} c′ prem q₀) q =
  subst≡ (λ r → _ ∣ _ ⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p₀ q) prem

-- Paired cast: keep the source cast as a source-only cast.
right-inj-inversion² sv vN (CTI2.cast⊑cast² c c′ prem q₀) q =
  CTI2.cast⊑² c prem q

-- Source-only cast around an injection value: no obligation matches.
right-inj-inversion² {gH = ＇ Y} (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ‵ ι} (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ★⇒★} (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ∀★} (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()

-- Source-only function cast: the premise components rebuild the
-- premise-level tag obligation.
right-inj-inversion² {gH = ★⇒★} (sv-cast sv fun)
    vN (CTI2.cast⊑² {p = ⇒⊑★ pA pB} c prem q₀) (⇒⊑⇒ qA qB) =
  CTI2.cast⊑² c
    (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ＇ Y} (sv-cast sv fun)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ‵ ι} (sv-cast sv fun)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ∀★} (sv-cast sv fun)
  vN (CTI2.cast⊑² c prem q₀) ()

-- Source-only universal cast: chase the tag through the cast with the
-- embedded consistency evidence.
right-inj-inversion² {W = W} {gH = gH} (sv-cast sv (all {c = c₁}))
    vN (CTI2.cast⊑² {p = p₀} .(∀ᶜ c₁) prem q₀) q =
  CTI2.cast⊑² (∀ᶜ c₁)
    (right-inj-inversion² sv vN prem
      (ground-cast-source⊑ (C.renameGroundᵐ (ηᴿʷ W) gH) nonstar-∀
        (C.renameᵐᶜ (ηᴸʷ W) (∀ᶜ c₁)) p₀ q₀ q))
    q

-- Source-only generalization cast: same, with the gen tag's source.
right-inj-inversion² {W = W} {gH = gH} (sv-cast sv (genᵥ A≢★ safe))
    vN (CTI2.cast⊑² {p = p₀} c prem q₀) q =
  CTI2.cast⊑² c
    (right-inj-inversion² sv vN prem
      (ground-cast-source⊑ (C.renameGroundᵐ (ηᴿʷ W) gH)
        (C.renameNonStar (toRenameᵗ (ηᴸʷ W)) (nonstar-from-≢★ A≢★))
        (C.renameᵐᶜ (ηᴸʷ W) c) p₀ q₀ q))
    q

-- Type abstraction against a non-∀ ground: only the ∀⊑ view is
-- possible, and its body is exactly a left-only lifted premise.
right-inj-inversion² {W = W} {gH = ＇ Y} (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ＇ Y} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ‵ ι} (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ‵ ι} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ★⇒★} (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ★ ⇒ ★} body))
    (∀⊑ Anv′ z∈A′ body)

-- Type abstraction against the ∀★ ground.  The Λ⊑² occurrence premise
-- exposes the body's head, which rules out bot-elim, refutes ∀⊑∀ by
-- occurrence preservation, and leaves the ∀⊑ rebuild.
right-inj-inversion² {gH = ∀★} (sv-Λ sv)
  vN (CTI2.Λ⊑² () var-∈ liftγ vV M′⊢ prem q₀) q
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-left z∈) liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV N⊢
    (right-inj-inversion² sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-fun-left z∈))
... | ()
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-right z∉ z∈) liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV N⊢
    (right-inj-inversion² sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-fun-right z∉ z∈))
... | ()
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv (∈-all z∈) liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-all z∈) liftγ vV N⊢
    (right-inj-inversion² sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑² Anv (∈-all z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-all z∈))
... | ()

-- Function-shaped reveal: the premise's ⇒⊑★ components rebuild the
-- premise-level tag obligation, and by ⊑-unique it does not matter
-- that this inhabitant differs from any other.
right-inj-inversion² {gH = ★⇒★} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑² {p = ⇒⊑★ pA pB} mono rb sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.reveal⊑² mono rb sc ⊢c
    (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ＇ Y} (sv-reveal-fun sv)
  vN (CTI2.reveal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ‵ ι} (sv-reveal-fun sv)
  vN (CTI2.reveal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ∀★} (sv-reveal-fun sv)
  vN (CTI2.reveal⊑² _ _ _ _ _ _) ()

-- Function-shaped conceal: same construction.
right-inj-inversion² {gH = ★⇒★} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑² {p = ⇒⊑★ pA pB} mono rb sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.conceal⊑² mono rb sc ⊢c
    (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ＇ Y} (sv-conceal-fun sv)
  vN (CTI2.conceal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ‵ ι} (sv-conceal-fun sv)
  vN (CTI2.conceal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ∀★} (sv-conceal-fun sv)
  vN (CTI2.conceal⊑² _ _ _ _ _ _) ()

-- Type applications are not spine values.
right-inj-inversion² () vN (CTI2.•⊑² _ _ _ _) q

------------------------------------------------------------------------
-- Identity-pivot universal wrappers
------------------------------------------------------------------------

-- These are the complete nothing-pivot subcases of the two universal
-- wrapper branches.  Their body conversions have equal endpoints and the
-- wrapper world is definitionally unchanged, so ordinary index transport
-- exposes the recursive injection obligation.

right-inj-reveal-all-id² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ γ′ : CtxImp W}
    {V : Term Δᴸ} {N : Term Δᴿ}
    {A B : Ty (suc Δᴸ)} {H : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {c : Conv↑ (suc Δᴸ) A B}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H} {p : `∀ A ⊑ᵂ⟨ W ⟩ ★}
  → SpineValue V
  → Value N
  → CTI2.SameCtx γ γ′
  → store-lift (sourceStoreʷ W) CTI2.⊢↑[ nothing ] c
  → W ∣ γ′ ⊢² V
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : `∀ B ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² V ↑ `∀↑ c ⊑ N ∶ q
right-inj-reveal-all-id² {W = W} {A = A} {B = B}
    {H = H} {c = c} sv vN sc c⊢ prem q =
  CTI2.reveal⊑² (λ _ eq → eq) CTI2.rebase-idᴸ sc (CTI2.⊢↑-∀-idˣ c⊢)
    (right-inj-inversion² sv vN prem
      (subst≡ (λ T → T ⊑ᵂ⟨ W ⟩ H)
        (sym (cong `∀ (pivot-id-endpoints↑ c⊢))) q))
    q

right-inj-conceal-all-id² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ γ′ : CtxImp W}
    {V : Term Δᴸ} {N : Term Δᴿ}
    {A B : Ty (suc Δᴸ)} {H : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {c : Conv↓ (suc Δᴸ) A B}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H} {p : `∀ A ⊑ᵂ⟨ W ⟩ ★}
  → SpineValue V
  → Value N
  → CTI2.SameCtx γ γ′
  → store-lift (sourceStoreʷ W) CTI2.⊢↓[ nothing ] c
  → W ∣ γ′ ⊢² V
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : `∀ B ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² V ↓ `∀↓ c ⊑ N ∶ q
right-inj-conceal-all-id² {W = W} {A = A} {B = B}
    {H = H} {c = c} sv vN sc c⊢ prem q =
  CTI2.conceal⊑² (λ _ eq → eq) CTI2.rebase-idᴸ sc (CTI2.⊢↓-∀-idˣ c⊢)
    (right-inj-inversion² sv vN prem
      (subst≡ (λ T → T ⊑ᵂ⟨ W ⟩ H)
        (sym (cong `∀ (pivot-id-endpoints↓ c⊢))) q))
    q
