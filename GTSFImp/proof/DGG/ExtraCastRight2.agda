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
--   * Stage 2: the right-injection inversion lemma, proved for all value
--     spines: constants, lambdas, type abstractions, inert casts, seals,
--     and function- and ∀-shaped reveal/conceal wrappers.  Because
--     obligations are propositions (proof.Imprecision.⊑-unique),
--     the free q of the wrapper rules carries no information beyond
--     its type; TagTransport supplies the universal-wrapper obligation.
--   * Binder-lifted world/rebase lemmas support the ∀-shaped frontier.
--     Identity-pivot universal wrappers have equal conversion endpoints;
--     indexed pivots use the TagTransport occurrence lemmas.
--   * The inversion carries a WFWorld hypothesis and threads it by
--     decay: var-rebased wrapper cases move their premises into the
--     honestified premise world (WorldDecay/TermImpDecay) before
--     recursing, which is the general form of the counterexample
--     repair recorded in ExtraCastRight2Counterexample.
--   * Bare-seal inversion is complete modulo OpenStrata: H-walk records
--     the remaining head walk from the SealPeelProbe analysis, H-absorb
--     isolates MovedLinkProbe's moved link, and H-Schain isolates
--     ChainRideProbe's target representation chain.  SealTransfer
--     supplies the transfer operation modulo its H-multi chain stratum.
--   * Version-2 pay-offs visible here: no renaming wrapper around the
--     relation, the Λ⊑² case recurses with the target data unchanged,
--     and the ground lemmas of proof.ImprecisionConsistency apply
--     directly to world-embedded obligations.

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
open import TyStore using (TyStore; store-lift; _∋_⦂_)
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
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.WorldDecay as WD
import proof.DGG.TermImpDecay as TD
import proof.DGG.TagTransport as TT
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.ConvImp using
  (pivot-id-endpoints↑; pivot-id-endpoints↓)
open CTI2 using
  (World; ηᴸʷ; ηᴿʷ; impEnvʷ; sourceStoreʷ; targetStoreʷ; embedᴿ;
   _⊑ᵂ⟨_⟩_; CtxImp; ctx-imp; _∣_⊢²_⊑_∶_)
open SVD using
  (AllValueView; allv-Λ; allv-∀; allv-gen; allv-reveal;
   allv-conceal; SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all;
   VarValueView; varv-seal; right-tag-variable-view;
   variable-obligation-aligns; seal-rebase-target;
   seal-tag-boundary-view²; decaySameCtxʳ)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; source-occurs-target; rename-occurs;
   ext-injective; toRenameᵗ-injective; nonstar-from-≢★; rename-⊑;
   fin-suc-injective)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using (toRename-keep-eq)

------------------------------------------------------------------------
-- Stage 1: statements
------------------------------------------------------------------------

-- A right-side world extension: the source store is untouched, the
-- target store follows the machine's store changes, and every type
-- obligation transports with the change.

record WorldExtendᴿ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    (χs : StoreChanges Δᴿ Δᴿ′) (W : World Δᴸ Δᴿ Δ)
    (W′ : World Δᴸ Δᴿ′ Δ′) : Set where
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

mapCtxᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
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
ExtraCastRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
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
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))

-- The inst catch-up companion: instantiating a polymorphic target
-- value allocates on the right and reduces to a value related in the
-- extended world.

InstCatchupRight² : Set
InstCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
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
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))

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
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))
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
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))
id-extra-cast-right² {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M′ = M′} {p = p} M⊑M′ vM vM′ a q =
  Δᴿ , Reduction.keep ∷ [] , Δ , W , sameWorldKeepExtendᴿ , M′ ,
  vM′ ,
  (M′ ⟨ id a ⟩
    —→[ Reduction.keep ]⟨ pure-step (β-id vM′) ⟩
  M′ ∎[]) ,
  subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ M′ ∶ q)
    (sym (mapCtxᴿ-keep γ))
    (subst≡ (λ r → W ∣ γ ⊢² M ⊑ M′ ∶ r)
      (PI.⊑-unique p q) M⊑M′)

------------------------------------------------------------------------
-- Stage 2: helpers
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
liftRebaseAt {Δᴸ = Δᴸ} {W = W} {W′ = W′} {Xᴸ = Xᴸ}
    {Xᴿ = Xᴿ} {v = v} rb =
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

  target-off : ∀ Y
    → toRenameᵗ (ηᴿʷ (CTI2.liftWorldBoth v W′)) Y
        ≡ toRenameᵗ (ηᴿʷ (CTI2.liftWorldBoth v W)) Y
  target-off Fin.zero = refl
  target-off (Fin.suc Y) =
    cong Fin.suc (CTI2.RebaseAt.ηᴿ-frozen rb Y)


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
-- Stage 2: right-injection inversion for spine values
------------------------------------------------------------------------

-- Threading mark-honesty and decay through the inversion.  The
-- inversion's recursion may enter a wrapper's premise world, which
-- the input derivation does not constrain to be mark-honest; the
-- var-rebased wrapper cases therefore decay their premises into the
-- honestified premise world before recursing.

impEnvMono-∘ : ∀ {Δᴸ Δᴿ Δ} {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
  → CTI2.ImpEnvMono W₁ W₂
  → CTI2.ImpEnvMono W₂ W₃
  → CTI2.ImpEnvMono W₁ W₃
impEnvMono-∘ m₁ m₂ Z eq = m₂ Z (m₁ Z eq)

sameCtx-∘ : ∀ {Δᴸ Δᴿ Δ₁ Δ₂ Δ₃}
    {W₁ : World Δᴸ Δᴿ Δ₁} {W₂ : World Δᴸ Δᴿ Δ₂}
    {W₃ : World Δᴸ Δᴿ Δ₃}
    {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂} {γ₃ : CtxImp W₃}
  → CTI2.SameCtx γ₁ γ₂
  → CTI2.SameCtx γ₂ γ₃
  → CTI2.SameCtx γ₁ γ₃
sameCtx-∘ CTI2.same-[] CTI2.same-[] = CTI2.same-[]
sameCtx-∘ (CTI2.same-∷ sc₁) (CTI2.same-∷ sc₂) =
  CTI2.same-∷ (sameCtx-∘ sc₁ sc₂)

rebase-target-membership : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
  → CTI2.RebaseAt W′ W X Y
  → targetStoreʷ W′ ∋ Y ⦂ S
  → targetStoreʷ W ∋ Y ⦂ S
rebase-target-membership ra Y∈ =
  subst≡ (λ Σ → Σ ∋ _ ⦂ _)
    (sym (CTI2.SameRuntime.targetStore-same
      (CTI2.RebaseAt.sameRuntime ra))) Y∈

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
  → CTI2.RebaseAt W′ W X Y
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
        (λ T → T ⊑ᵂ⟨ W ⟩ CTI2.resolveVar (targetStoreʷ W) Y)
        (SPT.resolveVar-nonvar X∈ nonvar-star)
        (CTI2.StoreRepImp.represented
          (CTI2.RebaseAt.storeRepresentations ra))))
    Sns

-- Compose the outer seal rebase with an inner seal-transfer link when
-- the inner source pivot did not move.  The anchor reconstruction is
-- exactly the unmoved branch isolated by MovedLinkProbe.
composeSealRebase : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTI2.RebaseAt W′ W Xᴸ Y
  → CTI2.RebaseAt W₂ W′ X₂ Y
  → toRenameᵗ (ηᴸʷ W₂) X₂ ≡ toRenameᵗ (ηᴸʷ W′) X₂
  → CTI2.RebaseAt W₂ W Xᴸ Y
composeSealRebase {Δᴸ = Δᴸ} {W = W} {W′ = W′} {W₂ = W₂}
    {Xᴸ = Xᴸ} {X₂ = X₂} {Y = Y} ra′ link agrees =
  CTI2.rebase-at
    (CTI2.same-runtime
      (trans (CTI2.SameRuntime.sourceStore-same
        (CTI2.RebaseAt.sameRuntime ra′))
        (CTI2.SameRuntime.sourceStore-same
          (CTI2.RebaseAt.sameRuntime link)))
      (trans (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime ra′))
        (CTI2.SameRuntime.targetStore-same
          (CTI2.RebaseAt.sameRuntime link))))
    source-off target-frozen (CTI2.RebaseAt.pivotAligned ra′)
    (CTI2.RebaseAt.storeRepresentations ra′)
  where
  source-off : ∀ {Z} → Z ≢ Xᴸ
    → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
  source-off {Z} Z≠Xᴸ with Fin._≟_ Z X₂
  source-off {.X₂} X₂≠Xᴸ | yes refl =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot ra′ X₂≠Xᴸ) (sym agrees)
  source-off {Z} Z≠Xᴸ | no Z≠X₂ =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot ra′ Z≠Xᴸ)
      (CTI2.RebaseAt.ηᴸ-off-pivot link Z≠X₂)

  target-frozen : ∀ Z
    → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
  target-frozen Z =
    trans (CTI2.RebaseAt.ηᴿ-frozen ra′ Z)
      (CTI2.RebaseAt.ηᴿ-frozen link Z)

-- `seal-transfer` is implemented in SealTransfer, which imports this
-- module for SpineValue.  The inversion receives that proved operation
-- through OpenStrata to keep the module dependency acyclic.  Its other
-- fields are precisely the three residual strata from the probe analysis.
record OpenStrata : Set where
  field
    seal-transfer : ∀ {Δᴸ Δᴿ Δ}
        {W₁ : World Δᴸ Δᴿ Δ} {γ₁ : CtxImp W₁}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Z : TyVar Δᴸ} {Y : TyVar Δᴿ}
        {p : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)}
      → SpineValue V
      → Value U
      → W₁ ∣ γ₁ ⊢² V ⊑ (U ↓ Conversion.seal Y ★) ∶ p
      → Σ[ W₂ ∈ World Δᴸ Δᴿ Δ ] Σ[ γ₂ ∈ CtxImp W₂ ]
          ( CTI2.RebaseAt W₂ W₁ Z Y
          × CTI2.ImpEnvMono W₁ W₂
          × CTI2.SameCtx γ₁ γ₂
          × Σ[ q₂ ∈ (＇ Z) ⊑ᵂ⟨ W₂ ⟩ ★ ]
              (W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂) )

    H-walk : ∀ {Δᴸ Δᴿ Δ}
        {W W′ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {R : Ty Δᴸ} {S : Ty Δᴿ}
        {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
        {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
        {p₀ : R ⊑ᵂ⟨ W′ ⟩ ★}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → SpineValue V
      → Value U
      → CTI2.ImpEnvMono W W′
      → CTI2.RebaseAt W′ W Xᴸ Y
      → CTI2.SameCtx γ γ′
      → sourceStoreʷ W ∋ Xᴸ ⦂ R
      → targetStoreʷ W ∋ Y ⦂ S
      → W′ ∣ γ′ ⊢² V
          ⊑ (U ↓ Conversion.seal Y S) ⟨ cY ⟩ ∶ p₀
      → W ∣ γ ⊢² V ↓ Conversion.seal Xᴸ R
          ⊑ U ↓ Conversion.seal Y S ∶ q

    H-Schain : ∀ {Δᴸ Δᴿ Δ}
        {W W′ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
        {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
      → SpineValue V
      → Inert c
      → Value U
      → CTI2.ImpEnvMono W W′
      → CTI2.RebaseAt W′ W Xᴸ Y
      → CTI2.SameCtx γ γ′
      → sourceStoreʷ W ∋ Xᴸ ⦂ ★
      → targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
      → W′ ∣ γ′ ⊢² V
          ⊑ U ↓ Conversion.seal Y (＇ Y₂) ∶ p₂
      → W ∣ γ ⊢²
          (V ⟨ c ⟩) ↓ Conversion.seal Xᴸ ★
          ⊑ U ↓ Conversion.seal Y (＇ Y₂) ∶ q

    H-absorb : ∀ {Δᴸ Δᴿ Δ}
        {W W′ W₂ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
        {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
        {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
        {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
      → SpineValue V
      → Inert c
      → Value U
      → CTI2.ImpEnvMono W W′
      → CTI2.RebaseAt W′ W Xᴸ Y
      → CTI2.SameCtx γ γ′
      → sourceStoreʷ W ∋ Xᴸ ⦂ ★
      → targetStoreʷ W ∋ Y ⦂ ★
      → W′ ∣ γ′ ⊢² V ⊑ U ↓ Conversion.seal Y ★ ∶ p₂
      → (link : CTI2.RebaseAt W₂ W′ X₂ Y)
      → CTI2.ImpEnvMono W′ W₂
      → CTI2.SameCtx γ′ γ₂
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
      → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W′) X₂
      → W ∣ γ ⊢²
          (V ⟨ c ⟩) ↓ Conversion.seal Xᴸ ★
          ⊑ U ↓ Conversion.seal Y ★ ∶ q

liftWorldLeft-WF : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CTI2.WFWorld W
  → CTI2.WFWorld (CTI2.liftWorldLeft X⊑★ W)
liftWorldLeft-WF wf Fin.zero ()
liftWorldLeft-WF wf (Fin.suc Xᴸ) eq with wf Xᴸ eq
liftWorldLeft-WF wf (Fin.suc Xᴸ) eq | Xᴿ , al =
  Xᴿ , cong Fin.suc al

-- If a spine value is related to a tagged target value, the tag can be
-- peeled off the target at any obligation for the tag's ground type.
-- The world is required to be mark-honest; the seal cases depend on it.
-- The identity-wrapper helpers are declared first so the inversion can
-- delegate to their proof bodies below.

right-inj-reveal-all-id² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ γ′ : CtxImp W}
    {V : Term Δᴸ} {N : Term Δᴿ}
    {A B : Ty (suc Δᴸ)} {H : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {c : Conv↑ (suc Δᴸ) A B}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H} {p : `∀ A ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.WFWorld W
  → OpenStrata
  → SpineValue V
  → Value N
  → CTI2.SameCtx γ γ′
  → store-lift (sourceStoreʷ W) CTI2.⊢↑[ nothing ] c
  → W ∣ γ′ ⊢² V
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : `∀ B ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² V ↑ `∀↑ c ⊑ N ∶ q

right-inj-conceal-all-id² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ γ′ : CtxImp W}
    {V : Term Δᴸ} {N : Term Δᴿ}
    {A B : Ty (suc Δᴸ)} {H : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {c : Conv↓ (suc Δᴸ) A B}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H} {p : `∀ A ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.WFWorld W
  → OpenStrata
  → SpineValue V
  → Value N
  → CTI2.SameCtx γ γ′
  → store-lift (sourceStoreʷ W) CTI2.⊢↓[ nothing ] c
  → W ∣ γ′ ⊢² V
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : `∀ B ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² V ↓ `∀↓ c ⊑ N ∶ q

right-inj-inversion² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ} {A : Ty Δᴸ} {H : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
    {p : A ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.WFWorld W
  → OpenStrata
  → SpineValue M
  → Value N
  → W ∣ γ ⊢² M
      ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : A ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² M ⊑ N ∶ q

-- Target-only cast: the premise already carries the tag obligation.
right-inj-inversion² wf open-strata sv vN
    (CTI2.⊑cast² {p = p₀} c′ prem q₀) q =
  subst≡ (λ r → _ ∣ _ ⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p₀ q) prem

-- Paired cast: keep the source cast as a source-only cast.
right-inj-inversion² wf open-strata sv vN
    (CTI2.cast⊑cast² c c′ prem q₀) q =
  CTI2.cast⊑² c prem q

-- Source-only cast around an injection value: no obligation matches.
right-inj-inversion² {gH = ＇ Y} wf open-strata (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ‵ ι} wf open-strata (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ∀★} wf open-strata (sv-cast sv inj)
  vN (CTI2.cast⊑² c prem q₀) ()

-- Source-only function cast: the premise components rebuild the
-- premise-level tag obligation.
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-cast sv fun)
    vN (CTI2.cast⊑² {p = ⇒⊑★ pA pB} c prem q₀) (⇒⊑⇒ qA qB) =
  CTI2.cast⊑² c
    (right-inj-inversion² wf open-strata sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ＇ Y} wf open-strata (sv-cast sv fun)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ‵ ι} wf open-strata (sv-cast sv fun)
  vN (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ∀★} wf open-strata (sv-cast sv fun)
  vN (CTI2.cast⊑² c prem q₀) ()

-- Source-only universal cast: chase the tag through the cast with the
-- embedded consistency evidence.
right-inj-inversion² {W = W} {gH = gH} wf open-strata
    (sv-cast sv (all {c = c₁}))
    vN (CTI2.cast⊑² {p = p₀} .(∀ᶜ c₁) prem q₀) q =
  CTI2.cast⊑² (∀ᶜ c₁)
    (right-inj-inversion² wf open-strata sv vN prem
      (ground-cast-source⊑ (C.renameGroundᵐ (ηᴿʷ W) gH) nonstar-∀
        (C.renameᵐᶜ (ηᴸʷ W) (∀ᶜ c₁)) p₀ q₀ q))
    q

-- Source-only generalization cast: same, with the gen tag's source.
right-inj-inversion² {W = W} {gH = gH} wf open-strata
    (sv-cast sv (genᵥ A≢★ safe))
    vN (CTI2.cast⊑² {p = p₀} c prem q₀) q =
  CTI2.cast⊑² c
    (right-inj-inversion² wf open-strata sv vN prem
      (ground-cast-source⊑ (C.renameGroundᵐ (ηᴿʷ W) gH)
        (C.renameNonStar (toRenameᵗ (ηᴸʷ W))
          (nonstar-from-≢★ A≢★))
        (C.renameᵐᶜ (ηᴸʷ W) c) p₀ q₀ q))
    q

-- Type abstraction against a non-∀ ground: only the ∀⊑ view is
-- possible, and its body is exactly a left-only lifted premise.
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² (liftWorldLeft-WF {W = W} wf) open-strata sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ＇ Y} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ‵ ι} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² (liftWorldLeft-WF {W = W} wf) open-strata sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ‵ ι} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ★⇒★} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² (liftWorldLeft-WF {W = W} wf) open-strata sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ★ ⇒ ★} body))
    (∀⊑ Anv′ z∈A′ body)

-- Type abstraction against the ∀★ ground.  The Λ⊑² occurrence premise
-- exposes the body's head, which rules out bot-elim, refutes ∀⊑∀ by
-- occurrence preservation, and leaves the ∀⊑ rebuild.
right-inj-inversion² {gH = ∀★} wf open-strata (sv-Λ sv)
  vN (CTI2.Λ⊑² () var-∈ liftγ vV M′⊢ prem q₀) q
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-left z∈) liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV N⊢
    (right-inj-inversion² (liftWorldLeft-WF {W = W} wf) open-strata sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-fun-left z∈))
... | ()
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-right z∉ z∈) liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV N⊢
    (right-inj-inversion² (liftWorldLeft-WF {W = W} wf) open-strata sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-fun-right z∉ z∈))
... | ()
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-Λ sv)
    vN (CTI2.Λ⊑² {A = A₀} Anv (∈-all z∈) liftγ vV
      (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-all z∈) liftγ vV N⊢
    (right-inj-inversion² (liftWorldLeft-WF {W = W} wf) open-strata sv vN prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-Λ sv)
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
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-reveal-fun sv)
    vN (CTI2.reveal⊑² {p = ⇒⊑★ pA pB} mono CTI2.rebase-idᴸ
      sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.reveal⊑² mono CTI2.rebase-idᴸ sc ⊢c
    (right-inj-inversion² wf open-strata sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-reveal-fun sv)
    vN (CTI2.reveal⊑² {p = ⇒⊑★ pA pB} mono
      (CTI2.rebase-onlyᴸ ts dis rep) sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.reveal⊑² mono (CTI2.rebase-onlyᴸ ts dis rep) sc ⊢c
    (right-inj-inversion² wf open-strata sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {W = W} {gH = ★⇒★} wf open-strata (sv-reveal-fun sv)
    vN (CTI2.reveal⊑² {W′ = W′} {p = ⇒⊑★ pA pB} mono
      (CTI2.rebase-varᴸ rb) sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.reveal⊑²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = WD.honestify W′}
      mono (WD.EnvDecay.env-mono (WD.honestify-decay {W = W′})))
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt WD.decay-refl (WD.honestify-decay {W = W′}) rb))
    (decaySameCtxʳ (WD.honestify-decay {W = W′}) sc) ⊢c
    (right-inj-inversion² (WD.honestify-WF W′) open-strata sv vN
      (TD.⊢²-decay (WD.honestify-decay {W = W′}) prem)
      (WD.decay⊑ᵂ (WD.honestify-decay {W = W′}) (⇒⊑⇒ pA pB)))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ＇ Y} wf open-strata (sv-reveal-fun sv)
  vN (CTI2.reveal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ‵ ι} wf open-strata (sv-reveal-fun sv)
  vN (CTI2.reveal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ∀★} wf open-strata (sv-reveal-fun sv)
  vN (CTI2.reveal⊑² _ _ _ _ _ _) ()

-- Function-shaped conceal: same construction.
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-conceal-fun sv)
    vN (CTI2.conceal⊑² {p = ⇒⊑★ pA pB} mono CTI2.rebase-idᴸ
      sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.conceal⊑² mono CTI2.rebase-idᴸ sc ⊢c
    (right-inj-inversion² wf open-strata sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-conceal-fun sv)
    vN (CTI2.conceal⊑² {p = ⇒⊑★ pA pB} mono
      (CTI2.rebase-onlyᴸ ts dis rep) sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.conceal⊑² mono (CTI2.rebase-onlyᴸ ts dis rep) sc ⊢c
    (right-inj-inversion² wf open-strata sv vN prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {W = W} {gH = ★⇒★} wf open-strata
    (sv-conceal-fun sv)
    vN (CTI2.conceal⊑² {W′ = W′} {p = ⇒⊑★ pA pB} mono
      (CTI2.rebase-varᴸ rb) sc ⊢c prem q₀)
    (⇒⊑⇒ qA qB) =
  CTI2.conceal⊑²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = WD.honestify W′}
      mono (WD.EnvDecay.env-mono (WD.honestify-decay {W = W′})))
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt (WD.honestify-decay {W = W′}) WD.decay-refl rb))
    (decaySameCtxʳ (WD.honestify-decay {W = W′}) sc) ⊢c
    (right-inj-inversion² (WD.honestify-WF W′) open-strata sv vN
      (TD.⊢²-decay (WD.honestify-decay {W = W′}) prem)
      (WD.decay⊑ᵂ (WD.honestify-decay {W = W′}) (⇒⊑⇒ pA pB)))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ＇ Y} wf open-strata (sv-conceal-fun sv)
  vN (CTI2.conceal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ‵ ι} wf open-strata (sv-conceal-fun sv)
  vN (CTI2.conceal⊑² _ _ _ _ _ _) ()
right-inj-inversion² {gH = ∀★} wf open-strata (sv-conceal-fun sv)
  vN (CTI2.conceal⊑² _ _ _ _ _ _) ()

-- Universal reveal: transport the requested tag obligation through the
-- body conversion.  Variable rebases recurse in the honestified world.
right-inj-inversion² wf open-strata (sv-reveal-all sv) vN
    (CTI2.reveal⊑² mono CTI2.rebase-idᴸ sc (CTI2.⊢↑-∀-idˣ c⊢)
      prem q₀) q =
  right-inj-reveal-all-id² wf open-strata sv vN sc c⊢ prem q
right-inj-inversion² {W = W} {gH = ★⇒★} wf open-strata
    (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  CTI2.reveal⊑² mono (CTI2.rebase-onlyᴸ ts dis rep) sc
    (CTI2.⊢↑-∀ˣ c⊢)
    (right-inj-inversion² wf open-strata sv vN prem
      (TT.transport↑-∀-fun c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q))
    q
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  CTI2.reveal⊑² mono (CTI2.rebase-onlyᴸ ts dis rep) sc
    (CTI2.⊢↑-∀ˣ c⊢)
    (right-inj-inversion² wf open-strata sv vN prem
      (TT.transport↑-∀-all c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q))
    q
right-inj-inversion² {W = W} {gH = ‵ ι} wf open-strata (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↑-∀-ι-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↑-∀-var-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)
right-inj-inversion² {W = W} {gH = ★⇒★} wf open-strata
    (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  CTI2.reveal⊑²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = WD.honestify W′} mono
      (WD.EnvDecay.env-mono (WD.honestify-decay {W = W′})))
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt WD.decay-refl (WD.honestify-decay {W = W′})
        rb))
    (decaySameCtxʳ (WD.honestify-decay {W = W′}) sc)
    (CTI2.⊢↑-∀ˣ c⊢)
    (right-inj-inversion² (WD.honestify-WF W′) open-strata sv vN
      (TD.⊢²-decay (WD.honestify-decay {W = W′}) prem)
      (WD.decay⊑ᵂ (WD.honestify-decay {W = W′})
        (TT.transport↑-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸʷ W′))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q)))
    q
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  CTI2.reveal⊑²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = WD.honestify W′} mono
      (WD.EnvDecay.env-mono (WD.honestify-decay {W = W′})))
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt WD.decay-refl (WD.honestify-decay {W = W′})
        rb))
    (decaySameCtxʳ (WD.honestify-decay {W = W′}) sc)
    (CTI2.⊢↑-∀ˣ c⊢)
    (right-inj-inversion² (WD.honestify-WF W′) open-strata sv vN
      (TD.⊢²-decay (WD.honestify-decay {W = W′}) prem)
      (WD.decay⊑ᵂ (WD.honestify-decay {W = W′})
        (TT.transport↑-∀-all c⊢
          (toRenameᵗ-injective (ηᴸʷ W′))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q)))
    q
right-inj-inversion² {W = W} {gH = ‵ ι} wf open-strata (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↑-∀-ι-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W′))
      (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata (sv-reveal-all sv) vN
    (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↑-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↑-∀-var-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W′))
      (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)

-- Universal conceal: the dual transport has the same obligations, while
-- the variable-rebase decay uses conceal's opposite rebase orientation.
right-inj-inversion² wf open-strata (sv-conceal-all sv) vN
    (CTI2.conceal⊑² mono CTI2.rebase-idᴸ sc (CTI2.⊢↓-∀-idˣ c⊢)
      prem q₀) q =
  right-inj-conceal-all-id² wf open-strata sv vN sc c⊢ prem q
right-inj-inversion² {W = W} {gH = ★⇒★} wf open-strata
    (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  CTI2.conceal⊑² mono (CTI2.rebase-onlyᴸ ts dis rep) sc
    (CTI2.⊢↓-∀ˣ c⊢)
    (right-inj-inversion² wf open-strata sv vN prem
      (TT.transport↓-∀-fun c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q))
    q
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata
    (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  CTI2.conceal⊑² mono (CTI2.rebase-onlyᴸ ts dis rep) sc
    (CTI2.⊢↓-∀ˣ c⊢)
    (right-inj-inversion² wf open-strata sv vN prem
      (TT.transport↓-∀-all c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q))
    q
right-inj-inversion² {W = W} {gH = ‵ ι} wf open-strata
    (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↓-∀-ι-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {p = p₀} mono (CTI2.rebase-onlyᴸ ts dis rep) sc
      (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↓-∀-var-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)
right-inj-inversion² {W = W} {gH = ★⇒★} wf open-strata
    (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  CTI2.conceal⊑²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = WD.honestify W′} mono
      (WD.EnvDecay.env-mono (WD.honestify-decay {W = W′})))
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt (WD.honestify-decay {W = W′}) WD.decay-refl
        rb))
    (decaySameCtxʳ (WD.honestify-decay {W = W′}) sc)
    (CTI2.⊢↓-∀ˣ c⊢)
    (right-inj-inversion² (WD.honestify-WF W′) open-strata sv vN
      (TD.⊢²-decay (WD.honestify-decay {W = W′}) prem)
      (WD.decay⊑ᵂ (WD.honestify-decay {W = W′})
        (TT.transport↓-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸʷ W′))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q)))
    q
right-inj-inversion² {W = W} {gH = ∀★} wf open-strata
    (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  CTI2.conceal⊑²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = WD.honestify W′} mono
      (WD.EnvDecay.env-mono (WD.honestify-decay {W = W′})))
    (CTI2.rebase-varᴸ
      (TD.decayRebaseAt (WD.honestify-decay {W = W′}) WD.decay-refl
        rb))
    (decaySameCtxʳ (WD.honestify-decay {W = W′}) sc)
    (CTI2.⊢↓-∀ˣ c⊢)
    (right-inj-inversion² (WD.honestify-WF W′) open-strata sv vN
      (TD.⊢²-decay (WD.honestify-decay {W = W′}) prem)
      (WD.decay⊑ᵂ (WD.honestify-decay {W = W′})
        (TT.transport↓-∀-all c⊢
          (toRenameᵗ-injective (ηᴸʷ W′))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q)))
    q
right-inj-inversion² {W = W} {gH = ‵ ι} wf open-strata
    (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↓-∀-ι-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W′))
      (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata (sv-conceal-all sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono
      (CTI2.rebase-varᴸ rb) sc (CTI2.⊢↓-∀ˣ c⊢) prem q₀) q =
  ⊥-elim
    (TT.transport↓-∀-var-⊥ c⊢
      (toRenameᵗ-injective (ηᴸʷ W′))
      (toRenameᵗ-injective (ηᴸʷ W))
      p₀ q)

-- Bare source seal.  A variable tag forces the target value to expose
-- the corresponding seal boundary and turns the one-sided rebase into
-- a paired link.
right-inj-inversion² {gH = ‵ ι} wf open-strata (sv-seal sv) vN
    (CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ X∈) prem q₀) q
    with q
right-inj-inversion² {gH = ‵ ι} wf open-strata (sv-seal sv) vN
    (CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ X∈) prem q₀) q
    | ()
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-seal sv) vN
    (CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ X∈) prem q₀) q
    with q
right-inj-inversion² {gH = ★⇒★} wf open-strata (sv-seal sv) vN
    (CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ X∈) prem q₀) q
    | ()
right-inj-inversion² {gH = ∀★} wf open-strata (sv-seal sv) vN
    (CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ X∈) prem q₀) q
    with q
right-inj-inversion² {gH = ∀★} wf open-strata (sv-seal sv) vN
    (CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ X∈) prem q₀) q
    | ()
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    with seal-rebase-target rb q | right-tag-variable-view vN prem
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    with prem
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.⊑cast² c′ prem₂ .p₀ =
  CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ Xᴸ∈) prem₂ q
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = `∀ A} (sv-Λ sv₀)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.Λ⊑² Anv z∈A liftγ vV U!⊢ prem₂ .p₀ =
  OpenStrata.H-walk open-strata (sv-Λ sv₀) vU mono ra′ sc Xᴸ∈
    (rebase-target-membership ra′ Y∈)
    (CTI2.Λ⊑² Anv z∈A liftγ vV U!⊢ prem₂ p₀)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.cast⊑² c prem₂ .p₀ =
  OpenStrata.H-walk open-strata (sv-cast sv₀ inert) vU mono ra′ sc
    Xᴸ∈ (rebase-target-membership ra′ Y∈)
    (CTI2.cast⊑² c prem₂ p₀)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.reveal⊑² mono₁ rb₁ sc₁ c⊢ prem₂ .p₀ =
  OpenStrata.H-walk open-strata sv vU mono ra′ sc Xᴸ∈
    (rebase-target-membership ra′ Y∈)
    (CTI2.reveal⊑² mono₁ rb₁ sc₁ c⊢ prem₂ p₀)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} sv) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.conceal⊑² mono₁ rb₁ sc₁ c⊢ prem₂ .p₀ =
  OpenStrata.H-walk open-strata sv vU mono ra′ sc Xᴸ∈
    (rebase-target-membership ra′ Y∈)
    (CTI2.conceal⊑² mono₁ rb₁ sc₁ c⊢ prem₂ p₀)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    with SPT.right-var-obligation-view {W = W′} {Y = Y} p₂
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned
    with SPT.var-consistency-view c
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₁ refl =
  CTI2.conceal⊑² mono rb sc (CTI2.⊢↓-sealˣ Xᴸ∈)
    (CTI2.cast⊑² c prem₂ p₂) q
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} {R = R} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl
    with S
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | ★
    with OpenStrata.seal-transfer open-strata sv₀ vU prem₂
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | ★
    | W₂ , γ₂ , link , mono₂ , sc₂ , q₂ , D₂
    with Fin._≟_ (toRenameᵗ (ηᴸʷ W₂) X₂)
      (toRenameᵗ (ηᴸʷ W′) X₂)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | ★
    | W₂ , γ₂ , link , mono₂ , sc₂ , q₂ , D₂ | yes agrees =
  CTI2.conceal⊑conceal²
    (impEnvMono-∘ {W₁ = W} {W₂ = W′} {W₃ = W₂} mono mono₂)
    (composeSealRebase ra′ link agrees)
    (sameCtx-∘ sc sc₂)
    (CTI2.⊢↓-sealˣ Xᴸ∈)
    (CTI2.⊢↓-sealˣ (rebase-target-membership ra′ Y∈))
    (CTI2.cast⊑² c D₂ ★⊑★) q
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | ★
    | W₂ , γ₂ , link , mono₂ , sc₂ , q₂ , D₂ | no moved =
  OpenStrata.H-absorb open-strata sv₀ inert vU mono ra′ sc Xᴸ∈
    (rebase-target-membership ra′ Y∈) prem₂ link mono₂ sc₂ D₂ moved
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | ＇ Y₂ =
  OpenStrata.H-Schain open-strata sv₀ inert vU mono ra′ sc Xᴸ∈
    (rebase-target-membership ra′ Y∈) prem₂
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | ‵ ι =
  ⊥-elim (seal-target-nonstar-⊥ Xᴸ∈ ra′
    (rebase-target-membership ra′ Y∈) nonvar-base nonstar-ι)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | A ⇒ B =
  ⊥-elim (seal-target-nonstar-⊥ Xᴸ∈ ra′
    (rebase-target-membership ra′ Y∈) nonvar-fun nonstar-⇒)
right-inj-inversion² {W = W} {gH = ＇ Y} wf open-strata
    (sv-seal {X = Xᴸ} (sv-cast sv₀ inert)) vN
    (CTI2.conceal⊑² {W′ = W′} {p = p₀} mono rb sc
      (CTI2.⊢↓-sealˣ Xᴸ∈) prem q₀) q
    | ra′ | varv-seal {W = U} vU Y∈ refl
    | CTI2.cast⊑cast² {p = p₂} c c′ prem₂ .p₀
    | X₂ , refl , aligned | inj₂ refl | `∀ A =
  ⊥-elim (seal-target-nonstar-⊥ Xᴸ∈ ra′
    (rebase-target-membership ra′ Y∈) nonvar-all nonstar-∀)

-- Type applications are not spine values.
right-inj-inversion² wf open-strata () vN (CTI2.•⊑² _ _ _ _) q

------------------------------------------------------------------------
-- Identity-pivot universal wrappers
------------------------------------------------------------------------

-- These are the complete nothing-pivot subcases of the two universal
-- wrapper branches.  Their body conversions have equal endpoints and the
-- wrapper world is definitionally unchanged, so ordinary index transport
-- exposes the recursive injection obligation.

right-inj-reveal-all-id² {W = W} {A = A} {B = B}
    {H = H} {c = c} wf open-strata sv vN sc c⊢ prem q =
  CTI2.reveal⊑² (λ _ eq → eq) CTI2.rebase-idᴸ sc
    (CTI2.⊢↑-∀-idˣ c⊢)
    (right-inj-inversion² wf open-strata sv vN prem
      (subst≡ (λ T → T ⊑ᵂ⟨ W ⟩ H)
        (sym (cong `∀ (pivot-id-endpoints↑ c⊢))) q))
    q

right-inj-conceal-all-id² {W = W} {A = A} {B = B}
    {H = H} {c = c} wf open-strata sv vN sc c⊢ prem q =
  CTI2.conceal⊑² (λ _ eq → eq) CTI2.rebase-idᴸ sc
    (CTI2.⊢↓-∀-idˣ c⊢)
    (right-inj-inversion² wf open-strata sv vN prem
      (subst≡ (λ T → T ⊑ᵂ⟨ W ⟩ H)
        (sym (cong `∀ (pivot-id-endpoints↓ c⊢))) q))
    q
