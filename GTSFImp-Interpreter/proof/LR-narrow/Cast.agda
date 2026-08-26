open import LR-narrow.CastObligations using
  (CastValueObligations; OpenPairedCastCase; precise-cast-values;
   imprecise-cast-values; paired-cast-values; open-function-injection;
   open-function-precise-injection;
   open-function-precise-generalization; open-universals;
   open-function-dynamic; open-base-dynamic; open-variable-dynamic;
   open-right-universal; open-universal-dynamic)

module proof.LR-narrow.Cast (ob : CastValueObligations) where

-- File Charter:
--   * Proves compatibility of the symmetric and one-sided CTI casts.
--   * Factors term evaluation from the shared related-value cast theorem.
--   * Keeps evaluator phase decomposition private.

open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using
  (1+n≰n; m∸n≤m; n≤1+n; ∸-monoʳ-≤; ≤-refl; ≤-trans)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import CastTerms
import Consistency as C
open C using (_[_]ᶜ)
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import Reduction
import Eval as E
open import Interpreter
open import proof.LR-narrow.TermSubstitution using (subst-closed)
open import proof.TypeInTermSubst using (toRename-wk-eq)
open import proof.LR-narrow.TypeRenamingComposition using
  (Hcong₄; Hcong₅; mk-all; mk-cast-term; rename∼-parallel≅)
open import proof.ImprecisionConsistency using
  (expand-cast-source⊑; ground-cast-target⊑;
   ground-target-nonvar-to-star⊑;
   ground-targets-unique⊑; nonvar-occurs-nonstar;
   consistency-target-occurs-source; source-occurs-target;
   target-occurs-source;
   ext-injective; rename-occurs; renameᵗ-injective; shift-ground;
   shift-injectiveᵗ; ty-all-injective;
   toRenameᵗ-injective; ty-var-injective)
import proof.TypeSafety.Progress as Progress
open import proof.TypeSafety.Progress using (no-bot-value)
open import proof.Consistency using (gen-safe)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.TermRelation
open import LR-narrow.DynamicPayload using
  (right-tags-and-payload; dynamic-payload-variable)
open import LR-narrow.ClosingSubstitutionProperties using
  (value-imprecision-endpoints; impreciseClosingSubstitution;
   preciseClosingSubstitution)
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return; value-question-complete)
open import proof.LR-narrow.BetaExpansion using (value-step-none)
open import proof.LR-narrow.StepExpansion using
  (nonvalue-zero-timed; PureStepReturn; pure-step-return;
   PureStepBlame; pure-step-blame; pure-step-return-invert;
   pure-step-return-expand; pure-step-blame-invert;
   pure-step-blame-expand; related-pure-step-expand)
open import proof.LR-narrow.Application using
  (prepend-result; prepend-return; value-return-exact; value-unique;
   paired-returns-reindex; application-semantic-bounded)
open import proof.LR-narrow.CastComposition using
  (cast-computations-related; precise-cast-computations-related;
   imprecise-cast-computations-related;
   computations-related-future-compose;
   computations-related-post-bind-compose)
open import proof.LR-narrow.ValueExtraction using
  (future-precise-monotone; future-imprecise-monotone;
   ReflexiveFuture; future-is-refl; future-refl-view;
   related-computation-values)
open import proof.LR-narrow.KeepStepExpansion using
  (paired-future-values-downward; paired-future-precise-step;
   paired-future-imprecise-step; related-precise-keep-step-expand;
   related-imprecise-keep-step-expand)
open import proof.LR-narrow.BindStepExpansion using
  (StepReturn; step-return; StepBlame; step-blame;
   step-return-invert; step-return-expand;
   step-blame-invert; step-blame-expand)
open import proof.LR-narrow.CastPhases using
  (cast-operand-nonvalue; cast-operand-step-question)
open import proof.LR-narrow.TypeApplication using
  (positive-universal-application; precise-body-lift-eq;
   imprecise-body-lift-eq)
open import proof.LR-narrow.Closure using
  (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof

reindex-center-imprecision : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A B A′ B′ : Ty Δ}
  → μ I.⊢ A ⊑ B
  → A ≡ A′
  → B ≡ B′
  → μ I.⊢ A′ ⊑ B′
reindex-center-imprecision p refl refl = p

dynamic-atom-tag-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W (I.X⊑★ mode) Vᴵ Vᴾ
  → TypedEndpoints W I.★⊑★ Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-atom-tag-endpoints {W = W} {Z = Z} {mode = mode}
    {Gᴾ = Gᴾ} gᴾ ground-center Gᴾ∼★
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} endpoints =
  typed-endpoints ★ ★ refl refl
    (imprecise-value endpoints) precise-tag-value
    Vᴵ⊢★ precise-tag-typed
  where
  precise-type-eq : preciseType endpoints ≡ Gᴾ
  precise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (trans (preciseEmbedded endpoints) (sym ground-center))

  imprecise-type-eq : impreciseType endpoints ≡ ★
  imprecise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (impreciseEmbedded endpoints)

  Vᴾ⊢Gᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ Vᴾ ⦂ A)
    precise-type-eq (precise-typed endpoints)

  Vᴵ⊢★ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ Vᴵ ⦂ A)
    imprecise-type-eq (imprecise-typed endpoints)

  precise-tag-value = precise-value endpoints 《
    inj ⦃ Gᵍ = gᴾ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      ⦃ Gns = C.ground-nonstar gᴾ ⦄ 》

  precise-tag-typed = ⊢⟨⟩ Vᴾ⊢Gᴾ (groundInjection gᴾ Gᴾ∼★)


dynamic-atom-tag-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) (suc k) Vᴵ Vᴾ
  → ValueImprecision W I.★⊑★ (suc k) Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-atom-tag-value {W = W} {Z = Z} {mode = mode}
    gᴾ ground-center Gᴾ∼★ (endpoints , inj₁ related) =
  dynamic-atom-tag-endpoints gᴾ ground-center Gᴾ∼★ endpoints ,
  inj₂ atom-tag
  where

  atom-tag = dynamic-atom-tag mode gᴾ ground-center Gᴾ∼★
    related
dynamic-atom-tag-value {W = W} {Z = Z} {mode = mode}
    gᴾ ground-center Gᴾ∼★ (endpoints , inj₂ related) =
  dynamic-atom-tag-endpoints gᴾ ground-center Gᴾ∼★ endpoints ,
  inj₁ (shape , payload-related)
  where
  payload-q = reindex-center-imprecision I.X⊑X
    (sym ground-center)
    (sym (aligned-imprecise-ground-center related))

  paired-related = ClosureProof.semantic-atom-value
    (aligned-atom-relation-holds related)

  payload-related = ClosureProof.value-imprecision-reindex
    payload-q I.X⊑X ground-center
    (aligned-imprecise-ground-center related)
    (value-imprecision-downward-to (n≤1+n _) paired-related)

  shape = dynamic-payload-shape _ _ gᴾ
    (aligned-imprecise-ground-proof related) _ _ Gᴾ∼★
    (aligned-imprecise-ground-to-star related) _ _
    (aligned-imprecise-tag-shape related) refl payload-q

dynamic-atom-tag-value-at : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (j : ℕ) {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) j Vᴵ Vᴾ
  → ValueImprecision W I.★⊑★ j Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-atom-tag-value-at zero gᴾ ground-center Gᴾ∼★ endpoints =
  dynamic-atom-tag-endpoints gᴾ ground-center Gᴾ∼★ endpoints
dynamic-atom-tag-value-at (suc j) gᴾ ground-center Gᴾ∼★ related =
  dynamic-atom-tag-value gᴾ ground-center Gᴾ∼★ related

right-dynamic-base-tag-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {ι : Base} {Gᴵ : Ty Δᴵ}
    (gᴵ : Ground Gᴵ) {μᴵ : C.Env∼ Δᴵ}
    (Gᴵ∼★ : μᴵ C.⊢ Gᴵ ∼★)
    (payload-q : impEnv (core W) I.⊢ ‵ ι
      ⊑ embedImprecise (core W) Gᴵ)
    {k : ℕ} {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W payload-q k Uᴵ Vᴾ
  → TypedEndpoints W (I.ι⊑★ {ι = ι})
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩) Vᴾ
right-dynamic-base-tag-endpoints {W = W} {Gᴵ = Gᴵ} gᴵ Gᴵ∼★
    payload-q related =
  typed-endpoints ★ (preciseType endpoints) refl
    (preciseEmbedded endpoints) imprecise-tag-value
    (precise-value endpoints) imprecise-tag-typed
    (precise-typed endpoints)
  where
  endpoints = value-imprecision-endpoints related

  imprecise-type-eq : impreciseType endpoints ≡ Gᴵ
  imprecise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (impreciseEmbedded endpoints)

  Uᴵ⊢Gᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    imprecise-type-eq (imprecise-typed endpoints)

  imprecise-tag-value = imprecise-value endpoints 《
    inj ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      ⦃ Gns = C.ground-nonstar gᴵ ⦄ 》

  imprecise-tag-typed = ⊢⟨⟩ Uᴵ⊢Gᴵ
    (groundInjection gᴵ Gᴵ∼★)

right-dynamic-base-tag-value-at : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (j : ℕ) {ι : Base} {Gᴵ : Ty Δᴵ}
    (gᴵ : Ground Gᴵ) {μᴵ : C.Env∼ Δᴵ}
    (Gᴵ∼★ : μᴵ C.⊢ Gᴵ ∼★)
    (payload-q : impEnv (core W) I.⊢ ‵ ι
      ⊑ embedImprecise (core W) Gᴵ)
    {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W payload-q j Uᴵ Vᴾ
  → ValueImprecision W (I.ι⊑★ {ι = ι}) j
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩) Vᴾ
right-dynamic-base-tag-value-at zero gᴵ Gᴵ∼★ payload-q related =
  right-dynamic-base-tag-endpoints gᴵ Gᴵ∼★ payload-q {k = zero} related
right-dynamic-base-tag-value-at (suc j) gᴵ Gᴵ∼★ payload-q related =
  right-dynamic-base-tag-endpoints gᴵ Gᴵ∼★ payload-q related ,
  right-tags-and-payload gᴵ Gᴵ∼★ payload-q
    (value-imprecision-downward-to (n≤1+n j) related)

dynamic-base-tags-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Gᴾ : Ty Δᴾ} {Gᴵ : Ty Δᴵ}
    (gᴾ : Ground Gᴾ) (gᴵ : Ground Gᴵ)
    {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
    (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★) (Gᴵ∼★ : μᴵ C.⊢ Gᴵ ∼★)
    (payload-q : impEnv (core W) I.⊢ embedPrecise (core W) Gᴾ
      ⊑ embedImprecise (core W) Gᴵ)
    {k : ℕ} {Uᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
  → ValueImprecision W payload-q k Uᴵ Uᴾ
  → TypedEndpoints W I.★⊑★
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩)
      (Uᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-base-tags-endpoints {W = W} {Gᴾ = Gᴾ} {Gᴵ = Gᴵ}
    gᴾ gᴵ Gᴾ∼★ Gᴵ∼★ payload-q related =
  typed-endpoints ★ ★ refl refl imprecise-tag-value precise-tag-value
    imprecise-tag-typed precise-tag-typed
  where
  endpoints = value-imprecision-endpoints related

  precise-type-eq : preciseType endpoints ≡ Gᴾ
  precise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (preciseEmbedded endpoints)

  imprecise-type-eq : impreciseType endpoints ≡ Gᴵ
  imprecise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (impreciseEmbedded endpoints)

  Uᴾ⊢Gᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    precise-type-eq (precise-typed endpoints)

  Uᴵ⊢Gᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    imprecise-type-eq (imprecise-typed endpoints)

  precise-tag-value = precise-value endpoints 《
    inj ⦃ Gᵍ = gᴾ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      ⦃ Gns = C.ground-nonstar gᴾ ⦄ 》

  imprecise-tag-value = imprecise-value endpoints 《
    inj ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      ⦃ Gns = C.ground-nonstar gᴵ ⦄ 》

  precise-tag-typed = ⊢⟨⟩ Uᴾ⊢Gᴾ
    (groundInjection gᴾ Gᴾ∼★)

  imprecise-tag-typed = ⊢⟨⟩ Uᴵ⊢Gᴵ
    (groundInjection gᴵ Gᴵ∼★)

dynamic-base-tags-value-at : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (j : ℕ)
    {Gᴾ : Ty Δᴾ} {Gᴵ : Ty Δᴵ}
    (gᴾ : Ground Gᴾ) (gᴵ : Ground Gᴵ)
    {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
    (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★) (Gᴵ∼★ : μᴵ C.⊢ Gᴵ ∼★)
    (payload-q : impEnv (core W) I.⊢ embedPrecise (core W) Gᴾ
      ⊑ embedImprecise (core W) Gᴵ)
    {Uᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
  → ValueImprecision W payload-q j Uᴵ Uᴾ
  → ValueImprecision W I.★⊑★ j
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩)
      (Uᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-base-tags-value-at zero gᴾ gᴵ Gᴾ∼★ Gᴵ∼★
    payload-q related =
  dynamic-base-tags-endpoints gᴾ gᴵ Gᴾ∼★ Gᴵ∼★ payload-q {k = zero}
    related
dynamic-base-tags-value-at (suc j) gᴾ gᴵ Gᴾ∼★ Gᴵ∼★
    payload-q related =
  dynamic-base-tags-endpoints gᴾ gᴵ Gᴾ∼★ Gᴵ∼★ payload-q related ,
  inj₁ (tags-and-payload gᴾ gᴵ Gᴾ∼★ Gᴵ∼★ payload-q
    (value-imprecision-downward-to (n≤1+n j) related))

ground-identity-injection-eq : ∀ {Δ} {G : Ty Δ}
    {μ : C.Env∼ Δ} (g : Ground G) (G∼★ : μ C.⊢ G ∼★)
    (ns : NonStar G) (a : Atom G)
  → C._! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄
      (C.id a) ⦃ Ans = ns ⦄ ≡ groundInjection g G∼★
ground-identity-injection-eq (＇ X) G∼★ ns (＇ .X)
    rewrite nonStar-unique ns (C.ground-nonstar (＇ X)) = refl
ground-identity-injection-eq (‵ ι) G∼★ ns (‵ .ι)
    rewrite nonStar-unique ns (C.ground-nonstar (‵ ι)) = refl
ground-identity-injection-eq ★⇒★ G∼★ ns ()
ground-identity-injection-eq ∀★ G∼★ ns ()

precise-atom-not-arrow : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {C : Ty Δᴾ} {A B : Ty Δᶜ}
  → Atom C
  → embedPrecise (core W) C ≡ A ⇒ B
  → ⊥
precise-atom-not-arrow (＇ X) ()
precise-atom-not-arrow (‵ ι) ()
precise-atom-not-arrow ★ ()

imprecise-atom-not-arrow : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {C : Ty Δᴵ} {A B : Ty Δᶜ}
  → Atom C
  → embedImprecise (core W) C ≡ A ⇒ B
  → ⊥
imprecise-atom-not-arrow (＇ X) ()
imprecise-atom-not-arrow (‵ ι) ()
imprecise-atom-not-arrow ★ ()

precise-atom-not-all : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {C : Ty Δᴾ} {A : Ty (suc Δᶜ)}
  → Atom C
  → embedPrecise (core W) C ≡ `∀ A
  → ⊥
precise-atom-not-all (＇ X) ()
precise-atom-not-all (‵ ι) ()
precise-atom-not-all ★ ()

precise-source-star : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {A : Ty Δᴾ}
  → embedPrecise (core W) A ≡ ★
  → A ≡ ★
precise-source-star {W = W} source = renameᵗ-injective
  (toRenameᵗ-injective (preciseEmbedding (core W))) source

imprecise-source-star : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {A : Ty Δᴵ}
  → embedImprecise (core W) A ≡ ★
  → A ≡ ★
imprecise-source-star {W = W} source = renameᵗ-injective
  (toRenameᵗ-injective (impreciseEmbedding (core W))) source

precise-star-nonstar-impossible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {A : Ty Δᴾ}
  → embedPrecise (core W) A ≡ ★
  → NonStar A
  → ⊥
precise-star-nonstar-impossible {W = W} {A = A} source nonstar =
  nonStar≢★ nonstar (precise-source-star {W = W} {A = A} source)

imprecise-star-nonstar-impossible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {A : Ty Δᴵ}
  → embedImprecise (core W) A ≡ ★
  → NonStar A
  → ⊥
imprecise-star-nonstar-impossible {W = W} {A = A} source nonstar =
  nonStar≢★ nonstar (imprecise-source-star {W = W} {A = A} source)

star-left-nonstar-impossible : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ}
  → μ I.⊢ ★ ⊑ A
  → NonStar A
  → ⊥
star-left-nonstar-impossible I.★⊑★ ()

variable-left-nonstar-target : ∀ {Δ} {μ : I.ImpEnv Δ}
    {X : TyVar Δ} {A : Ty Δ}
  → μ I.⊢ ＇ X ⊑ A
  → NonStar A
  → A ≡ ＇ X
variable-left-nonstar-target I.X⊑X nonstar = refl
variable-left-nonstar-target (I.X⊑★ mode) ()

dynamic-atom-target-occupant : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
    {Gᴾ : Ty Δᴾ} {Dᴵ : Ty Δᴵ} {Bᴾ Bᴵ : Ty Δᶜ}
  → embedPrecise (core W) Gᴾ ≡ ＇ Z
  → NonStar Dᴵ
  → (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
  → embedPrecise (core W) Gᴾ ≡ Bᴾ
  → embedImprecise (core W) Dᴵ ≡ Bᴵ
  → Σ[ Y ∈ TyVar Δᴵ ]
      C.toRenameᵗ (impreciseEmbedding (core W)) Y ≡ Z
dynamic-atom-target-occupant {W = W} {Z = Z} {Dᴵ = ★}
    ground-center () q targetᴾ targetᴵ
dynamic-atom-target-occupant {W = W} {Z = Z} {Dᴵ = ‵ ι}
    ground-center nonstar q targetᴾ targetᴵ
    with center-target
  where
  center-q : impEnv (core W) I.⊢ ＇ Z
      ⊑ embedImprecise (core W) (‵ ι)
  center-q = reindex-center-imprecision q
    (trans (sym targetᴾ) ground-center) (sym targetᴵ)

  center-target : embedImprecise (core W) (‵ ι) ≡ ＇ Z
  center-target = variable-left-nonstar-target center-q
    (C.renameNonStar
      (C.toRenameᵗ (impreciseEmbedding (core W))) nonstar)
dynamic-atom-target-occupant {Dᴵ = ‵ ι}
    ground-center nonstar q targetᴾ targetᴵ | ()
dynamic-atom-target-occupant {W = W} {Z = Z} {Dᴵ = ＇ Y}
    ground-center nonstar q targetᴾ targetᴵ =
  Y , ty-var-injective center-target
  where
  center-q : impEnv (core W) I.⊢ ＇ Z
      ⊑ embedImprecise (core W) (＇ Y)
  center-q = reindex-center-imprecision q
    (trans (sym targetᴾ) ground-center) (sym targetᴵ)

  center-target : embedImprecise (core W) (＇ Y) ≡ ＇ Z
  center-target = variable-left-nonstar-target center-q
    (C.renameNonStar
      (C.toRenameᵗ (impreciseEmbedding (core W))) nonstar)
dynamic-atom-target-occupant {W = W} {Z = Z} {Dᴵ = A ⇒ B}
    ground-center nonstar q targetᴾ targetᴵ
    with center-target
  where
  center-q : impEnv (core W) I.⊢ ＇ Z
      ⊑ embedImprecise (core W) (A ⇒ B)
  center-q = reindex-center-imprecision q
    (trans (sym targetᴾ) ground-center) (sym targetᴵ)

  center-target : embedImprecise (core W) (A ⇒ B) ≡ ＇ Z
  center-target = variable-left-nonstar-target center-q
    (C.renameNonStar
      (C.toRenameᵗ (impreciseEmbedding (core W))) nonstar)
dynamic-atom-target-occupant {Dᴵ = A ⇒ B}
    ground-center nonstar q targetᴾ targetᴵ | ()
dynamic-atom-target-occupant {W = W} {Z = Z} {Dᴵ = `∀ A}
    ground-center nonstar q targetᴾ targetᴵ
    with center-target
  where
  center-q : impEnv (core W) I.⊢ ＇ Z
      ⊑ embedImprecise (core W) (`∀ A)
  center-q = reindex-center-imprecision q
    (trans (sym targetᴾ) ground-center) (sym targetᴵ)

  center-target : embedImprecise (core W) (`∀ A) ≡ ＇ Z
  center-target = variable-left-nonstar-target center-q
    (C.renameNonStar
      (C.toRenameᵗ (impreciseEmbedding (core W))) nonstar)
dynamic-atom-target-occupant {Dᴵ = `∀ A}
    ground-center nonstar q targetᴾ targetᴵ | ()

base-consistency-no-generated-variable : ∀ {Δ} {μ : C.Env∼ Δ}
    {ι : Base} {B : Ty Δ} {X : TyVar Δ}
  → μ X ≡ C.★∼X
  → (c : μ C.⊢ ‵ ι ∼ B)
  → X ∈ᵗ B
  → ⊥
base-consistency-no-generated-variable mode ((C.gen c) A≢★)
    (∈-all occurs) =
  base-consistency-no-generated-variable mode c occurs

base-generalization-impossible : ∀ {Δ} {μ : C.Env∼ Δ}
    {ι : Base} {B : Ty (suc Δ)}
  → (c : C.genᵐ μ C.⊢ ⇑ᵗ (‵ ι) ∼ B)
  → NonVar B
  → Fin.zero ∈ᵗ B
  → ⊥
base-generalization-impossible c nonvar occurs =
  base-consistency-no-generated-variable refl c occurs

base-ground-other-impossible : ∀ {Δ} {μ : C.Env∼ Δ}
    {ι : Base} {B : Ty Δ}
  → (c : μ C.⊢ ‵ ι ∼ B)
  → NonStar B
  → B ≢ ‵ ι
  → ⊥
base-ground-other-impossible (C.id (‵ ι)) nonstar B≢ι = B≢ι refl
base-ground-other-impossible
    ((C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c) A≢★) nonstar B≢ι =
  base-generalization-impossible c Bnv occurs

precise-base-generalization-impossible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {C : Ty Δᴾ} {ι : Base}
    {μ : C.Env∼ Δᴾ} {B : Ty (suc Δᴾ)}
  → embedPrecise (core W) C ≡ ‵ ι
  → (c : C.genᵐ μ C.⊢ ⇑ᵗ C ∼ B)
  → NonVar B
  → Fin.zero ∈ᵗ B
  → ⊥
precise-base-generalization-impossible {W = W} {C = C} {ι = ι}
    {μ = μ} {B = B} source c nonvar occurs =
  base-generalization-impossible c′ nonvar occurs
  where
  source-eq : C ≡ ‵ ι
  source-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W))) source

  c′ : C.genᵐ μ C.⊢ ⇑ᵗ (‵ ι) ∼ B
  c′ = subst≡ (λ A → C.genᵐ μ C.⊢ ⇑ᵗ A ∼ B) source-eq c

variable-consistency-no-generated-variable : ∀ {Δ}
    {μ : C.Env∼ Δ} {X Y : TyVar Δ} {B : Ty Δ}
  → X ≢ Y
  → (c : μ C.⊢ ＇ X ∼ B)
  → Y ∈ᵗ B
  → ⊥
variable-consistency-no-generated-variable X≢Y (C.id (＇ X)) var-∈ =
  X≢Y refl
variable-consistency-no-generated-variable X≢Y ((C.gen c) A≢★)
    (∈-all occurs) =
  variable-consistency-no-generated-variable
    (λ { refl → X≢Y refl }) c occurs

variable-ground-other-impossible : ∀ {Δ} {μ : C.Env∼ Δ}
    {X : TyVar Δ} {B : Ty Δ}
  → (c : μ C.⊢ ＇ X ∼ B)
  → NonStar B
  → B ≢ ＇ X
  → ⊥
variable-ground-other-impossible (C.id (＇ X)) nonstar B≢X = B≢X refl
variable-ground-other-impossible
    ((C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c) A≢★) nonstar B≢X =
  variable-consistency-no-generated-variable (λ ()) c occurs

ground-cast-target-unique⊑ : ∀ {Δ} {μ : I.ImpEnv Δ}
    {ν : C.Env∼ Δ} {A B H G : Ty Δ}
  → Ground A
  → (h : Ground H)
  → (g : Ground G)
  → NonStar B
  → ν C.⊢ B ∼ G
  → μ I.⊢ A ⊑ H
  → μ I.⊢ A ⊑ B
  → H ≡ G
ground-cast-target-unique⊑ {G = G}
    (＇ X) h g Bns c I.X⊑X I.X⊑X
    with G ≟Ty ＇ X
ground-cast-target-unique⊑ {G = G}
    (＇ X) h g Bns c I.X⊑X I.X⊑X
    | yes G≡X = sym G≡X
ground-cast-target-unique⊑ {G = G}
    (＇ X) h g Bns c I.X⊑X I.X⊑X
    | no G≢X =
  ⊥-elim (variable-ground-other-impossible c
    (C.ground-nonstar g) G≢X)
ground-cast-target-unique⊑ (‵ ι) h g Bns c p q =
  ground-targets-unique⊑ h g p
    (ground-cast-target⊑ g Bns c q
      (ground-target-nonvar-to-star⊑ h nonvar-base p))
ground-cast-target-unique⊑ ★⇒★ h g Bns c p q =
  ground-targets-unique⊑ h g p
    (ground-cast-target⊑ g Bns c q
      (ground-target-nonvar-to-star⊑ h nonvar-fun p))
ground-cast-target-unique⊑ ∀★ h g Bns c p q =
  ground-targets-unique⊑ h g p
    (ground-cast-target⊑ g Bns c q
      (ground-target-nonvar-to-star⊑ h nonvar-all p))

ground-left-nonstar-target : ∀ {Δ} {μ : I.ImpEnv Δ}
    {G B : Ty Δ}
  → Ground G
  → μ I.⊢ G ⊑ B
  → NonStar B
  → G ≡ B
ground-left-nonstar-target (＇ X) I.X⊑X nonstar = refl
ground-left-nonstar-target (＇ X) (I.X⊑★ eq) ()
ground-left-nonstar-target (‵ ι) I.ι⊑ι nonstar = refl
ground-left-nonstar-target (‵ ι) I.ι⊑★ ()
ground-left-nonstar-target ★⇒★
    (I.⇒⊑⇒ I.★⊑★ I.★⊑★) nonstar = refl
ground-left-nonstar-target ★⇒★ (I.⇒⊑★ p q) ()
ground-left-nonstar-target ∀★ (I.∀⊑∀ I.★⊑★) nonstar = refl
ground-left-nonstar-target ∀★ I.∀★⊑★ ()
ground-left-nonstar-target ∀★ (I.∀⊑★ Ans p) ()

nonvar-left-variable-impossible : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A : Ty Δ} {X : TyVar Δ}
  → μ I.⊢ A ⊑ ＇ X
  → NonVar A
  → ⊥
nonvar-left-variable-impossible I.X⊑X ()
nonvar-left-variable-impossible
    (I.∀⊑ Anv occurs p) nonvar-all =
  nonvar-left-variable-impossible p Anv

ground-cast-square-tags-agree : ∀ {Δ}
    {μ : I.ImpEnv Δ} {ν₁ ν₂ : C.Env∼ Δ}
    {G₁ G₂ A₁ A₂ : Ty Δ}
  → Ground G₁
  → Ground G₂
  → NonStar A₁
  → NonStar A₂
  → ν₁ C.⊢ G₁ ∼ A₁
  → ν₂ C.⊢ G₂ ∼ A₂
  → μ I.⊢ A₁ ⊑ A₂
  → G₁ ≡ G₂
ground-cast-square-tags-agree {G₂ = G₂} (＇ X) g₂ ns₁ ns₂
    (C.id x) c₂ I.X⊑X with G₂ ≟Ty ＇ X
ground-cast-square-tags-agree (＇ X) g₂ ns₁ ns₂
    (C.id x) c₂ I.X⊑X | yes G₂≡X = sym G₂≡X
ground-cast-square-tags-agree (＇ X) g₂ ns₁ ns₂
    (C.id x) c₂ I.X⊑X | no G₂≢X =
  ⊥-elim (variable-ground-other-impossible (C.sym∼ c₂)
    (C.ground-nonstar g₂) G₂≢X)
ground-cast-square-tags-agree (＇ X) g₂ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★) c₂ q =
  ⊥-elim (variable-consistency-no-generated-variable
    (λ ()) c₁ occurs)
ground-cast-square-tags-agree {G₂ = G₂} (‵ ι) g₂ ns₁ ns₂
    (C.id x) c₂ I.ι⊑ι with G₂ ≟Ty ‵ ι
ground-cast-square-tags-agree (‵ ι) g₂ ns₁ ns₂
    (C.id x) c₂ I.ι⊑ι | yes G₂≡ι = sym G₂≡ι
ground-cast-square-tags-agree (‵ ι) g₂ ns₁ ns₂
    (C.id x) c₂ I.ι⊑ι | no G₂≢ι =
  ⊥-elim (base-ground-other-impossible (C.sym∼ c₂)
    (C.ground-nonstar g₂) G₂≢ι)
ground-cast-square-tags-agree (‵ ι) g₂ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★) c₂ q =
  ⊥-elim (base-generalization-impossible c₁ Bnv occurs)
ground-cast-square-tags-agree ★⇒★ (＇ X) ns₁ ns₂
    (c₁ C.↦ c₃) () (I.⇒⊑⇒ q q₁)
ground-cast-square-tags-agree ★⇒★ (‵ ι) ns₁ ns₂
    (c₁ C.↦ c₃) () (I.⇒⊑⇒ q q₁)
ground-cast-square-tags-agree ★⇒★ ★⇒★ ns₁ ns₂
    (c₁ C.↦ c₃) c₂ (I.⇒⊑⇒ q q₁) = refl
ground-cast-square-tags-agree ★⇒★ ∀★ ns₁ ns₂ (c₁ C.↦ c₃)
    (C.inst_ ⦃ Anv ⦄ ⦃ () ⦄ c₂ B≢★) (I.⇒⊑⇒ q q₁)
ground-cast-square-tags-agree ★⇒★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    (C.∀ᶜ c₂) (I.∀⊑∀ q)
    with source-occurs-target refl q occurs
ground-cast-square-tags-agree ★⇒★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    (C.∀ᶜ c₂) (I.∀⊑∀ q) | target-occurs
    with consistency-target-occurs-source refl c₂ target-occurs
ground-cast-square-tags-agree ★⇒★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    (C.∀ᶜ c₂) (I.∀⊑∀ q) | target-occurs | ()
ground-cast-square-tags-agree ★⇒★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    (C.inst_ ⦃ Anv ⦄ ⦃ () ⦄ c₂ B≢★) (I.∀⊑∀ q)
ground-cast-square-tags-agree ★⇒★ g₂ ns₁ ns₂
    (C.gen_ ⦃ Bnv₁ ⦄ ⦃ occurs₁ ⦄ c₁ A₁≢★)
    (C.gen_ ⦃ Bnv₂ ⦄ ⦃ occurs₂ ⦄ c₂ A₂≢★)
    (I.∀⊑∀ q) =
  shift-injectiveᵗ (ground-cast-square-tags-agree
    (shift-ground ★⇒★) (shift-ground g₂)
    (nonvar-occurs-nonstar Bnv₁ occurs₁)
    (nonvar-occurs-nonstar Bnv₂ occurs₂) c₁ c₂ q)
ground-cast-square-tags-agree ★⇒★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    C.bot-intro (I.∀⊑∀ q) =
  ⊥-elim (nonvar-left-variable-impossible q Bnv)
ground-cast-square-tags-agree {ν₂ = ν₂} ★⇒★ g₂ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★) c₂
    (I.∀⊑ Anv occurs₂ q) =
  shift-injectiveᵗ (ground-cast-square-tags-agree
    (shift-ground ★⇒★) (shift-ground g₂)
    (nonvar-occurs-nonstar Bnv occurs)
    (C.renameNonStar Fin.suc ns₂) c₁
    (C.rename∼ {μ = ν₂} {μ′ = C.extᵐ ν₂}
      Fin.suc (λ Y → refl) c₂) q)
ground-cast-square-tags-agree ∀★ ∀★ ns₁ ns₂
    (C.∀ᶜ c₁) (C.∀ᶜ c₂) (I.∀⊑∀ q) = refl
ground-cast-square-tags-agree ∀★ ∀★ ns₁ ns₂
    (C.∀ᶜ c₁) (C.inst_ ⦃ Anv ⦄ ⦃ () ⦄ c₂ B≢★)
    (I.∀⊑∀ q)
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂
    (C.∀ᶜ c₁)
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₂ A≢★)
    (I.∀⊑∀ q)
    with target-occurs-source q occurs
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂
    (C.∀ᶜ c₁)
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₂ A≢★)
    (I.∀⊑∀ q) | source-occurs
    with consistency-target-occurs-source refl c₁ source-occurs
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂
    (C.∀ᶜ c₁)
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₂ A≢★)
    (I.∀⊑∀ q) | source-occurs | ()
ground-cast-square-tags-agree ∀★ ∀★ ns₁ ns₂
    (C.∀ᶜ c₁) C.bot-intro (I.∀⊑∀ q) = refl
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂ (C.∀ᶜ c₁) c₂
    (I.∀⊑ Bnv occurs q)
    with consistency-target-occurs-source refl c₁ occurs
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂ (C.∀ᶜ c₁) c₂
    (I.∀⊑ Bnv occurs q) | ()
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂ (C.∀ᶜ c₁) c₂
    I.bot-elim
    with consistency-target-occurs-source refl c₁ var-∈
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂ (C.∀ᶜ c₁) c₂
    I.bot-elim | ()
ground-cast-square-tags-agree ∀★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    (C.∀ᶜ c₂) (I.∀⊑∀ q) = refl
ground-cast-square-tags-agree ∀★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    (C.inst_ ⦃ Anv₂ ⦄ ⦃ () ⦄ c₂ B≢★) (I.∀⊑∀ q)
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂
    (C.gen_ ⦃ Bnv₁ ⦄ ⦃ occurs₁ ⦄ c₁ A₁≢★)
    (C.gen_ ⦃ Bnv₂ ⦄ ⦃ occurs₂ ⦄ c₂ A₂≢★)
    (I.∀⊑∀ q) =
  shift-injectiveᵗ (ground-cast-square-tags-agree
    (shift-ground ∀★) (shift-ground g₂)
    (nonvar-occurs-nonstar Bnv₁ occurs₁)
    (nonvar-occurs-nonstar Bnv₂ occurs₂) c₁ c₂ q)
ground-cast-square-tags-agree ∀★ ∀★ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★)
    C.bot-intro (I.∀⊑∀ q) = refl
ground-cast-square-tags-agree {ν₂ = ν₂} ∀★ g₂ ns₁ ns₂
    (C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c₁ A≢★) c₂
    (I.∀⊑ Anv occurs₂ q) =
  shift-injectiveᵗ (ground-cast-square-tags-agree
    (shift-ground ∀★) (shift-ground g₂)
    (nonvar-occurs-nonstar Bnv occurs)
    (C.renameNonStar Fin.suc ns₂) c₁
    (C.rename∼ {μ = ν₂} {μ′ = C.extᵐ ν₂}
      Fin.suc (λ Y → refl) c₂) q)
ground-cast-square-tags-agree ∀★ g₂ ns₁ ns₂ C.bot-intro c₂ q =
  ground-targets-unique⊑ ∀★ g₂ I.bot-elim
    (expand-cast-source⊑ g₂ ns₂ c₂ I.bot⊑★ q)

dynamic-payload-projection-tags-agree : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Hᴾ Gᴾ : Ty Δᴾ} {Hᴵ Gᴵ Dᴵ : Ty Δᴵ}
    {Bᴾ Bᴵ : Ty Δᶜ}
    {μᴵ : C.Env∼ Δᴵ}
  → (hᴵ : Ground Hᴵ)
  → (gᴾ : Ground Gᴾ)
  → (gᴵ : Ground Gᴵ)
  → Hᴾ ≡ Gᴾ
  → impEnv (core W) I.⊢ embedPrecise (core W) Hᴾ
      ⊑ embedImprecise (core W) Hᴵ
  → (cᴵ : μᴵ C.⊢ Gᴵ ∼ Dᴵ)
  → (nsᴵ : NonStar Dᴵ)
  → (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
  → embedPrecise (core W) Gᴾ ≡ Bᴾ
  → embedImprecise (core W) Dᴵ ≡ Bᴵ
  → Hᴵ ≡ Gᴵ
dynamic-payload-projection-tags-agree {W = W} {Hᴾ = Hᴾ}
    {Gᴾ = Gᴾ} {Hᴵ = Hᴵ} {Gᴵ = Gᴵ} {Dᴵ = Dᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {μᴵ = μᴵ}
    hᴵ gᴾ gᴵ Hᴾ≡Gᴾ payload-q cᴵ nsᴵ q targetᴾ targetᴵ =
  renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W))) center-eq
  where
  ρᴾ = C.toRenameᵗ (preciseEmbedding (core W))
  ρᴵ = C.toRenameᵗ (impreciseEmbedding (core W))

  payload-q′ : impEnv (core W) I.⊢ renameᵗ ρᴾ Gᴾ ⊑ renameᵗ ρᴵ Hᴵ
  payload-q′ = reindex-center-imprecision payload-q
    (cong (renameᵗ ρᴾ) Hᴾ≡Gᴾ) refl

  target-q : impEnv (core W) I.⊢ renameᵗ ρᴾ Gᴾ ⊑ renameᵗ ρᴵ Dᴵ
  target-q = reindex-center-imprecision q (sym targetᴾ) (sym targetᴵ)

  embedded-cᴵ :
      C.renameEnv∼ (impreciseEmbedding (core W)) (C.flipᵐ μᴵ) C.⊢
        renameᵗ ρᴵ Dᴵ ∼ renameᵗ ρᴵ Gᴵ
  embedded-cᴵ = C.rename∼ {μ = C.flipᵐ μᴵ}
    {μ′ = C.renameEnv∼ (impreciseEmbedding (core W)) (C.flipᵐ μᴵ)}
    ρᴵ
    (C.renameEnv∼-preserves
      (impreciseEmbedding (core W)) (C.flipᵐ μᴵ))
    (C.sym∼ cᴵ)

  center-eq : renameᵗ ρᴵ Hᴵ ≡ renameᵗ ρᴵ Gᴵ
  center-eq = ground-cast-target-unique⊑
    (C.renameGround ρᴾ gᴾ) (C.renameGround ρᴵ hᴵ)
    (C.renameGround ρᴵ gᴵ) (C.renameNonStar ρᴵ nsᴵ)
    embedded-cᴵ payload-q′ target-q

dynamic-payload-projection-target-agrees : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Hᴾ Gᴾ : Ty Δᴾ} {Hᴵ Dᴵ : Ty Δᴵ}
    {Bᴾ Bᴵ : Ty Δᶜ}
  → (hᴵ : Ground Hᴵ)
  → (gᴾ : Ground Gᴾ)
  → Hᴾ ≡ Gᴾ
  → impEnv (core W) I.⊢ embedPrecise (core W) Hᴾ
      ⊑ embedImprecise (core W) Hᴵ
  → NonStar Dᴵ
  → (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
  → embedPrecise (core W) Gᴾ ≡ Bᴾ
  → embedImprecise (core W) Dᴵ ≡ Bᴵ
  → Dᴵ ≡ Hᴵ
dynamic-payload-projection-target-agrees {W = W} {Hᴾ = Hᴾ}
    {Gᴾ = Gᴾ} {Hᴵ = Hᴵ} {Dᴵ = Dᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    hᴵ gᴾ Hᴾ≡Gᴾ payload-q nsᴵ q targetᴾ targetᴵ =
  renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W))) center-eq
  where
  ρᴾ = C.toRenameᵗ (preciseEmbedding (core W))
  ρᴵ = C.toRenameᵗ (impreciseEmbedding (core W))

  payload-q′ : impEnv (core W) I.⊢ renameᵗ ρᴾ Gᴾ ⊑ renameᵗ ρᴵ Hᴵ
  payload-q′ = reindex-center-imprecision payload-q
    (cong (renameᵗ ρᴾ) Hᴾ≡Gᴾ) refl

  target-q : impEnv (core W) I.⊢ renameᵗ ρᴾ Gᴾ ⊑ renameᵗ ρᴵ Dᴵ
  target-q = reindex-center-imprecision q (sym targetᴾ) (sym targetᴵ)

  payload-eq : renameᵗ ρᴾ Gᴾ ≡ renameᵗ ρᴵ Hᴵ
  payload-eq = ground-left-nonstar-target
    (C.renameGround ρᴾ gᴾ) payload-q′
    (C.renameNonStar ρᴵ (C.ground-nonstar hᴵ))

  target-eq : renameᵗ ρᴾ Gᴾ ≡ renameᵗ ρᴵ Dᴵ
  target-eq = ground-left-nonstar-target
    (C.renameGround ρᴾ gᴾ) target-q (C.renameNonStar ρᴵ nsᴵ)

  center-eq : renameᵗ ρᴵ Dᴵ ≡ renameᵗ ρᴵ Hᴵ
  center-eq = trans (sym target-eq) payload-eq

dynamic-payload-cast-tags-agree : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Hᴾ Gᴾ Dᴾ : Ty Δᴾ} {Hᴵ Gᴵ Dᴵ : Ty Δᴵ}
    {Bᴾ Bᴵ : Ty Δᶜ}
    {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
  → (hᴵ : Ground Hᴵ)
  → (gᴾ : Ground Gᴾ)
  → (gᴵ : Ground Gᴵ)
  → Hᴾ ≡ Gᴾ
  → impEnv (core W) I.⊢ embedPrecise (core W) Hᴾ
      ⊑ embedImprecise (core W) Hᴵ
  → (cᴾ : μᴾ C.⊢ Gᴾ ∼ Dᴾ)
  → (nsᴾ : NonStar Dᴾ)
  → (cᴵ : μᴵ C.⊢ Gᴵ ∼ Dᴵ)
  → (nsᴵ : NonStar Dᴵ)
  → (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
  → embedPrecise (core W) Dᴾ ≡ Bᴾ
  → embedImprecise (core W) Dᴵ ≡ Bᴵ
  → Hᴵ ≡ Gᴵ
dynamic-payload-cast-tags-agree {W = W} {Hᴾ = Hᴾ}
    {Gᴾ = Gᴾ} {Dᴾ = Dᴾ} {Hᴵ = Hᴵ} {Gᴵ = Gᴵ} {Dᴵ = Dᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {μᴾ = μᴾ} {μᴵ = μᴵ}
    hᴵ gᴾ gᴵ Hᴾ≡Gᴾ payload-q cᴾ nsᴾ cᴵ nsᴵ
    q targetᴾ targetᴵ =
  renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W))) center-eq
  where
  ρᴾ = C.toRenameᵗ (preciseEmbedding (core W))
  ρᴵ = C.toRenameᵗ (impreciseEmbedding (core W))

  payload-q′ : impEnv (core W) I.⊢ renameᵗ ρᴾ Gᴾ ⊑ renameᵗ ρᴵ Hᴵ
  payload-q′ = reindex-center-imprecision payload-q
    (cong (renameᵗ ρᴾ) Hᴾ≡Gᴾ) refl

  target-q : impEnv (core W) I.⊢ renameᵗ ρᴾ Dᴾ ⊑ renameᵗ ρᴵ Dᴵ
  target-q = reindex-center-imprecision q (sym targetᴾ) (sym targetᴵ)

  embedded-cᴾ :
      C.renameEnv∼ (preciseEmbedding (core W)) μᴾ C.⊢
        renameᵗ ρᴾ Gᴾ ∼ renameᵗ ρᴾ Dᴾ
  embedded-cᴾ = C.rename∼ {μ = μᴾ}
    {μ′ = C.renameEnv∼ (preciseEmbedding (core W)) μᴾ}
    ρᴾ (C.renameEnv∼-preserves (preciseEmbedding (core W)) μᴾ) cᴾ

  embedded-cᴵ :
      C.renameEnv∼ (impreciseEmbedding (core W)) μᴵ C.⊢
        renameᵗ ρᴵ Gᴵ ∼ renameᵗ ρᴵ Dᴵ
  embedded-cᴵ = C.rename∼ {μ = μᴵ}
    {μ′ = C.renameEnv∼ (impreciseEmbedding (core W)) μᴵ}
    ρᴵ (C.renameEnv∼-preserves (impreciseEmbedding (core W)) μᴵ) cᴵ

  payload-eq : renameᵗ ρᴾ Gᴾ ≡ renameᵗ ρᴵ Hᴵ
  payload-eq = ground-left-nonstar-target
    (C.renameGround ρᴾ gᴾ) payload-q′
    (C.renameNonStar ρᴵ (C.ground-nonstar hᴵ))

  cast-eq : renameᵗ ρᴾ Gᴾ ≡ renameᵗ ρᴵ Gᴵ
  cast-eq = ground-cast-square-tags-agree
    (C.renameGround ρᴾ gᴾ) (C.renameGround ρᴵ gᴵ)
    (C.renameNonStar ρᴾ nsᴾ) (C.renameNonStar ρᴵ nsᴵ)
    embedded-cᴾ embedded-cᴵ target-q

  center-eq : renameᵗ ρᴵ Hᴵ ≡ renameᵗ ρᴵ Gᴵ
  center-eq = trans (sym payload-eq) cast-eq

center-ground-other-impossible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {G B : Ty Δᴾ} {Z : TyVar Δᶜ}
    {μ : C.Env∼ Δᴾ}
  → (g : Ground G)
  → embedPrecise (core W) G ≡ ＇ Z
  → (c : μ C.⊢ G ∼ B)
  → NonStar B
  → B ≢ G
  → ⊥
center-ground-other-impossible (＇ X) center c nonstar B≢G =
  variable-ground-other-impossible c nonstar B≢G
center-ground-other-impossible (‵ ι) () c nonstar B≢G
center-ground-other-impossible ★⇒★ () c nonstar B≢G
center-ground-other-impossible ∀★ () c nonstar B≢G

precise-variable-generalization-impossible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {C : Ty Δᴾ} {Z : TyVar Δᶜ}
    {μ : C.Env∼ Δᴾ} {B : Ty (suc Δᴾ)}
  → embedPrecise (core W) C ≡ ＇ Z
  → (c : C.genᵐ μ C.⊢ ⇑ᵗ C ∼ B)
  → Fin.zero ∈ᵗ B
  → ⊥
precise-variable-generalization-impossible {C = ＇ X} source c occurs =
  variable-consistency-no-generated-variable (λ ()) c occurs
precise-variable-generalization-impossible {C = ‵ ι} () c occurs
precise-variable-generalization-impossible {C = ★} () c occurs
precise-variable-generalization-impossible {C = A ⇒ B} () c occurs
precise-variable-generalization-impossible {C = `∀ A} () c occurs

imprecise-variable-generalization-impossible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {C : Ty Δᴵ} {Z : TyVar Δᶜ}
    {μ : C.Env∼ Δᴵ} {B : Ty (suc Δᴵ)}
  → embedImprecise (core W) C ≡ ＇ Z
  → (c : C.genᵐ μ C.⊢ ⇑ᵗ C ∼ B)
  → Fin.zero ∈ᵗ B
  → ⊥
imprecise-variable-generalization-impossible {C = ＇ X}
    source c occurs =
  variable-consistency-no-generated-variable (λ ()) c occurs
imprecise-variable-generalization-impossible {C = ‵ ι} () c occurs
imprecise-variable-generalization-impossible {C = ★} () c occurs
imprecise-variable-generalization-impossible {C = A ⇒ B} () c occurs
imprecise-variable-generalization-impossible {C = `∀ A} () c occurs

casted-value-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
    (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → Value (Vᴵ ⟨ cᴵ ⟩)
  → Value (Vᴾ ⟨ cᴾ ⟩)
  → TypedEndpoints W q (Vᴵ ⟨ cᴵ ⟩) (Vᴾ ⟨ cᴾ ⟩)
casted-value-endpoints {W = W} sourceᴾ sourceᴵ cᴾ cᴵ
    targetᴾ targetᴵ related imprecise-cast-value precise-cast-value =
  typed-endpoints _ _ targetᴵ targetᴾ imprecise-cast-value
    precise-cast-value (⊢⟨⟩ Vᴵ⊢Cᴵ cᴵ) (⊢⟨⟩ Vᴾ⊢Cᴾ cᴾ)
  where
  endpoints = value-imprecision-endpoints related

  precise-source-eq : preciseType endpoints ≡ _
  precise-source-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (trans (preciseEmbedded endpoints) (sym sourceᴾ))

  imprecise-source-eq : impreciseType endpoints ≡ _
  imprecise-source-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (trans (impreciseEmbedded endpoints) (sym sourceᴵ))

  Vᴾ⊢Cᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    precise-source-eq (precise-typed endpoints)

  Vᴵ⊢Cᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    imprecise-source-eq (imprecise-typed endpoints)

precise-casted-value-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ : Ty Δᴵ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
    (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Cᴵ ≡ Bᴵ)
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → Value Vᴵ
  → Value (Vᴾ ⟨ cᴾ ⟩)
  → TypedEndpoints W q Vᴵ (Vᴾ ⟨ cᴾ ⟩)
precise-casted-value-endpoints {W = W} sourceᴾ sourceᴵ cᴾ
    targetᴾ targetᴵ related imprecise-value′ precise-cast-value =
  typed-endpoints _ _ targetᴵ targetᴾ imprecise-value′
    precise-cast-value Vᴵ⊢Cᴵ (⊢⟨⟩ Vᴾ⊢Cᴾ cᴾ)
  where
  endpoints = value-imprecision-endpoints related

  precise-source-eq : preciseType endpoints ≡ _
  precise-source-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (trans (preciseEmbedded endpoints) (sym sourceᴾ))

  imprecise-source-eq : impreciseType endpoints ≡ _
  imprecise-source-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (trans (impreciseEmbedded endpoints) (sym sourceᴵ))

  Vᴾ⊢Cᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    precise-source-eq (precise-typed endpoints)

  Vᴵ⊢Cᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    imprecise-source-eq (imprecise-typed endpoints)

no-precise-bottom-value : ∀ {Δᴾ Δᴵ Δᶜ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ (`∀ (＇ Fin.zero)) ⊑ Aᴵ}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ⊥
no-precise-bottom-value {W = W} related =
  no-bot-value (precise-value endpoints) Vᴾ⊢bot
  where
  endpoints = value-imprecision-endpoints related

  precise-type-eq : preciseType endpoints ≡ `∀ (＇ Fin.zero)
  precise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (preciseEmbedded endpoints)

  Vᴾ⊢bot = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    precise-type-eq (precise-typed endpoints)

nonvalue-computations-zero : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → Mᴵ ≢ blame
  → Mᴾ ≢ blame
  → E.value? Mᴵ ≡ nothing
  → E.value? Mᴾ ≡ nothing
  → ComputationsRelated W R zero Mᴵ Mᴾ
nonvalue-computations-zero _ _ _ _ = ClosureProof.computations-related-zero

blame-now : ∀ {Δ} {Σ : TyStore Δ}
  → BlamesFrom Σ zero (blame {Δ = Δ})
blame-now = _ , [] , ↠-refl , refl

blame-not-returned : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {result : E.EvalResult (blame {Δ = Δ})}
  → interpretFrom Σ gas blame ≡ returned result
  → ⊥
blame-not-returned {gas = zero} ()
blame-not-returned {gas = suc gas} ()

precise-pure-step-to-blame : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → Mᴾ ≢ blame
  → E.value? Mᴾ ≡ nothing
  → (stepᴾ : Mᴾ —→ blame)
  → E.step? (preciseStore (core W)) Mᴾ ≡
      just (E.step-result keep blame (pure-step stepᴾ))
  → ComputationsRelated W R k Mᴵ Mᴾ
precise-pure-step-to-blame {W = W} {k = k} {Mᴵ = Mᴵ}
    {Mᴾ = Mᴾ} Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ = record
  { forward-return = λ n≤k returnᴵ → inj₂ immediate-blame
  ; backward-return = backward
  ; forward-blame = λ n≤k blameᴵ → immediate-blame
  }
  where
  immediate-blame : Σ[ m ∈ ℕ ]
      BlamesFrom (preciseStore (core W)) m Mᴾ
  immediate-blame = suc zero , pure-step-blame-expand
    {Σ = preciseStore (core W)} {gas = zero}
    {M = Mᴾ} {N = blame} Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ
    (blame-now {Σ = preciseStore (core W)})

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n Mᴾ
        ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W _ (k ∸ n) resultᴵ resultᴾ
  backward {n = zero} n≤k returnᴾ
      with pure-step-return-invert
        {Σ = preciseStore (core W)} {n = zero}
        {M = Mᴾ} {N = blame} Mᴾ≢blame value-eqᴾ
        stepᴾ step-eqᴾ returnᴾ
  backward {n = zero} n≤k returnᴾ | ()
  backward {n = suc n} n≤k returnᴾ
      with pure-step-return-invert
        {Σ = preciseStore (core W)} {n = suc n}
        {M = Mᴾ} {N = blame} Mᴾ≢blame value-eqᴾ
        stepᴾ step-eqᴾ returnᴾ
  backward {n = suc n} n≤k returnᴾ
      | pure-step-return resultᴾ′ returnᴾ′ resultᴾ-eq =
    ⊥-elim (blame-not-returned
      {Σ = preciseStore (core W)} {gas = n} returnᴾ′)

identity-cast-redex-question : ∀ {Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.cast-redex? V (C.id {μ = μ} a) ≡
        just (E.step-result keep V (pure-step (β-id vV′)))
identity-cast-redex-question (ƛ N) = (ƛ N) , refl
identity-cast-redex-question (Λ vV)
    with value-question-complete (Λ vV)
identity-cast-redex-question (Λ vV) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
identity-cast-redex-question ($ κ) = ($ κ) , refl
identity-cast-redex-question (vV 《 inert 》)
    with value-question-complete (vV 《 inert 》)
identity-cast-redex-question (vV 《 inert 》) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
identity-cast-redex-question (vV ↑ reveal)
    with value-question-complete (vV ↑ reveal)
identity-cast-redex-question (vV ↑ reveal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
identity-cast-redex-question (vV ↓ conceal)
    with value-question-complete (vV ↓ conceal)
identity-cast-redex-question (vV ↓ conceal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl

bot-intro-redex-question : ∀ {Δ}
    {V : Term Δ} {μ : C.Env∼ Δ}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.cast-redex? V (C.bot-intro {μ = μ}) ≡
        just (E.step-result keep blame
          (pure-step (blame-bot-intro vV′)))
bot-intro-redex-question (ƛ N) = (ƛ N) , refl
bot-intro-redex-question (Λ vV)
    with value-question-complete (Λ vV)
bot-intro-redex-question (Λ vV) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
bot-intro-redex-question ($ κ) = ($ κ) , refl
bot-intro-redex-question (vV 《 inert 》)
    with value-question-complete (vV 《 inert 》)
bot-intro-redex-question (vV 《 inert 》) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
bot-intro-redex-question (vV ↑ reveal)
    with value-question-complete (vV ↑ reveal)
bot-intro-redex-question (vV ↑ reveal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
bot-intro-redex-question (vV ↓ conceal)
    with value-question-complete (vV ↓ conceal)
bot-intro-redex-question (vV ↓ conceal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl

bot-intro-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ (V ⟨ C.bot-intro {μ = μ} ⟩) ≡
        just (E.step-result keep blame
          (pure-step (blame-bot-intro vV′)))
bot-intro-step-question {Σ = Σ} {V = V} vV
    with E.step? Σ V | value-step-none {Σ = Σ} vV
       | bot-intro-redex-question vV
bot-intro-step-question vV
    | nothing | step-eq | vV′ , redex-eq = vV′ , redex-eq
bot-intro-step-question vV
    | just step | () | redex-complete

bot-intro-cast-value-none : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ}
  → Value V
  → E.value? (V ⟨ C.bot-intro {μ = μ} ⟩) ≡ nothing
bot-intro-cast-value-none vV with value-question-complete vV
bot-intro-cast-value-none vV | vV′ , value-eq
    rewrite value-eq = refl

related-precise-bot-intro : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ} {μᴾ : C.Env∼ Δᴾ}
  → Value Vᴾ
  → ComputationsRelated W R k Mᴵ
      (Vᴾ ⟨ C.bot-intro {μ = μᴾ} ⟩)
related-precise-bot-intro {W = W} vVᴾ
    with bot-intro-step-question
      {Σ = preciseStore (core W)} vVᴾ
related-precise-bot-intro vVᴾ | vVᴾ′ , step-eq =
  precise-pure-step-to-blame (λ ())
    (bot-intro-cast-value-none vVᴾ)
    (blame-bot-intro vVᴾ′) step-eq

identity-cast-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ (V ⟨ C.id {μ = μ} a ⟩) ≡
        just (E.step-result keep V (pure-step (β-id vV′)))
identity-cast-step-question {Σ = Σ} {V = V} vV
    with E.step? Σ V | value-step-none {Σ = Σ} vV
       | identity-cast-redex-question vV
identity-cast-step-question vV
    | nothing | step-eq | vV′ , redex-eq = vV′ , redex-eq
identity-cast-step-question vV
    | just step | () | redex-complete

identity-cast-return-exact : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (gas : ℕ)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      interpretFrom Σ (suc gas) (V ⟨ C.id {μ = μ} a ⟩) ≡
        returned (E.result Δ (keep ∷ []) V
          (↠-step (pure-step (β-id vV′)) ↠-refl) vV′)
identity-cast-return-exact {Σ = Σ} gas vV
    with identity-cast-step-question {Σ = Σ} vV
identity-cast-return-exact {Σ = Σ} gas vV | vV′ , step-eq =
  vV′ , prepend-return {Σ = Σ} step-eq
    (value-return-exact {Σ = Σ} gas vV′)

identity-cast-zero-timed : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (vV : Value V)
  → interpretFrom Σ zero (V ⟨ C.id {μ = μ} a ⟩) ≡ timed
identity-cast-zero-timed vV with value-question-complete vV
identity-cast-zero-timed vV | vV′ , value-eq
    rewrite value-eq = refl

dynamic-atom-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → TypedEndpoints W (I.X⊑★ mode) Vᴵ Vᴾ
dynamic-atom-endpoints {k = zero} endpoints = endpoints
dynamic-atom-endpoints {k = suc k} (endpoints , behavior) = endpoints

dynamic-atom-source-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → DynamicAtomHolds (ValueImprecisionᵏ k W) (semanticEntry W Z) mode
      Vᴵ Vᴾ
  → TypedEndpoints W (I.X⊑★ mode) Vᴵ Vᴾ
dynamic-atom-source-endpoints {W = W} {Z = Z} {mode = mode} holds =
  ClosureProof.dynamic-holds-endpoints (semanticEntry W Z) mode
    (I.X⊑★ mode) holds

-- Sealed payloads related at a dynamic slot are related values at the
-- slot's center variable at the same index.

dynamic-atom-source-value-at : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (k : ℕ) {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → DynamicAtomHolds (ValueImprecisionᵏ k W) (semanticEntry W Z) mode
      Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
dynamic-atom-source-value-at zero holds =
  dynamic-atom-source-endpoints {k = zero} holds
dynamic-atom-source-value-at (suc k) holds =
  dynamic-atom-source-endpoints holds , inj₁ holds

transport-paired-atom-holds : ∀ {Δᴾ Δᴵ Δᶜ mode mode′}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ}
    {entry : SemanticEntry W X mode} {ℛ : PayloadRelation W}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → (eq : mode ≡ mode′)
  → PairedAtomHolds ℛ entry Vᴵ Vᴾ
  → PairedAtomHolds ℛ
      (subst≡ (SemanticEntry W X) eq entry) Vᴵ Vᴾ
transport-paired-atom-holds refl related = related

right-dynamic-tag-endpoints : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {Gᴵ : Ty Δᴵ}
    (gᴵ : Ground Gᴵ) {μᴵ : C.Env∼ Δᴵ}
    (Gᴵ∼★ : μᴵ C.⊢ Gᴵ ∼★)
    (payload-q : impEnv (core W) I.⊢ Aᴾ
      ⊑ embedImprecise (core W) Gᴵ)
    (output-q : impEnv (core W) I.⊢ Aᴾ ⊑ ★)
    {k : ℕ} {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W payload-q k Uᴵ Vᴾ
  → TypedEndpoints W output-q
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩) Vᴾ
right-dynamic-tag-endpoints {W = W} {Gᴵ = Gᴵ} gᴵ Gᴵ∼★
    payload-q output-q {Uᴵ = Uᴵ} related =
  typed-endpoints ★ (preciseType endpoints) refl
    (preciseEmbedded endpoints) imprecise-tag-value
    (precise-value endpoints) imprecise-tag-typed
    (precise-typed endpoints)
  where
  endpoints = value-imprecision-endpoints related

  imprecise-type-eq : impreciseType endpoints ≡ Gᴵ
  imprecise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (impreciseEmbedded endpoints)

  Uᴵ⊢Gᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ Uᴵ ⦂ A)
    imprecise-type-eq (imprecise-typed endpoints)

  imprecise-tag-value = imprecise-value endpoints 《
    inj ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      ⦃ Gns = C.ground-nonstar gᴵ ⦄ 》

  imprecise-tag-typed = ⊢⟨⟩ Uᴵ⊢Gᴵ
    (groundInjection gᴵ Gᴵ∼★)

right-dynamic-function-tag-value-at : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (j : ℕ) {A B : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ A ⊑ ★)
    (q : impEnv (core W) I.⊢ B ⊑ ★)
    {μᴵ : C.Env∼ Δᴵ} {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p q) j Uᴵ Vᴾ
  → ValueImprecision W (I.⇒⊑★ p q) j
      (Uᴵ ⟨ groundInjection ★⇒★ (C.⇒∼★ {μ = μᴵ}) ⟩) Vᴾ
right-dynamic-function-tag-value-at zero p q related =
  right-dynamic-tag-endpoints ★⇒★ C.⇒∼★
    (I.⇒⊑⇒ p q) (I.⇒⊑★ p q) {k = zero} related
right-dynamic-function-tag-value-at (suc j) p q related =
  right-dynamic-tag-endpoints ★⇒★ C.⇒∼★
    (I.⇒⊑⇒ p q) (I.⇒⊑★ p q) {k = suc j} related ,
  right-tags-and-payload ★⇒★ C.⇒∼★ (I.⇒⊑⇒ p q)
    (value-imprecision-downward-to
      {j = j} {k = suc j} (n≤1+n j) related)

right-dynamic-ground-tag-value-at : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (j : ℕ)
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    {Gᴵ : Ty Δᴵ} (gᴵ : Ground Gᴵ)
    {μᴵ : C.Env∼ Δᴵ} (Gᴵ∼★ : μᴵ C.⊢ Gᴵ ∼★)
    (payload-q : impEnv (core W) I.⊢
      embedPrecise (core W) Gᴾ ⊑ embedImprecise (core W) Gᴵ)
    {Bᴾ : Ty Δᶜ} (output-q : impEnv (core W) I.⊢ Bᴾ ⊑ ★)
    (left-eq : embedPrecise (core W) Gᴾ ≡ Bᴾ)
    {Uᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W payload-q j Uᴵ Vᴾ
  → ValueImprecision W output-q j
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩) Vᴾ
right-dynamic-ground-tag-value-at zero (＇ X) gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at zero (＇ X) gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.X⊑★ mode =
  ClosureProof.value-imprecision-reindex output-q (I.X⊑★ mode)
    {k = zero} (sym left-eq) refl
    (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q
      (I.X⊑★ mode) {k = zero} related)
right-dynamic-ground-tag-value-at zero (‵ ι) gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at zero (‵ ι) gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.ι⊑★ =
  ClosureProof.value-imprecision-reindex output-q I.ι⊑★
    {k = zero} (sym left-eq) refl
    (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q I.ι⊑★ {k = zero}
      related)
right-dynamic-ground-tag-value-at zero ★⇒★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at zero ★⇒★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.⇒⊑★ p q =
  ClosureProof.value-imprecision-reindex output-q (I.⇒⊑★ p q)
    {k = zero} (sym left-eq) refl
    (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q
      (I.⇒⊑★ p q) {k = zero} related)
right-dynamic-ground-tag-value-at zero ∀★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at zero ∀★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.∀★⊑★ =
  ClosureProof.value-imprecision-reindex output-q I.∀★⊑★
    {k = zero} (sym left-eq) refl
    (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q I.∀★⊑★ {k = zero}
      related)
right-dynamic-ground-tag-value-at {W = W} (suc j) (＇ X)
    {Gᴵ = Gᴵ} gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at {W = W} (suc j) (＇ X)
    {Gᴵ = Gᴵ} gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.X⊑★ mode =
  let paired-endpoints , paired-holds = paired-related
  in ClosureProof.value-imprecision-reindex output-q (I.X⊑★ mode)
       (sym left-eq) refl
       (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q
         (I.X⊑★ mode) related ,
       inj₂ (aligned-dynamic-atom-related Gᴵ gᴵ target-eq _ Gᴵ∼★
         _ refl paired-holds))
  where
  target-nonstar = C.renameNonStar
    (C.toRenameᵗ (impreciseEmbedding (core W)))
    (C.ground-nonstar gᴵ)

  target-eq = variable-left-nonstar-target payload-q target-nonstar

  paired-related = ClosureProof.value-imprecision-reindex I.X⊑X
    payload-q refl (sym target-eq) related
right-dynamic-ground-tag-value-at (suc j) (‵ ι) gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at (suc j) (‵ ι) gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.ι⊑★ =
  ClosureProof.value-imprecision-reindex output-q I.ι⊑★
    (sym left-eq) refl
    (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q I.ι⊑★ related ,
      right-tags-and-payload gᴵ Gᴵ∼★ payload-q
        (value-imprecision-downward-to (n≤1+n j) related))
right-dynamic-ground-tag-value-at (suc j) ★⇒★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at (suc j) ★⇒★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.⇒⊑★ p q =
  ClosureProof.value-imprecision-reindex output-q (I.⇒⊑★ p q)
    (sym left-eq) refl
    (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q
      (I.⇒⊑★ p q) related ,
      right-tags-and-payload gᴵ Gᴵ∼★ payload-q
        (value-imprecision-downward-to (n≤1+n j) related))
right-dynamic-ground-tag-value-at (suc j) ∀★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related
    with reindex-center-imprecision output-q (sym left-eq) refl
right-dynamic-ground-tag-value-at (suc j) ∀★ gᴵ Gᴵ∼★ payload-q
    output-q left-eq related | I.∀★⊑★ =
  ClosureProof.value-imprecision-reindex output-q I.∀★⊑★
    (sym left-eq) refl
    (right-dynamic-tag-endpoints gᴵ Gᴵ∼★ payload-q I.∀★⊑★ related ,
      right-tags-and-payload gᴵ Gᴵ∼★ payload-q
        (value-imprecision-downward-to (n≤1+n j) related))

related-imprecise-identity : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴵ : C.Env∼ Δᴵ} {aᴵ : Atom Bᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) Vᴾ
related-imprecise-identity {W = W} {p = p} {k = k}
    {μᴵ = μᴵ} {aᴵ = aᴵ} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-impossible
  }
  where
  endpoints = value-imprecision-endpoints related
  vVᴵ = imprecise-value endpoints
  vVᴾ = precise-value endpoints

  relation-after : ∀ n → FutureValueRelation p W future-refl
      (k ∸ n) Vᴵ Vᴾ
  relation-after n =
    value-imprecision-downward-to (m∸n≤m k n) related

  forward : ∀ {n} {resultᴵ}
    → n < k
    → interpretFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Vᴾ ]
          interpretFrom (preciseStore (core W)) m Vᴾ
            ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ)
  forward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  forward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  forward {n = zero} n≤k result-eq | zero-eq | ()
  forward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
       | value-return-exact {Σ = preciseStore (core W)} zero vVᴾ
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | precise-return
      with trans (sym imprecise-return) result-eq
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | precise-return | refl =
    inj₁ (zero , _ , precise-return ,
      paired-returns W future-refl refl refl
        (λ M → refl) (λ M → refl) (relation-after (suc n)))

  backward : ∀ {n} {resultᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n Vᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ]
        interpretFrom (impreciseStore (core W)) m
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = n} n≤k result-eq
      with value-return-exact {Σ = preciseStore (core W)} n vVᴾ
       | identity-cast-return-exact
          {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ}
          zero vVᴵ
  backward {n = n} n≤k result-eq
      | precise-return | vVᴵ′ , imprecise-return
      with trans (sym precise-return) result-eq
  backward {n = n} n≤k result-eq
      | precise-return | vVᴵ′ , imprecise-return | refl =
    suc zero , _ , imprecise-return ,
    paired-returns W future-refl refl refl
      (λ M → refl) (λ M → refl) (relation-after n)

  blame-impossible : ∀ {n}
    → n < k
    → BlamesFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩)
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq
      with trans (sym zero-eq) blame-eq
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq | ()
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return
      with trans (sym imprecise-return) blame-eq
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return | ()

related-precise-identity : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴾ : C.Env∼ Δᴾ} {aᴾ : Atom Bᴾ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k Vᴵ
      (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
related-precise-identity {W = W} {p = p} {k = k}
    {μᴾ = μᴾ} {aᴾ = aᴾ} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-impossible
  }
  where
  endpoints = value-imprecision-endpoints related
  vVᴵ = imprecise-value endpoints
  vVᴾ = precise-value endpoints

  relation-after : ∀ n → FutureValueRelation p W future-refl
      (k ∸ n) Vᴵ Vᴾ
  relation-after n =
    value-imprecision-downward-to (m∸n≤m k n) related

  forward : ∀ {n} {resultᴵ}
    → n < k
    → interpretFrom (impreciseStore (core W)) n Vᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ]
          interpretFrom (preciseStore (core W)) m
            (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩))
  forward {n = n} n≤k result-eq
      with value-return-exact {Σ = impreciseStore (core W)} n vVᴵ
       | identity-cast-return-exact
          {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} zero vVᴾ
  forward {n = n} n≤k result-eq
      | imprecise-return | vVᴾ′ , precise-return
      with trans (sym imprecise-return) result-eq
  forward {n = n} n≤k result-eq
      | imprecise-return | vVᴾ′ , precise-return | refl =
    inj₁ (suc zero , _ , precise-return ,
      paired-returns W future-refl refl refl
        (λ M → refl) (λ M → refl) (relation-after n))

  backward : ∀ {n} {resultᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Vᴵ ]
        interpretFrom (impreciseStore (core W)) m Vᴵ
          ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} vVᴾ
  backward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  backward {n = zero} n≤k result-eq | zero-eq | ()
  backward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} n vVᴾ
       | value-return-exact {Σ = impreciseStore (core W)} zero vVᴵ
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | imprecise-return
      with trans (sym precise-return) result-eq
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | imprecise-return | refl =
    zero , _ , imprecise-return ,
    paired-returns W future-refl refl refl
      (λ M → refl) (λ M → refl) (relation-after (suc n))

  blame-impossible : ∀ {n}
    → n < k
    → BlamesFrom (impreciseStore (core W)) n Vᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , blame-eq)
      with value-return-exact {Σ = impreciseStore (core W)} n vVᴵ
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , blame-eq) | imprecise-return
      with trans (sym imprecise-return) blame-eq
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , blame-eq) | imprecise-return | ()

related-identities : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴾ : C.Env∼ Δᴾ} {aᴾ : Atom Bᴾ}
    {μᴵ : C.Env∼ Δᴵ} {aᴵ : Atom Bᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩)
      (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
related-identities {W = W} {p = p} {k = k}
    {μᴾ = μᴾ} {aᴾ = aᴾ} {μᴵ = μᴵ} {aᴵ = aᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-impossible
  }
  where
  endpoints = value-imprecision-endpoints related
  vVᴵ = imprecise-value endpoints
  vVᴾ = precise-value endpoints

  relation-after : ∀ n → FutureValueRelation p W future-refl
      (k ∸ n) Vᴵ Vᴾ
  relation-after n =
    value-imprecision-downward-to (m∸n≤m k n) related

  forward : ∀ {n} {resultᴵ}
    → n < k
    → interpretFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ]
          interpretFrom (preciseStore (core W)) m
            (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩))
  forward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  forward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  forward {n = zero} n≤k result-eq | zero-eq | ()
  forward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
       | identity-cast-return-exact
          {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} zero vVᴾ
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | vVᴾ′ , precise-return
      with trans (sym imprecise-return) result-eq
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | vVᴾ′ , precise-return | refl =
    inj₁ (suc zero , _ , precise-return ,
      paired-returns W future-refl refl refl
        (λ M → refl) (λ M → refl) (relation-after (suc n)))

  backward : ∀ {n} {resultᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ]
        interpretFrom (impreciseStore (core W)) m
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} vVᴾ
  backward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  backward {n = zero} n≤k result-eq | zero-eq | ()
  backward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} n vVᴾ
       | identity-cast-return-exact
          {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} zero vVᴵ
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | vVᴵ′ , imprecise-return
      with trans (sym precise-return) result-eq
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | vVᴵ′ , imprecise-return | refl =
    suc zero , _ , imprecise-return ,
    paired-returns W future-refl refl refl
      (λ M → refl) (λ M → refl) (relation-after (suc n))

  blame-impossible : ∀ {n}
    → n < k
    → BlamesFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩)
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq
      with trans (sym zero-eq) blame-eq
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq | ()
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return
      with trans (sym imprecise-return) blame-eq
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return | ()

related-dynamic-tag-left : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation I.★⊑★) k Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
related-dynamic-tag-left {W = W} {k = k}
    gᴾ ground-center Gᴾ∼★ related =
  related-values-return (imprecise-value endpoints)
    (precise-value output-endpoints) at-every-index
  where
  endpoints = dynamic-atom-endpoints related

  output-endpoints =
    dynamic-atom-tag-endpoints gᴾ ground-center Gᴾ∼★ endpoints

  at-every-index : ∀ j → j ≤ k
    → FutureValueRelation I.★⊑★ W future-refl j _ _
  at-every-index j j≤k = dynamic-atom-tag-value-at j gᴾ
    ground-center Gᴾ∼★ (value-imprecision-downward-to j≤k related)

related-dynamic-id★-tag : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {μᴵ : C.Env∼ Δᴵ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation I.★⊑★) k
      (Vᴵ ⟨ C.id {μ = μᴵ} ★ ⟩)
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
related-dynamic-id★-tag {k = k} gᴾ ground-center Gᴾ∼★ related =
  related-imprecise-identity
    (dynamic-atom-tag-value-at k gᴾ ground-center Gᴾ∼★ related)

closed-value-compatible-bounded : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Cᴾ : Ty Δᴾ} {Cᴵ : Ty Δᴵ}
    {p : Cᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ∀ j → j ≤ k
  → CompiledTermRelation {W = W} p j [] Vᴾ Vᴵ
closed-value-compatible-bounded {W = W} {p = p} related j j≤k
    W′ W≼W′ related-empty =
  ClosureProof.computations-related-reindex p′ p′ refl refl
    (sym imprecise-close-eq) (sym precise-close-eq) immediate
  where
  related′ = ClosureProof.value-imprecision-future W≼W′
    (value-imprecision-downward-to j≤k related)

  endpoints′ = value-imprecision-endpoints related′
  p′ = liftCenterImprecision W≼W′ p

  immediate = related-values-return
    (imprecise-value endpoints′) (precise-value endpoints′)
    (λ i i≤j → value-imprecision-downward-to i≤j related′)

  imprecise-close-eq = subst-closed
    (closingSubstitution
      (impreciseClosingSubstitution {W = W′} {k = j} related-empty))
    (imprecise-typed endpoints′)

  precise-close-eq = subst-closed
    (closingSubstitution
      (preciseClosingSubstitution {W = W′} {k = j} related-empty))
    (precise-typed endpoints′)

precise-consistency-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {A B : Ty Δᴾ} {μ : C.Env∼ Δᴾ}
  → (W≼W′ : Future W W′)
  → μ C.⊢ A ∼ B
  → ClosureProof.precise-consistency-env-future W≼W′ μ C.⊢
      ClosureProof.precise-ground-type W≼W′ A ∼
      ClosureProof.precise-ground-type W≼W′ B
precise-consistency-future future-refl c = c
precise-consistency-future
    (future-paired W≼W′ related) c =
  C.renameᵐᶜ C.wk↪ᵗ (precise-consistency-future W≼W′ c)
precise-consistency-future (future-precise W≼W′ r★) c =
  C.renameᵐᶜ C.wk↪ᵗ (precise-consistency-future W≼W′ c)
precise-consistency-future (future-imprecise W≼W′) c =
  precise-consistency-future W≼W′ c

imprecise-consistency-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {A B : Ty Δᴵ} {μ : C.Env∼ Δᴵ}
  → (W≼W′ : Future W W′)
  → μ C.⊢ A ∼ B
  → ClosureProof.imprecise-consistency-env-future W≼W′ μ C.⊢
      ClosureProof.imprecise-ground-type W≼W′ A ∼
      ClosureProof.imprecise-ground-type W≼W′ B
imprecise-consistency-future future-refl c = c
imprecise-consistency-future
    (future-paired W≼W′ related) c =
  C.renameᵐᶜ C.wk↪ᵗ (imprecise-consistency-future W≼W′ c)
imprecise-consistency-future (future-precise W≼W′ r★) c =
  imprecise-consistency-future W≼W′ c
imprecise-consistency-future (future-imprecise W≼W′) c =
  C.renameᵐᶜ C.wk↪ᵗ (imprecise-consistency-future W≼W′ c)

wk-renamed-env-preserves-suc : ∀ {Δ} (μ : C.Env∼ Δ) X
  → C.renameEnv∼ C.wk↪ᵗ μ (Fin.suc X) ≡ μ X
wk-renamed-env-preserves-suc μ X = trans
  (cong (C.renameEnv∼ C.wk↪ᵗ μ) (sym (toRename-wk-eq X)))
  (C.renameEnv∼-preserves C.wk↪ᵗ μ X)

ext-toRename-wk-eq : ∀ {Δ} (X : Fin.Fin (suc Δ))
  → extᵗ (C.toRenameᵗ C.wk↪ᵗ) X ≡ extᵗ Fin.suc X
ext-toRename-wk-eq Fin.zero = refl
ext-toRename-wk-eq (Fin.suc X) = cong Fin.suc (toRename-wk-eq X)

rename-universal-cast-wk : ∀ {Δ} {μ : C.Env∼ Δ}
    {A B : Ty (suc Δ)} (M : Term Δ) (c : C.extᵐ μ C.⊢ A ∼ B)
  → renameᵗᵐ C.wk↪ᵗ (M ⟨ C.∀ᶜ c ⟩) ≡
      renameᵗᵐ C.wk↪ᵗ M ⟨ C.∀ᶜ (C.rename∼
        { μ = C.extᵐ μ }
        { μ′ = C.extᵐ (C.renameEnv∼ C.wk↪ᵗ μ) }
        (extᵗ Fin.suc)
        (C.extᵐ-rename Fin.suc (wk-renamed-env-preserves-suc μ)) c) ⟩
rename-universal-cast-wk {μ = μ} {A = A} {B = B} M c =
  HE.≅-to-≡
    (Hcong₅ mk-cast-term HE.refl
      (HE.≡-to-≅ (cong `∀ (renameᵗ-cong A ext-toRename-wk-eq)))
      (HE.≡-to-≅ (cong `∀ (renameᵗ-cong B ext-toRename-wk-eq)))
      HE.refl
      (Hcong₄ mk-all HE.refl
        (HE.≡-to-≅ (renameᵗ-cong A ext-toRename-wk-eq))
        (HE.≡-to-≅ (renameᵗ-cong B ext-toRename-wk-eq))
        inner))
  where
  inner = rename∼-parallel≅
    (extᵗ (C.toRenameᵗ C.wk↪ᵗ)) (extᵗ Fin.suc)
    (C.extᵐ-rename (C.toRenameᵗ C.wk↪ᵗ)
      (C.renameEnv∼-preserves C.wk↪ᵗ μ))
    (C.extᵐ-rename Fin.suc (wk-renamed-env-preserves-suc μ))
    refl ext-toRename-wk-eq c

precise-universal-body-consistency-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {A B : Ty (suc Δᴾ)} {μ : C.Env∼ Δᴾ}
  → (W≼W′ : Future W W′)
  → C.extᵐ μ C.⊢ A ∼ B
  → C.extᵐ (ClosureProof.precise-consistency-env-future W≼W′ μ) C.⊢
      liftPreciseBody W≼W′ A ∼ liftPreciseBody W≼W′ B
precise-universal-body-consistency-future future-refl c = c
precise-universal-body-consistency-future {μ = μ}
    (future-paired W≼W′ related) c =
  C.rename∼
    {μ = C.extᵐ
      (ClosureProof.precise-consistency-env-future W≼W′ μ)}
    {μ′ = C.extᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.precise-consistency-env-future W≼W′ μ))}
    (extᵗ Fin.suc)
    (C.extᵐ-rename Fin.suc
      (λ X → trans
        (cong (C.renameEnv∼ C.wk↪ᵗ
          (ClosureProof.precise-consistency-env-future W≼W′ μ))
          (sym (toRename-wk-eq X)))
        (C.renameEnv∼-preserves C.wk↪ᵗ
          (ClosureProof.precise-consistency-env-future W≼W′ μ) X)))
    (precise-universal-body-consistency-future W≼W′ c)
precise-universal-body-consistency-future {μ = μ}
    (future-precise W≼W′ r★) c =
  C.rename∼
    {μ = C.extᵐ
      (ClosureProof.precise-consistency-env-future W≼W′ μ)}
    {μ′ = C.extᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.precise-consistency-env-future W≼W′ μ))}
    (extᵗ Fin.suc)
    (C.extᵐ-rename Fin.suc
      (λ X → trans
        (cong (C.renameEnv∼ C.wk↪ᵗ
          (ClosureProof.precise-consistency-env-future W≼W′ μ))
          (sym (toRename-wk-eq X)))
        (C.renameEnv∼-preserves C.wk↪ᵗ
          (ClosureProof.precise-consistency-env-future W≼W′ μ) X)))
    (precise-universal-body-consistency-future W≼W′ c)
precise-universal-body-consistency-future
    (future-imprecise W≼W′) c =
  precise-universal-body-consistency-future W≼W′ c

imprecise-universal-body-consistency-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {A B : Ty (suc Δᴵ)} {μ : C.Env∼ Δᴵ}
  → (W≼W′ : Future W W′)
  → C.extᵐ μ C.⊢ A ∼ B
  → C.extᵐ (ClosureProof.imprecise-consistency-env-future W≼W′ μ) C.⊢
      liftImpreciseBody W≼W′ A ∼ liftImpreciseBody W≼W′ B
imprecise-universal-body-consistency-future future-refl c = c
imprecise-universal-body-consistency-future {μ = μ}
    (future-paired W≼W′ related) c =
  C.rename∼
    {μ = C.extᵐ
      (ClosureProof.imprecise-consistency-env-future W≼W′ μ)}
    {μ′ = C.extᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.imprecise-consistency-env-future W≼W′ μ))}
    (extᵗ Fin.suc)
    (C.extᵐ-rename Fin.suc
      (λ X → trans
        (cong (C.renameEnv∼ C.wk↪ᵗ
          (ClosureProof.imprecise-consistency-env-future W≼W′ μ))
          (sym (toRename-wk-eq X)))
        (C.renameEnv∼-preserves C.wk↪ᵗ
          (ClosureProof.imprecise-consistency-env-future W≼W′ μ) X)))
    (imprecise-universal-body-consistency-future W≼W′ c)
imprecise-universal-body-consistency-future
    (future-precise W≼W′ r★) c =
  imprecise-universal-body-consistency-future W≼W′ c
imprecise-universal-body-consistency-future {μ = μ}
    (future-imprecise W≼W′) c =
  C.rename∼
    {μ = C.extᵐ
      (ClosureProof.imprecise-consistency-env-future W≼W′ μ)}
    {μ′ = C.extᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.imprecise-consistency-env-future W≼W′ μ))}
    (extᵗ Fin.suc)
    (C.extᵐ-rename Fin.suc
      (λ X → trans
        (cong (C.renameEnv∼ C.wk↪ᵗ
          (ClosureProof.imprecise-consistency-env-future W≼W′ μ))
          (sym (toRename-wk-eq X)))
        (C.renameEnv∼-preserves C.wk↪ᵗ
          (ClosureProof.imprecise-consistency-env-future W≼W′ μ) X)))
    (imprecise-universal-body-consistency-future W≼W′ c)

lift-precise-universal-cast : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴾ}
    {A B : Ty (suc Δᴾ)} (M : Term Δᴾ)
    (c : C.extᵐ μ C.⊢ A ∼ B)
  → liftPreciseTerm W≼W′ (M ⟨ C.∀ᶜ c ⟩) ≡
      liftPreciseTerm W≼W′ M
        ⟨ C.∀ᶜ (precise-universal-body-consistency-future W≼W′ c) ⟩
lift-precise-universal-cast future-refl M c = refl
lift-precise-universal-cast (future-paired W≼W′ related) M c
    rewrite lift-precise-universal-cast W≼W′ M c =
  rename-universal-cast-wk (liftPreciseTerm W≼W′ M)
    (precise-universal-body-consistency-future W≼W′ c)
lift-precise-universal-cast (future-precise W≼W′ r★) M c
    rewrite lift-precise-universal-cast W≼W′ M c =
  rename-universal-cast-wk (liftPreciseTerm W≼W′ M)
    (precise-universal-body-consistency-future W≼W′ c)
lift-precise-universal-cast (future-imprecise W≼W′) M c =
  lift-precise-universal-cast W≼W′ M c

lift-imprecise-universal-cast : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴵ}
    {A B : Ty (suc Δᴵ)} (M : Term Δᴵ)
    (c : C.extᵐ μ C.⊢ A ∼ B)
  → liftImpreciseTerm W≼W′ (M ⟨ C.∀ᶜ c ⟩) ≡
      liftImpreciseTerm W≼W′ M
        ⟨ C.∀ᶜ (imprecise-universal-body-consistency-future W≼W′ c) ⟩
lift-imprecise-universal-cast future-refl M c = refl
lift-imprecise-universal-cast
    (future-paired W≼W′ related) M c
    rewrite lift-imprecise-universal-cast W≼W′ M c =
  rename-universal-cast-wk (liftImpreciseTerm W≼W′ M)
    (imprecise-universal-body-consistency-future W≼W′ c)
lift-imprecise-universal-cast (future-precise W≼W′ r★) M c =
  lift-imprecise-universal-cast W≼W′ M c
lift-imprecise-universal-cast (future-imprecise W≼W′) M c
    rewrite lift-imprecise-universal-cast W≼W′ M c =
  rename-universal-cast-wk (liftImpreciseTerm W≼W′ M)
    (imprecise-universal-body-consistency-future W≼W′ c)

precise-ground-type-arrow : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A B : Ty Δᴾ)
  → ClosureProof.precise-ground-type W≼W′ (A ⇒ B) ≡
      (ClosureProof.precise-ground-type W≼W′ A ⇒
        ClosureProof.precise-ground-type W≼W′ B)
precise-ground-type-arrow future-refl A B = refl
precise-ground-type-arrow (future-paired W≼W′ related) A B
    rewrite precise-ground-type-arrow W≼W′ A B = refl
precise-ground-type-arrow (future-precise W≼W′ r★) A B
    rewrite precise-ground-type-arrow W≼W′ A B = refl
precise-ground-type-arrow (future-imprecise W≼W′) A B =
  precise-ground-type-arrow W≼W′ A B

imprecise-ground-type-arrow : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A B : Ty Δᴵ)
  → ClosureProof.imprecise-ground-type W≼W′ (A ⇒ B) ≡
      (ClosureProof.imprecise-ground-type W≼W′ A ⇒
        ClosureProof.imprecise-ground-type W≼W′ B)
imprecise-ground-type-arrow future-refl A B = refl
imprecise-ground-type-arrow (future-paired W≼W′ related) A B
    rewrite imprecise-ground-type-arrow W≼W′ A B = refl
imprecise-ground-type-arrow (future-precise W≼W′ r★) A B =
  imprecise-ground-type-arrow W≼W′ A B
imprecise-ground-type-arrow (future-imprecise W≼W′) A B
    rewrite imprecise-ground-type-arrow W≼W′ A B = refl

precise-function-domain-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴾ}
    {A A′ : Ty Δᴾ}
  → C.flipᵐ μ C.⊢ A′ ∼ A
  → C.flipᵐ (ClosureProof.precise-consistency-env-future W≼W′ μ) C.⊢
      ClosureProof.precise-ground-type W≼W′ A′ ∼
      ClosureProof.precise-ground-type W≼W′ A
precise-function-domain-future future-refl c = c
precise-function-domain-future
    (future-paired W≼W′ related) {μ = μ} c =
  C.rename∼
    {μ = C.flipᵐ
      (ClosureProof.precise-consistency-env-future W≼W′ μ)}
    {μ′ = C.flipᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.precise-consistency-env-future W≼W′ μ))}
    (C.toRenameᵗ C.wk↪ᵗ)
    (λ X → cong C.flipVar∼
      (C.renameEnv∼-preserves C.wk↪ᵗ
        (ClosureProof.precise-consistency-env-future W≼W′ μ) X))
    (precise-function-domain-future W≼W′ c)
precise-function-domain-future
    (future-precise W≼W′ r★) {μ = μ} c =
  C.rename∼
    {μ = C.flipᵐ
      (ClosureProof.precise-consistency-env-future W≼W′ μ)}
    {μ′ = C.flipᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.precise-consistency-env-future W≼W′ μ))}
    (C.toRenameᵗ C.wk↪ᵗ)
    (λ X → cong C.flipVar∼
      (C.renameEnv∼-preserves C.wk↪ᵗ
        (ClosureProof.precise-consistency-env-future W≼W′ μ) X))
    (precise-function-domain-future W≼W′ c)
precise-function-domain-future (future-imprecise W≼W′) c =
  precise-function-domain-future W≼W′ c

imprecise-function-domain-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴵ}
    {A A′ : Ty Δᴵ}
  → C.flipᵐ μ C.⊢ A′ ∼ A
  → C.flipᵐ (ClosureProof.imprecise-consistency-env-future W≼W′ μ) C.⊢
      ClosureProof.imprecise-ground-type W≼W′ A′ ∼
      ClosureProof.imprecise-ground-type W≼W′ A
imprecise-function-domain-future future-refl c = c
imprecise-function-domain-future
    (future-paired W≼W′ related) {μ = μ} c =
  C.rename∼
    {μ = C.flipᵐ
      (ClosureProof.imprecise-consistency-env-future W≼W′ μ)}
    {μ′ = C.flipᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.imprecise-consistency-env-future W≼W′ μ))}
    (C.toRenameᵗ C.wk↪ᵗ)
    (λ X → cong C.flipVar∼
      (C.renameEnv∼-preserves C.wk↪ᵗ
        (ClosureProof.imprecise-consistency-env-future W≼W′ μ) X))
    (imprecise-function-domain-future W≼W′ c)
imprecise-function-domain-future (future-precise W≼W′ r★) c =
  imprecise-function-domain-future W≼W′ c
imprecise-function-domain-future
    (future-imprecise W≼W′) {μ = μ} c =
  C.rename∼
    {μ = C.flipᵐ
      (ClosureProof.imprecise-consistency-env-future W≼W′ μ)}
    {μ′ = C.flipᵐ
      (C.renameEnv∼ C.wk↪ᵗ
        (ClosureProof.imprecise-consistency-env-future W≼W′ μ))}
    (C.toRenameᵗ C.wk↪ᵗ)
    (λ X → cong C.flipVar∼
      (C.renameEnv∼-preserves C.wk↪ᵗ
        (ClosureProof.imprecise-consistency-env-future W≼W′ μ) X))
    (imprecise-function-domain-future W≼W′ c)

precise-function-consistency-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴾ}
    {A A′ B B′ : Ty Δᴾ}
  → C.flipᵐ μ C.⊢ A′ ∼ A
  → μ C.⊢ B ∼ B′
  → ClosureProof.precise-consistency-env-future W≼W′ μ C.⊢
      (ClosureProof.precise-ground-type W≼W′ A ⇒
        ClosureProof.precise-ground-type W≼W′ B) ∼
      (ClosureProof.precise-ground-type W≼W′ A′ ⇒
        ClosureProof.precise-ground-type W≼W′ B′)
precise-function-consistency-future W≼W′ c d =
  precise-function-domain-future W≼W′ c C.↦
  precise-consistency-future W≼W′ d

imprecise-function-consistency-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴵ}
    {A A′ B B′ : Ty Δᴵ}
  → C.flipᵐ μ C.⊢ A′ ∼ A
  → μ C.⊢ B ∼ B′
  → ClosureProof.imprecise-consistency-env-future W≼W′ μ C.⊢
      (ClosureProof.imprecise-ground-type W≼W′ A ⇒
        ClosureProof.imprecise-ground-type W≼W′ B) ∼
      (ClosureProof.imprecise-ground-type W≼W′ A′ ⇒
        ClosureProof.imprecise-ground-type W≼W′ B′)
imprecise-function-consistency-future W≼W′ c d =
  imprecise-function-domain-future W≼W′ c C.↦
  imprecise-consistency-future W≼W′ d

lift-precise-cast : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {A B : Ty Δᴾ} {μ : C.Env∼ Δᴾ}
    (M : Term Δᴾ) (c : μ C.⊢ A ∼ B)
  → liftPreciseTerm W≼W′ (M ⟨ c ⟩) ≡
      liftPreciseTerm W≼W′ M ⟨ precise-consistency-future W≼W′ c ⟩
lift-precise-cast future-refl M c = refl
lift-precise-cast (future-paired W≼W′ related) M c
    rewrite lift-precise-cast W≼W′ M c = refl
lift-precise-cast (future-precise W≼W′ r★) M c
    rewrite lift-precise-cast W≼W′ M c = refl
lift-precise-cast (future-imprecise W≼W′) M c =
  lift-precise-cast W≼W′ M c

lift-imprecise-cast : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {A B : Ty Δᴵ} {μ : C.Env∼ Δᴵ}
    (M : Term Δᴵ) (c : μ C.⊢ A ∼ B)
  → liftImpreciseTerm W≼W′ (M ⟨ c ⟩) ≡
      liftImpreciseTerm W≼W′ M
        ⟨ imprecise-consistency-future W≼W′ c ⟩
lift-imprecise-cast future-refl M c = refl
lift-imprecise-cast (future-paired W≼W′ related) M c
    rewrite lift-imprecise-cast W≼W′ M c = refl
lift-imprecise-cast (future-precise W≼W′ r★) M c =
  lift-imprecise-cast W≼W′ M c
lift-imprecise-cast (future-imprecise W≼W′) M c
    rewrite lift-imprecise-cast W≼W′ M c = refl

lift-precise-function-cast : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴾ}
    {A A′ B B′ : Ty Δᴾ} (M : Term Δᴾ)
    (c : C.flipᵐ μ C.⊢ A′ ∼ A) (d : μ C.⊢ B ∼ B′)
  → liftPreciseTerm W≼W′ (M ⟨ c C.↦ d ⟩) ≡
      liftPreciseTerm W≼W′ M
        ⟨ precise-function-consistency-future W≼W′ c d ⟩
lift-precise-function-cast future-refl M c d = refl
lift-precise-function-cast (future-paired W≼W′ related) M c d
    rewrite lift-precise-function-cast W≼W′ M c d = refl
lift-precise-function-cast (future-precise W≼W′ r★) M c d
    rewrite lift-precise-function-cast W≼W′ M c d = refl
lift-precise-function-cast (future-imprecise W≼W′) M c d =
  lift-precise-function-cast W≼W′ M c d

lift-imprecise-function-cast : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {μ : C.Env∼ Δᴵ}
    {A A′ B B′ : Ty Δᴵ} (M : Term Δᴵ)
    (c : C.flipᵐ μ C.⊢ A′ ∼ A) (d : μ C.⊢ B ∼ B′)
  → liftImpreciseTerm W≼W′ (M ⟨ c C.↦ d ⟩) ≡
      liftImpreciseTerm W≼W′ M
        ⟨ imprecise-function-consistency-future W≼W′ c d ⟩
lift-imprecise-function-cast future-refl M c d = refl
lift-imprecise-function-cast (future-paired W≼W′ related) M c d
    rewrite lift-imprecise-function-cast W≼W′ M c d = refl
lift-imprecise-function-cast (future-precise W≼W′ r★) M c d =
  lift-imprecise-function-cast W≼W′ M c d
lift-imprecise-function-cast (future-imprecise W≼W′) M c d
    rewrite lift-imprecise-function-cast W≼W′ M c d = refl

closed-cast-compatible-bounded : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
    (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
    {k : ℕ}
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Eᴾ Fᴾ : Ty Δᴾ′} {Eᴵ Fᴵ : Ty Δᴵ′}
      {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ′}
      (r : impEnv (core W′) I.⊢ Pᴾ ⊑ Pᴵ)
      (r-sourceᴾ : embedPrecise (core W′) Eᴾ ≡ Pᴾ)
      (r-sourceᴵ : embedImprecise (core W′) Eᴵ ≡ Pᴵ)
      {νᴾ : C.Env∼ Δᴾ′} (dᴾ : νᴾ C.⊢ Eᴾ ∼ Fᴾ)
      {νᴵ : C.Env∼ Δᴵ′} (dᴵ : νᴵ C.⊢ Eᴵ ∼ Fᴵ)
      (s : impEnv (core W′) I.⊢ Qᴾ ⊑ Qᴵ)
      (s-targetᴾ : embedPrecise (core W′) Fᴾ ≡ Qᴾ)
      (s-targetᴵ : embedImprecise (core W′) Fᴵ ≡ Qᴵ)
      {j : ℕ} {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ r j Uᴵ Uᴾ
    → ComputationsRelated W′ (FutureValueRelation s) j
        (Uᴵ ⟨ dᴵ ⟩) (Uᴾ ⟨ dᴾ ⟩))
  → (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ)
  → ValueImprecision W p k Vᴵ Vᴾ
  → ∀ j → j ≤ k
  → CompiledTermRelation {W = W}
      (reindex-center-imprecision q (sym targetᴾ) (sym targetᴵ)) j []
      (Vᴾ ⟨ cᴾ ⟩) (Vᴵ ⟨ cᴵ ⟩)
closed-cast-compatible-bounded {W = W} {Cᴾ = Cᴾ} {Dᴾ = Dᴾ}
    {Cᴵ = Cᴵ} {Dᴵ = Dᴵ}
    p sourceᴾ sourceᴵ cᴾ cᴵ q
    targetᴾ targetᴵ cast-values Vᴵ Vᴾ related j j≤k W′ W≼W′
    related-empty =
  ClosureProof.computations-related-reindex q′ q-local′
    (cong (liftCenterTy W≼W′) (sym targetᴾ))
    (cong (liftCenterTy W≼W′) (sym targetᴵ))
    (sym imprecise-close-eq) (sym precise-close-eq) casted
  where
  p′ = liftCenterImprecision W≼W′ p
  q′ = liftCenterImprecision W≼W′ q
  q-local = reindex-center-imprecision q (sym targetᴾ) (sym targetᴵ)
  q-local′ = liftCenterImprecision W≼W′ q-local

  sourceᴾ′ = trans
    (cong (embedPrecise (core W′))
      (ClosureProof.precise-ground-type-eq W≼W′ Cᴾ))
    (trans (embedPrecise-lift W≼W′ Cᴾ)
      (cong (liftCenterTy W≼W′) sourceᴾ))
  sourceᴵ′ = trans
    (cong (embedImprecise (core W′))
      (ClosureProof.imprecise-ground-type-eq W≼W′ Cᴵ))
    (trans (embedImprecise-lift W≼W′ Cᴵ)
      (cong (liftCenterTy W≼W′) sourceᴵ))
  targetᴾ′ = trans
    (cong (embedPrecise (core W′))
      (ClosureProof.precise-ground-type-eq W≼W′ Dᴾ))
    (trans (embedPrecise-lift W≼W′ Dᴾ)
      (cong (liftCenterTy W≼W′) targetᴾ))
  targetᴵ′ = trans
    (cong (embedImprecise (core W′))
      (ClosureProof.imprecise-ground-type-eq W≼W′ Dᴵ))
    (trans (embedImprecise-lift W≼W′ Dᴵ)
      (cong (liftCenterTy W≼W′) targetᴵ))

  cᴾ′ = precise-consistency-future W≼W′ cᴾ
  cᴵ′ = imprecise-consistency-future W≼W′ cᴵ

  related′ = ClosureProof.value-imprecision-future W≼W′
    (value-imprecision-downward-to j≤k related)

  casted = cast-values p′ sourceᴾ′ sourceᴵ′ cᴾ′ cᴵ′ q′
    targetᴾ′ targetᴵ′ related′

  endpoints′ = value-imprecision-endpoints related′

  precise-source-eq : preciseType endpoints′ ≡
      ClosureProof.precise-ground-type W≼W′ Cᴾ
  precise-source-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W′)))
    (trans (preciseEmbedded endpoints′) (sym sourceᴾ′))

  imprecise-source-eq : impreciseType endpoints′ ≡
      ClosureProof.imprecise-ground-type W≼W′ Cᴵ
  imprecise-source-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W′)))
    (trans (impreciseEmbedded endpoints′) (sym sourceᴵ′))

  precise-cast-typed = ⊢⟨⟩
    (subst≡
      (λ A → ⟨ _ , preciseStore (core W′) , [] ⟩ ⊢
        liftPreciseTerm W≼W′ Vᴾ ⦂ A)
      precise-source-eq (precise-typed endpoints′)) cᴾ′

  imprecise-cast-typed = ⊢⟨⟩
    (subst≡
      (λ A → ⟨ _ , impreciseStore (core W′) , [] ⟩ ⊢
        liftImpreciseTerm W≼W′ Vᴵ ⦂ A)
      imprecise-source-eq (imprecise-typed endpoints′)) cᴵ′

  precise-close-eq = trans
    (cong (close
      (preciseClosingSubstitution {W = W′} {k = j} related-empty))
      (lift-precise-cast W≼W′ Vᴾ cᴾ))
    (subst-closed
      (closingSubstitution
        (preciseClosingSubstitution {W = W′} {k = j} related-empty))
      precise-cast-typed)

  imprecise-close-eq = trans
    (cong (close
      (impreciseClosingSubstitution {W = W′} {k = j} related-empty))
      (lift-imprecise-cast W≼W′ Vᴵ cᴵ))
    (subst-closed
      (closingSubstitution
        (impreciseClosingSubstitution {W = W′} {k = j} related-empty))
      imprecise-cast-typed)

function-cast-redex-none : ∀ {Δ} {V : Term Δ} {μ : C.Env∼ Δ}
    {A A′ B B′ : Ty Δ}
    {c : C.flipᵐ μ C.⊢ A′ ∼ A} {d : μ C.⊢ B ∼ B′}
  → Value V
  → E.cast-redex? V (c C.↦ d) ≡ nothing
function-cast-redex-none (ƛ N) = refl
function-cast-redex-none (Λ vV) = refl
function-cast-redex-none ($ κ) = refl
function-cast-redex-none (vV 《 inert 》) = refl
function-cast-redex-none (vV ↑ reveal) = refl
function-cast-redex-none (vV ↓ conceal) = refl

universal-cast-redex-none : ∀ {Δ} {V : Term Δ} {μ : C.Env∼ Δ}
    {A B : Ty (suc Δ)} {c : C.extᵐ μ C.⊢ A ∼ B}
  → Value V
  → E.cast-redex? V (C.∀ᶜ c) ≡ nothing
universal-cast-redex-none (ƛ N) = refl
universal-cast-redex-none (Λ vV) = refl
universal-cast-redex-none ($ κ) = refl
universal-cast-redex-none (vV 《 inert 》) = refl
universal-cast-redex-none (vV ↑ reveal) = refl
universal-cast-redex-none (vV ↓ conceal) = refl

function-cast-step-none : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ}
    {A A′ B B′ : Ty Δ}
    {c : C.flipᵐ μ C.⊢ A′ ∼ A} {d : μ C.⊢ B ∼ B′}
  → Value V
  → E.step? Σ (V ⟨ c C.↦ d ⟩) ≡ nothing
function-cast-step-none {Σ = Σ} vV =
  value-step-none {Σ = Σ} (vV 《 fun 》)

function-cast-app-value-final-question : ∀ {Δ}
    {V U : Term Δ} {μ : C.Env∼ Δ}
    {A A′ B B′ : Ty Δ}
    {c : C.flipᵐ μ C.⊢ A′ ∼ A} {d : μ C.⊢ B ∼ B′}
  → (vV : Value V)
  → (vU : Value U)
  → Σ[ vU′ ∈ Value U ]
      E.app-value-final? (vV 《 fun 》) U ≡
        just (E.step-result keep ((V · (U ⟨ c ⟩)) ⟨ d ⟩)
          (pure-step (β-⇒ vV vU′)))
function-cast-app-value-final-question vV (ƛ N) = (ƛ N) , refl
function-cast-app-value-final-question vV (Λ vU)
    with value-question-complete (Λ vU)
function-cast-app-value-final-question vV (Λ vU)
    | vU′ , value-eq rewrite value-eq = vU′ , refl
function-cast-app-value-final-question vV ($ κ) = ($ κ) , refl
function-cast-app-value-final-question vV (vU 《 inert 》)
    with value-question-complete (vU 《 inert 》)
function-cast-app-value-final-question vV (vU 《 inert 》)
    | vU′ , value-eq rewrite value-eq = vU′ , refl
function-cast-app-value-final-question vV (vU ↑ reveal)
    with value-question-complete (vU ↑ reveal)
function-cast-app-value-final-question vV (vU ↑ reveal)
    | vU′ , value-eq rewrite value-eq = vU′ , refl
function-cast-app-value-final-question vV (vU ↓ conceal)
    with value-question-complete (vU ↓ conceal)
function-cast-app-value-final-question vV (vU ↓ conceal)
    | vU′ , value-eq rewrite value-eq = vU′ , refl

function-cast-app-final-question : ∀ {Δ}
    {V U : Term Δ} {μ : C.Env∼ Δ}
    {A A′ B B′ : Ty Δ}
    {c : C.flipᵐ μ C.⊢ A′ ∼ A} {d : μ C.⊢ B ∼ B′}
  → (vV : Value V)
  → (vU : Value U)
  → Σ[ vV′ ∈ Value V ] Σ[ vU′ ∈ Value U ]
      E.app-final? (V ⟨ c C.↦ d ⟩) U ≡
        just (E.step-result keep ((V · (U ⟨ c ⟩)) ⟨ d ⟩)
          (pure-step (β-⇒ vV′ vU′)))
function-cast-app-final-question vV vU
    with value-question-complete vV
function-cast-app-final-question vV vU | vV′ , value-eq
    rewrite value-eq with function-cast-app-value-final-question vV′ vU
function-cast-app-final-question vV vU | vV′ , value-eq
    | vU′ , final-eq = vV′ , vU′ , final-eq

function-cast-application-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V U : Term Δ} {μ : C.Env∼ Δ}
    {A A′ B B′ : Ty Δ}
    {c : C.flipᵐ μ C.⊢ A′ ∼ A} {d : μ C.⊢ B ∼ B′}
  → (vV : Value V)
  → (vU : Value U)
  → Σ[ vV′ ∈ Value V ] Σ[ vU′ ∈ Value U ]
      E.step? Σ ((V ⟨ c C.↦ d ⟩) · U) ≡
        just (E.step-result keep ((V · (U ⟨ c ⟩)) ⟨ d ⟩)
          (pure-step (β-⇒ vV′ vU′)))
function-cast-application-step-question {Σ = Σ} {V = V} {U = U}
    {c = c} {d = d} vV vU
    with E.step? Σ V | value-step-none {Σ = Σ} vV
function-cast-application-step-question {Σ = Σ} {V = V} {U = U}
    {c = c} {d = d} vV vU | nothing | refl
    with E.cast-redex? V (c C.↦ d)
       | function-cast-redex-none {V = V} {c = c} {d = d} vV
function-cast-application-step-question {Σ = Σ} {V = V} {U = U}
    {c = c} {d = d} vV vU | nothing | refl | nothing | refl
    with E.step? Σ U | value-step-none {Σ = Σ} vU
function-cast-application-step-question {V = V} {U = U}
    {c = c} {d = d} vV vU
    | nothing | refl | nothing | refl | nothing | refl
    with function-cast-app-final-question vV vU
function-cast-application-step-question vV vU
    | nothing | refl | nothing | refl | nothing | refl
    | vV′ , vU′ , final-eq =
  vV′ , vU′ , final-eq

universal-cast-type-application-step-question : ∀
    {Δ} {Σ : TyStore Δ} {V : Term Δ} {μ : C.Env∼ Δ}
    {A B : Ty (suc Δ)} {R : Ty Δ} {c : C.extᵐ μ C.⊢ A ∼ B}
  → Value V
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ ((V ⟨ C.∀ᶜ c ⟩) ⦂∀ B [ R ]) ≡
        just (E.step-result keep
          ((V ⦂∀ A [ R ]) ⟨ c [ R ]ᶜ ⟩)
          (pure-step (β-∀ vV′ refl)))
universal-cast-type-application-step-question
    {Σ = Σ} {V = V} {c = c} vV
    with E.step? Σ V | value-step-none {Σ = Σ} vV
universal-cast-type-application-step-question
    {Σ = Σ} {V = V} {c = c} vV
    | nothing | refl
    with E.cast-redex? V (C.∀ᶜ c)
       | universal-cast-redex-none {V = V} {c = c} vV
universal-cast-type-application-step-question
    {V = V} {B = B} {c = c} vV
    | nothing | refl | nothing | refl
    with E.value? V | value-question-complete vV | B ≟Ty B in type-eq
universal-cast-type-application-step-question vV
    | nothing | refl | nothing | refl
    | just vV′ | .vV′ , refl | yes refl
    rewrite type-eq = vV′ , refl
universal-cast-type-application-step-question vV
    | nothing | refl | nothing | refl
    | just vV′ | .vV′ , refl | no B≢B = ⊥-elim (B≢B refl)
universal-cast-type-application-step-question vV
    | nothing | refl | nothing | refl
    | nothing | vV′ , () | type-eq

groundProjection : ∀ {Δ} {μ : C.Env∼ Δ} {G B : Ty Δ}
  → (g : Ground G)
  → μ C.⊢★∼ G
  → μ C.⊢ G ∼ B
  → NonStar B
  → μ C.⊢ ★ ∼ B
groundProjection g ★∼G G∼B Bns =
  let instance
        ground-instance = g
        star-to-ground-instance = ★∼G
        target-nonstar-instance = Bns
  in C.？ G∼B

projection-cast-value-none : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {G B : Ty Δ}
    (g : Ground G) (★∼G : μ C.⊢★∼ G)
    (c : μ C.⊢ G ∼ B) (Bns : NonStar B)
  → Value V
  → E.value? (V ⟨ groundProjection g ★∼G c Bns ⟩) ≡ nothing
projection-cast-value-none g ★∼G c Bns vV
    with value-question-complete vV
projection-cast-value-none g ★∼G c Bns vV | vV′ , value-eq
    rewrite value-eq = refl

identity-cast-value-none : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {A : Ty Δ} (a : Atom A)
  → Value V
  → E.value? (V ⟨ C.id {μ = μ} a ⟩) ≡ nothing
identity-cast-value-none a vV with value-question-complete vV
identity-cast-value-none a vV | vV′ , value-eq
    rewrite value-eq = refl

cast-redex-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V N : Term Δ} {μ : C.Env∼ Δ} {A B : Ty Δ}
    {c : μ C.⊢ A ∼ B} {step : V ⟨ c ⟩ —→ N}
  → Value V
  → E.cast-redex? V c ≡
      just (E.step-result keep N (pure-step step))
  → E.step? Σ (V ⟨ c ⟩) ≡
      just (E.step-result keep N (pure-step step))
cast-redex-step-question {Σ = Σ} {V = V} vV redex-eq
    with E.step? Σ V | value-step-none {Σ = Σ} vV
cast-redex-step-question vV redex-eq | nothing | refl = redex-eq
cast-redex-step-question vV redex-eq | just step | ()

step-question-value-none : ∀ {Δ} {Σ : TyStore Δ}
    {M : Term Δ} {step : E.Step M}
  → E.step? Σ M ≡ just step
  → E.value? M ≡ nothing
step-question-value-none {Σ = Σ} {M = M} step-eq
    with E.value? M
step-question-value-none step-eq | nothing = refl
step-question-value-none {Σ = Σ} step-eq | just vM
    with value-step-none {Σ = Σ} vM
step-question-value-none step-eq | just vM | value-step-eq
    with trans (sym value-step-eq) step-eq
step-question-value-none step-eq | just vM | value-step-eq | ()

injection-expanded-redex-after-to-ground : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {A G : Ty Δ}
    (g : Ground G) (G∼★ : μ C.⊢ G ∼★)
    (A∼G : μ C.⊢ A ∼ G) (Ans : NonStar A)
    (vV : Value V) (A≢G : A ≢ G)
  → Progress.to-ground g A∼G ≡ Progress.other A≢G
  → Σ[ vV′ ∈ Value V ]
      E.cast-redex? V
        (C._! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄ A∼G
          ⦃ Ans = Ans ⦄) ≡
        just (E.step-result keep
          (V ⟨ A∼G ⟩ ⟨ groundInjection g G∼★ ⟩)
          (pure-step (ground ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄
            ⦃ Ans = Ans ⦄ ⦃ Gns = C.ground-nonstar g ⦄
            vV′ A≢G)))
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (ƛ N) A≢G to-ground-eq
    rewrite to-ground-eq = (ƛ N) , refl
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (Λ vV) A≢G to-ground-eq
    with value-question-complete (Λ vV)
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (Λ vV) A≢G to-ground-eq | vV′ , value-eq
    rewrite value-eq | to-ground-eq = vV′ , refl
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    ($ κ) A≢G to-ground-eq
    rewrite to-ground-eq = ($ κ) , refl
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (vV 《 inert 》) A≢G to-ground-eq
    with value-question-complete (vV 《 inert 》)
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (vV 《 inert 》) A≢G to-ground-eq | vV′ , value-eq
    rewrite value-eq | to-ground-eq = vV′ , refl
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (vV ↑ reveal) A≢G to-ground-eq
    with value-question-complete (vV ↑ reveal)
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (vV ↑ reveal) A≢G to-ground-eq | vV′ , value-eq
    rewrite value-eq | to-ground-eq = vV′ , refl
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (vV ↓ conceal) A≢G to-ground-eq
    with value-question-complete (vV ↓ conceal)
injection-expanded-redex-after-to-ground g G∼★ A∼G Ans
    (vV ↓ conceal) A≢G to-ground-eq | vV′ , value-eq
    rewrite value-eq | to-ground-eq = vV′ , refl

injection-expanded-redex-question : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {A G : Ty Δ}
    (g : Ground G) (G∼★ : μ C.⊢ G ∼★)
    (A∼G : μ C.⊢ A ∼ G) (Ans : NonStar A)
  → Value V
  → (A≢G : A ≢ G)
  → Σ[ vV′ ∈ Value V ]
      E.cast-redex? V
        (C._! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄ A∼G
          ⦃ Ans = Ans ⦄) ≡
        just (E.step-result keep
          (V ⟨ A∼G ⟩ ⟨ groundInjection g G∼★ ⟩)
          (pure-step (ground ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄
            ⦃ Ans = Ans ⦄ ⦃ Gns = C.ground-nonstar g ⦄
            vV′ A≢G)))
injection-expanded-redex-question g G∼★ A∼G Ans vV A≢G
    with Progress.to-ground g A∼G in to-ground-eq
injection-expanded-redex-question g G∼★ .(C.idᵍ g) Ans vV A≢G
    | Progress.same = ⊥-elim (A≢G refl)
injection-expanded-redex-question g G∼★ A∼G Ans vV A≢G
    | Progress.other source≢ground =
  injection-expanded-redex-after-to-ground g G∼★ A∼G Ans vV
    source≢ground to-ground-eq

data InjectionStepView {Δ : TyCtx} (Σ : TyStore Δ)
    {V : Term Δ} {μ : C.Env∼ Δ} {G : Ty Δ}
    (g : Ground G) (G∼★ : μ C.⊢ G ∼★) :
    ∀ {A : Ty Δ} → μ C.⊢ A ∼ G → NonStar A → Set where
  injection-same : InjectionStepView Σ g G∼★ (C.idᵍ g)
    (C.ground-nonstar g)

  injection-expanded : ∀ {A : Ty Δ} {A∼G : μ C.⊢ A ∼ G}
      {Ans : NonStar A}
    → (A≢G : A ≢ G)
    → (step :
        (V ⟨ (C._! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄ A∼G
          ⦃ Ans = Ans ⦄) ⟩) —→
        (V ⟨ A∼G ⟩ ⟨ groundInjection g G∼★ ⟩))
    → E.step? Σ
        (V ⟨ (C._! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄ A∼G
          ⦃ Ans = Ans ⦄) ⟩) ≡
        just (E.step-result keep
          (V ⟨ A∼G ⟩ ⟨ groundInjection g G∼★ ⟩)
          (pure-step step))
    → InjectionStepView Σ g G∼★ A∼G Ans

injection-step-view : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {A G : Ty Δ}
    (g : Ground G) (A∼G : μ C.⊢ A ∼ G)
    (G∼★ : μ C.⊢ G ∼★) (Ans : NonStar A)
  → Value V
  → InjectionStepView Σ {V = V} g G∼★ A∼G Ans
injection-step-view {Σ = Σ} {V = V} g A∼G G∼★ Ans vV
    with Progress.to-ground g A∼G
injection-step-view {Σ = Σ} {V = V} g .(C.idᵍ g) G∼★ Ans vV
    | Progress.same
    rewrite nonStar-unique Ans (C.ground-nonstar g) = injection-same
injection-step-view {Σ = Σ} {V = V} g A∼G G∼★ Ans vV
    | Progress.other A≢G
    with injection-expanded-redex-question g G∼★ A∼G Ans vV A≢G
injection-step-view {Σ = Σ} {V = V} g A∼G G∼★ Ans vV
    | Progress.other A≢G | vV′ , redex-eq =
  injection-expanded A≢G
    (ground ⦃ Gᵍ = g ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Ans = Ans ⦄ ⦃ Gns = C.ground-nonstar g ⦄ vV′ A≢G)
    (cast-redex-step-question {Σ = Σ} vV redex-eq)

cast-operand-pure-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {M N : Term Δ} {step : M —→ N}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → E.step? Σ M ≡ just (E.step-result keep N (pure-step step))
  → E.step? Σ (M ⟨ c ⟩) ≡
      just (E.step-result keep (N ⟨ c ⟩)
        (ξ-⟨⟩ (pure-step step) refl))
cast-operand-pure-step-question {Σ = Σ} {M = M} {N = N}
    {step = step} {c = c} step-eq with E.step? Σ M in operand-eq
cast-operand-pure-step-question step-eq | nothing with step-eq
cast-operand-pure-step-question step-eq | nothing | ()
cast-operand-pure-step-question {Σ = Σ} {M = M} {c = c} step-eq
    | just (E.step-result χ N′ next-step) with step-eq
cast-operand-pure-step-question {Σ = Σ} {M = M} {c = c} step-eq
    | just (E.step-result .keep ._ ._) | refl =
  refl

blame-cast-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → E.step? Σ (blame ⟨ c ⟩) ≡
      just (E.step-result keep blame (pure-step blame-⟨⟩))
blame-cast-step-question = refl

projection-expanded-redex-after-from-ground : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {G B : Ty Δ}
    (g : Ground G) (★∼G : μ C.⊢★∼ G)
    (G∼B : μ C.⊢ G ∼ B) (Bns : NonStar B)
    (vV : Value V) (B≢G : B ≢ G)
  → Progress.from-ground g G∼B ≡ Progress.other B≢G
  → Σ[ vV′ ∈ Value V ]
      E.cast-redex? V (groundProjection g ★∼G G∼B Bns) ≡
        just (E.step-result keep
          ((V ⟨ groundProjection g ★∼G (C.idᵍ g)
            (C.ground-nonstar g) ⟩) ⟨ G∼B ⟩)
          (pure-step (expand ⦃ Gᵍ = g ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Bns = Bns ⦄ ⦃ Gns = C.ground-nonstar g ⦄
            vV′ (λ G≡B → B≢G (sym G≡B)))))
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (ƛ N) B≢G from-ground-eq
    rewrite from-ground-eq = (ƛ N) , refl
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (Λ vV) B≢G from-ground-eq
    with value-question-complete (Λ vV)
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (Λ vV) B≢G from-ground-eq | vV′ , value-eq
    rewrite value-eq | from-ground-eq = vV′ , refl
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    ($ κ) B≢G from-ground-eq
    rewrite from-ground-eq = ($ κ) , refl
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (vV 《 inert 》) B≢G from-ground-eq
    with value-question-complete (vV 《 inert 》)
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (vV 《 inert 》) B≢G from-ground-eq | vV′ , value-eq
    rewrite value-eq | from-ground-eq = vV′ , refl
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (vV ↑ reveal) B≢G from-ground-eq
    with value-question-complete (vV ↑ reveal)
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (vV ↑ reveal) B≢G from-ground-eq | vV′ , value-eq
    rewrite value-eq | from-ground-eq = vV′ , refl
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (vV ↓ conceal) B≢G from-ground-eq
    with value-question-complete (vV ↓ conceal)
projection-expanded-redex-after-from-ground g ★∼G G∼B Bns
    (vV ↓ conceal) B≢G from-ground-eq | vV′ , value-eq
    rewrite value-eq | from-ground-eq = vV′ , refl

projection-expanded-redex-question : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {G B : Ty Δ}
    (g : Ground G) (★∼G : μ C.⊢★∼ G)
    (G∼B : μ C.⊢ G ∼ B) (Bns : NonStar B)
  → Value V
  → (B≢G : B ≢ G)
  → Σ[ vV′ ∈ Value V ]
      E.cast-redex? V (groundProjection g ★∼G G∼B Bns) ≡
        just (E.step-result keep
          ((V ⟨ groundProjection g ★∼G (C.idᵍ g)
            (C.ground-nonstar g) ⟩) ⟨ G∼B ⟩)
          (pure-step (expand ⦃ Gᵍ = g ⦄ ⦃ ★∼G = ★∼G ⦄
            ⦃ Bns = Bns ⦄ ⦃ Gns = C.ground-nonstar g ⦄
            vV′ (λ G≡B → B≢G (sym G≡B)))))
projection-expanded-redex-question g ★∼G G∼B Bns vV B≢G
    with Progress.from-ground g G∼B in from-ground-eq
projection-expanded-redex-question g ★∼G .(C.idᵍ g) Bns vV B≢G
    | Progress.same = ⊥-elim (B≢G refl)
projection-expanded-redex-question g ★∼G G∼B Bns vV B≢G
    | Progress.other target≢ground =
  projection-expanded-redex-after-from-ground g ★∼G G∼B Bns vV
    target≢ground from-ground-eq

data ProjectionStepView {Δ : TyCtx} (Σ : TyStore Δ)
    {V : Term Δ} {μ : C.Env∼ Δ} {G : Ty Δ}
    (g : Ground G) (★∼G : μ C.⊢★∼ G) :
    ∀ {B : Ty Δ} → μ C.⊢ G ∼ B → NonStar B → Set where
  projection-same : ProjectionStepView Σ g ★∼G (C.idᵍ g)
    (C.ground-nonstar g)

  projection-expanded : ∀ {B : Ty Δ} {G∼B : μ C.⊢ G ∼ B}
      {Bns : NonStar B}
      (B≢G : B ≢ G)
      (step : (V ⟨ groundProjection g ★∼G G∼B Bns ⟩) —→
        ((V ⟨ groundProjection g ★∼G (C.idᵍ g)
          (C.ground-nonstar g) ⟩) ⟨ G∼B ⟩))
    → E.step? Σ (V ⟨ groundProjection g ★∼G G∼B Bns ⟩) ≡
        just (E.step-result keep
          ((V ⟨ groundProjection g ★∼G (C.idᵍ g)
            (C.ground-nonstar g) ⟩) ⟨ G∼B ⟩)
          (pure-step step))
    → ProjectionStepView Σ g ★∼G G∼B Bns

projection-step-view : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {G B : Ty Δ}
    (g : Ground G) (G∼B : μ C.⊢ G ∼ B)
    (★∼G : μ C.⊢★∼ G) (Bns : NonStar B)
  → Value V
  → ProjectionStepView Σ {V = V} g ★∼G G∼B Bns
projection-step-view {Σ = Σ} {V = V} g G∼B ★∼G Bns vV
    with Progress.from-ground g G∼B
projection-step-view {Σ = Σ} {V = V} g .(C.idᵍ g) ★∼G Bns vV
    | Progress.same
    rewrite nonStar-unique Bns (C.ground-nonstar g) = projection-same
projection-step-view {Σ = Σ} {V = V} g G∼B ★∼G Bns vV
    | Progress.other B≢G
    with projection-expanded-redex-question g ★∼G G∼B Bns vV B≢G
projection-step-view {Σ = Σ} {V = V} g G∼B ★∼G Bns vV
    | Progress.other B≢G | vV′ , redex-eq = projection-expanded
      B≢G
      (expand ⦃ Gᵍ = g ⦄ ⦃ ★∼G = ★∼G ⦄
        ⦃ Bns = Bns ⦄ ⦃ Gns = C.ground-nonstar g ⦄
        vV′ (λ G≡B → B≢G (sym G≡B)))
      (cast-redex-step-question {Σ = Σ} vV redex-eq)

data TagProjectionStepView {Δ : TyCtx} (Σ : TyStore Δ)
    {U : Term Δ} {μ ν : C.Env∼ Δ} {H G : Ty Δ}
    (h : Ground H) (g : Ground G)
    (H∼★ : μ C.⊢ H ∼★) (★∼G : ν C.⊢★∼ G)
    (vU : Value U) : Set where
  tag-matched : H ≡ G
    → (step :
      ((U ⟨ groundInjection h H∼★ ⟩)
        ⟨ groundProjection g ★∼G (C.idᵍ g)
          (C.ground-nonstar g) ⟩) —→ U)
    → E.step? Σ
        ((U ⟨ groundInjection h H∼★ ⟩)
          ⟨ groundProjection g ★∼G (C.idᵍ g)
            (C.ground-nonstar g) ⟩) ≡
        just (E.step-result keep U (pure-step step))
    → TagProjectionStepView Σ h g H∼★ ★∼G vU

  tag-mismatched : H ≢ G
    → (step :
      ((U ⟨ groundInjection h H∼★ ⟩)
        ⟨ groundProjection g ★∼G (C.idᵍ g)
          (C.ground-nonstar g) ⟩) —→ blame)
    → E.step? Σ
        ((U ⟨ groundInjection h H∼★ ⟩)
          ⟨ groundProjection g ★∼G (C.idᵍ g)
            (C.ground-nonstar g) ⟩) ≡
        just (E.step-result keep blame (pure-step step))
    → TagProjectionStepView Σ h g H∼★ ★∼G vU

tag-matched-redex-question : ∀ {Δ} {U : Term Δ}
    {μ ν : C.Env∼ Δ} {H : Ty Δ}
    (h : Ground H) (H∼★ : μ C.⊢ H ∼★) (★∼H : ν C.⊢★∼ H)
  → Value U
  → Σ[ vU′ ∈ Value U ]
      E.cast-redex? (U ⟨ groundInjection h H∼★ ⟩)
        (groundProjection h ★∼H (C.idᵍ h)
          (C.ground-nonstar h)) ≡
        just (E.step-result keep U
          (pure-step (tag-untag ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
            ⦃ ★∼G = ★∼H ⦄ ⦃ Gns = C.ground-nonstar h ⦄ vU′)))
tag-matched-redex-question {U = U} (＇ X) H∼★ ★∼H vU
    with value-question-complete vU | X Fin.≟ X in X-eq
tag-matched-redex-question (＇ X) H∼★ ★∼H vU
    | vU′ , value-eq | yes refl
    rewrite value-eq | X-eq = vU′ , refl
tag-matched-redex-question (＇ X) H∼★ ★∼H vU
    | vU′ , value-eq | no X≢X = ⊥-elim (X≢X refl)
tag-matched-redex-question {U = U} (‵ ι) H∼★ ★∼H vU
    with value-question-complete vU | ι ≟Base ι in ι-eq
tag-matched-redex-question (‵ ι) H∼★ ★∼H vU
    | vU′ , value-eq | yes refl
    rewrite value-eq | ι-eq = vU′ , refl
tag-matched-redex-question (‵ ι) H∼★ ★∼H vU
    | vU′ , value-eq | no ι≢ι = ⊥-elim (ι≢ι refl)
tag-matched-redex-question {U = U} ★⇒★ H∼★ ★∼H vU
    with value-question-complete vU
tag-matched-redex-question ★⇒★ H∼★ ★∼H vU
    | vU′ , value-eq
    rewrite value-eq = vU′ , refl
tag-matched-redex-question {U = U} ∀★ H∼★ ★∼H vU
    with value-question-complete vU
tag-matched-redex-question ∀★ H∼★ ★∼H vU
    | vU′ , value-eq
    rewrite value-eq = vU′ , refl

tag-mismatched-redex-question : ∀ {Δ} {U : Term Δ}
    {μ ν : C.Env∼ Δ} {H G : Ty Δ}
    (h : Ground H) (g : Ground G)
    (H∼★ : μ C.⊢ H ∼★) (★∼G : ν C.⊢★∼ G)
    (vU : Value U)
  → H ≢ G
  → Σ[ H≢G′ ∈ H ≢ G ] Σ[ vU′ ∈ Value U ]
      E.cast-redex? (U ⟨ groundInjection h H∼★ ⟩)
        (groundProjection g ★∼G (C.idᵍ g)
          (C.ground-nonstar g)) ≡
        just (E.step-result keep blame
          (pure-step (tag-untag-bad ⦃ Gᵍ = h ⦄ ⦃ Hᵍ = g ⦄
            ⦃ G∼★ = H∼★ ⦄ ⦃ ★∼H = ★∼G ⦄
            ⦃ Gns = C.ground-nonstar h ⦄
            ⦃ Hns = C.ground-nonstar g ⦄ vU′ H≢G′)))
tag-mismatched-redex-question {U = U} {H = H} h (＇ X)
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty ＇ X in type-eq
tag-mismatched-redex-question h (＇ X) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h (＇ X) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl
tag-mismatched-redex-question {U = U} {H = H} h (‵ ι)
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty ‵ ι in type-eq
tag-mismatched-redex-question h (‵ ι) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h (‵ ι) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl
tag-mismatched-redex-question {U = U} {H = H} h ★⇒★
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty (★ ⇒ ★) in type-eq
tag-mismatched-redex-question h ★⇒★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h ★⇒★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl
tag-mismatched-redex-question {U = U} {H = H} h ∀★
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty (`∀ ★) in type-eq
tag-mismatched-redex-question h ∀★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h ∀★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl

tag-projection-step-view : ∀ {Δ} {Σ : TyStore Δ}
    {U : Term Δ} {μ ν : C.Env∼ Δ} {H G : Ty Δ}
    (h : Ground H) (g : Ground G)
    (H∼★ : μ C.⊢ H ∼★) (★∼G : ν C.⊢★∼ G)
    (vU : Value U)
  → TagProjectionStepView Σ h g H∼★ ★∼G vU
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = G}
    h g H∼★ ★∼G vU with H ≟Ty G
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = .H}
    h g H∼★ ★∼G vU | yes refl
    rewrite ground-unique g h
    with tag-matched-redex-question h H∼★ ★∼G vU
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = .H}
    h g H∼★ ★∼G vU | yes refl | vU′ , redex-eq =
  tag-matched refl
    (tag-untag ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
      ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = C.ground-nonstar h ⦄ vU′)
    (cast-redex-step-question {Σ = Σ}
      (vU′ 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》) redex-eq)
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = G}
    h g H∼★ ★∼G vU | no H≢G
    with tag-mismatched-redex-question h g H∼★ ★∼G vU H≢G
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = G}
    h g H∼★ ★∼G vU | no H≢G | H≢G′ , vU′ , redex-eq =
  tag-mismatched H≢G′
    (tag-untag-bad ⦃ Gᵍ = h ⦄ ⦃ Hᵍ = g ⦄
      ⦃ G∼★ = H∼★ ⦄ ⦃ ★∼H = ★∼G ⦄
      ⦃ Gns = C.ground-nonstar h ⦄
      ⦃ Hns = C.ground-nonstar g ⦄ vU′ H≢G′)
    (cast-redex-step-question {Σ = Σ}
      (vU′ 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》) redex-eq)

data GroundExpandedCastView {Δ : TyCtx}
    {V : Term Δ} {μ : C.Env∼ Δ} :
    ∀ {G B : Ty Δ}
    → Ground G
    → μ C.⊢ G ∼ B
    → NonStar B
    → Value V
    → Set where
  ground-cast-value : ∀ {G B} {g : Ground G}
      {c : μ C.⊢ G ∼ B} {Bns : NonStar B} {vV : Value V}
    → Value (V ⟨ c ⟩)
    → GroundExpandedCastView g c Bns vV
  ground-cast-blame : ∀ {vV : Value V}
      {bottom-nonstar : NonStar (`∀ (＇ Fin.zero))}
    → GroundExpandedCastView ∀★ C.bot-intro bottom-nonstar vV

ground-expanded-cast-view : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {G B : Ty Δ}
    (g : Ground G) (c : μ C.⊢ G ∼ B) (Bns : NonStar B)
    (vV : Value V)
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ G
  → B ≢ G
  → GroundExpandedCastView g c Bns vV
ground-expanded-cast-view (＇ X) (C.id x) Bns vV V⊢ B≢G =
  ⊥-elim (B≢G refl)
ground-expanded-cast-view (＇ X)
    ((C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c) A≢★)
    Bns vV V⊢ B≢G =
  ⊥-elim
    (variable-consistency-no-generated-variable (λ ()) c occurs)
ground-expanded-cast-view (‵ ι) (C.id x) Bns vV V⊢ B≢G =
  ⊥-elim (B≢G refl)
ground-expanded-cast-view (‵ ι)
    ((C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c) A≢★)
    Bns vV V⊢ B≢G =
  ⊥-elim (base-generalization-impossible c Bnv occurs)
ground-expanded-cast-view ★⇒★ (c C.↦ d) Bns vV V⊢ B≢G =
  ground-cast-value (vV 《 fun 》)
ground-expanded-cast-view ★⇒★
    ((C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c) A≢★)
    Bns vV V⊢ B≢G =
  ground-cast-value
    (vV 《 genᵥ A≢★ (gen-safe c A≢★ Bnv occurs) 》)
ground-expanded-cast-view ∀★ (C.∀ᶜ c) Bns vV V⊢ B≢G =
  ground-cast-value (vV 《 all 》)
ground-expanded-cast-view ∀★
    ((C.gen_ ⦃ Bnv ⦄ ⦃ occurs ⦄ c) A≢★)
    Bns vV V⊢ B≢G =
  ground-cast-value
    (vV 《 genᵥ A≢★ (gen-safe c A≢★ Bnv occurs) 》)
ground-expanded-cast-view ∀★ C.bot-intro Bns vV V⊢ B≢G =
  ground-cast-blame

-- The one-sided cast-on-value lemmas are open obligations; see
-- LR-narrow.CastObligations.

related-value-precise-cast : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ : Ty Δᴵ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
    (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Cᴵ ≡ Bᴵ)
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      Vᴵ (Vᴾ ⟨ cᴾ ⟩)
related-value-precise-cast = precise-cast-values ob

related-value-imprecise-cast : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
    (targetᴾ : embedPrecise (core W) Cᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Vᴵ ⟨ cᴵ ⟩) Vᴾ
related-value-imprecise-cast = imprecise-cast-values ob

-- The recursion is well founded lexicographically by the step index and
-- then by the consistency derivations: the function and universal cases
-- recurse on sub-casts at the same index and on arbitrary casts only
-- through a continuation consulted at a strictly smaller index.  Agda
-- cannot see the index through the composition continuation.
{-# TERMINATING #-}
related-value-casts : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
    (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Vᴵ ⟨ cᴵ ⟩) (Vᴾ ⟨ cᴾ ⟩)
related-value-casts p sourceᴾ sourceᴵ (C.id aᴾ) (C.id aᴵ) q
    targetᴾ targetᴵ related =
  ClosureProof.computations-related-reindex p q
    (trans (sym sourceᴾ) targetᴾ) (trans (sym sourceᴵ) targetᴵ)
    refl refl (related-identities related)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ (C.id aᴾ)
    (C._! cᴵ ⦃ Ans = nsᴵ ⦄) q targetᴾ targetᴵ related =
  ⊥-elim (imprecise-star-nonstar-impossible {W = W} sourceᴵ nsᴵ)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ (C.id aᴾ)
    (C.？_ cᴵ ⦃ Bns = nsᴵ ⦄) q targetᴾ targetᴵ related =
  ⊥-elim (star-left-nonstar-impossible local-q embedded-nonstar)
  where
  local-q = reindex-center-imprecision q
    (trans (sym targetᴾ) sourceᴾ) (sym targetᴵ)

  embedded-nonstar = C.renameNonStar
    (C.toRenameᵗ (impreciseEmbedding (core W))) nsᴵ
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ (C.id aᴾ)
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim (Aᴵ≢★ (imprecise-source-star {W = W} sourceᴵ))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C._! cᴾ ⦃ Ans = nsᴾ ⦄) cᴵ q targetᴾ targetᴵ related =
  ⊥-elim (precise-star-nonstar-impossible {W = W} sourceᴾ nsᴾ)
related-value-casts {W = W} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = zero} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  nonvalue-computations-zero (λ ()) (λ ())
    (identity-cast-value-none aᴵ (imprecise-value related))
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value related))
related-value-casts {W = W} {Bᴾ = Bᴾ} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (endpoints , inj₁ (shape , payload-related))
    with shape
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    with projection-step-view {Σ = preciseStore (core W)}
      gᴾ cᴾ ★∼Gᴾ nsᴾ (precise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (value-imprecision-endpoints payload-related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape .Gᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-matched refl precise-step precise-step-eq
    with identity-cast-step-question
      {Σ = impreciseStore (core W)} (imprecise-value endpoints)
related-value-casts {W = W} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape .Gᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-matched refl precise-step precise-step-eq
    | imprecise-value′ , imprecise-step-eq =
  related-pure-step-expand (λ ()) (λ ())
    (identity-cast-value-none aᴵ (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
      (C.ground-nonstar gᴾ) (precise-value endpoints))
    (β-id imprecise-value′) precise-step
    imprecise-step-eq precise-step-eq
    (related-values-return (imprecise-value endpoints)
      (precise-value payload-endpoints) at-every-index)
  where
  payload-endpoints = value-imprecision-endpoints payload-related

  right-eq : ★ ≡ Bᴵ
  right-eq = trans (sym sourceᴵ) targetᴵ

  local-q : impEnv (core W) I.⊢ Bᴾ ⊑ ★
  local-q = reindex-center-imprecision q refl (sym right-eq)

  at-every-index : ∀ j → j ≤ k
    → FutureValueRelation q W future-refl j
        (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩) Uᴾ
  at-every-index j j≤k = ClosureProof.value-imprecision-reindex
    q local-q refl (sym right-eq)
    (right-dynamic-ground-tag-value-at j gᴾ hᴵ Hᴵ∼★ payload-q
      local-q targetᴾ
      (value-imprecision-downward-to j≤k payload-related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-mismatched Hᴾ≢Gᴾ precise-step precise-step-eq =
  precise-pure-step-to-blame (λ ())
    (projection-cast-value-none gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
      (C.ground-nonstar gᴾ) (precise-value endpoints))
    precise-step precise-step-eq
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (value-imprecision-endpoints payload-related))
related-value-casts {W = W} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape .Gᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    | tag-matched refl inner-step inner-step-eq
    with identity-cast-step-question
      {Σ = impreciseStore (core W)} (imprecise-value endpoints)
related-value-casts {W = W} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape .Gᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    | tag-matched refl inner-step inner-step-eq
    | imprecise-value′ , imprecise-step-eq =
  related-pure-step-expand (λ ()) (λ ())
    (identity-cast-value-none aᴵ (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    (β-id imprecise-value′) precise-step
    imprecise-step-eq precise-step-eq after-inner
  where
  payload-endpoints = value-imprecision-endpoints payload-related

  right-eq : ★ ≡ Bᴵ
  right-eq = trans (sym sourceᴵ) targetᴵ

  local-q : impEnv (core W) I.⊢ Bᴾ ⊑ ★
  local-q = reindex-center-imprecision q refl (sym right-eq)

  payload-casted : ComputationsRelated W
      (FutureValueRelation local-q) k
      (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩) (Uᴾ ⟨ cᴾ ⟩)
  payload-casted = related-value-casts payload-q refl refl cᴾ
    (groundInjection hᴵ Hᴵ∼★) local-q targetᴾ refl
    payload-related

  payload-casted-q : ComputationsRelated W
      (FutureValueRelation q) k
      (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩) (Uᴾ ⟨ cᴾ ⟩)
  payload-casted-q = ClosureProof.computations-related-reindex
    local-q q refl right-eq refl refl payload-casted

  inner-value-eq = projection-cast-value-none gᴾ ★∼Gᴾ
    (C.idᵍ gᴾ) (C.ground-nonstar gᴾ)
    (precise-value endpoints)

  after-inner : ComputationsRelated W (FutureValueRelation q) k
      (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩)
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-inner = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    payload-casted-q
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    | tag-mismatched Hᴾ≢Gᴾ inner-step inner-step-eq
    with identity-cast-step-question
      {Σ = impreciseStore (core W)} (imprecise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    | tag-mismatched Hᴾ≢Gᴾ inner-step inner-step-eq
    | imprecise-value′ , imprecise-step-eq =
  related-pure-step-expand (λ ()) (λ ())
    (identity-cast-value-none aᴵ (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    (β-id imprecise-value′) precise-step
    imprecise-step-eq precise-step-eq after-inner
  where
  inner-value-eq = projection-cast-value-none gᴾ ★∼Gᴾ
    (C.idᵍ gᴾ) (C.ground-nonstar gᴾ) (precise-value endpoints)

  blame-tail : ComputationsRelated W (FutureValueRelation q) k
      (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩) (blame ⟨ cᴾ ⟩)
  blame-tail = precise-pure-step-to-blame (λ ()) refl blame-⟨⟩
    (blame-cast-step-question
      {Σ = preciseStore (core W)} {c = cᴾ})

  after-inner : ComputationsRelated W (FutureValueRelation q) k
      (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩)
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-inner = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    blame-tail
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (endpoints , inj₂ atom-related) with atom-related
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    with projection-step-view {Σ = preciseStore (core W)}
      gᴾ cᴾ ★∼Gᴾ nsᴾ (precise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-same
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (dynamic-atom-source-endpoints
        {W = W} {Z = Z} {mode = mode} {k = suc k}
        {Vᴵ = Vᴵ} {Vᴾ = Uᴾ} holds))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode .Gᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-same
    | tag-matched refl precise-step precise-step-eq
    with identity-cast-step-question
      {Σ = impreciseStore (core W)} (imprecise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode .Gᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-same
    | tag-matched refl precise-step precise-step-eq
    | imprecise-value′ , imprecise-step-eq =
  related-pure-step-expand (λ ()) (λ ())
    (identity-cast-value-none aᴵ (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
      (C.ground-nonstar gᴾ) (precise-value endpoints))
    (β-id imprecise-value′) precise-step
    imprecise-step-eq precise-step-eq continuation
  where
  source-q = I.X⊑★ mode
  source-related = dynamic-atom-source-value-at
    {W = W} (suc k) {Z = Z} {mode = mode}
    {Vᴵ = Vᴵ} {Vᴾ = Uᴾ} holds
  source-endpoints = dynamic-atom-source-endpoints
    {W = W} {Z = Z} {mode = mode} {k = suc k}
    {Vᴵ = Vᴵ} {Vᴾ = Uᴾ} holds

  source-immediate : ComputationsRelated W
      (FutureValueRelation source-q) k Vᴵ Uᴾ
  source-immediate = related-values-return
    (imprecise-value source-endpoints)
    (precise-value source-endpoints)
    (λ j j≤k → value-imprecision-downward-to
      (≤-trans j≤k (n≤1+n k)) source-related)

  precise-eq = trans (sym ground-center) targetᴾ
  imprecise-eq = trans (sym sourceᴵ) targetᴵ

  continuation = ClosureProof.computations-related-reindex
    source-q q precise-eq imprecise-eq refl refl source-immediate
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-same
    | tag-mismatched Hᴾ≢Gᴾ precise-step precise-step-eq =
  precise-pure-step-to-blame (λ ())
    (projection-cast-value-none gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
      (C.ground-nonstar gᴾ) (precise-value endpoints))
    precise-step precise-step-eq
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (dynamic-atom-source-endpoints
        {W = W} {Z = Z} {mode = mode} {k = suc k}
        {Vᴵ = Vᴵ} {Vᴾ = Uᴾ} holds))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode .Gᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched refl inner-step inner-step-eq =
  ⊥-elim (center-ground-other-impossible {W = W} hᴾ ground-center
    cᴾ nsᴾ Bᴾ≠Gᴾ)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-mismatched Hᴾ≠Gᴾ inner-step inner-step-eq
    with identity-cast-step-question
      {Σ = impreciseStore (core W)} (imprecise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.id aᴵ) q targetᴾ targetᴵ
    {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-mismatched Hᴾ≠Gᴾ inner-step inner-step-eq
    | imprecise-value′ , imprecise-step-eq =
  related-pure-step-expand (λ ()) (λ ())
    (identity-cast-value-none aᴵ (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    (β-id imprecise-value′) precise-step
    imprecise-step-eq precise-step-eq after-inner
  where
  inner-value-eq = projection-cast-value-none gᴾ ★∼Gᴾ
    (C.idᵍ gᴾ) (C.ground-nonstar gᴾ)
    (precise-value endpoints)

  blame-tail : ComputationsRelated W (FutureValueRelation q) k
      Vᴵ (blame ⟨ cᴾ ⟩)
  blame-tail = precise-pure-step-to-blame (λ ()) refl blame-⟨⟩
    (blame-cast-step-question
      {Σ = preciseStore (core W)} {c = cᴾ})

  after-inner : ComputationsRelated W (FutureValueRelation q) k
      Vᴵ
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-inner = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    blame-tail
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C._! cᴵ ⦃ Ans = nsᴵ ⦄) q targetᴾ targetᴵ related =
  ⊥-elim (imprecise-star-nonstar-impossible {W = W} sourceᴵ nsᴵ)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    {μᴵ = μᴵ}
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = zero} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related =
  nonvalue-computations-zero (λ ()) (λ ())
    (projection-cast-value-none gᴵ ★∼Gᴵ cᴵ nsᴵ
      (imprecise-value related))
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    {μᴵ = μᴵ}
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (endpoints , inj₁ (shape , payload-related)) with shape
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    with projection-step-view {Σ = preciseStore (core W)}
      gᴾ cᴾ ★∼Gᴾ nsᴾ (precise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (value-imprecision-endpoints payload-related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-matched Hᴾ≡Gᴾ precise-step precise-step-eq
    with projection-step-view {Σ = impreciseStore (core W)}
      gᴵ cᴵ ★∼Gᴵ nsᴵ (imprecise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    {μᴵ = μᴵ}
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-matched Hᴾ≡Gᴾ precise-step precise-step-eq
    | projection-same
    with tag-projection-step-view {Σ = impreciseStore (core W)}
      hᴵ gᴵ Hᴵ∼★ ★∼Gᴵ
      (imprecise-value (value-imprecision-endpoints payload-related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-matched Hᴾ≡Gᴾ precise-step precise-step-eq
    | projection-same
    | tag-matched Hᴵ≡Gᴵ imprecise-step imprecise-step-eq =
  related-pure-step-expand (λ ()) (λ ())
    (projection-cast-value-none gᴵ ★∼Gᴵ (C.idᵍ gᴵ)
      (C.ground-nonstar gᴵ) (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
      (C.ground-nonstar gᴾ) (precise-value endpoints))
    imprecise-step precise-step imprecise-step-eq precise-step-eq
    continuation
  where
  payload-endpoints = value-imprecision-endpoints payload-related

  precise-eq = trans
    (cong (embedPrecise (core W)) Hᴾ≡Gᴾ) targetᴾ
  imprecise-eq = trans
    (cong (embedImprecise (core W)) Hᴵ≡Gᴵ) targetᴵ

  immediate : ComputationsRelated W (FutureValueRelation payload-q) k
      Uᴵ Uᴾ
  immediate = related-values-return
    (imprecise-value payload-endpoints)
    (precise-value payload-endpoints)
    (λ j j≤k → value-imprecision-downward-to j≤k payload-related)

  continuation : ComputationsRelated W (FutureValueRelation q) k Uᴵ Uᴾ
  continuation = ClosureProof.computations-related-reindex
    payload-q q precise-eq imprecise-eq refl refl immediate
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-matched Hᴾ≡Gᴾ precise-step precise-step-eq
    | projection-same
    | tag-mismatched Hᴵ≢Gᴵ imprecise-step imprecise-step-eq =
  ⊥-elim (Hᴵ≢Gᴵ (sym
    (dynamic-payload-projection-target-agrees {W = W}
      hᴵ gᴾ Hᴾ≡Gᴾ payload-q (C.ground-nonstar gᴵ)
      q targetᴾ targetᴵ)))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-matched Hᴾ≡Gᴾ precise-step precise-step-eq
    | projection-expanded Dᴵ≠Gᴵ imprecise-step imprecise-step-eq =
  ⊥-elim (Dᴵ≠Gᴵ (trans target-agrees tags-agree))
  where
  target-agrees = dynamic-payload-projection-target-agrees {W = W}
    hᴵ gᴾ Hᴾ≡Gᴾ payload-q nsᴵ q targetᴾ targetᴵ

  tags-agree = dynamic-payload-projection-tags-agree {W = W}
    hᴵ gᴾ gᴵ Hᴾ≡Gᴾ payload-q cᴵ nsᴵ q targetᴾ targetᴵ
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-same
    | tag-mismatched Hᴾ≢Gᴾ precise-step precise-step-eq =
  precise-pure-step-to-blame (λ ())
    (projection-cast-value-none gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
      (C.ground-nonstar gᴾ) (precise-value endpoints))
    precise-step precise-step-eq
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (value-imprecision-endpoints payload-related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched Hᴾ≡Gᴾ inner-step inner-step-eq
    with projection-step-view {Σ = impreciseStore (core W)}
      gᴵ cᴵ ★∼Gᴵ nsᴵ (imprecise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched Hᴾ≡Gᴾ inner-step inner-step-eq
    | projection-same
    with tag-projection-step-view {Σ = impreciseStore (core W)}
      hᴵ gᴵ Hᴵ∼★ ★∼Gᴵ
      (imprecise-value (value-imprecision-endpoints payload-related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched Hᴾ≡Gᴾ inner-step inner-step-eq
    | projection-same
    | tag-matched Hᴵ≡Gᴵ imprecise-step imprecise-step-eq =
  related-pure-step-expand (λ ()) (λ ())
    (projection-cast-value-none gᴵ ★∼Gᴵ (C.idᵍ gᴵ)
      (C.ground-nonstar gᴵ) (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    imprecise-step precise-step imprecise-step-eq precise-step-eq
    after-outer
  where
  precise-inner-value-eq = projection-cast-value-none
    gᴾ ★∼Gᴾ (C.idᵍ gᴾ) (C.ground-nonstar gᴾ)
    (precise-value endpoints)

  payload-endpoints = value-imprecision-endpoints payload-related

  precise-payload-type-eq : preciseType payload-endpoints ≡ Gᴾ
  precise-payload-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (trans (preciseEmbedded payload-endpoints)
      (cong (embedPrecise (core W)) Hᴾ≡Gᴾ))

  precise-payload-typed = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ Uᴾ ⦂ A)
    precise-payload-type-eq (precise-typed payload-endpoints)

  precise-source-eq = cong (embedPrecise (core W)) (sym Hᴾ≡Gᴾ)

  imprecise-target-eq = trans
    (cong (embedImprecise (core W)) Hᴵ≡Gᴵ) targetᴵ

  residual : ComputationsRelated W (FutureValueRelation q) k
      Uᴵ (Uᴾ ⟨ cᴾ ⟩)
  residual with ground-expanded-cast-view
    gᴾ cᴾ nsᴾ
    (precise-value payload-endpoints) precise-payload-typed Bᴾ≠Gᴾ
  residual | ground-cast-value precise-cast-value =
    related-values-return (imprecise-value payload-endpoints)
      precise-cast-value casted-at
    where
    casted-at : ∀ j → j ≤ k
      → FutureValueRelation q W future-refl j Uᴵ (Uᴾ ⟨ cᴾ ⟩)
    casted-at zero j≤k = precise-casted-value-endpoints
      precise-source-eq refl cᴾ targetᴾ imprecise-target-eq
      payload-related (imprecise-value payload-endpoints)
      precise-cast-value
    casted-at (suc j) j≤k = related-computation-values
      (related-value-precise-cast payload-q precise-source-eq refl cᴾ q
        targetᴾ imprecise-target-eq
        (value-imprecision-downward-to j≤k payload-related))
      (imprecise-value payload-endpoints) precise-cast-value
  residual | ground-cast-blame =
    related-precise-bot-intro (precise-value payload-endpoints)

  after-outer : ComputationsRelated W (FutureValueRelation q) k Uᴵ
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-outer = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} precise-inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    residual
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    {μᴵ = μᴵ}
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched Hᴾ≡Gᴾ inner-step inner-step-eq
    | projection-same
    | tag-mismatched Hᴵ≢Gᴵ imprecise-step imprecise-step-eq =
  ⊥-elim (Hᴵ≢Gᴵ (dynamic-payload-cast-tags-agree
    {W = W} {μᴵ = μᴵ}
    hᴵ gᴾ gᴵ Hᴾ≡Gᴾ payload-q cᴾ nsᴾ (C.idᵍ {μ = μᴵ} gᴵ)
    (C.ground-nonstar gᴵ) q targetᴾ targetᴵ))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched Hᴾ≡Gᴾ inner-step inner-step-eq
    | projection-expanded Bᴵ≠Gᴵ imprecise-step imprecise-step-eq
    with tag-projection-step-view {Σ = impreciseStore (core W)}
      hᴵ gᴵ Hᴵ∼★ ★∼Gᴵ
      (imprecise-value (value-imprecision-endpoints payload-related))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape .Gᴾ .Gᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched refl inner-step inner-step-eq
    | projection-expanded Bᴵ≠Gᴵ imprecise-step imprecise-step-eq
    | tag-matched refl inner-stepᴵ inner-step-eqᴵ =
  related-pure-step-expand (λ ()) (λ ())
    (projection-cast-value-none gᴵ ★∼Gᴵ cᴵ nsᴵ
      (imprecise-value endpoints))
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    imprecise-step precise-step imprecise-step-eq precise-step-eq
    after-outer
  where
  imprecise-inner-value-eq = projection-cast-value-none
    gᴵ ★∼Gᴵ (C.idᵍ gᴵ) (C.ground-nonstar gᴵ)
    (imprecise-value endpoints)

  precise-inner-value-eq = projection-cast-value-none
    gᴾ ★∼Gᴾ (C.idᵍ gᴾ) (C.ground-nonstar gᴾ)
    (precise-value endpoints)

  residual : ComputationsRelated W (FutureValueRelation q) k
      (Uᴵ ⟨ cᴵ ⟩) (Uᴾ ⟨ cᴾ ⟩)
  residual = related-value-casts payload-q refl refl cᴾ cᴵ
    q targetᴾ targetᴵ payload-related

  after-precise-inner : ComputationsRelated W
      (FutureValueRelation q) k (Uᴵ ⟨ cᴵ ⟩)
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-precise-inner = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} precise-inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    residual

  after-imprecise-inner : ComputationsRelated W (FutureValueRelation q) k
      (((Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩)
        ⟨ groundProjection gᴵ ★∼Gᴵ (C.idᵍ gᴵ)
          (C.ground-nonstar gᴵ) ⟩) ⟨ cᴵ ⟩)
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-imprecise-inner = related-imprecise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴵ} imprecise-inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-stepᴵ) refl)
    (cast-operand-pure-step-question
      {Σ = impreciseStore (core W)} {c = cᴵ} inner-step-eqᴵ)
    after-precise-inner

  after-outer = after-imprecise-inner
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-matched Hᴾ≡Gᴾ inner-step inner-step-eq
    | projection-expanded Bᴵ≠Gᴵ imprecise-step imprecise-step-eq
    | tag-mismatched Hᴵ≢Gᴵ inner-stepᴵ inner-step-eqᴵ =
  ⊥-elim (Hᴵ≢Gᴵ (dynamic-payload-cast-tags-agree {W = W}
    hᴵ gᴾ gᴵ Hᴾ≡Gᴾ payload-q cᴾ nsᴾ cᴵ nsᴵ
    q targetᴾ targetᴵ))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₁ (shape , payload-related))
    | dynamic-payload-shape Hᴾ Hᴵ hᴾ hᴵ μᴾ′ μᴵ′
        Hᴾ∼★ Hᴵ∼★ Uᴾ Uᴵ refl refl payload-q
    | projection-expanded Bᴾ≠Gᴾ precise-step precise-step-eq
    | tag-mismatched Hᴾ≢Gᴾ inner-step inner-step-eq =
  related-precise-keep-step-expand (λ ())
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    (pure-step precise-step) precise-step-eq after-inner
  where
  inner-value-eq = projection-cast-value-none gᴾ ★∼Gᴾ
    (C.idᵍ gᴾ) (C.ground-nonstar gᴾ)
    (precise-value endpoints)

  blame-tail : ComputationsRelated W (FutureValueRelation q) (suc k)
      (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩
        ⟨ groundProjection gᴵ ★∼Gᴵ cᴵ nsᴵ ⟩)
      (blame ⟨ cᴾ ⟩)
  blame-tail = precise-pure-step-to-blame (λ ()) refl blame-⟨⟩
    (blame-cast-step-question
      {Σ = preciseStore (core W)} {c = cᴾ})

  after-inner : ComputationsRelated W (FutureValueRelation q) (suc k)
      (Uᴵ ⟨ groundInjection hᴵ Hᴵ∼★ ⟩
        ⟨ groundProjection gᴵ ★∼Gᴵ cᴵ nsᴵ ⟩)
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-inner = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    blame-tail
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₂ atom-related) with atom-related
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    with projection-step-view {Σ = preciseStore (core W)}
      gᴾ cᴾ ★∼Gᴾ nsᴾ (precise-value endpoints)
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-same
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (dynamic-atom-source-endpoints
        {W = W} {Z = Z} {mode = mode} {k = suc k}
        {Vᴾ = Uᴾ} holds))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode .Gᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-same
    | tag-matched refl precise-step precise-step-eq =
  ⊥-elim (dynamic-atom-no-target (semanticEntry W Z) mode
    holds
    (dynamic-atom-target-occupant {W = W} {Z = Z} {Gᴾ = Gᴾ}
      ground-center nsᴵ q targetᴾ targetᴵ))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-same
    | tag-mismatched Hᴾ≢Gᴾ precise-step precise-step-eq =
  precise-pure-step-to-blame (λ ())
    (projection-cast-value-none gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
      (C.ground-nonstar gᴾ) (precise-value endpoints))
    precise-step precise-step-eq
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    with tag-projection-step-view {Σ = preciseStore (core W)}
      hᴾ gᴾ Hᴾ∼★ ★∼Gᴾ
      (precise-value (dynamic-atom-source-endpoints
        {W = W} {Z = Z} {mode = mode} {k = suc k}
        {Vᴾ = Uᴾ} holds))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode .Gᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    | tag-matched refl inner-step inner-step-eq =
  related-precise-keep-step-expand (λ ())
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    (pure-step precise-step) precise-step-eq after-inner
  where
  source-q = I.X⊑★ mode
  source-related = dynamic-atom-source-value-at
    {W = W} (suc k) {Z = Z} {mode = mode}
    {Vᴵ = Vᴵ} {Vᴾ = Uᴾ} holds

  inner-value-eq = projection-cast-value-none gᴾ ★∼Gᴾ
    (C.idᵍ gᴾ) (C.ground-nonstar gᴾ)
    (precise-value endpoints)

  residual : ComputationsRelated W (FutureValueRelation q) (suc k)
      (Vᴵ ⟨ groundProjection gᴵ ★∼Gᴵ cᴵ nsᴵ ⟩)
      (Uᴾ ⟨ cᴾ ⟩)
  residual = related-value-casts source-q ground-center refl cᴾ
    (groundProjection gᴵ ★∼Gᴵ cᴵ nsᴵ)
    q targetᴾ targetᴵ source-related

  after-inner : ComputationsRelated W (FutureValueRelation q) (suc k)
      (Vᴵ ⟨ groundProjection gᴵ ★∼Gᴵ cᴵ nsᴵ ⟩)
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-inner = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    residual
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    (C.？_ {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ ★∼G = ★∼Gᴵ ⦄
      cᴵ ⦃ Bns = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k} {Vᴵ = Vᴵ}
    (endpoints , inj₂ atom-related)
    | dynamic-atom-tag-related Z mode Hᴾ hᴾ ground-center μᴾ′
        Hᴾ∼★ Uᴾ refl holds
    | projection-expanded Bᴾ≢Gᴾ precise-step precise-step-eq
    | tag-mismatched Hᴾ≢Gᴾ inner-step inner-step-eq =
  related-precise-keep-step-expand (λ ())
    (projection-cast-value-none gᴾ ★∼Gᴾ cᴾ nsᴾ
      (precise-value endpoints))
    (pure-step precise-step) precise-step-eq after-inner
  where
  inner-value-eq = projection-cast-value-none gᴾ ★∼Gᴾ
    (C.idᵍ gᴾ) (C.ground-nonstar gᴾ)
    (precise-value endpoints)

  blame-tail : ComputationsRelated W (FutureValueRelation q) (suc k)
      (Vᴵ ⟨ groundProjection gᴵ ★∼Gᴵ cᴵ nsᴵ ⟩)
      (blame ⟨ cᴾ ⟩)
  blame-tail = precise-pure-step-to-blame (λ ()) refl blame-⟨⟩
    (blame-cast-step-question
      {Σ = preciseStore (core W)} {c = cᴾ})

  after-inner : ComputationsRelated W (FutureValueRelation q) (suc k)
      (Vᴵ ⟨ groundProjection gᴵ ★∼Gᴵ cᴵ nsᴵ ⟩)
      (((Uᴾ ⟨ groundInjection hᴾ Hᴾ∼★ ⟩)
        ⟨ groundProjection gᴾ ★∼Gᴾ (C.idᵍ gᴾ)
          (C.ground-nonstar gᴾ) ⟩) ⟨ cᴾ ⟩)
  after-inner = related-precise-keep-step-expand (λ ())
    (cast-operand-nonvalue {c = cᴾ} inner-value-eq)
    (ξ-⟨⟩ (pure-step inner-step) refl)
    (cast-operand-pure-step-question
      {Σ = preciseStore (core W)} {c = cᴾ} inner-step-eq)
    blame-tail
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    (C.？_ {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ ★∼G = ★∼Gᴾ ⦄
      cᴾ ⦃ Bns = nsᴾ ⦄)
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim (Aᴵ≢★ (imprecise-source-star {W = W} sourceᴵ))
related-value-casts {W = W} I.★⊑★ sourceᴾ sourceᴵ
    ((C.gen cᴾ) Aᴾ≢★) cᴵ q targetᴾ targetᴵ related =
  ⊥-elim (Aᴾ≢★ (precise-source-star {W = W} sourceᴾ))
related-value-casts {W = W} (I.ι⊑ι {ι = ι}) sourceᴾ sourceᴵ
    (C.id aᴾ)
    {μᴵ = μᴵ}
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      (C.id aᴵ) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ {Vᴵ = Vᴵ} related =
  ClosureProof.computations-related-reindex I.ι⊑★ q
    (trans (sym sourceᴾ) targetᴾ) targetᴵ refl refl
    (ClosureProof.computations-related-reindex I.ι⊑★ I.ι⊑★
      refl refl (cong (λ c → Vᴵ ⟨ c ⟩) (sym injection-eq)) refl
      (related-precise-identity tagged-related))
  where
  embedded-cᴵ = C.rename∼ {μ = μᴵ}
    {μ′ = C.renameEnv∼ (impreciseEmbedding (core W)) μᴵ}
    (C.toRenameᵗ (impreciseEmbedding (core W)))
    (C.renameEnv∼-preserves (impreciseEmbedding (core W)) μᴵ)
    (C.id aᴵ)

  source-payload = subst≡
    (λ A → impEnv (core W) I.⊢ ‵ ι ⊑ A)
    (sym sourceᴵ) I.ι⊑ι

  payload-q = ground-cast-target⊑
    (C.renameGround (C.toRenameᵗ (impreciseEmbedding (core W))) gᴵ)
    (C.renameNonStar
      (C.toRenameᵗ (impreciseEmbedding (core W))) nsᴵ)
    embedded-cᴵ source-payload I.ι⊑★

  payload-related = ClosureProof.value-imprecision-reindex
    payload-q I.ι⊑ι refl sourceᴵ related

  tagged-related = right-dynamic-base-tag-value-at _ gᴵ Gᴵ∼★
    payload-q payload-related

  injection-eq = ground-identity-injection-eq gᴵ Gᴵ∼★ nsᴵ aᴵ
related-value-casts {W = W} (I.ι⊑ι {ι = ι}) sourceᴾ sourceᴵ
    (C.id aᴾ)
    {μᴵ = μᴵ}
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      ((C.gen cᴵ) Aᴵ≢★) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ related = ⊥-elim impossible
  where
  embedded-cᴵ = C.rename∼ {μ = μᴵ}
    {μ′ = C.renameEnv∼ (impreciseEmbedding (core W)) μᴵ}
    (C.toRenameᵗ (impreciseEmbedding (core W)))
    (C.renameEnv∼-preserves (impreciseEmbedding (core W)) μᴵ)
    ((C.gen cᴵ) Aᴵ≢★)

  source-payload = subst≡
    (λ A → impEnv (core W) I.⊢ ‵ ι ⊑ A)
    (sym sourceᴵ) I.ι⊑ι

  impossible : ⊥
  impossible with ground-cast-target⊑
    (C.renameGround (C.toRenameᵗ (impreciseEmbedding (core W))) gᴵ)
    (C.renameNonStar
      (C.toRenameᵗ (impreciseEmbedding (core W))) nsᴵ)
    embedded-cᴵ source-payload I.ι⊑★
  impossible | ()
related-value-casts (I.ι⊑ι {ι = ι}) sourceᴾ sourceᴵ (C.id aᴾ)
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with reindex-center-imprecision q
    (trans (sym targetᴾ) sourceᴾ) (sym targetᴵ)
  impossible | ()
related-value-casts (I.ι⊑ι {ι = ι}) sourceᴾ sourceᴵ (cᴾ C.!)
    (C.id aᴵ) q targetᴾ targetᴵ related =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with reindex-center-imprecision q (sym targetᴾ)
    (trans (sym targetᴵ) sourceᴵ)
  impossible | ()
related-value-casts {W = W} p sourceᴾ sourceᴵ
    {μᴾ = μᴾ}
    (C._! {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      (C.id aᴾ) ⦃ Ans = nsᴾ ⦄)
    {μᴵ = μᴵ}
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      (C.id aᴵ) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  ClosureProof.computations-related-reindex I.★⊑★ q
    targetᴾ targetᴵ imprecise-term-eq precise-term-eq
    (related-values-return
      (imprecise-value tagged-endpoints)
      (precise-value tagged-endpoints) at-every-index)
  where
  payload-q = reindex-center-imprecision p
    (sym sourceᴾ) (sym sourceᴵ)

  payload-related = ClosureProof.value-imprecision-reindex
    payload-q p sourceᴾ sourceᴵ related

  tagged-related = dynamic-base-tags-value-at k gᴾ gᴵ Gᴾ∼★
    Gᴵ∼★ payload-q payload-related

  tagged-endpoints = value-imprecision-endpoints tagged-related

  at-every-index : ∀ j → j ≤ k
    → FutureValueRelation I.★⊑★ W future-refl j _ _
  at-every-index j j≤k = dynamic-base-tags-value-at j gᴾ gᴵ
    Gᴾ∼★ Gᴵ∼★ payload-q
    (value-imprecision-downward-to j≤k payload-related)

  precise-injection-eq =
    ground-identity-injection-eq gᴾ Gᴾ∼★ nsᴾ aᴾ

  imprecise-injection-eq =
    ground-identity-injection-eq gᴵ Gᴵ∼★ nsᴵ aᴵ

  precise-term-eq = cong (λ c → Vᴾ ⟨ c ⟩)
    (sym precise-injection-eq)

  imprecise-term-eq = cong (λ c → Vᴵ ⟨ c ⟩)
    (sym imprecise-injection-eq)
related-value-casts {W = W} (I.ι⊑ι {ι = ι}) sourceᴾ sourceᴵ
    (C._! cᴾ)
    {μᴵ = μᴵ}
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      ((C.gen cᴵ) Aᴵ≢★) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ related = ⊥-elim impossible
  where
  embedded-cᴵ = C.rename∼ {μ = μᴵ}
    {μ′ = C.renameEnv∼ (impreciseEmbedding (core W)) μᴵ}
    (C.toRenameᵗ (impreciseEmbedding (core W)))
    (C.renameEnv∼-preserves (impreciseEmbedding (core W)) μᴵ)
    ((C.gen cᴵ) Aᴵ≢★)

  source-payload = subst≡
    (λ A → impEnv (core W) I.⊢ ‵ ι ⊑ A)
    (sym sourceᴵ) I.ι⊑ι

  impossible : ⊥
  impossible with ground-cast-target⊑
    (C.renameGround (C.toRenameᵗ (impreciseEmbedding (core W))) gᴵ)
    (C.renameNonStar
      (C.toRenameᵗ (impreciseEmbedding (core W))) nsᴵ)
    embedded-cᴵ source-payload I.ι⊑★
  impossible | ()
related-value-casts {W = W} (I.ι⊑ι {ι = ι}) sourceᴾ sourceᴵ
    {μᴾ = μᴾ}
    (C._! {G = Gᴾ} ⦃ Gᵍ = gᴾ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      ((C.gen cᴾ) Aᴾ≢★) ⦃ Ans = nsᴾ ⦄)
    (C._! cᴵ)
    q targetᴾ targetᴵ related = ⊥-elim impossible
  where
  embedded-cᴾ = C.rename∼ {μ = μᴾ}
    {μ′ = C.renameEnv∼ (preciseEmbedding (core W)) μᴾ}
    (C.toRenameᵗ (preciseEmbedding (core W)))
    (C.renameEnv∼-preserves (preciseEmbedding (core W)) μᴾ)
    ((C.gen cᴾ) Aᴾ≢★)

  source-payload = subst≡
    (λ A → impEnv (core W) I.⊢ ‵ ι ⊑ A)
    (sym sourceᴾ) I.ι⊑ι

  impossible : ⊥
  impossible with ground-cast-target⊑
    (C.renameGround (C.toRenameᵗ (preciseEmbedding (core W))) gᴾ)
    (C.renameNonStar
      (C.toRenameᵗ (preciseEmbedding (core W))) nsᴾ)
    embedded-cᴾ source-payload I.ι⊑★
  impossible | ()
related-value-casts I.ι⊑ι sourceᴾ sourceᴵ (cᴾ C.!)
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with reindex-center-imprecision q (sym targetᴾ)
    (sym targetᴵ)
  impossible | ()
related-value-casts {W = W} I.ι⊑ι sourceᴾ sourceᴵ
    ((C.gen_ ⦃ Bnvᴾ ⦄ ⦃ occursᴾ ⦄ cᴾ) Aᴾ≢★)
    (C.id aᴵ) q targetᴾ targetᴵ related =
  ⊥-elim (precise-base-generalization-impossible {W = W} sourceᴾ cᴾ
    Bnvᴾ occursᴾ)
related-value-casts {W = W} I.ι⊑ι sourceᴾ sourceᴵ
    ((C.gen_ ⦃ Bnvᴾ ⦄ ⦃ occursᴾ ⦄ cᴾ) Aᴾ≢★)
    (cᴵ C.!) q targetᴾ targetᴵ related =
  ⊥-elim (precise-base-generalization-impossible {W = W} sourceᴾ cᴾ
    Bnvᴾ occursᴾ)
related-value-casts {W = W} I.ι⊑ι sourceᴾ sourceᴵ
    ((C.gen_ ⦃ Bnvᴾ ⦄ ⦃ occursᴾ ⦄ cᴾ) Aᴾ≢★)
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim (precise-base-generalization-impossible {W = W} sourceᴾ cᴾ
    Bnvᴾ occursᴾ)
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ (C.id aᴾ)
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      (C.id aᴵ) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = zero} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related
    with reindex-center-imprecision q
      (trans (sym targetᴾ) sourceᴾ) (sym targetᴵ)
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ (C.id aᴾ)
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      (C.id aᴵ) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = zero} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related
    | I.X⊑★ mode =
  ClosureProof.computations-related-reindex (I.X⊑★ mode) q
    (trans (sym sourceᴾ) targetᴾ) targetᴵ
    (cong (λ c → Vᴵ ⟨ c ⟩) (sym injection-eq)) refl
    (related-precise-identity tagged-related)
  where
  payload-q = subst≡
    (λ A → impEnv (core W) I.⊢ _ ⊑ A)
    (sym sourceᴵ) I.X⊑X

  payload-related : ValueImprecision W payload-q zero Vᴵ Vᴾ
  payload-related = ClosureProof.value-imprecision-reindex
    payload-q I.X⊑X {k = zero} refl sourceᴵ related

  tagged-related : ValueImprecision W (I.X⊑★ mode) zero
      (Vᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩) Vᴾ
  tagged-related = right-dynamic-tag-endpoints {W = W} gᴵ
    Gᴵ∼★ payload-q (I.X⊑★ mode) {k = zero} payload-related

  injection-eq = ground-identity-injection-eq
    gᴵ Gᴵ∼★ nsᴵ aᴵ
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ (C.id aᴾ)
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      (C.id aᴵ) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k} related
    with reindex-center-imprecision q
      (trans (sym targetᴾ) sourceᴾ) (sym targetᴵ)
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ (C.id aᴾ)
    (C._! {G = Gᴵ} ⦃ Gᵍ = gᴵ ⦄ ⦃ G∼★ = Gᴵ∼★ ⦄
      (C.id aᴵ) ⦃ Ans = nsᴵ ⦄)
    q targetᴾ targetᴵ {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (endpoints , paired-holds)
    | I.X⊑★ mode =
  ClosureProof.computations-related-reindex (I.X⊑★ mode) q
    (trans (sym sourceᴾ) targetᴾ) targetᴵ
    (cong (λ c → Vᴵ ⟨ c ⟩) (sym injection-eq)) refl
    (related-precise-identity tagged-related)
  where
  payload-q = subst≡
    (λ A → impEnv (core W) I.⊢ _ ⊑ A)
    (sym sourceᴵ) I.X⊑X

  payload-related : ValueImprecision W payload-q (suc k) Vᴵ Vᴾ
  payload-related = ClosureProof.value-imprecision-reindex
    payload-q I.X⊑X refl sourceᴵ (endpoints , paired-holds)

  tagged-related : ValueImprecision W (I.X⊑★ mode) (suc k)
      (Vᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩) Vᴾ
  tagged-related =
    right-dynamic-tag-endpoints {W = W} gᴵ Gᴵ∼★
      payload-q (I.X⊑★ mode) payload-related ,
    inj₂ (aligned-dynamic-atom-related Gᴵ gᴵ sourceᴵ _ Gᴵ∼★
      Vᴵ refl paired-holds)

  injection-eq = ground-identity-injection-eq
    gᴵ Gᴵ∼★ nsᴵ aᴵ
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ (C.id aᴾ)
    (C._! ((C.gen_ ⦃ Bnvᴵ ⦄ ⦃ occursᴵ ⦄ cᴵ) Aᴵ≢★))
    q targetᴾ targetᴵ related =
  ⊥-elim (imprecise-variable-generalization-impossible
    {W = W} sourceᴵ cᴵ occursᴵ)
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ (C.id aᴾ)
    ((C.gen_ ⦃ Bnvᴵ ⦄ ⦃ occursᴵ ⦄ cᴵ) Aᴵ≢★) q
    targetᴾ targetᴵ related =
  ⊥-elim (imprecise-variable-generalization-impossible
    {W = W} sourceᴵ cᴵ occursᴵ)
related-value-casts I.X⊑X sourceᴾ sourceᴵ (cᴾ C.!) (C.id aᴵ) q
    targetᴾ targetᴵ related = ⊥-elim impossible
  where
  impossible : ⊥
  impossible with reindex-center-imprecision q
    (sym targetᴾ) (trans (sym targetᴵ) sourceᴵ)
  impossible | ()
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ
    ((C.id aᴾ) C.!)
    (C._! ((C.gen_ ⦃ Bnvᴵ ⦄ ⦃ occursᴵ ⦄ cᴵ) Aᴵ≢★))
    q targetᴾ targetᴵ related =
  ⊥-elim (imprecise-variable-generalization-impossible
    {W = W} sourceᴵ cᴵ occursᴵ)
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ
    (C._! ((C.gen_ ⦃ Bnvᴾ ⦄ ⦃ occursᴾ ⦄ cᴾ) Aᴾ≢★))
    (cᴵ C.!) q targetᴾ targetᴵ related =
  ⊥-elim (precise-variable-generalization-impossible
    {W = W} sourceᴾ cᴾ occursᴾ)
related-value-casts I.X⊑X sourceᴾ sourceᴵ (cᴾ C.!)
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with reindex-center-imprecision q
    (sym targetᴾ) (sym targetᴵ)
  impossible | ()
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ
    ((C.gen_ ⦃ Bnvᴾ ⦄ ⦃ occursᴾ ⦄ cᴾ) Aᴾ≢★)
    (C.id aᴵ) q targetᴾ targetᴵ related =
  ⊥-elim (precise-variable-generalization-impossible
    {W = W} sourceᴾ cᴾ occursᴾ)
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ
    ((C.gen_ ⦃ Bnvᴾ ⦄ ⦃ occursᴾ ⦄ cᴾ) Aᴾ≢★)
    (cᴵ C.!) q targetᴾ targetᴵ related =
  ⊥-elim (precise-variable-generalization-impossible
    {W = W} sourceᴾ cᴾ occursᴾ)
related-value-casts {W = W} I.X⊑X sourceᴾ sourceᴵ
    ((C.gen_ ⦃ Bnvᴾ ⦄ ⦃ occursᴾ ⦄ cᴾ) Aᴾ≢★)
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim (precise-variable-generalization-impossible
    {W = W} sourceᴾ cᴾ occursᴾ)
related-value-casts {W = W} (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (C.id aᴾ) cᴵ r
    targetᴾ targetᴵ related =
  ⊥-elim (precise-atom-not-arrow {W = W} aᴾ sourceᴾ)
related-value-casts {W = W} (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ) (C.id aᴵ) r targetᴾ targetᴵ related =
  ⊥-elim (imprecise-atom-not-arrow {W = W} aᴵ sourceᴵ)
related-value-casts {W = W}
    {Cᴾ = Aᴾ₀ ⇒ Bᴾ₀} {Dᴾ = Aᴾ₁ ⇒ Bᴾ₁}
    {Cᴵ = Aᴵ₀ ⇒ Bᴵ₀} {Dᴵ = Aᴵ₁ ⇒ Bᴵ₁}
    (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ) (c₁ᴵ C.↦ c₂ᴵ) r targetᴾ targetᴵ
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    with reindex-center-imprecision (I.⇒⊑⇒ p q)
           (sym sourceᴾ) (sym sourceᴵ)
       | reindex-center-imprecision r (sym targetᴾ) (sym targetᴵ)
related-value-casts {W = W}
    {Cᴾ = Aᴾ₀ ⇒ Bᴾ₀} {Dᴾ = Aᴾ₁ ⇒ Bᴾ₁}
    {Cᴵ = Aᴵ₀ ⇒ Bᴵ₀} {Dᴵ = Aᴵ₁ ⇒ Bᴵ₁}
    (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ) (c₁ᴵ C.↦ c₂ᴵ) r targetᴾ targetᴵ
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | I.⇒⊑⇒ source-domain source-codomain
    | I.⇒⊑⇒ target-domain target-codomain =
  ClosureProof.computations-related-reindex target-local r
    targetᴾ targetᴵ refl refl
    (related-values-return
      (imprecise-value source-endpoints 《 fun 》)
      (precise-value source-endpoints 《 fun 》) at-every-index)
  where
  source-local = I.⇒⊑⇒ source-domain source-codomain
  target-local = I.⇒⊑⇒ target-domain target-codomain

  source-related : ValueImprecision W source-local k Vᴵ Vᴾ
  source-related = ClosureProof.value-imprecision-reindex
    {W = W} source-local (I.⇒⊑⇒ p q)
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} sourceᴾ sourceᴵ related

  source-endpoints : TypedEndpoints W source-local Vᴵ Vᴾ
  source-endpoints = value-imprecision-endpoints source-related

  functions-related : ∀ j
    → ValueImprecision W source-local (suc j) Vᴵ Vᴾ
    → FunctionsRelated W target-domain target-codomain (suc j)
        (Vᴵ ⟨ c₁ᴵ C.↦ c₂ᴵ ⟩)
        (Vᴾ ⟨ c₁ᴾ C.↦ c₂ᴾ ⟩)

  function-head : ∀ j
    → ValueImprecision W source-local (suc j) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ target-domain)
        (suc j) Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation
          (liftCenterImprecision W≼W′ target-codomain))
        (suc j)
        (liftImpreciseTerm W≼W′
          (Vᴵ ⟨ c₁ᴵ C.↦ c₂ᴵ ⟩) · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ⟨ c₁ᴾ C.↦ c₂ᴾ ⟩) · Uᴾ)

  at-every-index : ∀ j → j ≤ k
    → FutureValueRelation target-local W future-refl j
        (Vᴵ ⟨ c₁ᴵ C.↦ c₂ᴵ ⟩)
        (Vᴾ ⟨ c₁ᴾ C.↦ c₂ᴾ ⟩)
  at-every-index zero j≤k = casted-value-endpoints
    {W = W} {p = source-local}
    refl refl (c₁ᴾ C.↦ c₂ᴾ) (c₁ᴵ C.↦ c₂ᴵ)
    {q = target-local} refl refl
    {k = zero} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (value-imprecision-downward-to j≤k source-related)
    (imprecise-value source-endpoints 《 fun 》)
    (precise-value source-endpoints 《 fun 》)
  at-every-index (suc j) sj≤k = casted-value-endpoints
    {W = W} {p = source-local}
    refl refl (c₁ᴾ C.↦ c₂ᴾ) (c₁ᴵ C.↦ c₂ᴵ)
    {q = target-local} refl refl
    {k = suc j} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    source-at-index
    (imprecise-value source-endpoints 《 fun 》)
    (precise-value source-endpoints 《 fun 》) ,
    functions-related j source-at-index
    where
    source-at-index : ValueImprecision W source-local (suc j) Vᴵ Vᴾ
    source-at-index = value-imprecision-downward-to sj≤k source-related

  functions-related zero related-at-suc =
    function-head zero related-at-suc , tt
  functions-related (suc j) related-at-suc =
    function-head (suc j) related-at-suc ,
    functions-related j
      (value-imprecision-downward-to
        {W = W} {p = source-local}
        {j = suc j} {k = suc (suc j)} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        (n≤1+n (suc j)) related-at-suc)

  function-head j related-at-suc W′ W≼W′
      {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ target-codomain)
      (liftCenterImprecision W≼W′ target-codomain)
      refl refl (sym imprecise-application-eq)
      (sym precise-application-eq) expanded
    where
    c₁ᴾ′ = precise-function-domain-future W≼W′ c₁ᴾ
    c₂ᴾ′ = precise-consistency-future W≼W′ c₂ᴾ
    c₁ᴵ′ = imprecise-function-domain-future W≼W′ c₁ᴵ
    c₂ᴵ′ = imprecise-consistency-future W≼W′ c₂ᴵ

    source-domainᴾ′ = trans
      (cong (embedPrecise (core W′))
        (ClosureProof.precise-ground-type-eq W≼W′ Aᴾ₀))
      (embedPrecise-lift W≼W′ Aᴾ₀)
    source-domainᴵ′ = trans
      (cong (embedImprecise (core W′))
        (ClosureProof.imprecise-ground-type-eq W≼W′ Aᴵ₀))
      (embedImprecise-lift W≼W′ Aᴵ₀)
    target-domainᴾ′ = trans
      (cong (embedPrecise (core W′))
        (ClosureProof.precise-ground-type-eq W≼W′ Aᴾ₁))
      (embedPrecise-lift W≼W′ Aᴾ₁)
    target-domainᴵ′ = trans
      (cong (embedImprecise (core W′))
        (ClosureProof.imprecise-ground-type-eq W≼W′ Aᴵ₁))
      (embedImprecise-lift W≼W′ Aᴵ₁)
    source-codomainᴾ′ = trans
      (cong (embedPrecise (core W′))
        (ClosureProof.precise-ground-type-eq W≼W′ Bᴾ₀))
      (embedPrecise-lift W≼W′ Bᴾ₀)
    source-codomainᴵ′ = trans
      (cong (embedImprecise (core W′))
        (ClosureProof.imprecise-ground-type-eq W≼W′ Bᴵ₀))
      (embedImprecise-lift W≼W′ Bᴵ₀)
    target-codomainᴾ′ = trans
      (cong (embedPrecise (core W′))
        (ClosureProof.precise-ground-type-eq W≼W′ Bᴾ₁))
      (embedPrecise-lift W≼W′ Bᴾ₁)
    target-codomainᴵ′ = trans
      (cong (embedImprecise (core W′))
        (ClosureProof.imprecise-ground-type-eq W≼W′ Bᴵ₁))
      (embedImprecise-lift W≼W′ Bᴵ₁)

    source-domain-local′ = reindex-center-imprecision
      (liftCenterImprecision W≼W′ source-domain)
      (sym source-domainᴾ′) (sym source-domainᴵ′)
    source-codomain-local′ = reindex-center-imprecision
      (liftCenterImprecision W≼W′ source-codomain)
      (sym source-codomainᴾ′) (sym source-codomainᴵ′)
    source-local′ = I.⇒⊑⇒ source-domain-local′ source-codomain-local′

    precise-source-function-eq = trans
      (cong₂ _⇒_ source-domainᴾ′ source-codomainᴾ′)
      (sym (liftCenterTy-arrow W≼W′
        (embedPrecise (core W) Aᴾ₀) (embedPrecise (core W) Bᴾ₀)))
    imprecise-source-function-eq = trans
      (cong₂ _⇒_ source-domainᴵ′ source-codomainᴵ′)
      (sym (liftCenterTy-arrow W≼W′
        (embedImprecise (core W) Aᴵ₀) (embedImprecise (core W) Bᴵ₀)))

    source-related′ : ValueImprecision W′ source-local′ (suc j)
        (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
    source-related′ = ClosureProof.value-imprecision-reindex
      {W = W′} source-local′
      (liftCenterImprecision W≼W′ source-local) {k = suc j}
      {Vᴵ = liftImpreciseTerm W≼W′ Vᴵ}
      {Vᴾ = liftPreciseTerm W≼W′ Vᴾ}
      precise-source-function-eq imprecise-source-function-eq
      (ClosureProof.value-imprecision-future
        {W = W} {W′ = W′} {p = source-local} {k = suc j}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} W≼W′ related-at-suc)

    function-callback : ∀ i → i ≤ j
      → CompiledTermRelation {W = W′} source-local′ i []
          (liftPreciseTerm W≼W′ Vᴾ) (liftImpreciseTerm W≼W′ Vᴵ)
    function-callback i i≤j = closed-value-compatible-bounded
      source-related′ i (≤-trans i≤j (n≤1+n j))

    argument-full-callback : ∀ i → i ≤ suc j
      → CompiledTermRelation {W = W′} source-domain-local′ i []
          (Uᴾ ⟨ c₁ᴾ′ ⟩) (Uᴵ ⟨ c₁ᴵ′ ⟩)
    argument-full-callback = closed-cast-compatible-bounded
      (liftCenterImprecision W≼W′ target-domain)
      target-domainᴾ′ target-domainᴵ′ c₁ᴾ′ c₁ᴵ′
      (liftCenterImprecision W≼W′ source-domain)
      source-domainᴾ′ source-domainᴵ′ related-value-casts
      Uᴵ Uᴾ argument-related

    argument-callback : ∀ i → i ≤ j
      → CompiledTermRelation {W = W′} source-domain-local′ i []
          (Uᴾ ⟨ c₁ᴾ′ ⟩) (Uᴵ ⟨ c₁ᴵ′ ⟩)
    argument-callback i i≤j =
      argument-full-callback i (≤-trans i≤j (n≤1+n j))

    source-endpoints′ : TypedEndpoints W′ source-local′
        (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
    source-endpoints′ = value-imprecision-endpoints
      {W = W′} {p = source-local′} {k = suc j}
      {Vᴵ = liftImpreciseTerm W≼W′ Vᴵ}
      {Vᴾ = liftPreciseTerm W≼W′ Vᴾ} source-related′
    argument-endpoints : TypedEndpoints W′
        (liftCenterImprecision W≼W′ target-domain) Uᴵ Uᴾ
    argument-endpoints = value-imprecision-endpoints
      {W = W′} {p = liftCenterImprecision W≼W′ target-domain}
      {k = suc j} {Vᴵ = Uᴵ} {Vᴾ = Uᴾ} argument-related

    precise-function-type-eq : preciseType source-endpoints′ ≡
        (ClosureProof.precise-ground-type W≼W′ Aᴾ₀ ⇒
          ClosureProof.precise-ground-type W≼W′ Bᴾ₀)
    precise-function-type-eq = renameᵗ-injective
      (toRenameᵗ-injective (preciseEmbedding (core W′)))
      (preciseEmbedded source-endpoints′)

    imprecise-function-type-eq : impreciseType source-endpoints′ ≡
        (ClosureProof.imprecise-ground-type W≼W′ Aᴵ₀ ⇒
          ClosureProof.imprecise-ground-type W≼W′ Bᴵ₀)
    imprecise-function-type-eq = renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W′)))
      (impreciseEmbedded source-endpoints′)

    precise-argument-type-eq : preciseType argument-endpoints ≡
        ClosureProof.precise-ground-type W≼W′ Aᴾ₁
    precise-argument-type-eq = renameᵗ-injective
      (toRenameᵗ-injective (preciseEmbedding (core W′)))
      (trans (preciseEmbedded argument-endpoints)
        (sym target-domainᴾ′))

    imprecise-argument-type-eq : impreciseType argument-endpoints ≡
        ClosureProof.imprecise-ground-type W≼W′ Aᴵ₁
    imprecise-argument-type-eq = renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W′)))
      (trans (impreciseEmbedded argument-endpoints)
        (sym target-domainᴵ′))

    precise-function-typed = subst≡
      (λ A → ⟨ _ , preciseStore (core W′) , [] ⟩ ⊢
        liftPreciseTerm W≼W′ Vᴾ ⦂ A)
      precise-function-type-eq (precise-typed source-endpoints′)

    imprecise-function-typed = subst≡
      (λ A → ⟨ _ , impreciseStore (core W′) , [] ⟩ ⊢
        liftImpreciseTerm W≼W′ Vᴵ ⦂ A)
      imprecise-function-type-eq (imprecise-typed source-endpoints′)

    precise-argument-typed = ⊢⟨⟩
      (subst≡
        (λ A → ⟨ _ , preciseStore (core W′) , [] ⟩ ⊢ Uᴾ ⦂ A)
        precise-argument-type-eq (precise-typed argument-endpoints)) c₁ᴾ′

    imprecise-argument-typed = ⊢⟨⟩
      (subst≡
        (λ A → ⟨ _ , impreciseStore (core W′) , [] ⟩ ⊢ Uᴵ ⦂ A)
        imprecise-argument-type-eq (imprecise-typed argument-endpoints)) c₁ᴵ′

    precise-applied-typed = ⊢· precise-function-typed
      precise-argument-typed
    imprecise-applied-typed = ⊢· imprecise-function-typed
      imprecise-argument-typed

    precise-close-eq = subst-closed
      (closingSubstitution
        (preciseClosingSubstitution {W = W′} {k = j} related-empty))
      precise-applied-typed
    imprecise-close-eq = subst-closed
      (closingSubstitution
        (impreciseClosingSubstitution {W = W′} {k = j} related-empty))
      imprecise-applied-typed

    applied-raw = application-semantic-bounded j
      function-callback
      argument-callback W′ future-refl related-empty

    applied : ComputationsRelated W′
        (FutureValueRelation source-codomain-local′) j
        (liftImpreciseTerm W≼W′ Vᴵ · (Uᴵ ⟨ c₁ᴵ′ ⟩))
        (liftPreciseTerm W≼W′ Vᴾ · (Uᴾ ⟨ c₁ᴾ′ ⟩))
    applied = ClosureProof.computations-related-reindex
      source-codomain-local′ source-codomain-local′ refl refl
      imprecise-close-eq precise-close-eq applied-raw

    casted = cast-computations-related
      {R = FutureValueRelation source-codomain-local′}
      {S = FutureValueRelation
        (liftCenterImprecision W≼W′ target-codomain)}
      source-codomain-local′ refl refl c₂ᴾ′ c₂ᴵ′
      (liftCenterImprecision W≼W′ target-codomain)
      target-codomainᴾ′ target-codomainᴵ′ j
      (liftImpreciseTerm W≼W′ Vᴵ · (Uᴵ ⟨ c₁ᴵ′ ⟩))
      (liftPreciseTerm W≼W′ Vᴾ · (Uᴾ ⟨ c₁ᴾ′ ⟩))
      (λ W′≼W″ sourceᴾ″ sourceᴵ″ cᴾ″ cᴵ″ targetᴾ″ targetᴵ″
          related″ →
        computations-related-future-compose W′≼W″
          (liftCenterImprecision W≼W′ target-codomain)
          (related-value-casts
            (liftCenterImprecision W′≼W″ source-codomain-local′)
            sourceᴾ″ sourceᴵ″ cᴾ″ cᴵ″
            (liftCenterImprecision W′≼W″
              (liftCenterImprecision W≼W′ target-codomain))
            targetᴾ″ targetᴵ″ related″)) applied

    expanded : ComputationsRelated W′
        (FutureValueRelation
          (liftCenterImprecision W≼W′ target-codomain))
        (suc j)
        ((liftImpreciseTerm W≼W′ Vᴵ
          ⟨ c₁ᴵ′ C.↦ c₂ᴵ′ ⟩) · Uᴵ)
        ((liftPreciseTerm W≼W′ Vᴾ
          ⟨ c₁ᴾ′ C.↦ c₂ᴾ′ ⟩) · Uᴾ)
    expanded with function-cast-application-step-question
      {Σ = impreciseStore (core W′)}
      (imprecise-value source-endpoints′)
      (imprecise-value argument-endpoints)
    expanded
      | vVᴵ′ , vUᴵ′ , imprecise-step-eq
      with function-cast-application-step-question
        {Σ = preciseStore (core W′)}
        (precise-value source-endpoints′)
        (precise-value argument-endpoints)
    expanded
      | vVᴵ′ , vUᴵ′ , imprecise-step-eq
      | vVᴾ′ , vUᴾ′ , precise-step-eq =
      related-pure-step-expand (λ ()) (λ ()) refl refl
        (β-⇒ vVᴵ′ vUᴵ′) (β-⇒ vVᴾ′ vUᴾ′)
        imprecise-step-eq precise-step-eq casted

    imprecise-application-eq = cong (_· Uᴵ)
      (lift-imprecise-function-cast W≼W′ Vᴵ c₁ᴵ c₂ᴵ)

    precise-application-eq = cong (_· Uᴾ)
      (lift-precise-function-cast W≼W′ Vᴾ c₁ᴾ c₂ᴾ)
related-value-casts {W = W} (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ) (C.id x C.!) r targetᴾ targetᴵ related =
  ⊥-elim (imprecise-atom-not-arrow {W = W} x sourceᴵ)
related-value-casts {W = W}
    {Cᴾ = Aᴾ₀ ⇒ Bᴾ₀} {Dᴾ = Aᴾ₁ ⇒ Bᴾ₁}
    {Cᴵ = Aᴵ₀ ⇒ Bᴵ₀}
    (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ)
    {μᴵ = μᴵ}
    (C._! {G = ★ ⇒ ★} ⦃ Gᵍ = ★⇒★ ⦄
      ⦃ G∼★ = C.⇒∼★ ⦄ (c₁ᴵ C.↦ c₂ᴵ) ⦃ Ans = nsᴵ ⦄)
    r targetᴾ targetᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    with reindex-center-imprecision (I.⇒⊑⇒ p q)
           (sym sourceᴾ) (sym sourceᴵ)
       | reindex-center-imprecision r (sym targetᴾ) (sym targetᴵ)
related-value-casts {W = W}
    {Cᴾ = Aᴾ₀ ⇒ Bᴾ₀} {Dᴾ = Aᴾ₁ ⇒ Bᴾ₁}
    {Cᴵ = Aᴵ₀ ⇒ Bᴵ₀}
    (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ)
    {μᴵ = μᴵ}
    (C._! {G = ★ ⇒ ★} ⦃ Gᵍ = ★⇒★ ⦄
      ⦃ G∼★ = C.⇒∼★ ⦄ (c₁ᴵ C.↦ c₂ᴵ) ⦃ Ans = nsᴵ ⦄)
    r targetᴾ targetᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | I.⇒⊑⇒ source-domain source-codomain
    | I.⇒⊑★ target-domain target-codomain
    with injection-step-view {Σ = impreciseStore (core W)}
      ★⇒★ (c₁ᴵ C.↦ c₂ᴵ) C.⇒∼★ nsᴵ
      (imprecise-value (value-imprecision-endpoints related))
related-value-casts {W = W}
    {Cᴾ = Aᴾ₀ ⇒ Bᴾ₀} {Dᴾ = Aᴾ₁ ⇒ Bᴾ₁}
    {Cᴵ = ★ ⇒ ★}
    (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ)
    {μᴵ = μᴵ}
    (C._! {G = ★ ⇒ ★} ⦃ Gᵍ = ★⇒★ ⦄
      ⦃ G∼★ = C.⇒∼★ ⦄ (C.id ★ C.↦ C.id ★)
      ⦃ Ans = nsᴵ ⦄)
    r targetᴾ targetᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | I.⇒⊑⇒ source-domain source-codomain
    | I.⇒⊑★ target-domain target-codomain
    | injection-same =
  paired-cast-values ob (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ)
    (C._! {G = ★ ⇒ ★} ⦃ Gᵍ = ★⇒★ ⦄
      ⦃ G∼★ = C.⇒∼★ ⦄ (C.id ★ C.↦ C.id ★)
      ⦃ Ans = nsᴵ ⦄)
    open-function-injection r targetᴾ targetᴵ related
related-value-casts {W = W}
    {Cᴾ = Aᴾ₀ ⇒ Bᴾ₀} {Dᴾ = Aᴾ₁ ⇒ Bᴾ₁}
    {Cᴵ = Aᴵ₀ ⇒ Bᴵ₀}
    (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ)
    {μᴵ = μᴵ}
    (C._! {G = ★ ⇒ ★} ⦃ Gᵍ = ★⇒★ ⦄
      ⦃ G∼★ = C.⇒∼★ ⦄ (c₁ᴵ C.↦ c₂ᴵ) ⦃ Ans = nsᴵ ⦄)
    r targetᴾ targetᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | I.⇒⊑⇒ source-domain source-codomain
    | I.⇒⊑★ target-domain target-codomain
    | injection-expanded Aᴵ≢★⇒★ imprecise-step imprecise-step-eq =
  ClosureProof.computations-related-reindex target-local r
    targetᴾ targetᴵ refl refl
    (related-imprecise-keep-step-expand (λ ())
      (step-question-value-none {Σ = impreciseStore (core W)}
        imprecise-step-eq)
      (pure-step imprecise-step) imprecise-step-eq residual)
  where
  source-local = I.⇒⊑⇒ source-domain source-codomain
  target-local = I.⇒⊑★ target-domain target-codomain
  payload-q = I.⇒⊑⇒ target-domain target-codomain

  source-related : ValueImprecision W source-local k Vᴵ Vᴾ
  source-related = ClosureProof.value-imprecision-reindex
    source-local (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ related

  source-endpoints = value-imprecision-endpoints source-related

  payload-at : ∀ j → j ≤ k
    → ValueImprecision W payload-q j
        (Vᴵ ⟨ c₁ᴵ C.↦ c₂ᴵ ⟩)
        (Vᴾ ⟨ c₁ᴾ C.↦ c₂ᴾ ⟩)
  payload-at zero j≤k = casted-value-endpoints
    refl refl (c₁ᴾ C.↦ c₂ᴾ) (c₁ᴵ C.↦ c₂ᴵ) refl refl
    source-related
    (imprecise-value source-endpoints 《 fun 》)
    (precise-value source-endpoints 《 fun 》)
  payload-at (suc j) j≤k = related-computation-values
    (related-value-casts source-local refl refl
      (c₁ᴾ C.↦ c₂ᴾ) (c₁ᴵ C.↦ c₂ᴵ)
      payload-q refl refl
      (value-imprecision-downward-to j≤k source-related))
    (imprecise-value source-endpoints 《 fun 》)
    (precise-value source-endpoints 《 fun 》)

  tagged-at : ∀ j → j ≤ k
    → FutureValueRelation target-local W future-refl j
        (Vᴵ ⟨ c₁ᴵ C.↦ c₂ᴵ ⟩
          ⟨ groundInjection ★⇒★ C.⇒∼★ ⟩)
        (Vᴾ ⟨ c₁ᴾ C.↦ c₂ᴾ ⟩)
  tagged-at j j≤k = right-dynamic-function-tag-value-at
    j target-domain target-codomain (payload-at j j≤k)

  tagged-endpoints = value-imprecision-endpoints
    (tagged-at k ≤-refl)

  residual = related-values-return
    (imprecise-value tagged-endpoints)
    (precise-value tagged-endpoints) tagged-at
related-value-casts (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ)
    (C._! ⦃ Gᵍ = ∀★ ⦄
      ((C.gen_ ⦃ z∈B = () ⦄ cᴵ) x)) r targetᴾ targetᴵ related
related-value-casts (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ
    (c₁ᴾ C.↦ c₂ᴾ) ((C.gen cᴵ) Aᴵ≢★) r
    targetᴾ targetᴵ related = ⊥-elim impossible
  where
  impossible : ⊥
  impossible with reindex-center-imprecision r
    (sym targetᴾ) (sym targetᴵ)
  impossible | ()
related-value-casts (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ (cᴾ C.!) cᴵ r
    targetᴾ targetᴵ related =
  paired-cast-values ob (I.⇒⊑⇒ p q)
    sourceᴾ sourceᴵ (cᴾ C.!) cᴵ open-function-precise-injection
    r targetᴾ targetᴵ related
related-value-casts (I.⇒⊑⇒ p q) sourceᴾ sourceᴵ ((C.gen cᴾ) Aᴾ≢★)
    cᴵ r targetᴾ targetᴵ related =
  paired-cast-values ob (I.⇒⊑⇒ p q)
    sourceᴾ sourceᴵ ((C.gen cᴾ) Aᴾ≢★) cᴵ
    open-function-precise-generalization r targetᴾ targetᴵ related
related-value-casts {W = W}
    {Cᴾ = `∀ Aᴾ₀} {Dᴾ = `∀ Aᴾ₁}
    {Cᴵ = `∀ Aᴵ₀} {Dᴵ = `∀ Aᴵ₁}
    (I.∀⊑∀ p) sourceᴾ sourceᴵ (C.∀ᶜ cᴾ) (C.∀ᶜ cᴵ)
    (I.∀⊑∀ q) targetᴾ targetᴵ
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  ClosureProof.computations-related-reindex target-local (I.∀⊑∀ q)
    targetᴾ targetᴵ refl refl
    (related-values-return
      (imprecise-value source-endpoints 《 all 》)
      (precise-value source-endpoints 《 all 》) at-every-index)
  where
  source-body = reindex-center-imprecision p
    (sym (ty-all-injective sourceᴾ))
    (sym (ty-all-injective sourceᴵ))

  target-body = reindex-center-imprecision q
    (sym (ty-all-injective targetᴾ))
    (sym (ty-all-injective targetᴵ))

  source-local = I.∀⊑∀ source-body
  target-local = I.∀⊑∀ target-body

  source-related : ValueImprecision W source-local k Vᴵ Vᴾ
  source-related = ClosureProof.value-imprecision-reindex
    source-local (I.∀⊑∀ p) sourceᴾ sourceᴵ related

  source-endpoints : TypedEndpoints W source-local Vᴵ Vᴾ
  source-endpoints = value-imprecision-endpoints source-related

  universals-related : ∀ j
    → ValueImprecision W source-local (suc j) Vᴵ Vᴾ
    → UniversalsRelated W target-body Aᴾ₁ Aᴵ₁ (suc j)
        (Vᴵ ⟨ C.∀ᶜ cᴵ ⟩) (Vᴾ ⟨ C.∀ᶜ cᴾ ⟩)

  universal-head : ∀ j
    → ValueImprecision W source-local (suc j) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
        (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
        (s : liftPreciseBody W≼W′ Aᴾ₁ [ Rᴾ ]ᵗ
          ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ Aᴵ₁ [ Rᴵ ]ᵗ)
      → let step = future-paired (future-refl {W = W′}) r
        in ComputationsRelated W′ (PostBindValueRelation step s) (suc j)
            (liftImpreciseTerm W≼W′ (Vᴵ ⟨ C.∀ᶜ cᴵ ⟩)
              ⦂∀ liftImpreciseBody W≼W′ Aᴵ₁ [ Rᴵ ])
            (liftPreciseTerm W≼W′ (Vᴾ ⟨ C.∀ᶜ cᴾ ⟩)
              ⦂∀ liftPreciseBody W≼W′ Aᴾ₁ [ Rᴾ ])

  at-every-index : ∀ j → j ≤ k
    → FutureValueRelation target-local W future-refl j
        (Vᴵ ⟨ C.∀ᶜ cᴵ ⟩) (Vᴾ ⟨ C.∀ᶜ cᴾ ⟩)
  at-every-index zero j≤k = casted-value-endpoints
    {W = W} {p = source-local} refl refl
    (C.∀ᶜ cᴾ) (C.∀ᶜ cᴵ) {q = target-local} refl refl
    {k = zero} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (value-imprecision-downward-to j≤k source-related)
    (imprecise-value source-endpoints 《 all 》)
    (precise-value source-endpoints 《 all 》)
  at-every-index (suc j) sj≤k =
    casted-value-endpoints
      {W = W} {p = source-local} refl refl
      (C.∀ᶜ cᴾ) (C.∀ᶜ cᴵ) {q = target-local} refl refl
      {k = suc j} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} source-at-index
      (imprecise-value source-endpoints 《 all 》)
      (precise-value source-endpoints 《 all 》) ,
    Aᴾ₁ , Aᴵ₁ , refl , refl , universals-related j source-at-index
    where
    source-at-index : ValueImprecision W source-local (suc j) Vᴵ Vᴾ
    source-at-index = value-imprecision-downward-to sj≤k source-related

  universals-related zero related-at-suc =
    universal-head zero related-at-suc , tt
  universals-related (suc j) related-at-suc =
    universal-head (suc j) related-at-suc ,
    universals-related j
      (value-imprecision-downward-to
        {W = W} {p = source-local}
        {j = suc j} {k = suc (suc j)} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        (n≤1+n (suc j)) related-at-suc)

  universal-head j related-at-suc W′ W≼W′ Rᴾ Rᴵ r s
      = ClosureProof.computations-related-post-bind-reindex s s refl refl
          imprecise-redex-eq precise-redex-eq expanded
    where
    step = future-paired (future-refl {W = W′}) r

    cᴾ′ = precise-universal-body-consistency-future W≼W′ cᴾ
    cᴵ′ = imprecise-universal-body-consistency-future W≼W′ cᴵ

    source-bodyᴾ-embedded = precise-body-lift-eq W≼W′ Aᴾ₀

    source-bodyᴵ-embedded = imprecise-body-lift-eq W≼W′ Aᴵ₀

    source-body-local′ = reindex-center-imprecision
      (liftCenterBodyImprecision W≼W′ source-body)
      (sym source-bodyᴾ-embedded) (sym source-bodyᴵ-embedded)

    source-allᴾ-eq = trans
      (cong (embedPrecise (core W′))
        (sym (trans
          (ClosureProof.precise-ground-type-eq W≼W′ (`∀ Aᴾ₀))
          (liftPreciseTy-universal W≼W′ Aᴾ₀))))
      (trans
        (cong (embedPrecise (core W′))
          (ClosureProof.precise-ground-type-eq W≼W′ (`∀ Aᴾ₀)))
        (embedPrecise-lift W≼W′ (`∀ Aᴾ₀)))

    source-allᴵ-eq = trans
      (cong (embedImprecise (core W′))
        (sym (trans
          (ClosureProof.imprecise-ground-type-eq W≼W′ (`∀ Aᴵ₀))
          (liftImpreciseTy-universal W≼W′ Aᴵ₀))))
      (trans
        (cong (embedImprecise (core W′))
          (ClosureProof.imprecise-ground-type-eq W≼W′ (`∀ Aᴵ₀)))
        (embedImprecise-lift W≼W′ (`∀ Aᴵ₀)))

    source-related′ : ValueImprecision W′
        (I.∀⊑∀ source-body-local′) (suc j)
        (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
    source-related′ = ClosureProof.value-imprecision-reindex
      (I.∀⊑∀ source-body-local′)
      (liftCenterImprecision W≼W′ source-local)
      source-allᴾ-eq source-allᴵ-eq
      (ClosureProof.value-imprecision-future
        {W = W} {W′ = W′} {p = source-local} {k = suc j}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} W≼W′ related-at-suc)

    source-s : liftPreciseBody W≼W′ Aᴾ₀ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ Aᴵ₀ [ Rᴵ ]ᵗ
    source-s = openRelatedBodyImprecision
      {W = W′} {Aᴾ = liftPreciseBody W≼W′ Aᴾ₀}
      {Aᴵ = liftImpreciseBody W≼W′ Aᴵ₀}
      {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} source-body-local′ r

    source-applied-at : (n : ℕ)
      → ValueImprecision W′ (I.∀⊑∀ source-body-local′) (suc n)
          (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
      → ComputationsRelated W′ (PostBindValueRelation step source-s) n
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ Aᴵ₀ [ Rᴵ ])
        (liftPreciseTerm W≼W′ Vᴾ
          ⦂∀ liftPreciseBody W≼W′ Aᴾ₀ [ Rᴾ ])
    source-applied-at zero related-at =
      nonvalue-computations-zero (λ ()) (λ ()) refl refl
    source-applied-at (suc j′) related-at =
      positive-universal-application
      {W = W′} {Cᴾ = liftPreciseBody W≼W′ Aᴾ₀}
      {Cᴵ = liftImpreciseBody W≼W′ Aᴵ₀}
      {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {p = source-body-local′}
      {r = r} {s = source-s}
      refl refl (s≤s z≤n)
      (value-imprecision-downward-to
        {W = W′} {p = I.∀⊑∀ source-body-local′}
        {j = suc j′} {k = suc (suc j′)}
        {Vᴵ = liftImpreciseTerm W≼W′ Vᴵ}
        {Vᴾ = liftPreciseTerm W≼W′ Vᴾ}
        (n≤1+n (suc j′)) related-at)

    source-applied : ComputationsRelated W′
        (PostBindValueRelation step source-s) j
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ Aᴵ₀ [ Rᴵ ])
        (liftPreciseTerm W≼W′ Vᴾ
          ⦂∀ liftPreciseBody W≼W′ Aᴾ₀ [ Rᴾ ])
    source-applied = source-applied-at j source-related′

    casted = cast-computations-related
      {R = PostBindValueRelation step source-s}
      {S = PostBindValueRelation step s}
      source-s refl refl (cᴾ′ [ Rᴾ ]ᶜ) (cᴵ′ [ Rᴵ ]ᶜ)
      s refl refl j
      (liftImpreciseTerm W≼W′ Vᴵ
        ⦂∀ liftImpreciseBody W≼W′ Aᴵ₀ [ Rᴵ ])
      (liftPreciseTerm W≼W′ Vᴾ
        ⦂∀ liftPreciseBody W≼W′ Aᴾ₀ [ Rᴾ ])
      (λ W′≼W″ sourceᴾ″ sourceᴵ″ dᴾ dᴵ targetᴾ″ targetᴵ″
          (bound≼W″ , factor , related″) →
        computations-related-post-bind-compose
          step W′≼W″ bound≼W″ factor s
          (related-value-casts
            (liftCenterImprecision W′≼W″ source-s)
            sourceᴾ″ sourceᴵ″ dᴾ dᴵ
            (liftCenterImprecision W′≼W″ s)
            targetᴾ″ targetᴵ″ related″)) source-applied

    source-endpoints′ : TypedEndpoints W′
        (I.∀⊑∀ source-body-local′)
        (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
    source-endpoints′ = value-imprecision-endpoints
      {W = W′} {p = I.∀⊑∀ source-body-local′} {k = suc j}
      {Vᴵ = liftImpreciseTerm W≼W′ Vᴵ}
      {Vᴾ = liftPreciseTerm W≼W′ Vᴾ} source-related′

    expanded : ComputationsRelated W′
        (PostBindValueRelation step s) (suc j)
        ((liftImpreciseTerm W≼W′ Vᴵ ⟨ C.∀ᶜ cᴵ′ ⟩)
          ⦂∀ liftImpreciseBody W≼W′ Aᴵ₁ [ Rᴵ ])
        ((liftPreciseTerm W≼W′ Vᴾ ⟨ C.∀ᶜ cᴾ′ ⟩)
          ⦂∀ liftPreciseBody W≼W′ Aᴾ₁ [ Rᴾ ])
    expanded
        with universal-cast-type-application-step-question
          {Σ = impreciseStore (core W′)}
          (imprecise-value source-endpoints′)
    expanded | vVᴵ′ , imprecise-step-eq
        with universal-cast-type-application-step-question
          {Σ = preciseStore (core W′)}
          (precise-value source-endpoints′)
    expanded | vVᴵ′ , imprecise-step-eq
      | vVᴾ′ , precise-step-eq =
      related-pure-step-expand (λ ()) (λ ()) refl refl
        (β-∀ vVᴵ′ refl) (β-∀ vVᴾ′ refl)
        imprecise-step-eq precise-step-eq casted

    imprecise-redex-eq = cong₂ (λ L B → L ⦂∀ B [ Rᴵ ])
      (sym (lift-imprecise-universal-cast W≼W′ Vᴵ cᴵ))
      refl

    precise-redex-eq = cong₂ (λ L B → L ⦂∀ B [ Rᴾ ])
      (sym (lift-precise-universal-cast W≼W′ Vᴾ cᴾ))
      refl
related-value-casts (I.∀⊑∀ p) sourceᴾ sourceᴵ cᴾ cᴵ q targetᴾ
    targetᴵ related =
  paired-cast-values ob (I.∀⊑∀ p)
    sourceᴾ sourceᴵ cᴾ cᴵ open-universals q targetᴾ targetᴵ related
related-value-casts (I.⇒⊑★ p q) sourceᴾ sourceᴵ cᴾ cᴵ r targetᴾ
    targetᴵ related =
  paired-cast-values ob (I.⇒⊑★ p q)
    sourceᴾ sourceᴵ cᴾ cᴵ open-function-dynamic r targetᴾ targetᴵ
    related
related-value-casts I.ι⊑★ sourceᴾ sourceᴵ cᴾ cᴵ q targetᴾ
    targetᴵ related =
  paired-cast-values ob I.ι⊑★
    sourceᴾ sourceᴵ cᴾ cᴵ open-base-dynamic q targetᴾ targetᴵ related
related-value-casts (I.X⊑★ mode) sourceᴾ sourceᴵ cᴾ cᴵ q targetᴾ
    targetᴵ related =
  paired-cast-values ob (I.X⊑★ mode)
    sourceᴾ sourceᴵ cᴾ cᴵ open-variable-dynamic q targetᴾ targetᴵ
    related
related-value-casts (I.∀⊑ nonvar occurs p) sourceᴾ sourceᴵ cᴾ cᴵ q
    targetᴾ targetᴵ related =
  paired-cast-values ob (I.∀⊑ nonvar occurs p)
    sourceᴾ sourceᴵ cᴾ cᴵ open-right-universal q targetᴾ targetᴵ
    related
related-value-casts I.∀★⊑★ sourceᴾ sourceᴵ C.bot-intro cᴵ q
    targetᴾ targetᴵ related =
  related-precise-bot-intro
    (precise-value (value-imprecision-endpoints related))
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ
    (C.inst_ ⦃ Anv ⦄ ⦃ occurs ⦄ cᴾ B≢★) cᴵ q
    targetᴾ targetᴵ related = ⊥-elim impossible
  where
  embedded-occurs = rename-occurs
    (extᵗ (C.toRenameᵗ (preciseEmbedding (core W))))
    (ext-injective
      (toRenameᵗ-injective (preciseEmbedding (core W)))) occurs

  impossible : ⊥
  impossible with subst≡ (Fin.zero ∈ᵗ_)
    (ty-all-injective sourceᴾ) embedded-occurs
  impossible | ()
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ (C.id x) cᴵ q
    targetᴾ targetᴵ related =
  ⊥-elim (precise-atom-not-all {W = W} x sourceᴾ)
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ cᴾ
    (C._! cᴵ ⦃ Ans = nsᴵ ⦄) q targetᴾ targetᴵ related =
  ⊥-elim (imprecise-star-nonstar-impossible {W = W} sourceᴵ nsᴵ)
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ cᴾ
    ((C.gen cᴵ) Aᴵ≢★) q targetᴾ targetᴵ related =
  ⊥-elim (Aᴵ≢★ (imprecise-source-star {W = W} sourceᴵ))
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ (C.∀ᶜ cᴾ)
    (C.id x) q targetᴾ targetᴵ {Vᴵ = Vᴵ} related
    with identity-cast-step-question
      {Σ = impreciseStore (core W)}
      (imprecise-value (value-imprecision-endpoints related))
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ (C.∀ᶜ cᴾ)
    (C.id x) q targetᴾ targetᴵ {Vᴵ = Vᴵ} related
    | vVᴵ , step-eq =
  related-imprecise-keep-step-expand (λ ())
    (identity-cast-value-none x
      (imprecise-value (value-imprecision-endpoints related)))
    (pure-step (β-id vVᴵ)) step-eq
    (related-value-precise-cast I.∀★⊑★ sourceᴾ sourceᴵ
      (C.∀ᶜ cᴾ) q targetᴾ targetᴵ related)
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ (C.∀ᶜ cᴾ)
    (C.？ cᴵ) q targetᴾ targetᴵ
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  cast-computations-related I.∀★⊑★ sourceᴾ sourceᴵ
    (C.∀ᶜ cᴾ) (C.？ cᴵ) q targetᴾ targetᴵ k Vᴵ Vᴾ
    (λ W≼W′ sourceᴾ′ sourceᴵ′ dᴾ dᴵ targetᴾ′ targetᴵ′
        related′ →
      computations-related-future-compose W≼W′ q
        (related-value-casts
          (liftCenterImprecision W≼W′ I.∀★⊑★)
          sourceᴾ′ sourceᴵ′ dᴾ dᴵ
          (liftCenterImprecision W≼W′ q)
          targetᴾ′ targetᴵ′ related′))
    (related-values-return
      (imprecise-value endpoints) (precise-value endpoints)
      (λ j j≤k → value-imprecision-downward-to j≤k related))
  where
  endpoints = value-imprecision-endpoints related
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ
    (C.id x₁ C.!) (C.id x) q targetᴾ targetᴵ related =
  ⊥-elim (precise-atom-not-all {W = W} x₁ sourceᴾ)
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ
    ((C.inst_ ⦃ Anv ⦄ ⦃ occurs ⦄ cᴾ B≢★) C.!)
    (C.id x) q targetᴾ targetᴵ related = ⊥-elim impossible
  where
  embedded-occurs = rename-occurs
    (extᵗ (C.toRenameᵗ (preciseEmbedding (core W))))
    (ext-injective
      (toRenameᵗ-injective (preciseEmbedding (core W)))) occurs

  impossible : ⊥
  impossible with subst≡ (Fin.zero ∈ᵗ_)
    (ty-all-injective sourceᴾ) embedded-occurs
  impossible | ()
related-value-casts I.∀★⊑★ sourceᴾ sourceᴵ
    (C._! {G = `∀ ★} ⦃ Gᵍ = ∀★ ⦄
      ((C.gen_ ⦃ z∈B = () ⦄ cᴾ) x₁))
    (C.id x) q targetᴾ targetᴵ related
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ
    (C._! {G = `∀ ★} ⦃ Gᵍ = ∀★ ⦄
      (C.∀ᶜ (C._! cᴾ ⦃ Ans = nsᴾ ⦄)))
    (C.id x) q targetᴾ targetᴵ related = ⊥-elim impossible
  where
  impossible = nonStar≢★
    (C.renameNonStar
      (extᵗ (C.toRenameᵗ (preciseEmbedding (core W)))) nsᴾ)
    (ty-all-injective sourceᴾ)
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ
    (C._! {G = `∀ ★} ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      (C.∀ᶜ (C.id ★)) ⦃ Ans = nsᴾ ⦄)
    (C.id x) q targetᴾ targetᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related with imprecise-source-star {W = W} sourceᴵ
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ
    (C._! {G = `∀ ★} ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      (C.∀ᶜ (C.id ★)) ⦃ Ans = nsᴾ ⦄)
    (C.id ★) q targetᴾ targetᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related | refl =
  ClosureProof.computations-related-reindex I.★⊑★ q
    targetᴾ targetᴵ refl
    (cong (λ c → Vᴾ ⟨ c ⟩) (sym precise-injection-eq))
    (related-imprecise-identity (tagged-at k ≤-refl))
  where
  precise-tag = groundInjection ∀★ Gᴾ∼★

  precise-injection-eq : C._! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      (C.∀ᶜ (C.id ★)) ⦃ Ans = nsᴾ ⦄ ≡ precise-tag
  precise-injection-eq
    rewrite nonStar-unique nsᴾ (C.ground-nonstar ∀★) = refl

  tagged-at : ∀ j → j ≤ k
    → ValueImprecision W I.★⊑★ j Vᴵ (Vᴾ ⟨ precise-tag ⟩)
  tagged-at zero j≤k = precise-casted-value-endpoints
    {W = W} {p = I.∀★⊑★} sourceᴾ sourceᴵ precise-tag
    {q = I.★⊑★} refl refl {k = zero} source-at
    (imprecise-value source-endpoints)
    (precise-value source-endpoints 《
      inj ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
        ⦃ Gns = C.ground-nonstar ∀★ ⦄ 》)
    where
    source-at : ValueImprecision W I.∀★⊑★ zero Vᴵ Vᴾ
    source-at = value-imprecision-downward-to j≤k related
    source-endpoints : TypedEndpoints W I.∀★⊑★ Vᴵ Vᴾ
    source-endpoints = value-imprecision-endpoints
      {W = W} {p = I.∀★⊑★} {k = zero} source-at
  tagged-at (suc j) sj≤k with
      value-imprecision-downward-to sj≤k related
  tagged-at (suc j) sj≤k
      | endpoints ,
        right-dynamic-payload-shape Gᴵ gᴵ μᴵ′ Gᴵ∼★ Uᴵ refl
          payload-q , payload-related =
    dynamic-base-tags-endpoints ∀★ gᴵ Gᴾ∼★ Gᴵ∼★
      payload-q payload-related ,
    inj₁ (tags-and-payload ∀★ gᴵ Gᴾ∼★ Gᴵ∼★
      payload-q payload-related)
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ (cᴾ C.!)
    (C.？_ cᴵ ⦃ Bns = nsᴵ ⦄) q targetᴾ targetᴵ related =
  ⊥-elim (star-left-nonstar-impossible local-q embedded-nonstar)
  where
  local-q = reindex-center-imprecision q (sym targetᴾ) (sym targetᴵ)

  embedded-nonstar = C.renameNonStar
    (C.toRenameᵗ (impreciseEmbedding (core W))) nsᴵ
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ ((C.gen cᴾ) x)
    (C.id x₁) q targetᴾ targetᴵ {Vᴵ = Vᴵ} related
    with identity-cast-step-question
      {Σ = impreciseStore (core W)}
      (imprecise-value (value-imprecision-endpoints related))
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ ((C.gen cᴾ) x)
    (C.id x₁) q targetᴾ targetᴵ {Vᴵ = Vᴵ} related
    | vVᴵ , step-eq =
  related-imprecise-keep-step-expand (λ ())
    (identity-cast-value-none x₁
      (imprecise-value (value-imprecision-endpoints related)))
    (pure-step (β-id vVᴵ)) step-eq
    (related-value-precise-cast I.∀★⊑★ sourceᴾ sourceᴵ
      ((C.gen cᴾ) x) q targetᴾ targetᴵ related)
related-value-casts {W = W} I.∀★⊑★ sourceᴾ sourceᴵ ((C.gen cᴾ) x)
    (C.？ cᴵ) q targetᴾ targetᴵ
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  cast-computations-related I.∀★⊑★ sourceᴾ sourceᴵ
    ((C.gen cᴾ) x) (C.？ cᴵ) q targetᴾ targetᴵ k Vᴵ Vᴾ
    (λ W≼W′ sourceᴾ′ sourceᴵ′ dᴾ dᴵ targetᴾ′ targetᴵ′
        related′ →
      computations-related-future-compose W≼W′ q
        (related-value-casts
          (liftCenterImprecision W≼W′ I.∀★⊑★)
          sourceᴾ′ sourceᴵ′ dᴾ dᴵ
          (liftCenterImprecision W≼W′ q)
          targetᴾ′ targetᴵ′ related′))
    (related-values-return
      (imprecise-value endpoints) (precise-value endpoints)
      (λ j j≤k → value-imprecision-downward-to j≤k related))
  where
  endpoints = value-imprecision-endpoints related
related-value-casts (I.∀⊑★ nonstar p) sourceᴾ sourceᴵ cᴾ cᴵ q
    targetᴾ targetᴵ related =
  paired-cast-values ob (I.∀⊑★ nonstar p)
    sourceᴾ sourceᴵ cᴾ cᴵ open-universal-dynamic q targetᴾ targetᴵ
    related
related-value-casts I.bot-elim sourceᴾ sourceᴵ cᴾ cᴵ q targetᴾ
    targetᴵ related = ⊥-elim (no-precise-bottom-value related)
related-value-casts I.bot⊑★ sourceᴾ sourceᴵ cᴾ cᴵ q targetᴾ
    targetᴵ related = ⊥-elim (no-precise-bottom-value related)

------------------------------------------------------------------------
-- Open structural cast compatibility
------------------------------------------------------------------------

cast-cast-compatible : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    {p : Cᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ}
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
  → (q : Dᴾ ⊑ᵂ⟨ core W ⟩ Dᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      (Mᴾ ⟨ cᴾ ⟩) (Mᴵ ⟨ cᴵ ⟩)
cast-cast-compatible {W = W} {Cᴾ = Cᴾ} {Dᴾ = Dᴾ}
    {Cᴵ = Cᴵ} {Dᴵ = Dᴵ} {p = p} cᴾ cᴵ
    {Mᴾ = Mᴾ} {Mᴵ = Mᴵ} q M-related k W′ W≼W′ γ =
  ClosureProof.computations-related-reindex q′ q′ refl refl
    (sym imprecise-cast-eq) (sym precise-cast-eq) casted
  where
  p′ = liftCenterImprecision W≼W′ p
  q′ = liftCenterImprecision W≼W′ q

  sourceᴾ′ = trans
    (cong (embedPrecise (core W′))
      (ClosureProof.precise-ground-type-eq W≼W′ Cᴾ))
    (embedPrecise-lift W≼W′ Cᴾ)

  sourceᴵ′ = trans
    (cong (embedImprecise (core W′))
      (ClosureProof.imprecise-ground-type-eq W≼W′ Cᴵ))
    (embedImprecise-lift W≼W′ Cᴵ)

  targetᴾ′ = trans
    (cong (embedPrecise (core W′))
      (ClosureProof.precise-ground-type-eq W≼W′ Dᴾ))
    (embedPrecise-lift W≼W′ Dᴾ)

  targetᴵ′ = trans
    (cong (embedImprecise (core W′))
      (ClosureProof.imprecise-ground-type-eq W≼W′ Dᴵ))
    (embedImprecise-lift W≼W′ Dᴵ)

  cᴾ′ = precise-consistency-future W≼W′ cᴾ
  cᴵ′ = imprecise-consistency-future W≼W′ cᴵ

  operand-related = M-related k W′ W≼W′ γ

  casted = cast-computations-related p′ sourceᴾ′ sourceᴵ′
    cᴾ′ cᴵ′ q′ targetᴾ′ targetᴵ′ k
    (close (impreciseClosingSubstitution γ)
      (liftImpreciseTerm W≼W′ Mᴵ))
    (close (preciseClosingSubstitution γ)
      (liftPreciseTerm W≼W′ Mᴾ))
    (λ W′≼W″ sourceᴾ″ sourceᴵ″ dᴾ dᴵ
        targetᴾ″ targetᴵ″ related →
      computations-related-future-compose W′≼W″ q′
        (related-value-casts
          (liftCenterImprecision W′≼W″ p′)
          sourceᴾ″ sourceᴵ″ dᴾ dᴵ
          (liftCenterImprecision W′≼W″ q′)
          targetᴾ″ targetᴵ″ related))
    operand-related

  precise-cast-eq = cong (close (preciseClosingSubstitution γ))
    (lift-precise-cast W≼W′ Mᴾ cᴾ)

  imprecise-cast-eq = cong (close (impreciseClosingSubstitution γ))
    (lift-imprecise-cast W≼W′ Mᴵ cᴵ)

right-cast-compatible : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    {p : Cᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ}
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
  → (q : Cᴾ ⊑ᵂ⟨ core W ⟩ Dᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      Mᴾ (Mᴵ ⟨ cᴵ ⟩)
right-cast-compatible {W = W} {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Dᴵ = Dᴵ}
    {p = p} cᴵ {Mᴾ = Mᴾ} {Mᴵ = Mᴵ}
    q M-related k W′ W≼W′ γ =
  ClosureProof.computations-related-reindex q′ q′ refl refl
    (sym imprecise-cast-eq) refl casted
  where
  p′ = liftCenterImprecision W≼W′ p
  q′ = liftCenterImprecision W≼W′ q

  sourceᴾ′ = trans
    (cong (embedPrecise (core W′))
      (ClosureProof.precise-ground-type-eq W≼W′ Cᴾ))
    (embedPrecise-lift W≼W′ Cᴾ)

  sourceᴵ′ = trans
    (cong (embedImprecise (core W′))
      (ClosureProof.imprecise-ground-type-eq W≼W′ Cᴵ))
    (embedImprecise-lift W≼W′ Cᴵ)

  targetᴵ′ = trans
    (cong (embedImprecise (core W′))
      (ClosureProof.imprecise-ground-type-eq W≼W′ Dᴵ))
    (embedImprecise-lift W≼W′ Dᴵ)

  cᴵ′ = imprecise-consistency-future W≼W′ cᴵ

  casted = imprecise-cast-computations-related p′ sourceᴾ′ sourceᴵ′
    cᴵ′ q′ sourceᴾ′ targetᴵ′ k
    (close (impreciseClosingSubstitution γ)
      (liftImpreciseTerm W≼W′ Mᴵ))
    (close (preciseClosingSubstitution γ)
      (liftPreciseTerm W≼W′ Mᴾ))
    (λ W′≼W″ sourceᴾ″ sourceᴵ″ dᴵ targetᴾ″ targetᴵ″
        related →
      computations-related-future-compose W′≼W″ q′
        (related-value-imprecise-cast
          (liftCenterImprecision W′≼W″ p′)
          sourceᴾ″ sourceᴵ″ dᴵ
          (liftCenterImprecision W′≼W″ q′)
          targetᴾ″ targetᴵ″ related))
    (M-related k W′ W≼W′ γ)

  imprecise-cast-eq = cong (close (impreciseClosingSubstitution γ))
    (lift-imprecise-cast W≼W′ Mᴵ cᴵ)

left-cast-compatible : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ : Ty Δᴵ}
    {p : Cᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ}
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
  → (q : Dᴾ ⊑ᵂ⟨ core W ⟩ Cᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      (Mᴾ ⟨ cᴾ ⟩) Mᴵ
left-cast-compatible {W = W} {Cᴾ = Cᴾ} {Dᴾ = Dᴾ}
    {Cᴵ = Cᴵ} {p = p} cᴾ {Mᴾ = Mᴾ} {Mᴵ = Mᴵ}
    q M-related k W′ W≼W′ γ =
  ClosureProof.computations-related-reindex q′ q′ refl refl refl
    (sym precise-cast-eq) casted
  where
  p′ = liftCenterImprecision W≼W′ p
  q′ = liftCenterImprecision W≼W′ q

  sourceᴾ′ = trans
    (cong (embedPrecise (core W′))
      (ClosureProof.precise-ground-type-eq W≼W′ Cᴾ))
    (embedPrecise-lift W≼W′ Cᴾ)

  sourceᴵ′ = trans
    (cong (embedImprecise (core W′))
      (ClosureProof.imprecise-ground-type-eq W≼W′ Cᴵ))
    (embedImprecise-lift W≼W′ Cᴵ)

  targetᴾ′ = trans
    (cong (embedPrecise (core W′))
      (ClosureProof.precise-ground-type-eq W≼W′ Dᴾ))
    (embedPrecise-lift W≼W′ Dᴾ)

  cᴾ′ = precise-consistency-future W≼W′ cᴾ

  casted = precise-cast-computations-related p′ sourceᴾ′ sourceᴵ′
    cᴾ′ q′ targetᴾ′ sourceᴵ′ k
    (close (impreciseClosingSubstitution γ)
      (liftImpreciseTerm W≼W′ Mᴵ))
    (close (preciseClosingSubstitution γ)
      (liftPreciseTerm W≼W′ Mᴾ))
    (λ W′≼W″ sourceᴾ″ sourceᴵ″ dᴾ targetᴾ″ targetᴵ″
        related →
      computations-related-future-compose W′≼W″ q′
        (related-value-precise-cast
          (liftCenterImprecision W′≼W″ p′)
          sourceᴾ″ sourceᴵ″ dᴾ
          (liftCenterImprecision W′≼W″ q′)
          targetᴾ″ targetᴵ″ related))
    (M-related k W′ W≼W′ γ)

  precise-cast-eq = cong (close (preciseClosingSubstitution γ))
    (lift-precise-cast W≼W′ Mᴾ cᴾ)
