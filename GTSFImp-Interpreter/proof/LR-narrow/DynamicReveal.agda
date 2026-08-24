open import proof.LR-narrow.RevealStatements

module proof.LR-narrow.DynamicReveal (ob : RevealObligations) where

-- File Charter:
--   * The one-sided structural reveal and conceal at a dynamic slot:
--     the precise endpoint's wrapper unseals (respectively seals) the
--     occurrences of the slot's center variable, exchanging them for
--     the recorded representation's imprecision below ★; the imprecise
--     endpoint carries no conversion.
--   * The seal case consumes (respectively produces) the dynamic
--     atom's payload at the same step index, which the reindexed
--     dynamic-seal clause supplies (Finding D resolution).
--   * A universal precise type is delegated to the obligations record.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (n≤1+n; ≤-trans; ≤-refl; m≤m+n; m≤n+m; <-irrefl)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
import Level
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; id↑; id↓; unseal; seal; _↦↑_; _↦↓_; replaceTy;
   〖_,_↑_〗; makeConceal; ⊢↓-seal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
import proof.Imprecision as PI
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; renameᵗ-injective; ext-injective;
   fin-suc-injective)
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing; structural-conceal-typing)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.KeepStepExpansion using
  (related-precise-keep-step-expand)
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.RevealLifting using
  (renameᵗ-replaceTy; liftPreciseTy-replace;
   liftPreciseTerm-reveal; liftPreciseTerm-conceal)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using
  (revealFrame; concealFrame; RevealFrm; reveal-frm; ConcealFrm;
   conceal-frm)
open import proof.LR-narrow.ArgumentFrame using
  (related-application-computation)
open import proof.LR-narrow.SlotLifting using
  (transported-reveal-eq; transported-conceal-eq;
   liftPreciseTy-arrow;
   ArrowImprecision; arrow-imprecision; arrow-imprecision-view)
open import proof.LR-narrow.TypeRenamingComposition using
  (pack↑; pack↓; apply↑; apply↓)
import proof.LR-narrow.PreciseReveal
open module PreciseRevealModule = proof.LR-narrow.PreciseReveal ob
  using (precise-endpoint-type; identity-reveal; identity-conceal;
         ArrowSource; arrow-arrow; arrow-star; arrow-source-view;
         sizeᵗ; renameᵗ-sizeᵗ; lift-sizeᵗ;
         size-bound-left; size-bound-right)

open RevealObligations ob using
  (blocked-dyn-reveal-universal; blocked-dyn-conceal-universal)

open PreciseComposition revealFrame using () renaming
  (precise-frame-computations-related to reveal-precise-composition;
   PrecisePlugValues to RevealPrecisePlugValues)
open PreciseComposition concealFrame using () renaming
  (precise-frame-computations-related to conceal-precise-composition;
   PrecisePlugValues to ConcealPrecisePlugValues)

------------------------------------------------------------------------
-- Consuming and producing the entry view
------------------------------------------------------------------------

dyn-holds-of : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {a : DynamicSemanticAtom W Z} {mode}
    {e : SemanticEntry W Z mode} {ℛ : PayloadRelation W}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → IsDynamicEntry a e
  → (eqm : mode ≡ I.X⊑★)
  → DynamicAtomHolds ℛ e eqm Vᴵ Vᴾ
  → DynamicHolds ℛ a Vᴵ Vᴾ
dyn-holds-of is-dynamic refl h = h

dyn-holds-to : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {a : DynamicSemanticAtom W Z} {mode}
    {e : SemanticEntry W Z mode} {ℛ : PayloadRelation W}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → IsDynamicEntry a e
  → (eqm : mode ≡ I.X⊑★)
  → DynamicHolds ℛ a Vᴵ Vᴾ
  → DynamicAtomHolds ℛ e eqm Vᴵ Vᴾ
dyn-holds-to is-dynamic refl h = h

dyn-no-paired : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {a : DynamicSemanticAtom W Z} {mode}
    {e : SemanticEntry W Z mode} {ℛ : PayloadRelation W}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → IsDynamicEntry a e
  → PairedAtomHolds ℛ e Vᴵ Vᴾ
  → ⊥
dyn-no-paired is-dynamic (Level.lift ())

-- Transports along a center-variable identification.

dyn-slot-consume : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : DynamicSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ dcenter d)
    {ℛ : PayloadRelation (core W)}
    (eqm : impEnv (core W) Z ≡ I.X⊑★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → DynamicAtomHolds ℛ (semanticEntry W Z) eqm Vᴵ Vᴾ
  → DynamicHolds ℛ (datom d) Vᴵ Vᴾ
dyn-slot-consume d refl eqm h = dyn-holds-of (dentry-is d) eqm h

dyn-slot-produce : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : DynamicSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ dcenter d)
    {ℛ : PayloadRelation (core W)}
    (eqm : impEnv (core W) Z ≡ I.X⊑★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → DynamicHolds ℛ (datom d) Vᴵ Vᴾ
  → DynamicAtomHolds ℛ (semanticEntry W Z) eqm Vᴵ Vᴾ
dyn-slot-produce d refl eqm h = dyn-holds-to (dentry-is d) eqm h

dyn-slot-refute-paired : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : DynamicSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ dcenter d)
    {ℛ : PayloadRelation (core W)}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → PairedAtomHolds ℛ (semanticEntry W Z) Vᴵ Vᴾ
  → ⊥
dyn-slot-refute-paired d refl h = dyn-no-paired (dentry-is d) h

------------------------------------------------------------------------
-- Dynamic slots transport along futures
------------------------------------------------------------------------

record DynamicEntryLift {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ}
    (a : DynamicSemanticAtom (core W) Z) {mode′}
    (e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′)
    : Set where
  constructor dynamic-entry-lift
  field
    dlifted-atom :
      DynamicSemanticAtom (core W′) (liftCenterVariable W≼W′ Z)
    dlifted-entry-is : IsDynamicEntry dlifted-atom e′
    dlifted-precise-variable : dynamicPreciseVariable dlifted-atom
      ≡ liftPreciseVariable W≼W′ (dynamicPreciseVariable a)
    dlifted-rep : dynamicRep dlifted-atom
      ≡ liftPreciseTy W≼W′ (dynamicRep a)

open DynamicEntryLift public

dynamic-entry-lift-view : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ}
    (a : DynamicSemanticAtom (core W) Z) {mode′}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ (dynamic-entry a) e′
  → DynamicEntryLift W≼W′ a e′
dynamic-entry-lift-view W≼W′ a (lift-dynamic eqX eqR) =
  dynamic-entry-lift _ is-dynamic eqX eqR

view-entry-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {W≼W′ : Future W W′} {Z : TyVar Δᶜ}
    {a : DynamicSemanticAtom (core W) Z} {mode mode′}
    {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → IsDynamicEntry a e
  → EntryLift W≼W′ e e′
  → EntryLift W≼W′ (dynamic-entry a) e′
view-entry-lift is-dynamic l = l

dyn-slot-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : DynamicSlot W) (W≼W′ : Future W W′)
  → DynamicEntryLift W≼W′ (datom d)
      (semanticEntry W′ (liftCenterVariable W≼W′ (dcenter d)))
dyn-slot-lift d W≼W′ = dynamic-entry-lift-view W≼W′ (datom d)
  (view-entry-lift (dentry-is d) (entry-future W≼W′ (dcenter d)))

dyn-slot-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → DynamicSlot W → (W≼W′ : Future W W′) → DynamicSlot W′
dyn-slot-future d W≼W′ = dynamic-slot
  (liftCenterVariable W≼W′ (dcenter d))
  (dlifted-atom (dyn-slot-lift d W≼W′))
  (dlifted-entry-is (dyn-slot-lift d W≼W′))

dyn-slot-precise-variable-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : DynamicSlot W) (W≼W′ : Future W W′)
  → dslotXᴾ (dyn-slot-future d W≼W′)
      ≡ liftPreciseVariable W≼W′ (dslotXᴾ d)
dyn-slot-precise-variable-lift d W≼W′ =
  dlifted-precise-variable (dyn-slot-lift d W≼W′)

dyn-slot-precise-rep-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : DynamicSlot W) (W≼W′ : Future W W′)
  → dslotRᴾ (dyn-slot-future d W≼W′)
      ≡ liftPreciseTy W≼W′ (dslotRᴾ d)
dyn-slot-precise-rep-lift d W≼W′ =
  dlifted-rep (dyn-slot-lift d W≼W′)

dyn-replace-precise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : DynamicSlot W) (W≼W′ : Future W W′) (B : Ty Δᴾ)
  → replaceTy (dslotXᴾ (dyn-slot-future d W≼W′))
      (dslotRᴾ (dyn-slot-future d W≼W′)) (liftPreciseTy W≼W′ B)
    ≡ liftPreciseTy W≼W′ (replaceTy (dslotXᴾ d) (dslotRᴾ d) B)
dyn-replace-precise-lift d W≼W′ B =
  trans (cong₂ (λ X R → replaceTy X R (liftPreciseTy W≼W′ B))
    (dyn-slot-precise-variable-lift d W≼W′)
    (dyn-slot-precise-rep-lift d W≼W′))
    (sym (liftPreciseTy-replace W≼W′ (dslotXᴾ d) (dslotRᴾ d) B))

------------------------------------------------------------------------
-- Endpoint typings of a dynamic wrapper
------------------------------------------------------------------------

dyn-reveal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ) ≡ Cᴾ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → Value (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗)
  → TypedEndpoints W q Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗)
dyn-reveal-endpoints W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ
    {Vᴾ = Vᴾ} related vᴾ =
  typed-endpoints (impreciseType endpoints)
    (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
    (impreciseEmbedded endpoints) targetᴾ
    (imprecise-value endpoints) vᴾ (imprecise-typed endpoints)
    (⊢reveal (structural-reveal-typing Bᴾ (dynamicBound (datom d)))
      (precise-endpoint-type W sourceᴾ related))
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

dyn-conceal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ) ≡ Cᴾ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → Value (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
  → TypedEndpoints W p Vᴵ
      (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
dyn-conceal-endpoints W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ
    {Vᴾ = Vᴾ} related vᴾ =
  typed-endpoints (impreciseType endpoints) Bᴾ
    (impreciseEmbedded endpoints) sourceᴾ
    (imprecise-value endpoints) vᴾ (imprecise-typed endpoints)
    (⊢conceal (structural-conceal-typing Bᴾ (dynamicBound (datom d)))
      (precise-endpoint-type W targetᴾ related))
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

var-injective : ∀ {Δ} {X Y : TyVar Δ}
  → _≡_ {A = Ty Δ} (＇ X) (＇ Y) → X ≡ Y
var-injective refl = refl

conceal-value-inversion : ∀ {Δ} {U : Term Δ} {A B : Ty Δ}
    {c : Conv↓ Δ A B}
  → Value (U ↓ c) → Value U
conceal-value-inversion (vU ↓ _) = vU

replaceTy-hit : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ)
  → replaceTy X R (＇ X) ≡ R
replaceTy-hit X R with X ≟ X
replaceTy-hit X R | yes refl = refl
replaceTy-hit X R | no X≢X = ⊥-elim (X≢X refl)

replaceTy-miss : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ) (Y : TyVar Δ)
  → (X ≡ Y → ⊥)
  → replaceTy X R (＇ Y) ≡ ＇ Y
replaceTy-miss X R Y X≢Y with X ≟ Y
replaceTy-miss X R Y X≢Y | yes eq = ⊥-elim (X≢Y eq)
replaceTy-miss X R Y X≢Y | no _ = refl

-- No imprecise endpoint type embeds to the dynamic slot's center
-- variable.

dyn-no-imprecise-embed : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : DynamicSlot W) {B : Ty Δᴵ}
  → embedImprecise (core W) B ≡ ＇ (dcenter d)
  → ⊥
dyn-no-imprecise-embed d {B = ＇ Y} eq =
  dynamicNoTargetOccupant (datom d) (Y , var-injective eq)
dyn-no-imprecise-embed d {B = ‵ ι} ()
dyn-no-imprecise-embed d {B = ★} ()
dyn-no-imprecise-embed d {B = A ⇒ B} ()
dyn-no-imprecise-embed d {B = `∀ A} ()

-- Refute a source imprecision whose imprecise center is the slot's
-- variable, through the endpoints of any related pair.

dyn-refute-center-right : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : DynamicSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ dcenter d)
    {Aᴾ : Ty Δᶜ} {p : impEnv (core W) I.⊢ Aᴾ ⊑ ＇ Z}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ⊥
dyn-refute-center-right {W = W} d {Z = Z} Z-eq {p = p} related =
  dyn-no-imprecise-embed d
    (subst≡
      (λ X → embedImprecise (core W)
        (impreciseType
          (ClosureProof.value-imprecision-endpoints related)) ≡ ＇ X)
      Z-eq
      (impreciseEmbedded
        (ClosureProof.value-imprecision-endpoints related)))

-- The lifted dynamic reveal and conceal are the wrappers at the
-- lifted slot and type.

dyn-lifted-reveal-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : DynamicSlot W) (W≼W′ : Future W W′) (V : Term Δᴾ) (B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ B 〗)
      ≡ liftPreciseTerm W≼W′ V
          ↑ 〖 dslotXᴾ (dyn-slot-future d W≼W′)
              , dslotRᴾ (dyn-slot-future d W≼W′)
              ↑ liftPreciseTy W≼W′ B 〗
dyn-lifted-reveal-precise d W≼W′ V B =
  trans (liftPreciseTerm-reveal W≼W′ V (dslotXᴾ d) (dslotRᴾ d) B)
    (cong (apply↑ (liftPreciseTerm W≼W′ V))
      (cong₂ (λ X R → pack↑ 〖 X , R ↑ liftPreciseTy W≼W′ B 〗)
        (sym (dyn-slot-precise-variable-lift d W≼W′))
        (sym (dyn-slot-precise-rep-lift d W≼W′))))

dyn-lifted-conceal-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : DynamicSlot W) (W≼W′ : Future W W′) (V : Term Δᴾ) (B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) B)
      ≡ liftPreciseTerm W≼W′ V
          ↓ makeConceal (dslotXᴾ (dyn-slot-future d W≼W′))
              (dslotRᴾ (dyn-slot-future d W≼W′))
              (liftPreciseTy W≼W′ B)
dyn-lifted-conceal-precise d W≼W′ V B =
  trans (liftPreciseTerm-conceal W≼W′ V (dslotXᴾ d) (dslotRᴾ d) B)
    (cong (apply↓ (liftPreciseTerm W≼W′ V))
      (cong₂ (λ X R →
          pack↓ (makeConceal X R (liftPreciseTy W≼W′ B)))
        (sym (dyn-slot-precise-variable-lift d W≼W′))
        (sym (dyn-slot-precise-rep-lift d W≼W′))))

------------------------------------------------------------------------
-- The dynamic reveal and conceal
------------------------------------------------------------------------

-- Lexicographic recursion: the type size decreases at a function type,
-- and the index decreases when a dynamic tag is unfolded.

mutual
  dyn-reveal-go : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation q) j
        Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗)
  dyn-reveal-go fuel j sz below W d {Bᴾ = ＇ Y} p size sourceᴾ q
      targetᴾ related with dslotXᴾ d ≟ Y
  dyn-reveal-go fuel j sz below W d {Bᴾ = ＇ Y} p size
      sourceᴾ q targetᴾ related | no X≢Y =
    ClosureProof.computations-related-reindex p q
      (trans (sym sourceᴾ) targetᴾ) refl refl refl
      (identity-reveal W p (＇ Y) related)
  dyn-reveal-go fuel j sz below W d {Bᴾ = ＇ Y} I.X⊑X size sourceᴾ q
      targetᴾ related | yes refl =
    ⊥-elim (dyn-refute-center-right d
      (trans (sym (var-injective sourceᴾ))
        (dynamicPreciseAligned (datom d)))
      related)
  dyn-reveal-go fuel zero sz below W d {Bᴾ = ＇ Y} (I.X⊑★ eqm) size
      sourceᴾ q targetᴾ related | yes refl =
    ClosureProof.computations-related-zero
  dyn-reveal-go fuel (suc j′) sz below W d {Bᴾ = ＇ Y} (I.X⊑★ eqm)
      size sourceᴾ q targetᴾ (endpoints , inj₂ aligned) | yes refl =
    ⊥-elim (dyn-slot-refute-paired d
      (trans (sym (var-injective sourceᴾ))
        (dynamicPreciseAligned (datom d)))
      (aligned-atom-relation-holds aligned))
  dyn-reveal-go fuel (suc j′) sz below W d {Bᴾ = ＇ Y} (I.X⊑★ eqm)
      size sourceᴾ q targetᴾ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      (endpoints , inj₁ holds) | yes refl =
    ClosureProof.computations-related-reindex q q refl refl refl
      (sym (cong (_↑ unseal (dslotXᴾ d) (dslotRᴾ d)) shape-eq))
      stepped
    where
    dh : DynamicHolds (ValueImprecisionᵏ (suc j′) W) (datom d) Vᴵ Vᴾ
    dh = dyn-slot-consume d
      (trans (sym (var-injective sourceᴾ))
        (dynamicPreciseAligned (datom d)))
      eqm holds

    Uᴾ = dynamicSealed dh

    shape-eq : Vᴾ ≡ Uᴾ ↓ seal (dslotXᴾ d) (dslotRᴾ d)
    shape-eq = dynamic-sealed-shape dh

    payload-q : ValueImprecision W q (suc j′) Vᴵ Uᴾ
    payload-q = ClosureProof.value-imprecision-reindex
      q (dynamicRep-related (datom d)) (sym targetᴾ) refl
      (dynamic-payload-related dh)

    vUᴾ : Value Uᴾ
    vUᴾ = conceal-value-inversion
      (subst≡ Value shape-eq (precise-value endpoints))

    inner : ComputationsRelated W (FutureValueRelation q) (suc j′)
        Vᴵ Uᴾ
    inner = related-values-return (imprecise-value endpoints) vUᴾ
      (λ i i≤j → value-imprecision-downward-to i≤j payload-q)

    stepped : ComputationsRelated W (FutureValueRelation q) (suc j′)
        Vᴵ ((Uᴾ ↓ seal (dslotXᴾ d) (dslotRᴾ d))
          ↑ unseal (dslotXᴾ d) (dslotRᴾ d))
    stepped
        with unseal-step-question {Σ = preciseStore (core W)}
          (dslotXᴾ d) (dslotRᴾ d) vUᴾ
    stepped | vUᴾ′ , step-eq =
      related-precise-keep-step-expand (λ ())
        (unseal-value-none (dslotXᴾ d) (dslotRᴾ d) vUᴾ′)
        (pure-step (conceal-reveal vUᴾ′)) step-eq inner
  dyn-reveal-go fuel j sz below W d {Bᴾ = ‵ ι} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex p q
      (trans (sym sourceᴾ) targetᴾ) refl refl refl
      (identity-reveal W p (‵ ι) related)
  dyn-reveal-go fuel j sz below W d {Bᴾ = ★} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex p q
      (trans (sym sourceᴾ) targetᴾ) refl refl refl
      (identity-reveal W p ★ related)
  dyn-reveal-go zero j sz below W d {Bᴾ = A₀ ⇒ B₀} p () sourceᴾ q
      targetᴾ related
  dyn-reveal-go (suc fuel) j sz below W d {Bᴾ = A₀ ⇒ B₀} p size
      sourceᴾ q targetᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↑ fun)
      (λ i i≤j → dyn-reveal-arrow fuel i sz
        (below-restrict i≤j ≤-refl below) W d p
        (size-bound-left size) (size-bound-right size) sourceᴾ
        q targetᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related
  dyn-reveal-go fuel j sz below W d {Bᴾ = `∀ B₁} p size sourceᴾ q
      targetᴾ related =
    blocked-dyn-reveal-universal below W d p sourceᴾ q targetᴾ
      related

  dyn-conceal-go : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Vᴵ (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
  dyn-conceal-go fuel j sz below W d {Bᴾ = ＇ Y} p size sourceᴾ q
      targetᴾ related with dslotXᴾ d ≟ Y
  dyn-conceal-go fuel j sz below W d {Bᴾ = ＇ Y} p size sourceᴾ q
      targetᴾ related | no X≢Y =
    ClosureProof.computations-related-reindex q p
      (trans (sym targetᴾ) sourceᴾ) refl refl refl
      (identity-conceal W q (＇ Y) related)
  dyn-conceal-go fuel j sz below W d {Bᴾ = ＇ Y} I.X⊑X size sourceᴾ
      q targetᴾ related | yes refl =
    ⊥-elim (dyn-refute-center-right d
      (trans (sym (var-injective sourceᴾ))
        (dynamicPreciseAligned (datom d)))
      related)
  dyn-conceal-go fuel zero sz below W d {Bᴾ = ＇ Y} (I.X⊑★ eqm) size
      sourceᴾ q targetᴾ related | yes refl =
    ClosureProof.computations-related-zero
  dyn-conceal-go fuel (suc j′) sz below W d {Bᴾ = ＇ Y} (I.X⊑★ eqm)
      size sourceᴾ q targetᴾ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | yes refl =
    related-values-return (imprecise-value endpoints)
      (precise-value endpoints ↓ seal)
      at-every-index
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

    payload-rep : ValueImprecision W (dynamicRep-related (datom d))
        (suc j′) Vᴵ Vᴾ
    payload-rep = ClosureProof.value-imprecision-reindex
      (dynamicRep-related (datom d)) q targetᴾ refl related

    Z-eq : _ ≡ dcenter d
    Z-eq = trans (sym (var-injective sourceᴾ))
      (dynamicPreciseAligned (datom d))

    conceal-endpoints : TypedEndpoints W (I.X⊑★ eqm) Vᴵ
        (Vᴾ ↓ seal (dslotXᴾ d) (dslotRᴾ d))
    conceal-endpoints = typed-endpoints
      (impreciseType endpoints) (＇ dslotXᴾ d)
      (impreciseEmbedded endpoints) sourceᴾ
      (imprecise-value endpoints)
      (precise-value endpoints ↓ seal)
      (imprecise-typed endpoints)
      (⊢conceal (⊢↓-seal (dynamicBound (datom d)))
        (precise-endpoint-type W targetᴾ related))

    at-every-index : ∀ (i : ℕ) → i ≤ suc j′
      → FutureValueRelation (I.X⊑★ eqm) W future-refl i Vᴵ
          (Vᴾ ↓ seal (dslotXᴾ d) (dslotRᴾ d))
    at-every-index zero i≤j = conceal-endpoints
    at-every-index (suc i′) si≤j =
      conceal-endpoints ,
      inj₁ (dyn-slot-produce d Z-eq eqm
        (dynamic-holds Vᴾ refl
          (value-imprecision-downward-to si≤j payload-rep)))
  dyn-conceal-go fuel j sz below W d {Bᴾ = ‵ ι} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex q p
      (trans (sym targetᴾ) sourceᴾ) refl refl refl
      (identity-conceal W q (‵ ι) related)
  dyn-conceal-go fuel j sz below W d {Bᴾ = ★} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex q p
      (trans (sym targetᴾ) sourceᴾ) refl refl refl
      (identity-conceal W q ★ related)
  dyn-conceal-go zero j sz below W d {Bᴾ = A₀ ⇒ B₀} p () sourceᴾ q
      targetᴾ related
  dyn-conceal-go (suc fuel) j sz below W d {Bᴾ = A₀ ⇒ B₀} p size
      sourceᴾ q targetᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↓ fun)
      (λ i i≤j → dyn-conceal-arrow fuel i sz
        (below-restrict i≤j ≤-refl below) W d p
        (size-bound-left size) (size-bound-right size) sourceᴾ
        q targetᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related
  dyn-conceal-go fuel j sz below W d {Bᴾ = `∀ B₁} p size sourceᴾ q
      targetᴾ related =
    blocked-dyn-conceal-universal below W d p sourceᴾ q targetᴾ
      related

  -- Wrapping a related computation on the precise endpoint.

  dyn-revealed-computations : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation p) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation q) j
        Mᴵ (Mᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗)
  dyn-revealed-computations fuel j sz below W d {Bᴾ = Bᴾ} p size
      sourceᴾ q targetᴾ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    reveal-precise-composition
      {R = FutureValueRelation p} {S = FutureValueRelation q}
      (reveal-frm 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : RevealPrecisePlugValues W (FutureValueRelation p)
        (FutureValueRelation q) j
        (reveal-frm 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗)
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
        value-related =
      computations-related-future-compose W≼W′ q
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ q) (liftCenterImprecision W≼W′ q)
          refl refl refl
          (sym (transported-reveal-eq χsᴾ Mᴾ (dslotXᴾ d) (dslotRᴾ d) Bᴾ
            (trans (termsᴾ (Mᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ Bᴾ 〗))
              (trans (dyn-lifted-reveal-precise d W≼W′ Mᴾ Bᴾ)
                (cong (λ M → M ↑ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
          (dyn-reveal-go fuel i sz (below-restrict i≤j ≤-refl below)
            W′ (dyn-slot-future d W≼W′)
            (liftCenterImprecision W≼W′ p)
            (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ Bᴾ)) size)
            (trans (embedPrecise-lift W≼W′ Bᴾ)
              (cong (liftCenterTy W≼W′) sourceᴾ))
            (liftCenterImprecision W≼W′ q)
            (trans (cong (embedPrecise (core W′))
              (dyn-replace-precise-lift d W≼W′ Bᴾ))
              (trans (embedPrecise-lift W≼W′ _)
                (cong (liftCenterTy W≼W′) targetᴾ)))
            value-related))

  dyn-concealed-computations : ∀ (fuel j sz : ℕ)
      (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation q) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Mᴵ (Mᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ)
  dyn-concealed-computations fuel j sz below W d {Bᴾ = Bᴾ} p size
      sourceᴾ q targetᴾ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    conceal-precise-composition
      {R = FutureValueRelation q} {S = FutureValueRelation p}
      (conceal-frm (makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ)) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : ConcealPrecisePlugValues W (FutureValueRelation q)
        (FutureValueRelation p) j
        (conceal-frm (makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ))
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
        value-related =
      computations-related-future-compose W≼W′ p
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ p) (liftCenterImprecision W≼W′ p)
          refl refl refl
          (sym (transported-conceal-eq χsᴾ Mᴾ (dslotXᴾ d) (dslotRᴾ d)
            Bᴾ
            (trans
              (termsᴾ (Mᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) Bᴾ))
              (trans (dyn-lifted-conceal-precise d W≼W′ Mᴾ Bᴾ)
                (cong (λ M → M ↓ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
          (dyn-conceal-go fuel i sz (below-restrict i≤j ≤-refl below)
            W′ (dyn-slot-future d W≼W′)
            (liftCenterImprecision W≼W′ p)
            (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ Bᴾ)) size)
            (trans (embedPrecise-lift W≼W′ Bᴾ)
              (cong (liftCenterTy W≼W′) sourceᴾ))
            (liftCenterImprecision W≼W′ q)
            (trans (cong (embedPrecise (core W′))
              (dyn-replace-precise-lift d W≼W′ Bᴾ))
              (trans (embedPrecise-lift W≼W′ _)
                (cong (liftCenterTy W≼W′) targetᴾ)))
            value-related))

  -- One head of the wrapped function value: the precise endpoint
  -- redistributes the wrapper over the application.

  dyn-reveal-arrow-head : ∀ (fuel m sz : ℕ)
      (below : Below (suc m) sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {A₀ B₀ : Ty Δᴾ} {Pᴵ Qᴵ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ embedPrecise (core W) A₀ ⊑ Pᴵ)
      (p₂ : impEnv (core W) I.⊢ embedPrecise (core W) B₀ ⊑ Qᴵ)
      (q₁ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (dslotXᴾ d) (dslotRᴾ d) A₀) ⊑ Pᴵ)
      (q₂ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (dslotXᴾ d) (dslotRᴾ d) B₀) ⊑ Qᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
        {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecisionᵏ (suc m) W′ (liftCenterImprecision W≼W′ q₁)
        Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (liftImpreciseTerm W≼W′ Vᴵ · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ A₀ ⇒ B₀ 〗) · Uᴾ)
  dyn-reveal-arrow-head fuel m sz below W d {A₀ = A₀} {B₀ = B₀}
      p₁ p₂ q₁ q₂ sizeA sizeB {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ q₂) (liftCenterImprecision W≼W′ q₂)
      refl refl refl (sym precise-redex-eq) expanded
    where
    d′ = dyn-slot-future d W≼W′
    A′ = liftPreciseTy W≼W′ A₀
    B′ = liftPreciseTy W≼W′ B₀
    cᴾ = makeConceal (dslotXᴾ d′) (dslotRᴾ d′) A′
    dᴾ = 〖 dslotXᴾ d′ , dslotRᴾ d′ ↑ B′ 〗
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

    precise-redex-eq :
        liftPreciseTerm W≼W′
          (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ A₀ ⇒ B₀ 〗) · Uᴾ
        ≡ (Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ
    precise-redex-eq
        rewrite dyn-lifted-reveal-precise d W≼W′ Vᴾ (A₀ ⇒ B₀)
              | liftPreciseTy-arrow W≼W′ A₀ B₀ = refl

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
          (liftCenterImprecision W≼W′ p₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
        (liftCenterImprecision W≼W′ p₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p₁ p₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    concealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₁)) (suc m)
        Uᴵ (Uᴾ ↓ cᴾ)
    concealed = dyn-conceal-go fuel (suc m) sz below W′ d′
      (liftCenterImprecision W≼W′ p₁)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ A₀)) sizeA)
      (embedPrecise-lift W≼W′ A₀)
      (liftCenterImprecision W≼W′ q₁)
      (trans (cong (embedPrecise (core W′))
        (dyn-replace-precise-lift d W≼W′ A₀))
        (embedPrecise-lift W≼W′ _))
      argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (Vᴵ′ · Uᴵ) (Vᴾ′ · (Uᴾ ↓ cᴾ))
    applied = related-application-computation lifted-function concealed

    contracted : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ · (Uᴾ ↓ cᴾ)) ↑ dᴾ)
    contracted = dyn-revealed-computations fuel (suc m) sz below W′ d′
      (liftCenterImprecision W≼W′ p₂)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ B₀)) sizeB)
      (embedPrecise-lift W≼W′ B₀)
      (liftCenterImprecision W≼W′ q₂)
      (trans (cong (embedPrecise (core W′))
        (dyn-replace-precise-lift d W≼W′ B₀))
        (embedPrecise-lift W≼W′ _))
      applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ)
    expanded
        with reveal-fun-app-step-question
               {Σ = preciseStore (core W′)} cᴾ dᴾ
               (precise-value function-endpoints)
               (precise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
          (liftCenterImprecision W≼W′ p₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴾ , vUᴾ , step-eqᴾ =
      related-precise-keep-step-expand (λ ())
        (reveal-fun-app-value-none cᴾ dᴾ)
        (pure-step (β-reveal-⇒ vVᴾ vUᴾ)) step-eqᴾ contracted

  dyn-conceal-arrow-head : ∀ (fuel m sz : ℕ)
      (below : Below (suc m) sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {A₀ B₀ : Ty Δᴾ} {Pᴵ Qᴵ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ embedPrecise (core W) A₀ ⊑ Pᴵ)
      (p₂ : impEnv (core W) I.⊢ embedPrecise (core W) B₀ ⊑ Qᴵ)
      (q₁ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (dslotXᴾ d) (dslotRᴾ d) A₀) ⊑ Pᴵ)
      (q₂ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (dslotXᴾ d) (dslotRᴾ d) B₀) ⊑ Qᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
        {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecisionᵏ (suc m) W′ (liftCenterImprecision W≼W′ p₁)
        Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (liftImpreciseTerm W≼W′ Vᴵ · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀)) · Uᴾ)
  dyn-conceal-arrow-head fuel m sz below W d {A₀ = A₀} {B₀ = B₀}
      p₁ p₂ q₁ q₂ sizeA sizeB {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ p₂) (liftCenterImprecision W≼W′ p₂)
      refl refl refl (sym precise-redex-eq) expanded
    where
    d′ = dyn-slot-future d W≼W′
    A′ = liftPreciseTy W≼W′ A₀
    B′ = liftPreciseTy W≼W′ B₀
    cᴾ = 〖 dslotXᴾ d′ , dslotRᴾ d′ ↑ A′ 〗
    dᴾ = makeConceal (dslotXᴾ d′) (dslotRᴾ d′) B′
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

    precise-redex-eq :
        liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀)) · Uᴾ
        ≡ (Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ
    precise-redex-eq
        rewrite dyn-lifted-conceal-precise d W≼W′ Vᴾ (A₀ ⇒ B₀)
              | liftPreciseTy-arrow W≼W′ A₀ B₀ = refl

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
        (liftCenterImprecision W≼W′ q₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ q₁ q₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    revealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₁)) (suc m)
        Uᴵ (Uᴾ ↑ cᴾ)
    revealed = dyn-reveal-go fuel (suc m) sz below W′ d′
      (liftCenterImprecision W≼W′ p₁)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ A₀)) sizeA)
      (embedPrecise-lift W≼W′ A₀)
      (liftCenterImprecision W≼W′ q₁)
      (trans (cong (embedPrecise (core W′))
        (dyn-replace-precise-lift d W≼W′ A₀))
        (embedPrecise-lift W≼W′ _))
      argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) (Vᴾ′ · (Uᴾ ↑ cᴾ))
    applied = related-application-computation lifted-function revealed

    contracted : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ · (Uᴾ ↑ cᴾ)) ↓ dᴾ)
    contracted = dyn-concealed-computations fuel (suc m) sz below
      W′ d′
      (liftCenterImprecision W≼W′ p₂)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ B₀)) sizeB)
      (embedPrecise-lift W≼W′ B₀)
      (liftCenterImprecision W≼W′ q₂)
      (trans (cong (embedPrecise (core W′))
        (dyn-replace-precise-lift d W≼W′ B₀))
        (embedPrecise-lift W≼W′ _))
      applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ)
    expanded
        with conceal-fun-app-step-question
               {Σ = preciseStore (core W′)} cᴾ dᴾ
               (precise-value function-endpoints)
               (precise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴾ , vUᴾ , step-eqᴾ =
      related-precise-keep-step-expand (λ ())
        (conceal-fun-app-value-none cᴾ dᴾ)
        (pure-step (β-conceal-⇒ vVᴾ vUᴾ)) step-eqᴾ contracted

  -- The value relation of a wrapped function value.

  dyn-reveal-arrow : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {A₀ B₀ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → embedPrecise (core W) (A₀ ⇒ B₀) ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W)
        (replaceTy (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀)) ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ValueImprecision W q j
        Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
  dyn-reveal-arrow fuel zero sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related =
    dyn-reveal-endpoints W d p sourceᴾ q targetᴾ {k = zero} related
      (precise-value endpoints ↑ fun)
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {k = zero} related
  dyn-reveal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related with sourceᴾ
  dyn-reveal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related | refl with arrow-source-view p
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ with targetᴾ
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ | refl
      with arrow-imprecision-view q
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑⇒ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-arrow p₁ p₂ | refl
      | arrow-imprecision q₁ q₂ =
    dyn-reveal-endpoints W d (I.⇒⊑⇒ p₁ p₂) sourceᴾ (I.⇒⊑⇒ q₁ q₂)
      targetᴾ {k = suc i} related
      (precise-value endpoints ↑ fun) ,
    functions (suc i) ≤-refl related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      related

    functions : ∀ (m : ℕ) → m ≤ suc i
      → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) m Vᴵ Vᴾ
      → FunctionsRelated W q₁ q₂ m Vᴵ
          (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
    functions zero m≤ rel = tt
    functions (suc m) sm≤ rel =
      (λ W′ W≼W′ argument-related →
        dyn-reveal-arrow-head fuel m sz
          (below-restrict sm≤ ≤-refl below) W d p₁ p₂ q₁ q₂
          sizeA sizeB rel W′ W≼W′ argument-related) ,
      functions m (≤-trans (n≤1+n m) sm≤)
        (value-imprecision-downward-to
          {W = W} {p = I.⇒⊑⇒ p₁ p₂} {j = m} {k = suc m}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n m) rel)
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ with targetᴾ
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ | refl
      with arrow-source-view q
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      with right-imprecise-ground shape in g-eq
         | right-imprecise-ground-proof shape
         | right-payload-imprecision shape
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ＇ X | ()
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ‵ ι | ()
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ∀★ | ()
  dyn-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ★⇒★ | w =
    dyn-reveal-endpoints W d (I.⇒⊑★ p₁ p₂) sourceᴾ (I.⇒⊑★ q₁ q₂)
      targetᴾ {k = suc i}
      (endpoints , shape , payload-back)
      (precise-value endpoints ↑ fun) ,
    shape′ ,
    payload′
    where
    payload-back : ValueImprecision W
        (right-payload-imprecision shape) i
        (right-dynamic-imprecise-payload shape) Vᴾ
    payload-back = ClosureProof.value-imprecision-reindex
      (right-payload-imprecision shape) w refl
      (cong (embedImprecise (core W)) g-eq) payload

    new-imprecision : impEnv (core W) I.⊢
        embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) A₀)
        ⇒ embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) B₀)
        ⊑ embedImprecise (core W) (right-imprecise-ground shape)
    new-imprecision = subst≡
      (λ G → impEnv (core W) I.⊢
        embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) A₀)
        ⇒ embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) B₀)
        ⊑ embedImprecise (core W) G)
      (sym g-eq) (I.⇒⊑⇒ q₁ q₂)

    shape′ : RightDynamicPayloadShape W
        (embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) A₀)
        ⇒ embedPrecise (core W)
          (replaceTy (dslotXᴾ d) (dslotRᴾ d) B₀)) Vᴵ
    shape′ = right-dynamic-payload-shape
      (right-imprecise-ground shape)
      (right-imprecise-ground-proof shape)
      (right-imprecise-consistency-env shape)
      (right-imprecise-ground-to-star shape)
      (right-dynamic-imprecise-payload shape)
      (right-dynamic-imprecise-shape shape)
      new-imprecision

    recursive : ValueImprecision W (I.⇒⊑⇒ q₁ q₂) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
    recursive = dyn-reveal-arrow fuel i sz
      (below-restrict (n≤1+n i) ≤-refl below) W d w
      sizeA sizeB refl (I.⇒⊑⇒ q₁ q₂) refl payload

    payload′ : ValueImprecision W
        (right-payload-imprecision shape′) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
    payload′ = ClosureProof.value-imprecision-reindex
      new-imprecision (I.⇒⊑⇒ q₁ q₂) refl
      (cong (embedImprecise (core W)) g-eq) recursive

  dyn-conceal-arrow : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
      {A₀ B₀ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → embedPrecise (core W) (A₀ ⇒ B₀) ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W)
        (replaceTy (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀)) ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ValueImprecision W p j
        Vᴵ (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀))
  dyn-conceal-arrow fuel zero sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related =
    dyn-conceal-endpoints W d p sourceᴾ q targetᴾ {k = zero} related
      (precise-value endpoints ↓ fun)
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {k = zero} related
  dyn-conceal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related with sourceᴾ
  dyn-conceal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related | refl with arrow-source-view p
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ with targetᴾ
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ | refl
      with arrow-imprecision-view q
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑⇒ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-arrow p₁ p₂ | refl
      | arrow-imprecision q₁ q₂ =
    dyn-conceal-endpoints W d (I.⇒⊑⇒ p₁ p₂) sourceᴾ (I.⇒⊑⇒ q₁ q₂)
      targetᴾ {k = suc i} related
      (precise-value endpoints ↓ fun) ,
    functions (suc i) ≤-refl related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      related

    functions : ∀ (m : ℕ) → m ≤ suc i
      → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) m Vᴵ Vᴾ
      → FunctionsRelated W p₁ p₂ m Vᴵ
          (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀))
    functions zero m≤ rel = tt
    functions (suc m) sm≤ rel =
      (λ W′ W≼W′ argument-related →
        dyn-conceal-arrow-head fuel m sz
          (below-restrict sm≤ ≤-refl below) W d p₁ p₂ q₁ q₂
          sizeA sizeB rel W′ W≼W′ argument-related) ,
      functions m (≤-trans (n≤1+n m) sm≤)
        (value-imprecision-downward-to
          {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = m} {k = suc m}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n m) rel)
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ with targetᴾ
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ | refl
      with arrow-source-view q
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      with right-imprecise-ground shape in g-eq
         | right-imprecise-ground-proof shape
         | right-payload-imprecision shape
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ＇ X | ()
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ‵ ι | ()
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ∀★ | ()
  dyn-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ★⇒★ | w =
    dyn-conceal-endpoints W d (I.⇒⊑★ p₁ p₂) sourceᴾ (I.⇒⊑★ q₁ q₂)
      targetᴾ {k = suc i}
      (endpoints , shape , payload-back)
      (precise-value endpoints ↓ fun) ,
    shape′ ,
    payload′
    where
    payload-back : ValueImprecision W
        (right-payload-imprecision shape) i
        (right-dynamic-imprecise-payload shape) Vᴾ
    payload-back = ClosureProof.value-imprecision-reindex
      (right-payload-imprecision shape) w refl
      (cong (embedImprecise (core W)) g-eq) payload

    new-imprecision : impEnv (core W) I.⊢
        embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀
        ⊑ embedImprecise (core W) (right-imprecise-ground shape)
    new-imprecision = subst≡
      (λ G → impEnv (core W) I.⊢
        embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀
        ⊑ embedImprecise (core W) G)
      (sym g-eq) (I.⇒⊑⇒ p₁ p₂)

    shape′ : RightDynamicPayloadShape W
        (embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀) Vᴵ
    shape′ = right-dynamic-payload-shape
      (right-imprecise-ground shape)
      (right-imprecise-ground-proof shape)
      (right-imprecise-consistency-env shape)
      (right-imprecise-ground-to-star shape)
      (right-dynamic-imprecise-payload shape)
      (right-dynamic-imprecise-shape shape)
      new-imprecision

    recursive : ValueImprecision W (I.⇒⊑⇒ p₁ p₂) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀))
    recursive = dyn-conceal-arrow fuel i sz
      (below-restrict (n≤1+n i) ≤-refl below) W d
      (I.⇒⊑⇒ p₁ p₂)
      sizeA sizeB refl w refl payload

    payload′ : ValueImprecision W
        (right-payload-imprecision shape′) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (A₀ ⇒ B₀))
    payload′ = ClosureProof.value-imprecision-reindex
      new-imprecision (I.⇒⊑⇒ p₁ p₂) refl
      (cong (embedImprecise (core W)) g-eq) recursive

------------------------------------------------------------------------
-- The dynamic reveal and conceal, with the fuel instantiated
------------------------------------------------------------------------

dyn-reveal : ∀ {k sz : ℕ} → Below k sz → DynRevealAt k
dyn-reveal {k = k} below W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ related =
  dyn-reveal-go (sizeᵗ Bᴾ) k _ below W d p ≤-refl sourceᴾ q targetᴾ
    related

dyn-conceal : ∀ {k sz : ℕ} → Below k sz → DynConcealAt k
dyn-conceal {k = k} below W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ related =
  dyn-conceal-go (sizeᵗ Bᴾ) k _ below W d p ≤-refl sourceᴾ q targetᴾ
    related
