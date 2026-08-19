module proof.DGG.CtxImp where

-- File Charter:
--   * Defines the local world layer shared by cast-term imprecision and its
--     metatheory: endpoint embeddings, world builders, and world invariants.
--   * Defines world-indexed term-context imprecision and its lift/transport
--     operations.
--   * Defines canonical store representations, local rebasing, occupancy,
--     and wrapper-partner predicates used at cast boundaries.
--   * Exports no term-imprecision relation and depends only on the underlying
--     type, store, consistency, conversion, and cast-term syntax layers.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import TermCtx using (TermCtx)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _∼_; _↪ᵗ_; empty; keep; skip;
   toRenameᵗ; id; _!)
open import Conversion using (Conv↑; Conv↓; _⊢↑_; _⊢↓_)
open import Conversion using
  (unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_; `∀↓_; id↓;
   ⊢↑-∀; ⊢↑-id; PivotJoin; join-none; join-left; join-right; join-both;
   _⊢↑[_]_; ⊢↑-unsealˣ; ⊢↑-⇒ˣ; ⊢↑-∀ˣ; ⊢↑-∀-idˣ; ⊢↑-idˣ;
   _⊢↓[_]_; ⊢↓-sealˣ; ⊢↓-⇒ˣ; ⊢↓-∀ˣ; ⊢↓-∀-idˣ; ⊢↓-idˣ)
open import Imprecision
open import Primitives using (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms
  using
    (Term; Var; Value; Ctx; ⟨_,_,_⟩; _⊢_⦂_; `_ ; ƛ_; _·_; Λ_;
     _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame; ⇑ᵗᵐ;
     ⊢·; ⊢⟨⟩; ⊢•; ⊢reveal)

------------------------------------------------------------------------
-- Local worlds
------------------------------------------------------------------------

record World (Δᴸ Δᴿ Δ : TyCtx) : Set where
  constructor world
  field
    ηᴸʷ : Δᴸ ↪ᵗ Δ
    ηᴿʷ : Δᴿ ↪ᵗ Δ
    impEnvʷ : ImpEnv Δ
    sourceStoreʷ : TyStore Δᴸ
    targetStoreʷ : TyStore Δᴿ

open World public

embedᴸ : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Ty Δᴸ
  → Ty Δ
embedᴸ W = renameᵗ (toRenameᵗ (ηᴸʷ W))

embedᴿ : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → Ty Δ
embedᴿ W = renameᵗ (toRenameᵗ (ηᴿʷ W))

infix 4 _⊑ᵂ⟨_⟩_

_⊑ᵂ⟨_⟩_ : ∀ {Δᴸ Δᴿ Δ}
  → Ty Δᴸ
  → World Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → Set
A ⊑ᵂ⟨ W ⟩ B = impEnvʷ W ⊢ embedᴸ W A ⊑ embedᴿ W B

liftWorldBoth : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (Nat.suc Δᴸ) (Nat.suc Δᴿ) (Nat.suc Δ)
liftWorldBoth v W =
  world (keep (ηᴸʷ W)) (keep (ηᴿʷ W))
    (extendᵐ v (impEnvʷ W))
    (store-lift (sourceStoreʷ W))
    (store-lift (targetStoreʷ W))

-- A universal binder on the source side only: the target context, its
-- store, and its embedding stay fixed, so target terms and types cross
-- the binder unweakened.

liftWorldLeft : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (Nat.suc Δᴸ) Δᴿ (Nat.suc Δ)
liftWorldLeft v W =
  world (keep (ηᴸʷ W)) (skip (ηᴿʷ W))
    (extendᵐ v (impEnvʷ W))
    (store-lift (sourceStoreʷ W))
    (targetStoreʷ W)

leftOnlyWorld : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → Ty Δᴸ
  → World (Nat.suc Δᴸ) Δᴿ (Nat.suc Δ)
leftOnlyWorld v W A =
  world (keep (ηᴸʷ W)) (skip (ηᴿʷ W))
    (extendᵐ v (impEnvʷ W))
    (store-bind (sourceStoreʷ W) A)
    (targetStoreʷ W)

rightOnlyWorld : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ)
rightOnlyWorld W B =
  world (skip (ηᴸʷ W)) (keep (ηᴿʷ W))
    (instᵐ (impEnvʷ W))
    (sourceStoreʷ W)
    (store-bind (targetStoreʷ W) B)

bothBindWorld : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → Ty Δᴸ
  → Ty Δᴿ
  → World (Nat.suc Δᴸ) (Nat.suc Δᴿ) (Nat.suc Δ)
bothBindWorld v W A B =
  world (keep (ηᴸʷ W)) (keep (ηᴿʷ W))
    (extendᵐ v (impEnvʷ W))
    (store-bind (sourceStoreʷ W) A)
    (store-bind (targetStoreʷ W) B)

record SameRuntime {Δᴸ Δᴿ Δ}
    (W W′ : World Δᴸ Δᴿ Δ) : Set where
  constructor same-runtime
  field
    sourceStore-same : sourceStoreʷ W′ ≡ sourceStoreʷ W
    targetStore-same : targetStoreʷ W′ ≡ targetStoreʷ W

-- Imprecision marks may only decay toward the dynamic type as a rule
-- descends into its premise: every center the conclusion world marks
-- X⊑★ stays X⊑★ in the premise world, while precise marks may weaken
-- to X⊑★.  Equality is too strong: a rebase that displaces a target
-- variable leaves its old partner precise but unaligned, and the
-- stale mark blocks tag cancellation (see
-- proof.DGG.ExtraCastRight2Counterexample).  Each wrapper rule
-- carries this premise from its conclusion world to its premise
-- world; the rebase records no longer constrain the marks.

ImpEnvMono : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
  → Set
ImpEnvMono W W′ =
  ∀ Z → impEnvʷ W Z ≡ X⊑★ → impEnvʷ W′ Z ≡ X⊑★

-- A world is mark-honest when every source variable whose center is
-- marked precise has an aligned target variable.  This is the world
-- invariant that outlaws stale precise marks: the counterexample's
-- input world fails it at the displaced source variable, and the
-- repaired derivation dynamizes into a world that satisfies it.
-- There is no mirror condition for target variables because type
-- imprecision has no rule with a bare variable on the imprecise side.

WFWorld : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → Set
WFWorld {Δᴸ} {Δᴿ} W =
  ∀ (Xᴸ : TyVar Δᴸ)
  → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑X
  → Σ[ Xᴿ ∈ TyVar Δᴿ ]
      toRenameᵗ (ηᴿʷ W) Xᴿ ≡ toRenameᵗ (ηᴸʷ W) Xᴸ

------------------------------------------------------------------------
-- Term-context imprecision in local worlds
------------------------------------------------------------------------

record CtxImpEntry {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ) : Set where
  constructor ctx-imp
  field
    srcTyʷ : Ty Δᴸ
    tgtTyʷ : Ty Δᴿ
    impTyʷ : srcTyʷ ⊑ᵂ⟨ W ⟩ tgtTyʷ

open CtxImpEntry public

CtxImp : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → Set
CtxImp W = List (CtxImpEntry W)

srcCtxʷ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CtxImp W
  → TermCtx Δᴸ
srcCtxʷ = map srcTyʷ

tgtCtxʷ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CtxImp W
  → TermCtx Δᴿ
tgtCtxʷ = map tgtTyʷ

infix 4 _∋ʷ_⦂_

data _∋ʷ_⦂_ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} :
    CtxImp W → Var → CtxImpEntry W → Set where
  Zʷ : ∀ {γ A B p}
      ----------------------------------------------
    → (ctx-imp A B p ∷ γ) ∋ʷ Nat.zero ⦂ ctx-imp A B p

  Sʷ : ∀ {γ e e′ x}
    → γ ∋ʷ x ⦂ e
      -----------------------------
    → (e′ ∷ γ) ∋ʷ Nat.suc x ⦂ e

data SameCtx {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ Δ′} :
    CtxImp W → CtxImp W′ → Set where
  same-[] : SameCtx [] []

  same-∷ : ∀ {γ γ′ A B p p′}
    → SameCtx γ γ′
      ------------------------------------------------------
    → SameCtx (ctx-imp A B p ∷ γ) (ctx-imp A B p′ ∷ γ′)

data LiftCtx {Δᴸ Δᴿ Δ} (v : VarImp) {W : World Δᴸ Δᴿ Δ} :
    CtxImp W → CtxImp (liftWorldBoth v W) → Set where
  lift-[] : LiftCtx v [] []

  lift-∷ : ∀ {γ γ′ A B p p′}
    → LiftCtx v γ γ′
      -------------------------------------------------------------
    → LiftCtx v (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) (⇑ᵗ B) p′ ∷ γ′)

data LiftCtxᴸ {Δᴸ Δᴿ Δ} (v : VarImp) {W : World Δᴸ Δᴿ Δ} :
    CtxImp W → CtxImp (liftWorldLeft v W) → Set where
  liftᴸ-[] : LiftCtxᴸ v [] []

  liftᴸ-∷ : ∀ {γ γ′ A B p p′}
    → LiftCtxᴸ v γ γ′
      -------------------------------------------------------------
    → LiftCtxᴸ v (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) B p′ ∷ γ′)

-- Smart-comma left lifts are the guarded non-front source-only premise
-- worlds used by the M5 instantiation catch-up.  The alias case merges the
-- pending source binder with an existing target alias center; the fresh-behind
-- case keeps remaining source-only binders behind the generated target window.

data SmartLiftCtxᴸ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ} :
    CtxImp W → CtxImp Wᵐ → Set where
  smart-lift-[] : SmartLiftCtxᴸ [] []

  smart-lift-∷ : ∀ {γ γᵐ A B p pᵐ}
    → SmartLiftCtxᴸ γ γᵐ
      -------------------------------------------------------------
    → SmartLiftCtxᴸ (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) B pᵐ ∷ γᵐ)


record SmartFreshBehindGuard {Δᴸ Δᴿ Δ Δᵐ}
    (W : World Δᴸ Δᴿ Δ)
    (Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ) : Set where
  constructor smart-fresh-behind-guard
  field
    oldCenters : Δ ↪ᵗ Δᵐ
    sourceStore-lifted :
      sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)
    targetStore-same :
      targetStoreʷ Wᵐ ≡ targetStoreʷ W
    transport⊑ᵂ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ B
      → A ⊑ᵂ⟨ Wᵐ ⟩ B
    old-mark-mono : ∀ Z
      → impEnvʷ W Z ≡ X⊑★
      → impEnvʷ Wᵐ (toRenameᵗ oldCenters Z) ≡ X⊑★
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ
        ≡ toRenameᵗ oldCenters (toRenameᵗ (ηᴿʷ W) Xᴿ)
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ oldCenters (toRenameᵗ (ηᴸʷ W) Xᴸ)
    fresh-not-target : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ
        ≢ toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero
    fresh-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero) ≡ X⊑★
    target-mark-mono : ∀ Xᴿ
      → impEnvʷ W (toRenameᵗ (ηᴿʷ W) Xᴿ) ≡ X⊑★
      → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★


record SmartAliasMergeGuard {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ)
    (β α : Fin.Fin Δᴿ) : Set where
  constructor smart-alias-merge-guard
  field
    β:=＇α : targetStoreʷ W ∋ β ⦂ ＇ α
    α:=★ : targetStoreʷ W ∋ α ⦂ ★
    sourceStore-lifted :
      sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)
    targetStore-same :
      targetStoreʷ Wᵐ ≡ targetStoreʷ W
    transport⊑ᵂ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ B
      → A ⊑ᵂ⟨ Wᵐ ⟩ B
    old-mark-mono : ∀ Z
      → impEnvʷ W Z ≡ X⊑★
      → impEnvʷ Wᵐ Z ≡ X⊑★
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
    pending-at-alias :
      toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero ≡ toRenameᵗ (ηᴿʷ W) β
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ (ηᴸʷ W) Xᴸ
    no-old-source-at-alias : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ W) Xᴸ ≢ toRenameᵗ (ηᴿʷ W) β
    alias-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) β) ≡ X⊑★
    name-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) α) ≡ X⊑★
    target-mark-off-footprint : ∀ Xᴿ
      → Xᴿ ≢ β
      → Xᴿ ≢ α
      → impEnvʷ W (toRenameᵗ (ηᴿʷ W) Xᴿ) ≡ X⊑★
      → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★


data SmartCommaLiftᴸ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    ∀ {Δᵐ} → World (Nat.suc Δᴸ) Δᴿ Δᵐ → Set where
  smart-fresh-behind :
    ∀ {Δᵐ} {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    → SmartFreshBehindGuard W Wᵐ
    → SmartCommaLiftᴸ W Wᵐ

  smart-merge-alias :
    ∀ {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
    → SmartAliasMergeGuard W Wᵐ β α
    → SmartCommaLiftᴸ W Wᵐ

smartCommaLift-transport⊑ᵂ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → SmartCommaLiftᴸ W Wᵐ
  → ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ B
  → A ⊑ᵂ⟨ Wᵐ ⟩ B
smartCommaLift-transport⊑ᵂ (smart-fresh-behind guard) =
  SmartFreshBehindGuard.transport⊑ᵂ guard
smartCommaLift-transport⊑ᵂ (smart-merge-alias guard) =
  SmartAliasMergeGuard.transport⊑ᵂ guard

------------------------------------------------------------------------
-- Store representations and local rebasing
------------------------------------------------------------------------

-- A type variable's canonical store representation: follow the store's
-- representation chain until it ends at a non-variable type or at a
-- store-lift (universally bound) variable.  Chains terminate because a
-- store-bind entry mentions only strictly older variables, so both
-- functions recurse on the tail of the store.

resolveVar : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
resolveRep : ∀ {Δ} → TyStore Δ → Ty Δ → Ty Δ

resolveVar (store-lift Σ) Fin.zero = ＇ Fin.zero
resolveVar (store-lift Σ) (Fin.suc X) = ⇑ᵗ (resolveVar Σ X)
resolveVar (store-bind Σ A) Fin.zero = ⇑ᵗ (resolveRep Σ A)
resolveVar (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (resolveVar Σ X)

resolveRep Σ (＇ X) = resolveVar Σ X
resolveRep Σ (‵ ι) = ‵ ι
resolveRep Σ ★ = ★
resolveRep Σ (A ⇒ B) = A ⇒ B
resolveRep Σ (`∀ A) = `∀ A

record StoreRepImp {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor store-rep-imp
  field
    represented :
      resolveVar (sourceStoreʷ W) Xᴸ
        ⊑ᵂ⟨ W ⟩ resolveVar (targetStoreʷ W) Xᴿ

-- RebaseAt W W′ Xᴸ Xᴿ is an asymmetric source re-parking update.
-- Reduction only introduces one reveal or conceal wrapper per fresh
-- type variable, so descending through one wrapper may change the
-- source pivot's center.  The stores, the center context, and the
-- imprecision environment stay fixed; every old target variable's
-- center is frozen; the pivots are aligned in W′; and their canonical
-- store representations are related in W′.

record RebaseAt {Δᴸ Δᴿ Δ} (W W′ : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    sameRuntime : SameRuntime W W′
    ηᴸ-off-pivot : ∀ {Y} → Y ≢ Xᴸ
      → toRenameᵗ (ηᴸʷ W′) Y ≡ toRenameᵗ (ηᴸʷ W) Y
    ηᴿ-frozen : ∀ Y
      → toRenameᵗ (ηᴿʷ W′) Y ≡ toRenameᵗ (ηᴿʷ W) Y
    pivotAligned : toRenameᵗ (ηᴸʷ W′) Xᴸ ≡ toRenameᵗ (ηᴿʷ W′) Xᴿ
    storeRepresentations : StoreRepImp W′ Xᴸ Xᴿ

sameWorldRebaseAt : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
  → StoreRepImp W Xᴸ Xᴿ
    --------------------
  → RebaseAt W W Xᴸ Xᴿ
sameWorldRebaseAt aligned reps =
  rebase-at (same-runtime refl refl)
    (λ _ → refl) (λ _ → refl) aligned reps

-- One-sided wrappers carry an optional pivot: a conversion with no
-- pivot (an identity-shaped conversion) keeps the world fixed, and a
-- conversion pivoted on a variable may rebase exactly there.

data RebaseAtᴸ {Δᴸ Δᴿ Δ} : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Set where
  rebase-idᴸ : ∀ {W}
      ------------------------
    → RebaseAtᴸ W W nothing

  rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------
    → RebaseAtᴸ W W′ (just Xᴸ)

  -- A source pivot with no aligned target variable.  The target views
  -- the pivot's center as dynamic, so its canonical representation
  -- must sit below ★; there is no alignment to change, so the world
  -- stays fixed.  Type imprecision has no rule with a bare variable on
  -- the imprecise side, so RebaseAtᴿ needs no mirror constructor.
  -- The disalignment premise makes "no aligned target variable"
  -- explicit: no target variable embeds at the pivot's center, which
  -- lets inversion refute the X⊑X view of a concealed pivot.
  rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (ηᴿʷ W) Xᴿ ≢ toRenameᵗ (ηᴸʷ W) Xᴸ)
    → resolveVar (sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
      -------------------------
    → RebaseAtᴸ W W (just Xᴸ)

-- Source-side seal descent exposes just enough target-shape information
-- to preserve the seal-name/representation distinction.  A source seal
-- whose representation is literally ★ may descend against any target.
-- Otherwise the target must either be untagged at the top level or tagged
-- only after an aligned target-name seal.

data NotTopTag {Δ : TyCtx} : Term Δ → Set where
  not-` : ∀ x → NotTopTag (` x)
  not-ƛ : ∀ {M} → NotTopTag (ƛ M)
  not-· : ∀ {L M} → NotTopTag (L · M)
  not-Λ : ∀ {M} → NotTopTag (Λ M)
  not-⦂∀ : ∀ {M A B} → NotTopTag (M ⦂∀ A [ B ])
  not-$ : ∀ κ → NotTopTag ($ κ)
  not-⊕ : ∀ {L M} op → NotTopTag (L ⊕[ op ] M)
  not-↑ : ∀ {M A B} {c : Conv↑ Δ A B} → NotTopTag (M ↑ c)
  not-↓ : ∀ {M A B} {c : Conv↓ Δ A B} → NotTopTag (M ↓ c)
  not-blame : NotTopTag blame

CenterAligned : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned W X Y =
  toRenameᵗ (ηᴸʷ W) X ≡ toRenameᵗ (ηᴿʷ W) Y

Occupied : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δ
  → Set
Occupied {Δᴿ = Δᴿ} W Z =
  Σ[ Y ∈ TyVar Δᴿ ] toRenameᵗ (ηᴿʷ W) Y ≡ Z

NoTargetOccupant : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δ
  → Set
NoTargetOccupant W Z = Occupied W Z → ⊥

NoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → Set
NoTargetOccupantAtSource W X =
  NoTargetOccupant W (toRenameᵗ (ηᴸʷ W) X)

data Rep★PartnerOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged : ∀ {P Xᴿ? M′}
    → NotTopTag M′
      ------------------------------------
    → Rep★PartnerOK W X P Xᴿ? M′

  rep★-nonvar-tag : ∀ {P Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      ------------------------------------------------------------
    → Rep★PartnerOK W X P Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-var-tag : ∀ {P M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CenterAligned W X Y
      ------------------------------------------------------------
    → Rep★PartnerOK W X P (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

  rep★-matched-inner-tags : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → X₂ ≢ X
    → CenterAligned W X₂ Y₂
      ------------------------------------------------------------
    → Rep★PartnerOK W X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

  rep★-round-trip : ∀ {P Xᴿ? M′ A μ}
      {X∼★ : μ ⊢ (＇ X) ∼★}
      {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
    → Rep★PartnerOK W X P Xᴿ? M′
      ------------------------------------------------------------
    → Rep★PartnerOK W X
        ((P ↓ seal X ★)
          ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
              ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        Xᴿ? M′

-- Source-only `seal X ★` is guarded directly by
-- `NoTargetOccupantAtSource` in the term relation.  This classifier covers
-- only non-`★` source seals and non-seal source-conceal cases.

data SourceConcealOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-nonstar-plain-ok : ∀ {P X R Xᴿ? M′}
    → NonStar R
    → NotTopTag M′
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) Xᴿ? M′

  seal-nonstar-name-protected-ok : ∀ {P X R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
    → NonStar R
    → CenterAligned W X Y
      ----------------------------------------------------
    → SourceConcealOK W P (seal X R) (just Y)
        ((M ↓ seal Y S) ⟨ c ⟩)

  fun-conceal-ok : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealOK W P (c ↦↓ d) Xᴿ? M′

  all-conceal-ok : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealOK W P (`∀↓ c) Xᴿ? M′

  id-conceal-ok : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealOK W P (id↓ A) Xᴿ? M′

data MatchedConcealPartnerOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  matched-seal-star-partner : ∀ {P X Xᴿ? M′}
    → Rep★PartnerOK W X P Xᴿ? M′
      ----------------------------------------------------
    → MatchedConcealPartnerOK W P (seal X ★) Xᴿ? M′

  matched-seal-nonstar : ∀ {P X R Xᴿ? M′}
    → NonStar R
      ----------------------------------------------------
    → MatchedConcealPartnerOK W P (seal X R) Xᴿ? M′

  matched-fun-conceal-target : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK W P (c ↦↓ d) Xᴿ? M′

  matched-all-conceal-target : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → MatchedConcealPartnerOK W P (`∀↓ c) Xᴿ? M′

  matched-id-conceal-target : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK W P (id↓ A) Xᴿ? M′

data TagRebaseAtᴸ {Δᴸ Δᴿ Δ}
    : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Maybe (TyVar Δᴿ) → Set where
  tag-rebase-idᴸ : ∀ {W}
      ----------------------------------
    → TagRebaseAtᴸ W W nothing nothing

  tag-rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------------------
    → TagRebaseAtᴸ W W′ (just Xᴸ) (just Xᴿ)

  tag-rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (ηᴿʷ W) Xᴿ
            ≢ toRenameᵗ (ηᴸʷ W) Xᴸ)
    → resolveVar (sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
      -------------------------------------------------
    → TagRebaseAtᴸ W W (just Xᴸ) nothing

forgetTagRebaseᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
    --------------------------
  → RebaseAtᴸ W W′ Xᴸ?
forgetTagRebaseᴸ tag-rebase-idᴸ = rebase-idᴸ
forgetTagRebaseᴸ (tag-rebase-varᴸ rb) = rebase-varᴸ rb
forgetTagRebaseᴸ (tag-rebase-onlyᴸ to-star disaligned represented) =
  rebase-onlyᴸ to-star disaligned represented

data RebaseAtᴿ {Δᴸ Δᴿ Δ} : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴿ) → Set where
  rebase-idᴿ : ∀ {W}
      ------------------------
    → RebaseAtᴿ W W nothing

  rebase-varᴿ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------
    → RebaseAtᴿ W W′ (just Xᴿ)
