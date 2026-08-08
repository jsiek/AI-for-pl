module proof.DGG.CastTermImprecision2 where

-- File Charter:
--   * Experiments with the Issue 117 redesign of cast-term imprecision.
--   * Keeps type imprecision single-context, but makes each term-imprecision
--     premise carry its current local source/target embeddings into that
--     center context.
--   * Represents local rebasing explicitly, letting reveal/conceal wrappers
--     descend with a different alignment.
--   * Rebasing is asymmetric: a RebaseAt keeps the runtime stores and
--     the center context fixed, may move only the source pivot, and
--     freezes every old target variable's center.  Imprecision marks are
--     not pinned by the rebase; instead every wrapper rule carries
--     ImpEnvMono, letting marks decay toward X⊑★ from conclusion to
--     premise, and WFWorld names the worlds whose precise marks are
--     honestly aligned.
--   * Store representations are canonical: a pivot variable is compared
--     through resolveVar, which follows the store's representation chain
--     to its end instead of stopping at an arbitrary intermediate type.
--   * Conversion typing is indexed by an optional pivot.  A conversion
--     built only from identity leaves has no pivot and its wrapper rule
--     keeps the world fixed; only a conversion that seals or unseals an
--     actual variable can rebase, and only at that variable.
--   * Source-only structure needs no target counterpart: Λ⊑² lifts the
--     world on the left only and compares the target term unweakened,
--     and a rebase-onlyᴸ pivot handles a source variable with no
--     aligned target variable, justified by the target seeing ★ there.
--     There is no right-only mirror because type imprecision has no
--     rule with a bare variable on the imprecise side.
--   * Records the Example 12 alignments Xᴸ≅Xᴿ, Xᴸ≅Zᴿ, and Xᴸ≅Yᴿ as first-class
--     store-representation witnesses.
--   * Records a left-hand analogue of Example 12 where the source store, not
--     the target store, has the representation path to ★.
--   * Records a variant where the target store has a representation path to
--     ℕ, showing that representation paths are not only a ★ phenomenon.
--   * The more rules in this relation, the more cases to prove in the DGG.
--     So don't add rules unless they are absolutely necessary!
--     Avoid rules that are not syntax directed.

open import Data.Empty using (⊥-elim)
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
  (Env∼; _⊢_∼_; _∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; id; _!)
open import Conversion using (Conv↑; Conv↓; _⊢↑_; _⊢↓_)
open import Conversion using
  (unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_; `∀↓_; id↓;
   ⊢↑-∀; ⊢↑-id)
open import Imprecision
open import Primitives using (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms
  using
    (Term; Var; Value; Ctx; ⟨_,_,_⟩; _⊢_⦂_; `_ ; ƛ_; _·_; Λ_;
     _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame; ⇑ᵗᵐ;
     ⊢·; ⊢⟨⟩; ⊢•; ⊢reveal)
import proof.DGG.Examples as Ex

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

data SealPartnerOK {Δᴸ Δᴿ : TyCtx} :
    Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-target : ∀ {Xᴿ? M′}
      ------------------------------------
    → SealPartnerOK ★ Xᴿ? M′

  plain-target : ∀ {R Xᴿ? M′}
    → NotTopTag M′
      ------------------------------------
    → SealPartnerOK R Xᴿ? M′

  name-protected-target : ∀ {R X S M μ}
      {c : μ ⊢ (＇ X) ∼ ★}
      ----------------------------------------------------
    → SealPartnerOK R (just X) ((M ↓ seal X S) ⟨ c ⟩)

data SourceConcealPartnerOK {Δᴸ Δᴿ : TyCtx} :
    {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-ok : ∀ {X R Xᴿ? M′}
    → SealPartnerOK R Xᴿ? M′
      ----------------------------------------------------
    → SourceConcealPartnerOK (seal X R) Xᴿ? M′

  fun-conceal-target : ∀ {A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealPartnerOK (c ↦↓ d) Xᴿ? M′

  all-conceal-target : ∀ {A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealPartnerOK (`∀↓ c) Xᴿ? M′

  id-conceal-target : ∀ {A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealPartnerOK (id↓ A) Xᴿ? M′

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

------------------------------------------------------------------------
-- Conversion typing indexed by an optional converted variable
------------------------------------------------------------------------

-- The pivot of a composite conversion is the join of the pivots of its
-- halves: an identity half contributes nothing, and two variable halves
-- must agree.  An all-identity conversion therefore has pivot nothing
-- and cannot be retyped at an arbitrary variable.

data PivotJoin {Δ : TyCtx} :
    Maybe (TyVar Δ) → Maybe (TyVar Δ) → Maybe (TyVar Δ) → Set where
  join-none :
      ----------------------------------
      PivotJoin nothing nothing nothing

  join-left : ∀ {X}
      ------------------------------------
    → PivotJoin (just X) nothing (just X)

  join-right : ∀ {X}
      ------------------------------------
    → PivotJoin nothing (just X) (just X)

  join-both : ∀ {X}
      -------------------------------------
    → PivotJoin (just X) (just X) (just X)

infix 4 _⊢↑[_]_ _⊢↓[_]_

mutual
  data _⊢↑[_]_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Maybe (TyVar Δ) → ∀ {A B} → Conv↑ Δ A B → Set where
    ⊢↑-unsealˣ : ∀ {X R}
      → Σ ∋ X ⦂ R
        ----------------------------
      → Σ ⊢↑[ just X ] unseal X R

    ⊢↑-⇒ˣ : ∀ {p q r A A′ B B′}
        {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
      → PivotJoin p q r
      → Σ ⊢↓[ p ] c
      → Σ ⊢↑[ q ] d
        -----------------
      → Σ ⊢↑[ r ] c ↦↑ d

    ⊢↑-∀ˣ : ∀ {X A B} {c : Conv↑ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↑[ just (Fin.suc X) ] c
        -------------------------
      → Σ ⊢↑[ just X ] `∀↑ c

    ⊢↑-∀-idˣ : ∀ {A B} {c : Conv↑ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↑[ nothing ] c
        -------------------------
      → Σ ⊢↑[ nothing ] `∀↑ c

    ⊢↑-idˣ : ∀ {A}
        -----------------------
      → Σ ⊢↑[ nothing ] id↑ A

  data _⊢↓[_]_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Maybe (TyVar Δ) → ∀ {A B} → Conv↓ Δ A B → Set where
    ⊢↓-sealˣ : ∀ {X R}
      → Σ ∋ X ⦂ R
        --------------------------
      → Σ ⊢↓[ just X ] seal X R

    ⊢↓-⇒ˣ : ∀ {p q r A A′ B B′}
        {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
      → PivotJoin p q r
      → Σ ⊢↑[ p ] c
      → Σ ⊢↓[ q ] d
        -----------------
      → Σ ⊢↓[ r ] c ↦↓ d

    ⊢↓-∀ˣ : ∀ {X A B} {c : Conv↓ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↓[ just (Fin.suc X) ] c
        -------------------------
      → Σ ⊢↓[ just X ] `∀↓ c

    ⊢↓-∀-idˣ : ∀ {A B} {c : Conv↓ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↓[ nothing ] c
        -------------------------
      → Σ ⊢↓[ nothing ] `∀↓ c

    ⊢↓-idˣ : ∀ {A}
        -----------------------
      → Σ ⊢↓[ nothing ] id↓ A

------------------------------------------------------------------------
-- Typed cast-term imprecision with recursive worlds
------------------------------------------------------------------------

infix 4 _∣_⊢²_⊑_∶_

data _∣_⊢²_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B → Set where

  x⊑x² : ∀ {x A B p}
    → γ ∋ʷ x ⦂ ctx-imp A B p
      --------------------------------
    → W ∣ γ ⊢² ` x ⊑ ` x ∶ p

  ƛ⊑ƛ² : ∀ {M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′}
      {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢² M ⊑ M′ ∶ pB
      ---------------------------------------------------
    → W ∣ γ ⊢² ƛ M ⊑ ƛ M′ ∶ ⇒⊑⇒ pA pB

  ·⊑·² : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′}
      {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢² M ⊑ M′ ∶ pA
      ------------------------------------------------
    → W ∣ γ ⊢² L · M ⊑ L′ · M′ ∶ pB

  Λ⊑Λ² : ∀ {γ′ V V′ A B}
      {p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B}
    → LiftCtx X⊑X γ γ′
    → Value V
    → Value V′
    → liftWorldBoth X⊑X W ∣ γ′ ⊢² V ⊑ V′ ∶ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ B)
      -------------------------------------------------
    → W ∣ γ ⊢² Λ V ⊑ Λ V′ ∶ q

  -- The NonVar and occurrence premises mirror the ∀⊑ type rule; the
  -- extra-cast-right inversion needs them to refute the ∀⊑∀ and
  -- bot-elim views of q.
  Λ⊑² : ∀ {γ′ V M A B}
      {p : A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → LiftCtxᴸ X⊑★ γ γ′
    → Value V
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ B
    → liftWorldLeft X⊑★ W ∣ γ′ ⊢² V ⊑ M ∶ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
      -------------------------------------------
    → W ∣ γ ⊢² Λ V ⊑ M ∶ q

  •⊑•² : ∀ {M M′ C C′ A A′}
    → (p∀ : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → (r : (C [ A ]ᵗ) ⊑ᵂ⟨ W ⟩ (C′ [ A′ ]ᵗ))
      --------------------------------------------------
    → W ∣ γ ⊢² M ⦂∀ C [ A ] ⊑ M′ ⦂∀ C′ [ A′ ] ∶ r

  •⊑² : ∀ {M M′ C A B}
    → (p∀ : `∀ C ⊑ᵂ⟨ W ⟩ B)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵂ⟨ W ⟩ ★)
    → (r : (C [ A ]ᵗ) ⊑ᵂ⟨ W ⟩ B)
      ----------------------------------------
    → W ∣ γ ⊢² M ⦂∀ C [ A ] ⊑ M′ ∶ r

  κ⊑κ² : ∀ (κ : Const)
    → (p : constTy κ ⊑ᵂ⟨ W ⟩ constTy κ)
      ----------------------------------------------------
    → W ∣ γ ⊢² $ κ ⊑ $ κ ∶ p

  cast⊑cast² : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵂ⟨ W ⟩ C′} {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    → (c : ν ⊢ C ∼ A)
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      -------------------------------------
    → W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑cast² : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴿ}
    → (c′ : ν ⊢ B ∼ B′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑reveal² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↑ Δᴿ B B′}
    → ImpEnvMono W W′
    → RebaseAtᴿ W W′ Xᴿ?
    → SameCtx γ γ′
    → targetStoreʷ W ⊢↑[ Xᴿ? ] c′
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↓ Δᴿ B B′}
    → ImpEnvMono W W′
    → RebaseAtᴿ W′ W Xᴿ?
    → SameCtx γ γ′
    → targetStoreʷ W ⊢↓[ Xᴿ? ] c′
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ↓ c′ ∶ q

  cast⊑² : ∀ {M M′ A A′ B}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴸ}
    → (c : ν ⊢ A ∼ A′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ q

  reveal⊑² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↑ Δᴸ A A′}
    → ImpEnvMono W W′
    → RebaseAtᴸ W W′ Xᴸ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↑[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↑ c ⊑ M′ ∶ q

  conceal⊑² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealPartnerOK c Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q

  reveal⊑reveal² : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
    → ImpEnvMono W Wᵖ
    → RebaseAt W Wᵖ Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → sourceStoreʷ W ⊢↑[ just Xᴸ ] c
    → targetStoreʷ W ⊢↑[ just Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑conceal² : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    → ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → sourceStoreʷ W ⊢↓[ just Xᴸ ] c
    → targetStoreʷ W ⊢↓[ just Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q

  -- Source blame is below any well-typed target term.  The left side
  -- is the more static one (A ⊑ ★ for any closed type A, with ★ on
  -- the right): once the more static side has blamed, imprecision
  -- places no constraint on the more dynamic side.
  blame⊑² : ∀ {M′ A B}
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M′ ⦂ B
    → (p : A ⊑ᵂ⟨ W ⟩ B)
      ------------------------------
    → W ∣ γ ⊢² blame ⊑ M′ ∶ p

  ⊕⊑⊕² : (op : Prim)
    → ∀ {L L′ M M′}
      {p q : primArgTy op ⊑ᵂ⟨ W ⟩ primArgTy op}
    → W ∣ γ ⊢² L ⊑ L′ ∶ p
    → W ∣ γ ⊢² M ⊑ M′ ∶ q
    → (r : primResultTy op ⊑ᵂ⟨ W ⟩ primResultTy op)
      ------------------------------------------------
    → W ∣ γ ⊢² L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ r

------------------------------------------------------------------------
-- Example 12 local alignments
------------------------------------------------------------------------

example12-source-store : TyStore 1
example12-source-store = store-bind store-empty (‵ `ℕ)

example12-target-store : TyStore 3
example12-target-store =
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) (‵ `ℕ)

example12-imp-env : ImpEnv 3
example12-imp-env Fin.zero = X⊑★
example12-imp-env (Fin.suc Fin.zero) = X⊑★
example12-imp-env (Fin.suc (Fin.suc Fin.zero)) = X⊑★

example12-ηᴿ : 3 ↪ᵗ 3
example12-ηᴿ = keep (keep (keep empty))

example12-ηᴸ-X : 1 ↪ᵗ 3
example12-ηᴸ-X = keep (skip (skip empty))

example12-ηᴸ-Y : 1 ↪ᵗ 3
example12-ηᴸ-Y = skip (keep empty)

example12-ηᴸ-Z : 1 ↪ᵗ 3
example12-ηᴸ-Z = skip (skip (keep empty))

example12-ηᴸ-X-maps : toRenameᵗ example12-ηᴸ-X Fin.zero ≡ Fin.zero
example12-ηᴸ-X-maps = refl

example12-ηᴸ-Y-maps :
  toRenameᵗ example12-ηᴸ-Y Fin.zero ≡ Fin.suc Fin.zero
example12-ηᴸ-Y-maps = refl

example12-ηᴸ-Z-maps :
  toRenameᵗ example12-ηᴸ-Z Fin.zero ≡ Fin.suc (Fin.suc Fin.zero)
example12-ηᴸ-Z-maps = refl

example12-world-X : World 1 3 3
example12-world-X =
  world example12-ηᴸ-X example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store

example12-world-Y : World 1 3 3
example12-world-Y =
  world example12-ηᴸ-Y example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store

example12-world-Z : World 1 3 3
example12-world-Z =
  world example12-ηᴸ-Z example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store

example12-source-X∋ :
  example12-source-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-source-X∋ = Z∋ refl

example12-target-X∋ :
  example12-target-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-target-X∋ = Z∋ refl

example12-target-Y∋ :
  example12-target-store ∋ Fin.suc Fin.zero
    ⦂ ＇ (Fin.suc (Fin.suc Fin.zero))
example12-target-Y∋ = S-bind∋ (Z∋ refl) refl

example12-target-Z∋ :
  example12-target-store ∋ Fin.suc (Fin.suc Fin.zero) ⦂ ★
example12-target-Z∋ = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

example12-X-representation : StoreRepImp example12-world-X Fin.zero Fin.zero
example12-X-representation = store-rep-imp ι⊑ι

example12-Z-representation :
  StoreRepImp example12-world-Z Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-Z-representation = store-rep-imp ι⊑★

example12-Y-representation :
  StoreRepImp example12-world-Y Fin.zero (Fin.suc Fin.zero)
example12-Y-representation = store-rep-imp ι⊑★

example12-rebase-X-to-Z :
  RebaseAt example12-world-X example12-world-Z
    Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-rebase-X-to-Z =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) }) (λ _ → refl)
    refl example12-Z-representation

example12-rebase-X-to-Y :
  RebaseAt example12-world-X example12-world-Y Fin.zero (Fin.suc Fin.zero)
example12-rebase-X-to-Y =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) }) (λ _ → refl)
    refl example12-Y-representation

example12-outer-function :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ example12-world-X ⟩ (＇ Fin.zero ⇒ ＇ Fin.zero)
example12-outer-function = ⇒⊑⇒ X⊑X X⊑X

example12-Z-function :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ example12-world-Z ⟩
      (＇ (Fin.suc (Fin.suc Fin.zero))
        ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
example12-Z-function = ⇒⊑⇒ X⊑X X⊑X

example12-Y-function :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ example12-world-Y ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
example12-Y-function = ⇒⊑⇒ X⊑X X⊑X

example12-Z-function-to-star :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ example12-world-Z ⟩ (★ ⇒ ★)
example12-Z-function-to-star = ⇒⊑⇒ (X⊑★ refl) (X⊑★ refl)

example12-Y-function-to-star :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ example12-world-Y ⟩ (★ ⇒ ★)
example12-Y-function-to-star = ⇒⊑⇒ (X⊑★ refl) (X⊑★ refl)

------------------------------------------------------------------------
-- β-reveal-∀ followed by β-Λ: a path to ℕ, not ★
------------------------------------------------------------------------

-- The target wraps the polymorphic identity in an explicit universal reveal.
-- When applied at ℕ, β-reveal-∀ first allocates X ↦ ℕ.  The β-Λ exposed under
-- that reveal then instantiates at the fresh X and allocates Y ↦ X.  Comparing
-- the source's ordinary X ↦ ℕ cell against target Y therefore needs the
-- representation path Y ↦ X ↦ ℕ, not a path to ★.

example12-nat-chain-source : Term 0
example12-nat-chain-source = Ex.example12-left

example12-nat-chain-source-⊢ :
  Ex.∅ ⊢ example12-nat-chain-source ⦂ Ex.ℕᵗ
example12-nat-chain-source-⊢ = Ex.example12-left-⊢

example12-nat-chain-reveal :
  Conv↑ 0 (`∀ Ex.X⇒X) (`∀ Ex.X⇒X)
example12-nat-chain-reveal = `∀↑ (id↑ Ex.X⇒X)

example12-nat-chain-reveal-⊢ :
  store-empty ⊢↑ example12-nat-chain-reveal
example12-nat-chain-reveal-⊢ = ⊢↑-∀ ⊢↑-id

example12-nat-chain-reveal-⊢ˣ :
  store-empty ⊢↑[ nothing ] example12-nat-chain-reveal
example12-nat-chain-reveal-⊢ˣ = ⊢↑-∀-idˣ ⊢↑-idˣ

example12-nat-chain-target : Term 0
example12-nat-chain-target =
  ((Ex.polyId ↑ example12-nat-chain-reveal)
    ⦂∀ Ex.X⇒X [ Ex.ℕᵗ ]) · Ex.c

example12-nat-chain-target-⊢ :
  Ex.∅ ⊢ example12-nat-chain-target ⦂ Ex.ℕᵗ
example12-nat-chain-target-⊢ =
  ⊢· (⊢• (⊢reveal example12-nat-chain-reveal-⊢ Ex.polyId-⊢))
    Ex.c-⊢

example12-nat-chain-source-store : TyStore 1
example12-nat-chain-source-store = store-bind store-empty (‵ `ℕ)

example12-nat-chain-target-store : TyStore 2
example12-nat-chain-target-store =
  store-bind (store-bind store-empty (‵ `ℕ)) (＇ Fin.zero)

example12-nat-chain-imp-env : ImpEnv 2
example12-nat-chain-imp-env Fin.zero = X⊑X
example12-nat-chain-imp-env (Fin.suc Fin.zero) = X⊑X

example12-nat-chain-ηᴿ : 2 ↪ᵗ 2
example12-nat-chain-ηᴿ = keep (keep empty)

example12-nat-chain-ηᴸ-X : 1 ↪ᵗ 2
example12-nat-chain-ηᴸ-X = skip (keep empty)

example12-nat-chain-ηᴸ-Y : 1 ↪ᵗ 2
example12-nat-chain-ηᴸ-Y = keep empty

example12-nat-chain-world-X : World 1 2 2
example12-nat-chain-world-X =
  world example12-nat-chain-ηᴸ-X example12-nat-chain-ηᴿ
    example12-nat-chain-imp-env
    example12-nat-chain-source-store
    example12-nat-chain-target-store

example12-nat-chain-world-Y : World 1 2 2
example12-nat-chain-world-Y =
  world example12-nat-chain-ηᴸ-Y example12-nat-chain-ηᴿ
    example12-nat-chain-imp-env
    example12-nat-chain-source-store
    example12-nat-chain-target-store

example12-nat-chain-source-X∋ :
  example12-nat-chain-source-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-nat-chain-source-X∋ = Z∋ refl

example12-nat-chain-target-Y∋ :
  example12-nat-chain-target-store ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
example12-nat-chain-target-Y∋ = Z∋ refl

example12-nat-chain-target-X∋ :
  example12-nat-chain-target-store ∋ Fin.suc Fin.zero ⦂ ‵ `ℕ
example12-nat-chain-target-X∋ = S-bind∋ (Z∋ refl) refl

example12-nat-chain-X-representation :
  StoreRepImp example12-nat-chain-world-X Fin.zero (Fin.suc Fin.zero)
example12-nat-chain-X-representation = store-rep-imp ι⊑ι

example12-nat-chain-Y-representation :
  StoreRepImp example12-nat-chain-world-Y Fin.zero Fin.zero
example12-nat-chain-Y-representation = store-rep-imp ι⊑ι

example12-nat-chain-rebase-X-to-Y :
  RebaseAt example12-nat-chain-world-X example12-nat-chain-world-Y
    Fin.zero Fin.zero
example12-nat-chain-rebase-X-to-Y =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) }) (λ _ → refl)
    refl example12-nat-chain-Y-representation

------------------------------------------------------------------------
-- Example 12 variant with the representation path on the left
------------------------------------------------------------------------

-- The source is Example 12's up/down detour.  The target stops after the
-- upcast to ★ ⇒ ★ and casts the argument to ★, so the pair still has the
-- source on the more precise side: ℕ ⊑ ★.

example12-left-path-source : Term 0
example12-left-path-source = Ex.example12-right

example12-left-path-source-⊢ :
  Ex.∅ ⊢ example12-left-path-source ⦂ Ex.ℕᵗ
example12-left-path-source-⊢ = Ex.example12-right-⊢

example12-ℕ! : Ex.ℕᵗ ∼ ★
example12-ℕ! = id (‵ `ℕ) !

example12-left-path-target : Term 0
example12-left-path-target =
  (Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩)
    · (Ex.c ⟨ example12-ℕ! ⟩)

example12-left-path-target-⊢ :
  Ex.∅ ⊢ example12-left-path-target ⦂ ★
example12-left-path-target-⊢ =
  ⊢· (⊢⟨⟩ Ex.polyId-⊢ Ex.ν̅α-α♯→α♭)
    (⊢⟨⟩ Ex.c-⊢ example12-ℕ!)

example12-left-path-source-store : TyStore 3
example12-left-path-source-store =
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) (‵ `ℕ)

example12-left-path-target-store : TyStore 1
example12-left-path-target-store = store-bind store-empty ★

example12-left-path-imp-env : ImpEnv 3
example12-left-path-imp-env Fin.zero = X⊑X
example12-left-path-imp-env (Fin.suc Fin.zero) = X⊑X
example12-left-path-imp-env (Fin.suc (Fin.suc Fin.zero)) = X⊑X

example12-left-path-ηᴸ : 3 ↪ᵗ 3
example12-left-path-ηᴸ = keep (keep (keep empty))

example12-left-path-ηᴿ-X : 1 ↪ᵗ 3
example12-left-path-ηᴿ-X = keep (skip (skip empty))

example12-left-path-ηᴿ-Y : 1 ↪ᵗ 3
example12-left-path-ηᴿ-Y = skip (keep empty)

example12-left-path-ηᴿ-Z : 1 ↪ᵗ 3
example12-left-path-ηᴿ-Z = skip (skip (keep empty))

example12-left-path-world-X : World 3 1 3
example12-left-path-world-X =
  world example12-left-path-ηᴸ example12-left-path-ηᴿ-X
    example12-left-path-imp-env
    example12-left-path-source-store
    example12-left-path-target-store

example12-left-path-world-Y : World 3 1 3
example12-left-path-world-Y =
  world example12-left-path-ηᴸ example12-left-path-ηᴿ-Y
    example12-left-path-imp-env
    example12-left-path-source-store
    example12-left-path-target-store

example12-left-path-world-Z : World 3 1 3
example12-left-path-world-Z =
  world example12-left-path-ηᴸ example12-left-path-ηᴿ-Z
    example12-left-path-imp-env
    example12-left-path-source-store
    example12-left-path-target-store

example12-left-path-source-X∋ :
  example12-left-path-source-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-left-path-source-X∋ = Z∋ refl

example12-left-path-source-Y∋ :
  example12-left-path-source-store ∋ Fin.suc Fin.zero
    ⦂ ＇ (Fin.suc (Fin.suc Fin.zero))
example12-left-path-source-Y∋ = S-bind∋ (Z∋ refl) refl

example12-left-path-source-Z∋ :
  example12-left-path-source-store ∋ Fin.suc (Fin.suc Fin.zero) ⦂ ★
example12-left-path-source-Z∋ =
  S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

example12-left-path-target-U∋ :
  example12-left-path-target-store ∋ Fin.zero ⦂ ★
example12-left-path-target-U∋ = Z∋ refl

example12-left-path-X-representation :
  StoreRepImp example12-left-path-world-X Fin.zero Fin.zero
example12-left-path-X-representation = store-rep-imp ι⊑★

example12-left-path-Z-representation :
  StoreRepImp example12-left-path-world-Z
    (Fin.suc (Fin.suc Fin.zero)) Fin.zero
example12-left-path-Z-representation = store-rep-imp ★⊑★

example12-left-path-Y-representation :
  StoreRepImp example12-left-path-world-Y (Fin.suc Fin.zero) Fin.zero
example12-left-path-Y-representation = store-rep-imp ★⊑★
