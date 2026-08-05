module proof.DGG.CastTermImprecision2 where

-- File Charter:
--   * Experiments with the Issue 117 redesign of cast-term imprecision.
--   * Keeps type imprecision single-context, but makes each term-imprecision
--     premise carry its current local source/target embeddings into that
--     center context.
--   * Represents local rebasing explicitly, letting reveal/conceal wrappers
--     descend with a different alignment.
--   * Records the Example 12 alignments Xᴸ≅Xᴿ, Xᴸ≅Zᴿ, and Xᴸ≅Yᴿ as first-class
--     store-representation witnesses.
--   * Records a left-hand analogue of Example 12 where the source store, not
--     the target store, has the representation path to ★.
--   * Records a variant where the target store has a representation path to
--     ℕ, showing that representation paths are not only a ★ phenomenon.
--   * The more rules in this relation, the more cases to prove in the DGG.
--     So don't add rules unless they are absolutely necessary!
--     Avoid rules that are not syntax directed.

open import Data.List using (List; []; _∷_; map)
open import Data.Nat as Nat using (ℕ)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

record SameRuntime {Δᴸ Δᴿ Δ Δ′}
    (W : World Δᴸ Δᴿ Δ) (W′ : World Δᴸ Δᴿ Δ′) : Set where
  constructor same-runtime
  field
    sourceStore-same : sourceStoreʷ W′ ≡ sourceStoreʷ W
    targetStore-same : targetStoreʷ W′ ≡ targetStoreʷ W

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

------------------------------------------------------------------------
-- Store representations and local rebasing
------------------------------------------------------------------------

data LeadsTo : ∀ {Δ} → TyStore Δ → Ty Δ → Ty Δ → Set where
  leads-here : ∀ {Δ} {Σ : TyStore Δ} {A : Ty Δ}
      ------------------
    → LeadsTo Σ A A

  leads-var : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ} {A B : Ty Δ}
    → Σ ∋ X ⦂ A
    → LeadsTo Σ A B
      -----------------------
    → LeadsTo Σ (＇ X) B

infix 4 _⊢_↝_

data _⊢_↝_ {Δ} (Σ : TyStore Δ) : TyVar Δ → Ty Δ → Set where
  var-leads : ∀ {X A B}
    → Σ ∋ X ⦂ A
    → LeadsTo Σ A B
      ----------------
    → Σ ⊢ X ↝ B

record StoreRepImp {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor store-rep-imp
  field
    sourceRepTy : Ty Δᴸ
    targetRepTy : Ty Δᴿ
    sourceRep : sourceStoreʷ W ⊢ Xᴸ ↝ sourceRepTy
    targetRep : targetStoreʷ W ⊢ Xᴿ ↝ targetRepTy
    represented : sourceRepTy ⊑ᵂ⟨ W ⟩ targetRepTy

record RebaseAt {Δᴸ Δᴿ Δ Δ′}
    (W : World Δᴸ Δᴿ Δ) (W′ : World Δᴸ Δᴿ Δ′)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    sameRuntime : SameRuntime W W′
    pivotAligned : toRenameᵗ (ηᴸʷ W′) Xᴸ ≡ toRenameᵗ (ηᴿʷ W′) Xᴿ
    storeRepresentations : StoreRepImp W′ Xᴸ Xᴿ

sameWorldRebaseAt : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
  → StoreRepImp W Xᴸ Xᴿ
    --------------------
  → RebaseAt W W Xᴸ Xᴿ
sameWorldRebaseAt = rebase-at (same-runtime refl refl)

------------------------------------------------------------------------
-- Conversion typing indexed by the converted variable
------------------------------------------------------------------------

infix 4 _⊢↑[_]_ _⊢↓[_]_

mutual
  data _⊢↑[_]_ {Δ : TyCtx} (Σ : TyStore Δ) (X : TyVar Δ) :
      ∀ {A B} → Conv↑ Δ A B → Set where
    ⊢↑-unsealˣ : ∀ {R}
      → Σ ∋ X ⦂ R
        ---------------------
      → Σ ⊢↑[ X ] unseal X R

    ⊢↑-⇒ˣ : ∀ {A A′ B B′}
        {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
      → Σ ⊢↓[ X ] c
      → Σ ⊢↑[ X ] d
        -----------------
      → Σ ⊢↑[ X ] c ↦↑ d

    ⊢↑-∀ˣ : ∀ {A B} {c : Conv↑ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↑[ Fin.suc X ] c
        --------------------
      → Σ ⊢↑[ X ] `∀↑ c

    ⊢↑-idˣ : ∀ {A}
        -----------------
      → Σ ⊢↑[ X ] id↑ A

  data _⊢↓[_]_ {Δ : TyCtx} (Σ : TyStore Δ) (X : TyVar Δ) :
      ∀ {A B} → Conv↓ Δ A B → Set where
    ⊢↓-sealˣ : ∀ {R}
      → Σ ∋ X ⦂ R
        -------------------
      → Σ ⊢↓[ X ] seal X R

    ⊢↓-⇒ˣ : ∀ {A A′ B B′}
        {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
      → Σ ⊢↑[ X ] c
      → Σ ⊢↓[ X ] d
        -----------------
      → Σ ⊢↓[ X ] c ↦↓ d

    ⊢↓-∀ˣ : ∀ {A B} {c : Conv↓ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↓[ Fin.suc X ] c
        --------------------
      → Σ ⊢↓[ X ] `∀↓ c

    ⊢↓-idˣ : ∀ {A}
        -----------------
      → Σ ⊢↓[ X ] id↓ A

data IdentityReveal {Δ : TyCtx} : ∀ {A B} → Conv↑ Δ A B → Set where
  identity-reveal-id : ∀ {A}
      ---------------------------
    → IdentityReveal (id↑ A)

  identity-reveal-∀ : ∀ {A B} {c : Conv↑ (Nat.suc Δ) A B}
    → IdentityReveal c
      -------------------------
    → IdentityReveal (`∀↑ c)

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

  Λ⊑² : ∀ {γ′ V M A B}
      {p : A ⊑ᵂ⟨ liftWorldBoth X⊑★ W ⟩ ⇑ᵗ B}
    → LiftCtx X⊑★ γ γ′
    → Value V
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ B
    → liftWorldBoth X⊑★ W ∣ γ′ ⊢² V ⊑ ⇑ᵗᵐ M ∶ p
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

  -- TODO: Find a way to remove the below rule
  ⊑id-reveal² : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {c′ : Conv↑ Δᴿ B B′}
    → IdentityReveal c′
    → targetStoreʷ W ⊢↑ c′
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑reveal² : ∀ {Δ′} {W′ : World Δᴸ Δᴿ Δ′}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↑ Δᴿ B B′}
    → RebaseAt W W′ Xᴸ Xᴿ
    → SameCtx γ γ′
    → targetStoreʷ W ⊢↑[ Xᴿ ] c′
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal² : ∀ {Δ′} {W′ : World Δᴸ Δᴿ Δ′}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↓ Δᴿ B B′}
    → RebaseAt W′ W Xᴸ Xᴿ
    → SameCtx γ γ′
    → targetStoreʷ W ⊢↓[ Xᴿ ] c′
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

  reveal⊑² : ∀ {Δ′} {W′ : World Δᴸ Δᴿ Δ′}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↑ Δᴸ A A′}
    → RebaseAt W W′ Xᴸ Xᴿ
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↑[ Xᴸ ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↑ c ⊑ M′ ∶ q

  conceal⊑² : ∀ {Δ′} {W′ : World Δᴸ Δᴿ Δ′}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → RebaseAt W′ W Xᴸ Xᴿ
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q

  reveal⊑reveal² : ∀ {Δᵖ}
      {Wᵖ : World Δᴸ Δᴿ Δᵖ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
    → RebaseAt W Wᵖ Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → sourceStoreʷ W ⊢↑[ Xᴸ ] c
    → targetStoreʷ W ⊢↑[ Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑conceal² : ∀ {Δᵖ}
      {Wᵖ : World Δᴸ Δᴿ Δᵖ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    → RebaseAt Wᵖ W Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → sourceStoreʷ W ⊢↓[ Xᴸ ] c
    → targetStoreʷ W ⊢↓[ Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q

  blame⊑blame² : ∀ {A B}
    → (p : A ⊑ᵂ⟨ W ⟩ B)
      ------------------------------
    → W ∣ γ ⊢² blame ⊑ blame ∶ p

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

example12-Z-leads-star :
  LeadsTo example12-target-store (＇ (Fin.suc (Fin.suc Fin.zero))) ★
example12-Z-leads-star = leads-var example12-target-Z∋ leads-here

example12-X-representation : StoreRepImp example12-world-X Fin.zero Fin.zero
example12-X-representation =
  store-rep-imp (‵ `ℕ) (‵ `ℕ)
    (var-leads example12-source-X∋ leads-here)
    (var-leads example12-target-X∋ leads-here)
    ι⊑ι

example12-Z-representation :
  StoreRepImp example12-world-Z Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-Z-representation =
  store-rep-imp (‵ `ℕ) ★
    (var-leads example12-source-X∋ leads-here)
    (var-leads example12-target-Z∋ leads-here)
    ι⊑★

example12-Y-representation :
  StoreRepImp example12-world-Y Fin.zero (Fin.suc Fin.zero)
example12-Y-representation =
  store-rep-imp (‵ `ℕ) ★
    (var-leads example12-source-X∋ leads-here)
    (var-leads example12-target-Y∋ example12-Z-leads-star)
    ι⊑★

example12-rebase-X-to-Z :
  RebaseAt example12-world-X example12-world-Z
    Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-rebase-X-to-Z =
  rebase-at (same-runtime refl refl) refl example12-Z-representation

example12-rebase-X-to-Y :
  RebaseAt example12-world-X example12-world-Y Fin.zero (Fin.suc Fin.zero)
example12-rebase-X-to-Y =
  rebase-at (same-runtime refl refl) refl example12-Y-representation

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

example12-nat-chain-target-X⇝ℕ :
  LeadsTo example12-nat-chain-target-store (＇ (Fin.suc Fin.zero)) (‵ `ℕ)
example12-nat-chain-target-X⇝ℕ =
  leads-var example12-nat-chain-target-X∋ leads-here

example12-nat-chain-X-representation :
  StoreRepImp example12-nat-chain-world-X Fin.zero (Fin.suc Fin.zero)
example12-nat-chain-X-representation =
  store-rep-imp (‵ `ℕ) (‵ `ℕ)
    (var-leads example12-nat-chain-source-X∋ leads-here)
    (var-leads example12-nat-chain-target-X∋ leads-here)
    ι⊑ι

example12-nat-chain-Y-representation :
  StoreRepImp example12-nat-chain-world-Y Fin.zero Fin.zero
example12-nat-chain-Y-representation =
  store-rep-imp (‵ `ℕ) (‵ `ℕ)
    (var-leads example12-nat-chain-source-X∋ leads-here)
    (var-leads example12-nat-chain-target-Y∋
      example12-nat-chain-target-X⇝ℕ)
    ι⊑ι

example12-nat-chain-rebase-X-to-Y :
  RebaseAt example12-nat-chain-world-X example12-nat-chain-world-Y
    Fin.zero Fin.zero
example12-nat-chain-rebase-X-to-Y =
  rebase-at (same-runtime refl refl) refl
    example12-nat-chain-Y-representation

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

example12-left-path-source-Z⇝★ :
  LeadsTo example12-left-path-source-store
    (＇ (Fin.suc (Fin.suc Fin.zero))) ★
example12-left-path-source-Z⇝★ =
  leads-var example12-left-path-source-Z∋ leads-here

example12-left-path-source-Y⇝★ :
  LeadsTo example12-left-path-source-store (＇ (Fin.suc Fin.zero)) ★
example12-left-path-source-Y⇝★ =
  leads-var example12-left-path-source-Y∋ example12-left-path-source-Z⇝★

example12-left-path-X-representation :
  StoreRepImp example12-left-path-world-X Fin.zero Fin.zero
example12-left-path-X-representation =
  store-rep-imp (‵ `ℕ) ★
    (var-leads example12-left-path-source-X∋ leads-here)
    (var-leads example12-left-path-target-U∋ leads-here)
    ι⊑★

example12-left-path-Z-representation :
  StoreRepImp example12-left-path-world-Z
    (Fin.suc (Fin.suc Fin.zero)) Fin.zero
example12-left-path-Z-representation =
  store-rep-imp ★ ★
    (var-leads example12-left-path-source-Z∋ leads-here)
    (var-leads example12-left-path-target-U∋ leads-here)
    ★⊑★

example12-left-path-Y-representation :
  StoreRepImp example12-left-path-world-Y (Fin.suc Fin.zero) Fin.zero
example12-left-path-Y-representation =
  store-rep-imp ★ ★
    (var-leads example12-left-path-source-Y∋
      example12-left-path-source-Z⇝★)
    (var-leads example12-left-path-target-U∋ leads-here)
    ★⊑★

example12-left-path-rebase-X-to-Z :
  RebaseAt example12-left-path-world-X example12-left-path-world-Z
    (Fin.suc (Fin.suc Fin.zero)) Fin.zero
example12-left-path-rebase-X-to-Z =
  rebase-at (same-runtime refl refl) refl
    example12-left-path-Z-representation

example12-left-path-rebase-X-to-Y :
  RebaseAt example12-left-path-world-X example12-left-path-world-Y
    (Fin.suc Fin.zero) Fin.zero
example12-left-path-rebase-X-to-Y =
  rebase-at (same-runtime refl refl) refl
    example12-left-path-Y-representation
