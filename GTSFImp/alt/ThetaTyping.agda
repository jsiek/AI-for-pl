module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  Anchors index
--     telescopes and terms, but never occur in regular types `Ty Δ`.
--   * Defines the first-order classifier for exactly two semantic consumers:
--     the spelling premise used by crossings here, and allocation later.
--   * Makes `∀-bound` entries deliberately unspellable, preventing lexical
--     variables from being mistaken for anchor-backed representation slots.
--   * Enforces closed interiors for ν, wk, reveal, and conceal.

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TermCtx
open import Primitives
open import Consistency
open import alt.ThetaTerms
open import alt.Conversion

------------------------------------------------------------------------
-- Regular-variable classifier
------------------------------------------------------------------------

private
  variable
    Θ : AnchorCtx
    Δ : TyCtx

data Binding (Θ : AnchorCtx) : Set where
  ∀-bound : Binding Θ
  slot≔ : TyVar Θ → Binding Θ

infixr 5 _∷_

data Classifier (Θ : AnchorCtx) : TyCtx → Set where
  [] : Classifier Θ zero
  _∷_ : ∀ {Δ} → Binding Θ → Classifier Θ Δ
    → Classifier Θ (suc Δ)

lookupClassifier : Classifier Θ Δ → TyVar Δ → Binding Θ
lookupClassifier (b ∷ κ) zero = b
lookupClassifier (b ∷ κ) (suc Y) = lookupClassifier κ Y

insert∀ : Classifier Θ Δ → Classifier Θ (suc Δ)
insert∀ κ = ∀-bound ∷ κ

insertSlot : TyVar (suc Δ) → TyVar Θ
  → Classifier Θ Δ → Classifier Θ (suc Δ)
insertSlot zero α κ = slot≔ α ∷ κ
insertSlot (suc Y) α (b ∷ κ) = b ∷ insertSlot Y α κ

------------------------------------------------------------------------
-- Spelling: one representation, written in two type contexts
------------------------------------------------------------------------

-- `Spell κ A R` says that A (over the ambient regular context) and R (over
-- the telescope's type context) are the same representation, written in the
-- two contexts, according to κ.  Its generalized core makes a type-local `∀` binder on
-- each side correspond exactly as `LiftRel` did for v2 transport.

VarSpell : TyCtx → TyCtx → Set₁
VarSpell Δ Δᵀ = TyVar Δ → Ty Δᵀ → Set

data ClassifierSpell {Θ Δ} (κ : Classifier Θ Δ) : VarSpell Δ Θ where
  spell-slot : ∀ {Y α}
    → lookupClassifier κ Y ≡ slot≔ α
    → ClassifierSpell κ Y (＇ α)

-- There is intentionally no `∀-bound` case above.  Lexical variables are
-- unspellable: this is the preservation guard that keeps them from being
-- spelled into the telescope's type context.

data LiftSpell {Θ Δ} (ρ : VarSpell Δ Θ) :
    VarSpell (suc Δ) (suc Θ) where
  spell-zero : LiftSpell ρ zero (＇ zero)

  spell-suc : ∀ {Y A B}
    → ρ Y A
    → B ≡ ⇑ᵗ A
    → LiftSpell ρ (suc Y) B

data SpellBy {Θ Δ} (ρ : VarSpell Δ Θ) : Ty Δ → Ty Θ → Set where
  spell-by-var : ∀ {Y A}
    → ρ Y A
    → SpellBy ρ (＇ Y) A

  spell-base : ∀ {ι}
    → SpellBy ρ (‵ ι) (‵ ι)

  spell-star : SpellBy ρ ★ ★

  spell-fun : ∀ {A B R S}
    → SpellBy ρ A R
    → SpellBy ρ B S
    → SpellBy ρ (A ⇒ B) (R ⇒ S)

  spell-all : ∀ {A R}
    → SpellBy (LiftSpell ρ) A R
    → SpellBy ρ (`∀ A) (`∀ R)

Spell : Classifier Θ Δ → Ty Δ → Ty Θ → Set
Spell κ = SpellBy (ClassifierSpell κ)

spell-var : ∀ {κ : Classifier Θ Δ} {Y α}
  → lookupClassifier κ Y ≡ slot≔ α
  → Spell κ (＇ Y) (＇ α)
spell-var eq = spell-by-var (spell-slot eq)

------------------------------------------------------------------------
-- Typing contexts
------------------------------------------------------------------------

record Ctx : Set where
  constructor ⟨_,_,_,_,_⟩
  field
    Θᵉ : AnchorCtx
    Ξᵉ : Tele Θᵉ
    Δᵉ : TyCtx
    κᵉ : Classifier Θᵉ Δᵉ
    Γᵉ : TermCtx Δᵉ

open Ctx public

infixl 5 _,ᶜ_

_,ᶜ_ : (Γ : Ctx) → Ty (Δᵉ Γ) → Ctx
⟨ Θ , Ξ , Δ , κ , Γ ⟩ ,ᶜ A =
  ⟨ Θ , Ξ , Δ , κ , A ∷ Γ ⟩

∀-ctx : Ctx → Ctx
∀-ctx ⟨ Θ , Ξ , Δ , κ , Γ ⟩ =
  ⟨ Θ , Ξ , suc Δ , insert∀ κ , ⇑ᶜ Γ ⟩

infix 4 _∋ᵗ_⦂_

_∋ᵗ_⦂_ : (Γ : Ctx) → Var → Ty (Δᵉ Γ) → Set
Γ ∋ᵗ x ⦂ A = TermCtx._∋_⦂_ (Γᵉ Γ) x A

------------------------------------------------------------------------
-- Pointwise anchor weakening for the ν consumer
------------------------------------------------------------------------

weakenBinding : Binding Θ → Binding (suc Θ)
weakenBinding ∀-bound = ∀-bound
weakenBinding (slot≔ α) = slot≔ (suc α)

weakenClassifier : Classifier Θ Δ → Classifier (suc Θ) Δ
weakenClassifier [] = []
weakenClassifier (b ∷ κ) = weakenBinding b ∷ weakenClassifier κ

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _⊢_⦂_

data _⊢_⦂_ : (Γ : Ctx)
    → Term (Θᵉ Γ) (Δᵉ Γ) → Ty (Δᵉ Γ) → Set where
  ⊢` : ∀ {Γ x A}
    → Γ ∋ᵗ x ⦂ A
      ---------------
    → Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {Γ A B M}
    → Γ ,ᶜ A ⊢ M ⦂ B
      -------------------------
    → Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ A B L M}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
      ------------------------------
    → Γ ⊢ (L · M) ⦂ B

  -- DEFERRED: value restriction
  ⊢Λ : ∀ {Γ A M}
    → ∀-ctx Γ ⊢ M ⦂ A
      --------------------
    → Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢⦂∀ : ∀ {Γ C A L}
    → Γ ⊢ L ⦂ `∀ C
      -----------------------------
    → Γ ⊢ L ⦂∀ C [ A ] ⦂ C [ A ]ᵗ

  ⊢$ : ∀ {Γ} (κ : Const)
      -----------------------
    → Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {Γ L M}
    → (op : Prim)
    → Γ ⊢ L ⦂ primArgTy op
    → Γ ⊢ M ⦂ primArgTy op
      -------------------------------------
    → Γ ⊢ (L ⊕[ op ] M) ⦂ primResultTy op

  ⊢⟨⟩ : ∀ {Γ M A B μ}
    → Γ ⊢ M ⦂ A
    → (c : μ ⊢ A ∼ B)
      -----------------
    → Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢ν : ∀ {Θ} {Ξ : Tele Θ} {Δ} {κ : Classifier Θ Δ}
      {Γ : TermCtx Δ} {R : Ty Θ} {M B}
    → ⟨ suc Θ , tele-bind Ξ R , Δ , weakenClassifier κ , [] ⟩
        ⊢ M ⦂ B
      --------------------------------------
    → ⟨ Θ , Ξ , Δ , κ , Γ ⟩ ⊢ ν[ R ] M ⦂ B

  ⊢reveal : ∀ {Θ} {Ξ : Tele Θ} {Δ} {κ : Classifier Θ Δ}
      {Γ : TermCtx Δ} {M A B Y α R R′ c}
    → Ξ ∋ν α ⦂ R
    → Spell (insertSlot Y α κ) R′ R
    → ⊢↑[ Y ⦂ R′ ] c ⦂ A ↝ wkᵗ Y B
    → ⟨ Θ , Ξ , suc Δ , insertSlot Y α κ , [] ⟩ ⊢ M ⦂ A
      --------------------------------------------
    → ⟨ Θ , Ξ , Δ , κ , Γ ⟩ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  ⊢conceal : ∀ {Θ} {Ξ : Tele Θ} {Δ} {κ : Classifier Θ Δ}
      {Γ′ : TermCtx (suc Δ)} {M A B Y α R R′ c}
    → Ξ ∋ν α ⦂ R
    → Spell (insertSlot Y α κ) R′ R
    → ⊢↓[ Y ⦂ R′ ] c ⦂ wkᵗ Y A ↝ B
    → ⟨ Θ , Ξ , Δ , κ , [] ⟩ ⊢ M ⦂ A
      -------------------------------------------
    → ⟨ Θ , Ξ , suc Δ , insertSlot Y α κ , Γ′ ⟩
        ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame : ∀ {Γ A}
      ---------------
    → Γ ⊢ blame ⦂ A
