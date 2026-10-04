module proof.DGG.notes.StarEmbedding where

-- File Charter:
--   * THE PROPOSAL CHECKED HERE ("★-embedding"): the right embedding of a
--     world may send a right-only name whose rep. var is bound to ★
--     (e.g. the `+Y^β`, β:=★, that `Inst` + TyBeta create) to the type
--     ★ instead of to a center name.  Type imprecision `_⊢_⊑_`
--     (Imprecision.agda) is UNCHANGED; only the world layer changes.
--     `⊑⟪⟫` is the PLAIN one-sided rule: no `Opens`, no InstX in the
--     relation.  Findings in StarEmbedding.md.  NOT a Def module, not
--     imported by All.agda; nothing outside this file and its .md is
--     edited.
--   * ENCODING (§1).  A ★-world `World★ Δ Δ′` is a real `World` plus a
--     list of Booleans `σʷ`, parallel to `names Δ′` (head = index 0):
--     `true` marks a ★-embedded right name.  The right embedding is the
--     SUBSTITUTION `embᴿ★ = substᵗ (starSub σ (emb ηᴿ))`, which sends a
--     marked name to ★ and every other name to its center name.  A marked
--     name keeps a PHANTOM right-only center name in the underlying real
--     world; no embedded type can mention it, so the overlay is
--     equivalent to an embedding `names Δ′ → center ⊎ ★` (erase the
--     phantom center names; conversely insert one right-only center name
--     per marked name).  The overlay lets every real `Interior`,
--     `ConversionInterior` and `WfWorld` proof of examples/ be reused.
--     The WfWorld condition (`WfWorld★`): a marked name is bound to a
--     ★ rep. var and is right-only (`StarOK`).  Marks of names a
--     boundary introduces are chosen by the derivation (as marks, D11);
--     continuing names keep theirs (`star-cont`).
--   * §2 the LOCAL COPY of conversion imprecision over ★-worlds: the
--     clauses of ConversionImprecision, plus four MIRROR clauses for a
--     right seal/unseal of a ★-embedded name (`conv-id⊑seal★`,
--     `conv-⊑⨾seal★`, `conv-id⊑unseal★`, `conv-⊑unseal⨾★`).
--   * §3 the LOCAL COPY of the term relation: TermImprecision's 15 rules
--     with the same constructor names, ⊑ᵂ read through the ★-world, and
--     `⊑⟪⟫` WITHOUT `Opens`.
--   * §4 counterexample K: every synchronization pair (lk⊑rk, lk₁⊑rk₁,
--     lk₁⊑rk₃, lk₁⊑rk₄, VL⊑RF), with no opening; the final pair twice
--     (natural ⟪⟫⊑⟪⟫ derivation, which needs the mirror clauses; and
--     ⊑⟪⟫ first, which does not); sim-K★, simBack-K-merge★, dgg1-K★.
--   * §5 the corpus blocks that needed an opening: P3 = Ch, L3c (pre,
--     post), L3d (before, after), Cg, C2 (a gen-cast left ∀-value, by
--     cast⊑cast), C12, R2c (pre and post the right's Merge).
--   * §6 risks: (a) a CONCRETE COUNTEREXAMPLE for the ★-embedded
--     relation: left `(λx:ℕ.x) 5` against a right Inst boundary that
--     tags with its own name.  The pair is related (`cx-related`; in no
--     real world, `real-ℕ⊑Y`), the left reaches 5, every right run
--     blames (`cx-no-right-value`): DGG part 1 fails.  Locally,
--     `five⊑R₇`/`castRedexNoBlame-fails` refute CastRedexNoBlame and
--     SimBackBlame (STATEMENTS-CORE M26, M22).  (c) uniqueness of the
--     index survives (`⊑ᵂ★-unique`); (d) the embedding is not a renaming
--     (`embᴿ★-not-renaming`).
--   * VERDICT: every K pair and every corpus block derives without
--     openings, but the ★-embedding over-relates and is unsound for the
--     DGG as stated; see StarEmbedding.md.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; head; drop; replicate)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
open import Imprecision
open import ImprecisionWorld
  hiding (CtxImpEntry; ctx-imp; tyᴸ; tyᴿ; impʷ; CtxImp; lhs; rhs;
          _∋ʷ_⦂_; Zʷ; Sʷ; LiftCtx; lift-[]; lift-∷; LiftCtxᴸ; liftᴸ-[];
          liftᴸ-∷)
open import TermImprecision
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; nu-ty;
         BdyTy; bdy-ty; ⟪⟫-inv; cast-inv; ν-inv)
open import proof.ImprecisionWorld
  using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])
import proof.Imprecision as PI

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. ★-worlds
------------------------------------------------------------------------

infixl 9 _‼_
_‼_ : List Bool → ℕ → Bool
[] ‼ k            = false
(b ∷ σ) ‼ zero    = b
(b ∷ σ) ‼ (suc k) = σ ‼ k

-- the right embedding as a substitution: a marked name goes to ★
starSub : List Bool → Renameᵗ → Substᵗ
starSub σ ρ X = if σ ‼ X then ★ else ` (ρ X)

record World★ (Δ Δ′ : Ctxᵗ) : Set where
  constructor w★
  field
    wᵇ : World Δ Δ′          -- the real world (phantom centers included)
    σʷ : List Bool           -- ★-marks of the right names
open World★ public

embᴿ★ : World★ Δ Δ′ → Ty → Ty
embᴿ★ W = substᵗ (starSub (σʷ W) (emb (ηᴿʷ (wᵇ W))))

-- type imprecision at a ★-world: `_⊢_⊑_` itself, unchanged.  It is
-- wrapped in a one-field record only so that Agda can recover the two
-- types from an index (`substᵗ`, unlike `renameᵗ`, is not
-- constructor-headed, so the bare definition leaves A′ unsolved).
infix 4 _⊑ᵂ★⟨_⟩_
record _⊑ᵂ★⟨_⟩_ (A : Ty) (W : World★ Δ Δ′) (A′ : Ty) : Set where
  constructor ⟦_⟧
  field ty★ : μʷ (wᵇ W) ⊢ embᴸ (wᵇ W) A ⊑ embᴿ★ W A′
open _⊑ᵂ★⟨_⟩_ public

⇒★ : ∀ {W : World★ Δ Δ′} {A A′ B B′}
  → A ⊑ᵂ★⟨ W ⟩ A′ → B ⊑ᵂ★⟨ W ⟩ B′ → (A ⇒ B) ⊑ᵂ★⟨ W ⟩ (A′ ⇒ B′)
⇒★ ⟦ p ⟧ ⟦ q ⟧ = ⟦ ⇒⊑⇒ p q ⟧

-- a right name no left name joins
RightOnly : World Δ Δ′ → ℕ → Set
RightOnly {Δ = Δ} W k = ∀ {X} → Δ ∋tv X → ¬ Joins W X k

-- the WfWorld condition of the proposal: only a right-only name bound to
-- ★ may go to ★
StarOK : World Δ Δ′ → ℕ → Set
StarOK {Δ′ = Δ′} W k =
  Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k

record WfWorld★ (W : World★ Δ Δ′) : Set where
  constructor wf★
  field
    wf-base : WfWorld (wᵇ W)
    wf-star : ∀ {k} → σʷ W ‼ k ≡ true → StarOK (wᵇ W) k
open WfWorld★ public

-- world operations: a Λ on both sides adds an unmarked right name; a
-- left-only Λ and a ν leave the right names alone
infixl 6 _⊕★_
_⊕★_ : World★ Δ Δ′ → VarImp → World★ (underΛ Δ) (underΛ Δ′)
w★ W σ ⊕★ m = w★ (W ⊕ m) (false ∷ σ)

_⊕ᴸ★ : World★ Δ Δ′ → World★ (underΛ Δ) Δ′
w★ W σ ⊕ᴸ★ = w★ (W ⊕ᴸ) σ

underν²★ : (R R′ : Ty) → World★ Δ Δ′
  → World★ (allocate R Δ) (allocate R′ Δ′)
underν²★ R R′ (w★ W σ) = w★ (underν² R R′ W) σ

-- the interior world: the real one, plus continuing right names keep
-- their ★-mark; the marks of introduced names are chosen
record Interior★ (W : World★ Δ Δ′) (Θ Θ′ : Boundary)
    (Wᵢ : World★ Δᵢ Δ′ᵢ) : Set where
  constructor int★
  field
    int-base  : Interior (wᵇ W) Θ Θ′ (wᵇ Wᵢ)
    star-cont : ∀ {X′ X′ₑ} → Δ′ᵢ ∋tv X′ → toExt Θ′ X′ ≡ just X′ₑ
      → σʷ Wᵢ ‼ X′ ≡ σʷ W ‼ X′ₑ
open Interior★ public

-- the conversion-context world, likewise (a continuing name is one whose
-- rep. var has an exterior name); a marked conversion name is StarOK
record ConversionInterior★ (W : World★ Δ Δ′) (Θ Θ′ : Boundary)
    (Wᶜ : World★ Δᶜ Δ′ᶜ) : Set where
  constructor conv★
  field
    conv-base      : ConversionInterior (wᵇ W) Θ Θ′ (wᵇ Wᶜ)
    conv-star-cont : ∀ {X′ X′ₑ β} → Δ′ᶜ ∋ᵗ X′ := β → Δ′ ∋ᵗ X′ₑ := β
      → σʷ Wᶜ ‼ X′ ≡ σʷ W ‼ X′ₑ
    conv-star-ok   : ∀ {k} → σʷ Wᶜ ‼ k ≡ true → StarOK (wᵇ Wᶜ) k
open ConversionInterior★ public

-- no marks
ff‼ : ∀ n {k} → replicate n false ‼ k ≡ true → ⊥
ff‼ zero ()
ff‼ (suc n) {zero} ()
ff‼ (suc n) {suc k} e = ff‼ n e

------------------------------------------------------------------------
-- 2. Conversion imprecision over ★-worlds (local copy + mirrors)
------------------------------------------------------------------------

mutual
  data MidImp {Δ Δ′ : Ctxᵗ} (W : World★ Δ Δ′) : Mid → Mid → Set where
    conv-id⊑id : ∀ {A A′} → A ⊑ᵂ★⟨ W ⟩ A′ → MidImp W (id A) (id A′)
    conv-↦⊑↦ : ∀ {s s′ c c′} → ConvImp W s s′ → ConvImp W c c′
      → MidImp W (s ↦ c) (s′ ↦ c′)
    conv-∀⊑∀ : ∀ {c c′} → ConvImp (W ⊕★ X⊑X) c c′
      → MidImp W (`∀ c) (`∀ c′)
    conv-∀⊑ : ∀ {c g′} → ConvImp (W ⊕ᴸ★) c ⌞ g′ ⌟ → MidImp W (`∀ c) g′

  data TailImp {Δ Δ′ : Ctxᵗ} (W : World★ Δ Δ′) : Tail → Tail → Set where
    conv-mid⊑mid : ∀ {g g′} → MidImp W g g′ → TailImp W (mid g) (mid g′)
    conv-seal⊑seal : ∀ {X X′} → Joins (wᵇ W) X X′
      → TailImp W (seal X) (seal X′)
    conv-⨾seal⊑⨾seal : ∀ {t t′ X X′} → TailImp W t t′ → Joins (wᵇ W) X X′
      → TailImp W (t ⨾seal X) (t′ ⨾seal X′)
    conv-seal⊑id★ : ∀ {X} → μʷ (wᵇ W) ∋ˡ emb (ηᴸʷ (wᵇ W)) X := X⊑★
      → TailImp W (seal X) (mid (id ★))
    conv-⨾seal⊑ : ∀ {t t′ X} → TailImp W t t′
      → μʷ (wᵇ W) ∋ˡ emb (ηᴸʷ (wᵇ W)) X := X⊑★
      → TailImp W (t ⨾seal X) t′
    -- NEW (★-embedding): a right seal of a ★-embedded name is ★ ⇒ ★
    -- through the embedding; it faces a left identity at a type ⊑ ★
    conv-id⊑seal★ : ∀ {A X′} → A ⊑ᵂ★⟨ W ⟩ ★ → σʷ W ‼ X′ ≡ true
      → TailImp W (mid (id A)) (seal X′)
    conv-⊑⨾seal★ : ∀ {t t′ X′} → TailImp W t t′ → σʷ W ‼ X′ ≡ true
      → TailImp W t (t′ ⨾seal X′)

  data ConvImp {Δ Δ′ : Ctxᵗ} (W : World★ Δ Δ′) : Conv → Conv → Set where
    conv-tail⊑tail : ∀ {t t′} → TailImp W t t′
      → ConvImp W (tail t) (tail t′)
    conv-unseal⊑unseal : ∀ {X X′} → Joins (wᵇ W) X X′
      → ConvImp W (unseal X) (unseal X′)
    conv-unseal⨾⊑unseal⨾ : ∀ {X X′ c c′} → Joins (wᵇ W) X X′
      → ConvImp W c c′ → ConvImp W (unseal X ⨾ c) (unseal X′ ⨾ c′)
    conv-unseal⊑id★ : ∀ {X} → μʷ (wᵇ W) ∋ˡ emb (ηᴸʷ (wᵇ W)) X := X⊑★
      → ConvImp W (unseal X) ⌞ id ★ ⌟
    conv-unseal⨾⊑ : ∀ {X c c′}
      → μʷ (wᵇ W) ∋ˡ emb (ηᴸʷ (wᵇ W)) X := X⊑★ → ConvImp W c c′
      → ConvImp W (unseal X ⨾ c) c′
    -- NEW (★-embedding): the unseal mirrors
    conv-id⊑unseal★ : ∀ {A X′} → A ⊑ᵂ★⟨ W ⟩ ★ → σʷ W ‼ X′ ≡ true
      → ConvImp W ⌞ id A ⌟ (unseal X′)
    conv-⊑unseal⨾★ : ∀ {X′ c c′} → ConvImp W c c′ → σʷ W ‼ X′ ≡ true
      → ConvImp W c (unseal X′ ⨾ c′)

------------------------------------------------------------------------
-- 3. The relation over ★-worlds (local copy; ⊑⟪⟫ without Opens)
------------------------------------------------------------------------

record CtxImpEntry (W : World★ Δ Δ′) : Set where
  constructor ctx-imp
  field
    tyᴸ  : Ty
    tyᴿ  : Ty
    impʷ : tyᴸ ⊑ᵂ★⟨ W ⟩ tyᴿ
open CtxImpEntry public

CtxImp : World★ Δ Δ′ → Set
CtxImp W = List (CtxImpEntry W)

lhs rhs : {W : World★ Δ Δ′} → CtxImp W → List Ty
lhs = Data.List.map tyᴸ
rhs = Data.List.map tyᴿ

infix 4 _∋ʷ_⦂_
data _∋ʷ_⦂_ {W : World★ Δ Δ′} : CtxImp W → ℕ → CtxImpEntry W → Set where
  Zʷ : ∀ {γ e} → (e ∷ γ) ∋ʷ zero ⦂ e
  Sʷ : ∀ {γ e e′ x} → γ ∋ʷ x ⦂ e → (e′ ∷ γ) ∋ʷ suc x ⦂ e

data LiftCtx {W : World★ Δ Δ′} (m : VarImp)
    : CtxImp W → CtxImp (W ⊕★ m) → Set where
  lift-[] : LiftCtx m [] []
  lift-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtx m γ γ′
    → LiftCtx m (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ A′) p′ ∷ γ′)

data LiftCtxᴸ {W : World★ Δ Δ′} : CtxImp W → CtxImp (W ⊕ᴸ★) → Set where
  liftᴸ-[] : LiftCtxᴸ [] []
  liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
    → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

NuConversionImp : ∀ {Δ Δ′ A A′ C C′ c c′ B B′}
  → (W : World★ Δ Δ′)
  → NuTy Δ A C c B → NuTy Δ′ A′ C′ c′ B′ → Set
NuConversionImp {c = c} {c′ = c′} W
  (nu-ty {R = R} {Δᶜ = Δᶜ} _ _ _ _ _ _)
  (nu-ty {R = R′} {Δᶜ = Δ′ᶜ} _ _ _ _ _ _) =
  Σ[ Wᶜ ∈ World★ Δᶜ Δ′ᶜ ]
    (ConversionInterior★ (underν²★ R R′ W) TyBetaBoundary TyBetaBoundary Wᶜ
    × ConvImp Wᶜ c c′)

BdyConversionImp : ∀ {Δ Δ′ Δᵢ Δ′ᵢ Θ Θ′} {Aᵢ A′ᵢ c c′ A A′}
  → (W : World★ Δ Δ′)
  → BdyTy Δ Θ Δᵢ Aᵢ c A → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′ → Set
BdyConversionImp {Θ = Θ} {Θ′ = Θ′} {c = c} {c′ = c′} W
  (bdy-ty {Δᶜ = Δᶜ} _ _ _ _ _) (bdy-ty {Δᶜ = Δ′ᶜ} _ _ _ _ _) =
  Σ[ Wᶜ ∈ World★ Δᶜ Δ′ᶜ ] (ConversionInterior★ W Θ Θ′ Wᶜ × ConvImp Wᶜ c c′)

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ} (W : World★ Δ Δ′) (γ : CtxImp W)
    : Term → Term → {A A′ : Ty} → A ⊑ᵂ★⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {x A A′} {p : A ⊑ᵂ★⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {k ι} → Lit k ι → (p : ι ⊑ᵂ★⟨ W ⟩ ι) → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {N N′ A A′ B B′} {pA : A ⊑ᵂ★⟨ W ⟩ A′} {pB : B ⊑ᵂ★⟨ W ⟩ B′}
    → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒★ pA pB

  ·⊑· : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ★⟨ W ⟩ A′} {pB : B ⊑ᵂ★⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒★ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  blame⊑ : ∀ {ℓ M′ A A′}
    → Δ ⊢ᵗ A → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′ → (p : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ★⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {M M′ μ c B A A′} {p : B ⊑ᵂ★⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → (q : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  ⊑cast : ∀ {M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ★⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ′ μ′ c′ B′ A′ → (q : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {γ′ V V′ A A′} {r : A ⊑ᵂ★⟨ W ⊕★ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′ → Value V → Value V′
    → W ⊕★ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ★⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  Λ⊑ : ∀ {γ′ V M′ A B′} {r : A ⊑ᵂ★⟨ W ⊕ᴸ★ ⟩ B′}
    → NonVar A → 0 ∈ᵗ A → LiftCtxᴸ γ γ′ → Value V
    → W ⊕ᴸ★ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂ★⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  ν⊑ν : ∀ {L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ★⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r → A ⊑ᵂ★⟨ W ⟩ A′
    → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′ → (q : B ⊑ᵂ★⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {L M′ A C c B B′} {r : `∀ C ⊑ᵂ★⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r → A ⊑ᵂ★⟨ W ⟩ ★ → NuTy Δ A C c B
    → (q : B ⊑ᵂ★⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World★ Δᵢ Δ′ᵢ}
      {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ★⟨ Wᵢ ⟩ A′ᵢ}
    → Interior★ W Θ Θ′ Wᵢ → WfWorld★ Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′ → (q : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⟪⟫⊑ : ∀ {Δᵢ} {Wᵢ : World★ Δᵢ Δ′}
      {M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ★⟨ Wᵢ ⟩ A′}
    → Interior★ W Θ [] Wᵢ → WfWorld★ Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A → (q : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  -- THE PLAIN RIGHT-ONLY BOUNDARY RULE (no Opens): the ★-embedding of
  -- the right-only names the boundary introduces is chosen in Wᵢ
  ⊑⟪⟫ : ∀ {Δ′ᵢ} {Wᵢ : World★ Δ Δ′ᵢ}
      {M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ★⟨ Wᵢ ⟩ A′ᵢ}
    → Interior★ W [] Θ′ Wᵢ → WfWorld★ Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′ → (q : A ⊑ᵂ★⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

------------------------------------------------------------------------
-- Shared pieces
------------------------------------------------------------------------

-- ∀X.X→X ⊑ ★→★ at any ★-world (∀⊑, X⊑★, X⊑★)
∀id⊑★ : (W : World★ Δ Δ′) → `∀ (` 0 ⇒ ` 0) ⊑ᵂ★⟨ W ⟩ (★ ⇒ ★)
∀id⊑★ W = ⟦ ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here)) ⟧

ℕ⊑★ : ∀ {W : World★ Δ Δ′} → `ℕ ⊑ᵂ★⟨ W ⟩ ★
ℕ⊑★ = ⟦ ι⊑★ base-ℕ ⟧

ℕ⊑ℕ : ∀ {W : World★ Δ Δ′} → `ℕ ⊑ᵂ★⟨ W ⟩ `ℕ
ℕ⊑ℕ = ⟦ ι⊑ι base-ℕ ⟧

★⊑★′ : ∀ {W : World★ Δ Δ′} → ★ ⊑ᵂ★⟨ W ⟩ ★
★⊑★′ = ⟦ ★⊑★ ⟧

five⊑★ : ∀ {Δ Ξ′} {W : World★ Δ (Ξ′ ∣ [])} {γ : CtxImp W}
  → W ∣ γ ⊢ $ 5 ⊑ $ 5 ⟨ [] ∣ `ℕ ! ⟩ ∶ ℕ⊑★
five⊑★ = ⊑cast (κ⊑κ lit-$ ℕ⊑ℕ) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

------------------------------------------------------------------------
-- 4. Counterexample K with no opening
------------------------------------------------------------------------

module K where
  open import examples.TypeCheck using (tc; tf)
  open import examples.TermImprecisionExamples
    using (idX; revX; Θ₀; ΔL; ΔLᵢ; ∀X⇒X; int₀; conv₀; Wν; Wν-conv)
  open import examples.TermImprecisionRebaseExamples using (id★↦)
  open import examples.CambridgeExamples using (I; instI)
  open import examples.TermImprecisionRegressionExamples
    using (KK; cId; cK; VL; Nk; Rarg₃; Bm; RF; LK; LK₁; RK; RK₁; RK₃;
           RK₄; ΔRk; vRF; st₀; st₁; st₂; st₃; st₄; stM; Wk1; Wk1ᵢ;
           Wk1-wf; Wk1ᵢ-wf; Wk1ᵢ-int; Wk1ᵢ-conv; νK-ty; instI₀-ty; bVL;
           instI-ty; Wk; Wk-wf; IntK-ro; ΘX; ΔRX; bindX-int; bindX-conv;
           Θ₂; int-Θ₂; bBm; WiR; IntK-Θ₂; bNR; bOutK; id★↦ᴿk-ty)
  open import proof.DGG.Evolve
    using (_⟿[_∣_]_; ev-done; ev-R; ev-noneᴸ; ev-noneᴿ; applyˢ; allocs)

  ∅★ Wk1★ Wk★ : _
  ∅★   = w★ ∅ʷ []
  Wk1★ = w★ Wk1 []
  Wk★  = w★ Wk []

  ∀id⊑∀id : ∀ {Δ Δ′} {W : World★ Δ Δ′}
    → `∀ (` 0 ⇒ ` 0) ⊑ᵂ★⟨ W ⟩ `∀ (` 0 ⇒ ` 0)
  ∀id⊑∀id = ⟦ ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X) ⟧

  X⊑X★ : ∀ {Δ Δ′} {W : World★ Δ Δ′} → ` 0 ⊑ᵂ★⟨ W ⊕★ X⊑X ⟩ ` 0
  X⊑X★ = ⟦ X⊑X ⟧

  cId⊑cId : ∀ {Δ Δ′} {W : World★ Δ Δ′} → ` 0 ⊑ᵂ★⟨ W ⟩ ` 0
    → ConvImp W cId cId
  cId⊑cId x = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
    where i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id x))

  ---------------------------------------------------------------------
  -- (LK, RK) and (LK₁, RK₁): no right-only name, σ = []

  Wν★-conv : ConversionInterior★ (underν²★ `ℕ `ℕ ∅★) Θ₀ Θ₀
    (w★ Wν (false ∷ []))
  Wν★-conv = conv★ Wν-conv (λ _ ()) (λ {k} e → ⊥-elim (ff‼ 1 {k} e))

  lk⊑rk : ∅★ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅★
  lk⊑rk =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ ∅★} tf tf (x⊑x Zʷ))
      (⊑cast
        (ν⊑ν
          (Λ⊑Λ lift-[] (V-simple (S-Λ (V-simple S-ƛ)))
            (V-simple (S-Λ (V-simple S-ƛ)))
            (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = ⟦ X⊑X ⟧} tf tf (x⊑x Zʷ)) ⟦ ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X) ⟧)
            ⟦ ∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)) ⟧)
          ℕ⊑ℕ νK-ty νK-ty
          (w★ Wν (false ∷ []) , Wν★-conv ,
           conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId ⟦ X⊑X ⟧))))
          ∀id⊑∀id)
        instI₀-ty (∀id⊑★ ∅★))

  Wk1ᵢ★ : World★ ΔLᵢ ΔLᵢ
  Wk1ᵢ★ = w★ Wk1ᵢ (false ∷ [])

  Wk1ᵢ★-int : Interior★ Wk1★ Θ₀ Θ₀ Wk1ᵢ★
  Wk1ᵢ★-int = int★ Wk1ᵢ-int λ { (_ , here) () ; (_ , there ()) _ }

  Wk1ᵢ★-wf : WfWorld★ Wk1ᵢ★
  Wk1ᵢ★-wf = wf★ Wk1ᵢ-wf (λ {k} e → ⊥-elim (ff‼ 1 {k} e))

  lk₁⊑rk₁ : Wk1★ ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1★
  lk₁⊑rk₁ =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk1★} tf tf (x⊑x Zʷ))
      (⊑cast
        (⟪⟫⊑⟪⟫ Wk1ᵢ★-int Wk1ᵢ★-wf
          (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = ⟦ X⊑X ⟧} tf tf (x⊑x Zʷ)) ⟦ ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X) ⟧)
          bVL bVL
          (Wk1ᵢ★ , conv★ Wk1ᵢ-conv (λ _ ()) (λ {k} e → ⊥-elim (ff‼ 1 {k} e)) ,
           conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId ⟦ X⊑X ⟧))))
          ∀id⊑∀id)
        instI-ty (∀id⊑★ Wk1★))

  ---------------------------------------------------------------------
  -- (LK₁, RK₃) before the right's Merge: ⊑⟪⟫ at Θ₀ with Y ★-embedded

  -- inside the Inst boundary `+Y^β`: Y right-only, ★-embedded
  WiY★ : World★ ΔL (reps ΔRk ∣ (0 ∷ []))
  WiY★ = w★ (Wk ⊕ʳ X⊑X ^ 0) (true ∷ [])

  IntY★ : Interior★ Wk★ [] Θ₀ WiY★
  IntY★ = int★ IntK-ro λ { (_ , here) () ; (_ , there ()) _ }

  WiY★-wf : WfWorld★ WiY★
  WiY★-wf = wf★ (wf-world (right-only joint[]) agree
                   (namedᴸ-≤1 (Wk ⊕ʳ X⊑X ^ 0) ≤1-[])
                   (namedᴿ-≤1 (Wk ⊕ʳ X⊑X ^ 0) ≤1-∷[]))
              star
    where
    agree : ∀ {α β} → Paired (Wk ⊕ʳ X⊑X ^ 0) α β
      → Agree (Wk ⊕ʳ X⊑X ^ 0) α β
    agree (inj₁ here⇔) = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())
    star : ∀ {k} → (true ∷ []) ‼ k ≡ true → StarOK (Wk ⊕ʳ X⊑X ^ 0) k
    star {zero} refl = 0 , here , r-here , λ { (_ , ()) }
    star {suc k} ()

  -- inside both inner `+X^α` (the left's VL boundary, the right's Nk
  -- boundary): left [X], right [Y ★-embedded, X]; X joined through the
  -- global pair (αᴸ, αᴿ); Y keeps a phantom right-only center name
  WXL : World ΔLᵢ ΔRX
  WXL = world (X⊑X ∷ X⊑X ∷ []) (skip (keep []↪)) (keep (keep []↪))
          ((0 , 1) ∷ []) []

  WXL★ : World★ ΔLᵢ ΔRX
  WXL★ = w★ WXL (true ∷ false ∷ [])

  WXL-ro : RightOnly WXL 0
  WXL-ro (_ , here) ()
  WXL-ro (_ , there ()) _

  WXL-starok : ∀ {k} → (true ∷ false ∷ []) ‼ k ≡ true → StarOK WXL k
  WXL-starok {zero} refl = 0 , here , r-here , WXL-ro
  WXL-starok {suc zero} ()
  WXL-starok {suc (suc k)} ()

  WXL★-wf : WfWorld★ WXL★
  WXL★-wf = wf★ (wf-world (right-only (both (inj₁ here⇔) joint[])) agree
                  (namedᴸ-≤1 WXL ≤1-∷[]) uniqᴿ)
              WXL-starok
    where
    agree : ∀ {α β} → Paired WXL α β → Agree WXL α β
    agree (inj₁ here⇔) = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())
    uniqᴿ : NamedUniqueᴿ WXL
    uniqᴿ _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
    uniqᴿ _ _ _ (inj₁ here⇔) (inj₁ (there⇔ ()))
    uniqᴿ _ _ _ (inj₁ (there⇔ ())) _
    uniqᴿ _ _ _ (inj₂ ()) _
    uniqᴿ _ _ _ _ (inj₂ ())

  -- the fresh left X joins the right X (paired), not the right Y
  WXL-fresh : ∀ {X X′ α β}
    → ΔLᵢ ∋ᵗ X := α → ΔRX ∋ᵗ X′ := β
    → (Joins WXL X X′ → Paired (wᵇ WiY★) α β)
      × (Paired (wᵇ WiY★) α β → Joins WXL X X′)
  WXL-fresh here here =
    (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
  WXL-fresh here (there here) = (λ _ → inj₁ here⇔) , (λ _ → refl)
  WXL-fresh here (there (there ()))
  WXL-fresh (there ()) _

  IntX : Interior (Wk ⊕ʳ X⊑X ^ 0) Θ₀ ΘX WXL
  IntX = record
    { int-left   = int₀
    ; int-right  = bindX-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ a b _ → WXL-fresh a b
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ
        { (_ , here) refl here → here
        ; (_ , there here) () _
        ; (_ , there (there ())) _ _
        }
    }

  IntX★ : Interior★ WiY★ Θ₀ ΘX WXL★
  IntX★ = int★ IntX λ
    { (_ , here) refl → refl
    ; (_ , there here) ()
    ; (_ , there (there ())) _
    }

  ConvX : ConversionInterior (Wk ⊕ʳ X⊑X ^ 0) Θ₀ ΘX WXL
  ConvX = record
    { conv-left       = conv₀
    ; conv-right      = bindX-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ a b _ → WXL-fresh a b
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ
        { here here here → here
        ; here (there ()) _
        ; (there here) (there ()) _
        ; (there (there ())) _ _
        }
    }

  ConvX★ : ConversionInterior★ WiY★ Θ₀ ΘX WXL★
  ConvX★ = conv★ ConvX
    (λ { here here → refl ; here (there ()) ; (there here) (there ())
       ; (there (there ())) _ })
    WXL-starok

  -- cK = ∀Y.(id(Y) → id(Y))  ⊑  cId = id(Y) → id(Y), right Y ★-embedded:
  -- the left-only ∀ is opened at X⊑★ (conv-∀⊑), id(Y) ⊑ id(★)
  cK⊑cId : ConvImp WXL★ cK cId
  cK⊑cId =
    conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑
      (cId⊑cId ⟦ X⊑★ here ⟧)))

  -- the interior pair: Λ⊑ (left-only Y at X⊑★) over λ⊑λ at Y ⊑ ★
  ΛI⊑idX : ∀ {Δ Δ′} {W : World★ Δ Δ′}
    → (x : ` 0 ⊑ᵂ★⟨ W ⊕ᴸ★ ⟩ ` 0)
    → underΛ Δ ⊢ᵗ ` 0 → Δ′ ⊢ᵗ ` 0
    → (q : ∀X⇒X ⊑ᵂ★⟨ W ⟩ (` 0 ⇒ ` 0))
    → W ∣ [] ⊢ I ⊑ idX ∶ q
  ΛI⊑idX x wl wr q =
    Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (ƛ⊑ƛ {pA = x} {pB = x} wl wr (x⊑x Zʷ)) q

  idX-body : WXL★ ∣ [] ⊢ I ⊑ idX ∶ ⟦ ty★ (∀id⊑★ WXL★) ⟧
  idX-body = ΛI⊑idX ⟦ X⊑★ here ⟧ tf tf ⟦ ty★ (∀id⊑★ WXL★) ⟧

  VL⊑Nk : WiY★ ∣ [] ⊢ VL ⊑ Nk ∶ ⟦ ty★ (∀id⊑★ WiY★) ⟧
  VL⊑Nk =
    ⟪⟫⊑⟪⟫ IntX★ WXL★-wf idX-body bVL bNR (WXL★ , ConvX★ , cK⊑cId)
      ⟦ ty★ (∀id⊑★ WiY★) ⟧

  VL⊑Rarg₃ : Wk★ ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk★
  VL⊑Rarg₃ =
    ⊑cast (⊑⟪⟫ IntY★ WiY★-wf VL⊑Nk bOutK (∀id⊑★ Wk★))
      id★↦ᴿk-ty (∀id⊑★ Wk★)

  lk₁⊑rk₃ : Wk★ ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk★
  lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk★} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

  ---------------------------------------------------------------------
  -- (LK₁, RK₄) and (VL, RF) after the right's Merge

  -- (a) THE NATURAL DERIVATION: ⟪⟫⊑⟪⟫ at (+X^α) ∥ (+Y^β, +X^α), interior
  -- world WXL★ again, interior index ∀Y.Y→Y ⊑ ★→★.  Its conversion
  -- premise `cK ⊑ −Y → +Y` needs the MIRROR clauses (§2).
  IntXΘ₂ : Interior Wk Θ₀ Θ₂ WXL
  IntXΘ₂ = record
    { int-left   = int₀
    ; int-right  = int-Θ₂
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ a b _ → WXL-fresh a b
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ
        { (_ , here) () _ ; (_ , there here) () _
        ; (_ , there (there ())) _ _ }
    }

  IntXΘ₂★ : Interior★ Wk★ Θ₀ Θ₂ WXL★
  IntXΘ₂★ = int★ IntXΘ₂ λ
    { (_ , here) () ; (_ , there here) () ; (_ , there (there ())) _ }

  convΘ₂ : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ᶜ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  convΘ₂ = conversion (conv-bind (_ , there here)
    (conv-bind (_ , here) conv[] fresh[] ins-here)
    (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

  ConvXΘ₂ : ConversionInterior Wk Θ₀ Θ₂ WXL
  ConvXΘ₂ = record
    { conv-left       = conv₀
    ; conv-right      = convΘ₂
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ a b _ → WXL-fresh a b
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  ConvXΘ₂★ : ConversionInterior★ Wk★ Θ₀ Θ₂ WXL★
  ConvXΘ₂★ = conv★ ConvXΘ₂ (λ _ ()) WXL-starok

  -- cK = ∀Y.(id(Y) → id(Y))  ⊑  revX = −Y → +Y (Y ★-embedded): conv-∀⊑,
  -- then the mirrors id(Y) ⊑ −Y and id(Y) ⊑ +Y at Y ⊑ ★
  cK⊑revX : ConvImp WXL★ cK revX
  cK⊑revX =
    conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑
      (conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
        (conv-tail⊑tail (conv-id⊑seal★ ⟦ X⊑★ here ⟧ refl))
        (conv-id⊑unseal★ ⟦ X⊑★ here ⟧ refl))))))

  VL⊑Bm-nat : Wk★ ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk★
  VL⊑Bm-nat =
    ⟪⟫⊑⟪⟫ IntXΘ₂★ WXL★-wf idX-body bVL bBm (WXL★ , ConvXΘ₂★ , cK⊑revX)
      (∀id⊑★ Wk★)

  -- (b) ⊑⟪⟫ FIRST (no conversion premise, no mirror clause): the merged
  -- right boundary, Y ★-embedded and X right-only; then ⟪⟫⊑ peels VL's
  -- boundary, whose fresh X rejoins the right X through (αᴸ, αᴿ)
  WiR★ : World★ ΔL ΔRX
  WiR★ = w★ WiR (true ∷ false ∷ [])

  IntR★ : Interior★ Wk★ [] Θ₂ WiR★
  IntR★ = int★ IntK-Θ₂ λ
    { (_ , here) () ; (_ , there here) () ; (_ , there (there ())) _ }

  WiR★-wf : WfWorld★ WiR★
  WiR★-wf = wf★ (wf-world (right-only (right-only joint[])) agree
                  (namedᴸ-≤1 WiR ≤1-[]) uniqᴿ)
              star
    where
    agree : ∀ {α β} → Paired WiR α β → Agree WiR α β
    agree (inj₁ here⇔) = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())
    uniqᴿ : NamedUniqueᴿ WiR
    uniqᴿ (_ , ()) _ _ _ _
    star : ∀ {k} → (true ∷ false ∷ []) ‼ k ≡ true → StarOK WiR k
    star {zero} refl = 0 , here , r-here , λ { (_ , ()) }
    star {suc zero} ()
    star {suc (suc k)} ()

  IntL : Interior WiR Θ₀ [] WXL
  IntL = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ a b _ → WXL-fresh a b
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ
        { (_ , here) refl m → m ; (_ , there here) refl m → m
        ; (_ , there (there ())) _ _ }
    }

  IntL★ : Interior★ WiR★ Θ₀ [] WXL★
  IntL★ = int★ IntL λ _ → λ { refl → refl }

  VL⊑idX : WiR★ ∣ [] ⊢ VL ⊑ idX ∶ ⟦ ty★ (∀id⊑★ WiR★) ⟧
  VL⊑idX = ⟪⟫⊑ IntL★ WXL★-wf idX-body bVL ⟦ ty★ (∀id⊑★ WiR★) ⟧

  VL⊑Bm : Wk★ ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk★
  VL⊑Bm = ⊑⟪⟫ IntR★ WiR★-wf VL⊑idX bBm (∀id⊑★ Wk★)

  VL⊑RF : Wk★ ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk★
  VL⊑RF = ⊑cast VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk★)

  VL⊑RF-nat : Wk★ ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk★
  VL⊑RF-nat = ⊑cast VL⊑Bm-nat id★↦ᴿk-ty (∀id⊑★ Wk★)

  lk₁⊑rk₄ : Wk★ ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk★
  lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk★} tf tf (x⊑x Zʷ)) VL⊑RF

  ---------------------------------------------------------------------
  -- The obligations the relation before D26 refuted on K, met here
  -- with no opening (the outer worlds have no right names, so σ = []
  -- and the real evolution of the base world is the evolution)

  Wk★-wf : WfWorld★ Wk★
  Wk★-wf = wf★ Wk-wf λ ()

  sim-K★ :
    ∃[ N′ ] Σ[ r′ ∈ ΔL ⊢ RK₁ -→* N′ ]
      Σ[ W′ ∈ World★ ΔL (applyˢ (allocs r′) ΔL) ]
        (Wk1 ⟿[ none ∷ [] ∣ allocs r′ ] wᵇ W′) × WfWorld★ W′
        × Σ[ q ∈ ∀X⇒X ⊑ᵂ★⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ N′ ∶ q)
  sim-K★ =
    RF , (st₁ then st₂ then st₃ then st₄ then done) , Wk★ ,
    ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done)))) ,
    Wk★-wf , ∀id⊑★ Wk★ , VL⊑RF

  simBack-K-merge★ :
    Σ[ r ∈ ΔL ⊢ VL -→* VL ] Σ[ r″ ∈ ΔRk ⊢ RF -→* RF ]
      Σ[ W′ ∈ World★ (applyˢ (allocs r) ΔL)
                     (applyˢ (allocs (stM then r″)) ΔRk) ]
        (Wk ⟿[ allocs r ∣ allocs (stM then r″) ] wᵇ W′) × WfWorld★ W′
        × Σ[ q ∈ ∀X⇒X ⊑ᵂ★⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ RF ∶ q)
  simBack-K-merge★ =
    done , done , Wk★ , ev-noneᴿ ev-done , Wk★-wf , _ , VL⊑RF

  dgg1-K★ :
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RK -→* V′ ] Value V′
      × Σ[ W′ ∈ World★ ΔL (applyˢ (allocs r′) empty) ]
          Σ[ q ∈ ∀X⇒X ⊑ᵂ★⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ V′ ∶ q)
  dgg1-K★ =
    RF , (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF ,
    Wk★ , ∀id⊑★ Wk★ , VL⊑RF

------------------------------------------------------------------------
-- 5. The corpus blocks that needed an opening
------------------------------------------------------------------------

module Corpus where
  open import examples.TypeCheck using (tc; tf)
  open import examples.ImprecisionExamples using (L1)
  open import examples.CambridgeExamples using (I; C2-L; C12-L)
  open import examples.TermImprecisionExamples
    using (idX; revX; Θ₀; L1′; ΔL; ΔR; ΔRᵢ; ∀X⇒X; int₀; conv₀; W₁; Wᵢ₁;
           Wᵢ₁-int; Wᵢ₁-conv; Wᵢ₁-wf; bL-ty; bR-ty; νL-ty; W₃; R3′;
           int-ro₃)
  open import examples.TermImprecisionRebaseExamples
    using (id★↦ᴿ-ty; Cg-R₂; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty; I★genI; I★gen;
           C2-L-ν-ty; genI-ty; C12-R₂; C12-ν₂-ty; genIᴿ-ty; Wν₂; Wν₂-conv;
           unbind₀-int)
  open import examples.TermImprecisionRegressionExamples using (Θ₀-int)
  open import proof.DGG.notes.ForallBoundaryFixes
    using (B⟨id⟩; L3c₁; L3c₂; R3c₃; νLₗ-ty; W₂d; Wᵢ₂d; Wᵢ₂d-int;
           Wᵢ₂d-conv; Wᵢ₂d-wf; bL₂-ty; Bα; V2; L2c₂; R2c₄; R2c₅; N; Nu;
           Bin; N₀; Θ₁; Θm; ΔR2; ΞR; W4; unb-int; bind₁-int; bind₁-conv;
           Θm-int; Θm-conv; bBᴿ; bUᴿ; bMᴿ; tagNᴿ; tagN₀ᴿ; bOut₄; bOut₅;
           id★↦ᴿ₂-ty)

  ∀id⊑∀id : ∀ {Δ Δ′} {W : World★ Δ Δ′}
    → `∀ (` 0 ⇒ ` 0) ⊑ᵂ★⟨ W ⟩ `∀ (` 0 ⇒ ` 0)
  ∀id⊑∀id = ⟦ ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X) ⟧

  revX⊑revX★ : ∀ {Δ Δ′} {W : World★ Δ Δ′}
    → Joins (wᵇ W) 0 0 → ConvImp W revX revX
  revX⊑revX★ j =
    conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
      (conv-tail⊑tail (conv-seal⊑seal j)) (conv-unseal⊑unseal j)))

  ff1 : ∀ {A : Set} {k} → (false ∷ []) ‼ k ≡ true → A
  ff1 {k = k} e = ⊥-elim (ff‼ 1 {k} e)

  ---------------------------------------------------------------------
  -- THE CORE: a left Λ against a right Inst boundary [+X^αᴿ] λx:X.x,
  -- by the plain ⊑⟪⟫ (X ★-embedded) over Λ⊑ (X⊑★) over λ⊑λ.  Any
  -- outer world W with no right names; the interior world W ⊕ʳ X⊑X ^ 0
  -- (a phantom right-only center name for X).

  core★ : ∀ {Δ} {W : World Δ ΔR} {γ : CtxImp (w★ W [])}
    → Interior W [] Θ₀ (W ⊕ʳ X⊑X ^ 0)
    → WfWorld (W ⊕ʳ X⊑X ^ 0)
    → RightOnly (W ⊕ʳ X⊑X ^ 0) 0
    → w★ W [] ∣ γ ⊢ I ⊑ idX ⟪ Θ₀ , revX ⟫ ∶ ∀id⊑★ (w★ W [])
  core★ {W = W} int wf ro =
    ⊑⟪⟫ {Wᵢ = w★ (W ⊕ʳ X⊑X ^ 0) (true ∷ [])}
      (int★ int λ { (_ , here) () ; (_ , there ()) _ })
      (wf★ wf star)
      (Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
        (ƛ⊑ƛ {pA = ⟦ X⊑★ here ⟧} {pB = ⟦ X⊑★ here ⟧}
          (wf-var (_ , here)) tf (x⊑x Zʷ))
        ⟦ ty★ (∀id⊑★ (w★ (W ⊕ʳ X⊑X ^ 0) (true ∷ []))) ⟧)
      bR-ty (∀id⊑★ (w★ W []))
    where
    star : ∀ {k} → (true ∷ []) ‼ k ≡ true → StarOK (W ⊕ʳ X⊑X ^ 0) k
    star {zero} refl = 0 , here , r-here , ro
    star {suc k} ()

  W₃★ W₁★ : _
  W₃★ = w★ W₃ []
  W₁★ = w★ W₁ []

  W₃ʳ-wf : WfWorld (W₃ ⊕ʳ X⊑X ^ 0)
  W₃ʳ-wf = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 (W₃ ⊕ʳ X⊑X ^ 0) ≤1-[]) (namedᴿ-≤1 (W₃ ⊕ʳ X⊑X ^ 0) ≤1-∷[])

  W₃ʳ-ro : RightOnly (W₃ ⊕ʳ X⊑X ^ 0) 0
  W₃ʳ-ro (_ , ())

  int-ro₁ : Interior W₁ [] Θ₀ (W₁ ⊕ʳ X⊑X ^ 0)
  int-ro₁ = record
    { int-left   = interior changes[]
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  -- αᴿ is paired (globally) with the left's store rep. var αᴸ, but no
  -- left NAME denotes αᴸ here, so X stays right-only and may go to ★
  W₁ʳ-wf : WfWorld (W₁ ⊕ʳ X⊑X ^ 0)
  W₁ʳ-wf = wf-world (right-only joint[]) agree
    (namedᴸ-≤1 (W₁ ⊕ʳ X⊑X ^ 0) ≤1-[]) (namedᴿ-≤1 (W₁ ⊕ʳ X⊑X ^ 0) ≤1-∷[])
    where
    agree : ∀ {α β} → Paired (W₁ ⊕ʳ X⊑X ^ 0) α β
      → Agree (W₁ ⊕ʳ X⊑X ^ 0) α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  W₁ʳ-ro : RightOnly (W₁ ⊕ʳ X⊑X ^ 0) 0
  W₁ʳ-ro (_ , ())

  ---------------------------------------------------------------------
  -- P3 = Ch (the block after the right's Inst, TyBeta, Beta)

  p3★ : W₃★ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
  p3★ =
    ·⊑· (ν⊑ (⊑cast (core★ int-ro₃ W₃ʳ-wf W₃ʳ-ro) id★↦ᴿ-ty (∀id⊑★ W₃★))
             ℕ⊑★ νL-ty (⇒★ ℕ⊑★ ℕ⊑★))
        five⊑★

  ch-x0★ : W₃★ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
  ch-x0★ = p3★

  ---------------------------------------------------------------------
  -- L3c: before and after the left's TyBeta of copy 1

  copy2★ : ∀ {Δ} {W : World Δ ΔR}
    → Interior W [] Θ₀ (W ⊕ʳ X⊑X ^ 0) → WfWorld (W ⊕ʳ X⊑X ^ 0)
    → RightOnly (W ⊕ʳ X⊑X ^ 0) 0
    → w★ W [] ∣ ctx-imp `ℕ ★ ℕ⊑★ ∷ [] ⊢ I ⊑ B⟨id⟩ ∶ ∀id⊑★ (w★ W [])
  copy2★ {W = W} int wf ro =
    ⊑cast (core★ int wf ro) id★↦ᴿ-ty (∀id⊑★ (w★ W []))

  l3c-pre★ : W₃★ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃★
  l3c-pre★ =
    ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2★ int-ro₃ W₃ʳ-wf W₃ʳ-ro)) p3★

  Wᵢ₁★ : World★ _ _
  Wᵢ₁★ = w★ Wᵢ₁ (false ∷ [])

  copy1★ : W₁★ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
  copy1★ =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ {Wᵢ = Wᵢ₁★} (int★ Wᵢ₁-int λ { (_ , here) () ; (_ , there ()) _ })
          (wf★ Wᵢ₁-wf (λ {k} → ff1 {k = k}))
          (ƛ⊑ƛ {pA = ⟦ X⊑X ⟧} {pB = ⟦ X⊑X ⟧} tf tf (x⊑x Zʷ))
          bL-ty bR-ty
          (Wᵢ₁★ , conv★ Wᵢ₁-conv (λ _ ()) (λ {k} → ff1 {k = k}) ,
           revX⊑revX★ refl)
          (⇒★ ℕ⊑★ ℕ⊑★))
        id★↦ᴿ-ty (⇒★ ℕ⊑★ ℕ⊑★))
      five⊑★

  l3c-post★ : W₁★ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ ∀id⊑★ W₁★
  l3c-post★ =
    ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2★ int-ro₁ W₁ʳ-wf W₁ʳ-ro)) copy1★

  ---------------------------------------------------------------------
  -- L3d: both copies instantiated on the left

  l3d-before★ : W₁★ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
  l3d-before★ =
    ·⊑· (ν⊑ (⊑cast (core★ int-ro₁ W₁ʳ-wf W₁ʳ-ro) id★↦ᴿ-ty (∀id⊑★ W₁★))
             ℕ⊑★ νLₗ-ty (⇒★ ℕ⊑★ ℕ⊑★))
        five⊑★

  W₂d★ Wᵢ₂d★ : World★ _ _
  W₂d★  = w★ W₂d []
  Wᵢ₂d★ = w★ Wᵢ₂d (false ∷ [])

  l3d-after★ : W₂d★ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
  l3d-after★ =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ {Wᵢ = Wᵢ₂d★}
          (int★ Wᵢ₂d-int λ { (_ , here) () ; (_ , there ()) _ })
          (wf★ Wᵢ₂d-wf (λ {k} → ff1 {k = k}))
          (ƛ⊑ƛ {pA = ⟦ X⊑X ⟧} {pB = ⟦ X⊑X ⟧} tf tf (x⊑x Zʷ))
          bL₂-ty bR-ty
          (Wᵢ₂d★ , conv★ Wᵢ₂d-conv (λ _ ()) (λ {k} → ff1 {k = k}) ,
           revX⊑revX★ refl)
          (⇒★ ℕ⊑★ ℕ⊑★))
        id★↦ᴿ-ty (⇒★ ℕ⊑★ ℕ⊑★))
      five⊑★

  ---------------------------------------------------------------------
  -- Cg: the right's Inst boundary over a gen wrapper; left a Λ

  Wi3★ : World★ empty ΔRᵢ
  Wi3★ = w★ (W₃ ⊕ʳ X⊑X ^ 0) (true ∷ [])

  int3★ : Interior★ W₃★ [] Θ₀ Wi3★
  int3★ = int★ int-ro₃ λ { (_ , here) () ; (_ , there ()) _ }

  Wi3★-wf : WfWorld★ Wi3★
  Wi3★-wf = wf★ W₃ʳ-wf star
    where
    star : ∀ {k} → (true ∷ []) ‼ k ≡ true → StarOK (W₃ ⊕ʳ X⊑X ^ 0) k
    star {zero} refl = 0 , here , r-here , W₃ʳ-ro
    star {suc k} ()

  -- inside the right's −X: the left's Y left-only at X⊑★, no right name
  Wu : World (underΛ empty) ΔR
  Wu = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] []

  IntU : Interior ((W₃ ⊕ʳ X⊑X ^ 0) ⊕ᴸ) [] (unbind 0 0 ∷ []) Wu
  IntU = record
    { int-left   = interior changes[]
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) refl here → here ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  Wu★-wf : WfWorld★ (w★ Wu [])
  Wu★-wf = wf★ (wf-world (left-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
                  (namedᴸ-≤1 Wu ≤1-∷[]) (namedᴿ-≤1 Wu ≤1-[]))
             (λ ())

  X⇒X⊑★⇒★ : ∀ {Δ Δ′} {W : World★ Δ Δ′} {A′}
    → ` 0 ⊑ᵂ★⟨ W ⟩ A′ → (` 0 ⇒ ` 0) ⊑ᵂ★⟨ W ⟩ (A′ ⇒ A′)
  X⇒X⊑★⇒★ x = ⇒★ x x

  cg-body : Wi3★ ∣ [] ⊢ I ⊑ I★gen ∶ ⟦ ty★ (∀id⊑★ Wi3★) ⟧
  cg-body =
    Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (⊑cast {A = ` 0 ⇒ ` 0}
        (⊑⟪⟫ {Wᵢ = w★ Wu []} (int★ IntU λ { (_ , ()) _ }) Wu★-wf
          (ƛ⊑ƛ {pA = ⟦ X⊑★ here ⟧} {pB = ⟦ X⊑★ here ⟧} tf wf-★ (x⊑x Zʷ))
          I★⁻ᴿ-ty (X⇒X⊑★⇒★ ⟦ X⊑★ here ⟧))
        tagᴿ-ty ⟦ ⇒⊑⇒ (X⊑★ here) (X⊑★ here) ⟧)
      ⟦ ty★ (∀id⊑★ Wi3★) ⟧

  cg-x0★ : W₃★ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
  cg-x0★ =
    ·⊑·
      (ν⊑ (⊑cast (⊑⟪⟫ int3★ Wi3★-wf cg-body Bg-ty (∀id⊑★ W₃★))
                 id★↦ᴿ-ty (∀id⊑★ W₃★))
          ℕ⊑★ νL-ty (⇒★ ℕ⊑★ ℕ⊑★))
      five⊑★

  ---------------------------------------------------------------------
  -- C2: the LEFT ∀-value is a gen cast `(λx:★.x)⟨gen X.(X! → X?)⟩`, not
  -- a Λ.  No opening is needed: cast⊑cast relates it to the right's
  -- `(…)⟨X! → X?⟩` (coercions are compared only through their types:
  -- ∀X.X→X ⊑ X→X with X ★-embedded is ∀X.X→X ⊑ ★→★), over a plain
  -- ⊑⟪⟫ for the right's −X

  IntN : Interior (W₃ ⊕ʳ X⊑X ^ 0) [] (unbind 0 0 ∷ []) W₃
  IntN = record
    { int-left   = interior changes[]
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  W₃★-wf : WfWorld★ W₃★
  W₃★-wf = wf★ (wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
                 (namedᴸ-≤1 W₃ ≤1-[]) (namedᴿ-≤1 W₃ ≤1-[]))
             (λ ())

  c2-body : Wi3★ ∣ [] ⊢ I★genI ⊑ I★gen ∶ ⟦ ty★ (∀id⊑★ Wi3★) ⟧
  c2-body =
    cast⊑cast
      (⊑⟪⟫ {Wᵢ = W₃★} (int★ IntN λ { (_ , ()) _ }) W₃★-wf
        (ƛ⊑ƛ {pA = ★⊑★′} {pB = ★⊑★′} tf tf (x⊑x Zʷ))
        I★⁻ᴿ-ty (⇒★ ★⊑★′ ★⊑★′))
      genI-ty tagᴿ-ty ⟦ ty★ (∀id⊑★ Wi3★) ⟧

  c2-x0★ : W₃★ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
  c2-x0★ =
    ·⊑·
      (ν⊑ (⊑cast (⊑⟪⟫ int3★ Wi3★-wf c2-body Bg-ty (∀id⊑★ W₃★))
                 id★↦ᴿ-ty (∀id⊑★ W₃★))
          ℕ⊑★ C2-L-ν-ty (⇒★ ℕ⊑★ ℕ⊑★))
      five⊑★

  ---------------------------------------------------------------------
  -- C12: ν⊑ν around the core

  c12-x0★ : W₃★ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ℕ⊑ℕ
  c12-x0★ =
    ·⊑·
      (ν⊑ν
        (⊑cast
          (⊑cast (core★ int-ro₃ W₃ʳ-wf W₃ʳ-ro) id★↦ᴿ-ty (∀id⊑★ W₃★))
          genIᴿ-ty ∀id⊑∀id)
        ℕ⊑ℕ νL-ty C12-ν₂-ty
        (w★ Wν₂ (false ∷ []) , conv★ Wν₂-conv (λ _ ()) (λ {k} → ff1 {k = k}) ,
         revX⊑revX★ refl)
        (⇒★ ℕ⊑ℕ ℕ⊑ℕ))
      (κ⊑κ lit-$ ℕ⊑ℕ)

  ---------------------------------------------------------------------
  -- R2c: the right's Merge inside its Inst boundary, against the left's
  -- gen-cast ∀-value V2 (αᴸ:=★).  Before and after the Merge, with the
  -- plain rules (no InstExpand, no ∀⊑⟪+⟫ᵃ)

  W4★ : World★ ΔR ΔR2
  W4★ = w★ W4 []

  Wi4★ : World★ ΔR (ΞR ∣ (0 ∷ []))
  Wi4★ = w★ (W4 ⊕ʳ X⊑X ^ 0) (true ∷ [])

  Int4 : Interior W4 [] Θ₀ (W4 ⊕ʳ X⊑X ^ 0)
  Int4 = record
    { int-left   = interior changes[]
    ; int-right  = Θ₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  Int4★ : Interior★ W4★ [] Θ₀ Wi4★
  Int4★ = int★ Int4 λ { (_ , here) () ; (_ , there ()) _ }

  Wi4★-wf : WfWorld★ Wi4★
  Wi4★-wf = wf★ (wf-world (right-only joint[]) agree
                  (namedᴸ-≤1 (W4 ⊕ʳ X⊑X ^ 0) ≤1-[])
                  (namedᴿ-≤1 (W4 ⊕ʳ X⊑X ^ 0) ≤1-∷[]))
              star
    where
    agree : ∀ {α β} → Paired (W4 ⊕ʳ X⊑X ^ 0) α β
      → Agree (W4 ⊕ʳ X⊑X ^ 0) α β
    agree (inj₁ here⇔) = rep-rep r-here (r-there r-here) ★⊑★
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())
    star : ∀ {k} → (true ∷ []) ‼ k ≡ true → StarOK (W4 ⊕ʳ X⊑X ^ 0) k
    star {zero} refl = 0 , here , r-here , λ { (_ , ()) }
    star {suc k} ()

  -- inside the right's −Y: no names
  W4u : World ΔR (ΞR ∣ [])
  W4u = world [] []↪ []↪ ((0 , 1) ∷ []) []

  IntU4 : Interior (W4 ⊕ʳ X⊑X ^ 0) [] (unbind 0 0 ∷ []) W4u
  IntU4 = record
    { int-left   = interior changes[]
    ; int-right  = unb-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    }

  W4u★-wf : WfWorld★ (w★ W4u [])
  W4u★-wf = wf★ (wf-world joint[] agree (namedᴸ-≤1 W4u ≤1-[])
                  (namedᴿ-≤1 W4u ≤1-[]))
              (λ ())
    where
    agree : ∀ {α β} → Paired W4u α β → Agree W4u α β
    agree (inj₁ here⇔) = rep-rep r-here (r-there r-here) ★⊑★
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  -- inside the two `+X^α` (left Θ₀ over αᴸ, right Θ₁ over αᴿ): X joined
  Wb : World ΔRᵢ (ΞR ∣ (1 ∷ []))
  Wb = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 1) ∷ []) []

  Wb★-wf : WfWorld★ (w★ Wb (false ∷ []))
  Wb★-wf = wf★ (wf-world (both (inj₁ here⇔) joint[]) agree
                 (namedᴸ-≤1 Wb ≤1-∷[]) (namedᴿ-≤1 Wb ≤1-∷[]))
             (λ {k} → ff1 {k = k})
    where
    agree : ∀ {α β} → Paired Wb α β → Agree Wb α β
    agree (inj₁ here⇔) = rep-rep r-here (r-there r-here) ★⊑★
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  IntB : Interior W4u Θ₀ Θ₁ Wb
  IntB = record
    { int-left   = int₀
    ; int-right  = bind₁-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  ConvB : ConversionInterior W4u Θ₀ Θ₁ Wb
  ConvB = record
    { conv-left       = conv₀
    ; conv-right      = bind₁-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  ★⇒★⊑ : ∀ {Δ Δ′} {W : World★ Δ Δ′} → (★ ⇒ ★) ⊑ᵂ★⟨ W ⟩ (★ ⇒ ★)
  ★⇒★⊑ = ⇒★ ★⊑★′ ★⊑★′

  Bα⊑Bin : w★ W4u [] ∣ [] ⊢ Bα ⊑ Bin ∶ ★⇒★⊑
  Bα⊑Bin =
    ⟪⟫⊑⟪⟫ {Wᵢ = w★ Wb (false ∷ [])}
      (int★ IntB λ { (_ , here) () ; (_ , there ()) _ }) Wb★-wf
      (ƛ⊑ƛ {pA = ⟦ X⊑X ⟧} {pB = ⟦ X⊑X ⟧} tf tf (x⊑x Zʷ)) bR-ty bBᴿ
      (w★ Wb (false ∷ []) , conv★ ConvB (λ _ ()) (λ {k} → ff1 {k = k}) ,
       revX⊑revX★ refl)
      ★⇒★⊑

  Bα⊑Nu : Wi4★ ∣ [] ⊢ Bα ⊑ Nu ∶ ★⇒★⊑
  Bα⊑Nu =
    ⊑⟪⟫ {Wᵢ = w★ W4u []} (int★ IntU4 λ { (_ , ()) _ }) W4u★-wf Bα⊑Bin bUᴿ ★⇒★⊑

  genI₂-ty : CastTy ΔR [] _ (★ ⇒ ★) ∀X⇒X
  genI₂-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = V2})))

  V2⊑N : Wi4★ ∣ [] ⊢ V2 ⊑ N ∶ ⟦ ty★ (∀id⊑★ Wi4★) ⟧
  V2⊑N = cast⊑cast Bα⊑Nu genI₂-ty tagNᴿ ⟦ ty★ (∀id⊑★ Wi4★) ⟧

  r2c-pre★ : W4★ ∣ [] ⊢ L2c₂ ⊑ R2c₄ ∶ ∀id⊑★ W4★
  r2c-pre★ =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4★} tf tf (x⊑x Zʷ))
      (⊑cast (⊑⟪⟫ Int4★ Wi4★-wf V2⊑N bOut₄ (∀id⊑★ W4★))
             id★↦ᴿ₂-ty (∀id⊑★ W4★))

  -- after the right's Merge: the merged right boundary (−Y, +X^αᴿ)
  -- against the left's +X^αᴸ; Y (★-embedded) is removed, X joined
  IntM : Interior (W4 ⊕ʳ X⊑X ^ 0) Θ₀ Θm Wb
  IntM = record
    { int-left   = int₀
    ; int-right  = Θm-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    }

  -- the conversion contexts keep Y (Θm's unbind is skipped): left [X],
  -- right [X, Y], Y ★-embedded (it continues from the exterior)
  Wcm : World ΔRᵢ (ΞR ∣ (1 ∷ 0 ∷ []))
  Wcm = world (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))
          ((0 , 1) ∷ []) []

  ConvM : ConversionInterior (W4 ⊕ʳ X⊑X ^ 0) Θ₀ Θm Wcm
  ConvM = record
    { conv-left       = conv₀
    ; conv-right      = Θm-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
        ; here (there (there ())) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ
        { (there here) here here → there here
        ; here (there ()) _
        ; (there here) (there ()) _
        ; (there (there ())) _ _
        }
    }

  ConvM★ : ConversionInterior★ Wi4★ Θ₀ Θm (w★ Wcm (false ∷ true ∷ []))
  ConvM★ = conv★ ConvM
    (λ { (there here) here → refl ; here (there ()) ; (there here) (there ())
       ; (there (there ())) _ })
    ok
    where
    ok : ∀ {k} → (false ∷ true ∷ []) ‼ k ≡ true → StarOK Wcm k
    ok {zero} ()
    ok {suc zero} refl =
      0 , there here , r-here , λ { (_ , here) () ; (_ , there ()) _ }
    ok {suc (suc k)} ()

  Bα⊑Bm : Wi4★ ∣ [] ⊢ Bα ⊑ idX ⟪ Θm , revX ⟫ ∶ ★⇒★⊑
  Bα⊑Bm =
    ⟪⟫⊑⟪⟫ {Wᵢ = w★ Wb (false ∷ [])}
      (int★ IntM λ { (_ , here) () ; (_ , there ()) _ }) Wb★-wf
      (ƛ⊑ƛ {pA = ⟦ X⊑X ⟧} {pB = ⟦ X⊑X ⟧} tf tf (x⊑x Zʷ)) bR-ty bMᴿ
      (w★ Wcm (false ∷ true ∷ []) , ConvM★ , revX⊑revX★ refl)
      ★⇒★⊑

  V2⊑N₀ : Wi4★ ∣ [] ⊢ V2 ⊑ N₀ ∶ ⟦ ty★ (∀id⊑★ Wi4★) ⟧
  V2⊑N₀ = cast⊑cast Bα⊑Bm genI₂-ty tagN₀ᴿ ⟦ ty★ (∀id⊑★ Wi4★) ⟧

  r2c-post★ : W4★ ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4★
  r2c-post★ =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4★} tf tf (x⊑x Zʷ))
      (⊑cast (⊑⟪⟫ Int4★ Wi4★-wf V2⊑N₀ bOut₅ (∀id⊑★ W4★))
             id★↦ᴿ₂-ty (∀id⊑★ W4★))

------------------------------------------------------------------------
-- 6. Risks
------------------------------------------------------------------------

module Risks where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.TermImprecisionExamples
    using (Θ₀; ΔR; ΔRᵢ; int₀; W₃; int-ro₃)
  open import examples.TermImprecisionRebaseExamples
    using (id★↦; id★↦ᴿ-ty)
  open import examples.TermImprecisionRegressionExamples using (justStep)
  open import proof.TypeSafety.Determinism using (det)
  open import proof.TypeSafety.Irreducible using (irreducible)
  open Corpus using (Wi3★; int3★; Wi3★-wf; W₃★; IntN; W₃★-wf)

  ---------------------------------------------------------------------
  -- (a) OVER-RELATING: a counterexample to DGG part 1 for the
  -- ★-embedded relation.
  --
  --   L  (λx:ℕ. x) 5
  --   R  ((ΛY. λx:Y. x⟨Y!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  --
  -- After the right's Inst and TyBeta, its function is the boundary
  -- `[+Y^β] (λx:Y. x⟨Y!⟩) ⟨−Y → id(★)⟩`, β:=★.  With Y ★-embedded,
  -- `λx:ℕ.x ⊑ λx:Y.x⟨Y!⟩` holds at `ℕ ⊑ Y` read as `ℕ ⊑ ★`.  The left
  -- reaches 5; the right tags the sealed 5 with the boundary's own name
  -- Y, which cannot leave the boundary, and the outer check blames
  -- (TagUntagBad-⟪⟫).

  5★ : Term
  5★ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  ℕ? : Coercion
  ℕ? = `ℕ ？ 0

  tagY : Term
  tagY = ` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩

  VY : Term
  VY = Λ (ƛ (` 0) ∙ tagY)

  revY★ : Conv
  revY★ = reveal 0 (` 0 ⇒ ★)

  BdY : Term
  BdY = (ƛ (` 0) ∙ tagY) ⟪ Θ₀ , revY★ ⟫

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  sealed5 : Term
  sealed5 = 5★ ⟪ unb₀ , tail (seal 0) ⟫

  CXL CXR R₁ R₂ R₃ R₄ R₅ R₆ R₇ : Term
  CXL = (ƛ `ℕ ∙ ` 0) · $ 5
  CXR = ((VY ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  R₁  = (((ν ★ · VY ⟨ revY★ ⟩) ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  R₂  = ((BdY ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  R₃  = ((BdY · (5★ ⟨ [] ∣ idᵖ ★ ⟩)) ⟨ [] ∣ idᵖ ★ ⟩) ⟨ [] ∣ ℕ? ⟩
  R₄  = ((BdY · 5★) ⟨ [] ∣ idᵖ ★ ⟩) ⟨ [] ∣ ℕ? ⟩
  R₅  = ((((ƛ (` 0) ∙ tagY) · sealed5) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫)
          ⟨ [] ∣ idᵖ ★ ⟩) ⟨ [] ∣ ℕ? ⟩
  R₆  = (((sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫)
          ⟨ [] ∣ idᵖ ★ ⟩) ⟨ [] ∣ ℕ? ⟩
  R₇  = ((sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫)
          ⟨ [] ∣ ℕ? ⟩

  CXL-⊢ : empty ∣ [] ⊢ CXL ⦂ `ℕ
  CXL-⊢ = tc

  CXR-⊢ : empty ∣ [] ⊢ CXR ⦂ `ℕ
  CXR-⊢ = tc

  -- the runs, pinned to evalTerms
  CXL-states : evalTerms 10 CXL-⊢ ≡ CXL ∷ $ 5 ∷ []
  CXL-states = refl

  CXR-states : evalTerms 30 CXR-⊢
    ≡ CXR ∷ R₁ ∷ R₂ ∷ R₃ ∷ R₄ ∷ R₅ ∷ R₆ ∷ R₇ ∷ blame 0 ∷ []
  CXR-states = refl

  -- THE PAIR (L, R₂) IS RELATED, in W₃ with Y ★-embedded inside
  bBdY : BdyTy ΔR Θ₀ ΔRᵢ (` 0 ⇒ ★) revY★ (★ ⇒ ★)
  bBdY = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = BdY}))))

  tagY-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) ((` 0) !) (` 0) ★
  tagY-ty = proj₂ (proj₂ (cast-inv {Γ = ` 0 ∷ []}
    (tc {Δ = ΔRᵢ} {Γ = ` 0 ∷ []} {M = tagY})))

  ℕ⊑Y : `ℕ ⊑ᵂ★⟨ Wi3★ ⟩ ` 0
  ℕ⊑Y = ⟦ ι⊑★ base-ℕ ⟧

  cx-related : W₃★ ∣ [] ⊢ CXL ⊑ R₂ ∶ ℕ⊑ℕ
  cx-related =
    ⊑cast
      (·⊑· {pA = ℕ⊑★} {pB = ℕ⊑★}
        (⊑cast
          (⊑⟪⟫ int3★ Wi3★-wf
            (ƛ⊑ƛ {pA = ℕ⊑Y} {pB = ℕ⊑★} tf tf
              (⊑cast (x⊑x Zʷ) tagY-ty ℕ⊑★))
            bBdY (⇒★ ℕ⊑★ ℕ⊑★))
          id★↦ᴿ-ty (⇒★ ℕ⊑★ ℕ⊑★))
        five⊑★)
      (proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = R₂})))) ℕ⊑ℕ

  -- the same pair has no derivation in any REAL world: the right
  -- embedding is a renaming, so `ℕ ⊑ Y` is `ℕ ⊑ ` k`, which no rule of
  -- `_⊢_⊑_` derives (and λx:ℕ.x is no ∀-value, so Opens is empty)
  real-ℕ⊑Y : ∀ {Δ Δ′} {W : World Δ Δ′} → ¬ (`ℕ ⊑ᵂ⟨ W ⟩ ` 0)
  real-ℕ⊑Y ()

  -- the right side is doomed: every run from R₂ ends in blame
  data Doomed (Δ : Ctxᵗ) : Term → Set where
    d-blame : ∀ {ℓ} → Doomed Δ (blame ℓ)
    d-step  : ∀ {M M₁ A} → ¬ Value M → Δ ∣ [] ⊢ M ⦂ A
      → Δ ⊢ M -→ M₁ ∣ none → Doomed Δ M₁ → Doomed Δ M

  doomed : ∀ {Δ M V} → Doomed Δ M → Δ ⊢ M -→* V → Value V → ⊥
  doomed d-blame done (V-simple ())
  doomed d-blame (st then r) v = proj₂ irreducible st
  doomed (d-step nv ⊢M st d) done v = nv v
  doomed (d-step nv ⊢M st d) (st′ then r) v
    with det ⊢M st st′
  doomed (d-step nv ⊢M st d) (st′ then r) v | refl , refl = doomed d r v

  nv? : ∀ {M} → ¬ Value (M ⟨ [] ∣ ℕ? ⟩)
  nv? (V-simple (S-cast _ ()))

  R₂-doomed : Doomed ΔR R₂
  R₂-doomed =
    d-step {M₁ = R₃} {A = `ℕ} nv? tc (justStep refl)
    (d-step {M₁ = R₄} {A = `ℕ} nv? tc (justStep refl)
    (d-step {M₁ = R₅} {A = `ℕ} nv? tc (justStep refl)
    (d-step {M₁ = R₆} {A = `ℕ} nv? tc (justStep refl)
    (d-step {M₁ = R₇} {A = `ℕ} nv? tc (justStep refl)
    (d-step {M₁ = blame 0} {A = `ℕ} nv? tc (justStep refl)
      d-blame)))))

  -- DGG part 1 fails on the related pair: the left reaches a value, the
  -- right reaches none
  cx-left-value : empty ⊢ CXL -→* $ 5
  cx-left-value = justStep refl then done

  cx-no-right-value : ¬ (∃[ V′ ] Σ[ r′ ∈ ΔR ⊢ R₂ -→* V′ ] Value V′)
  cx-no-right-value (V′ , r′ , v) = doomed R₂-doomed r′ v

  -- ... and the failure is local: the left value 5 is already related to
  -- R₇, whose next step is TagUntagBad-⟪⟫.  So SimBackBlame
  -- (STATEMENTS-CORE M22) is false for the ★-embedded relation: a right
  -- step to blame against a left value that never blames.
  bR₇ : BdyTy ΔR Θ₀ ΔRᵢ ★ ⌞ id ★ ⌟ ★
  bR₇ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔR} {M = (sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩)
                        ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫}))))

  bSeal : BdyTy ΔRᵢ unb₀ ΔR ★ (tail (seal 0)) (` 0)
  bSeal = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔRᵢ} {M = sealed5}))))

  five⊑R₇ : W₃★ ∣ [] ⊢ $ 5 ⊑ R₇ ∶ ℕ⊑ℕ
  five⊑R₇ =
    ⊑cast
      (⊑⟪⟫ int3★ Wi3★-wf
        (⊑cast
          (⊑⟪⟫ {Wᵢ = W₃★} (int★ IntN λ { (_ , ()) _ }) W₃★-wf five⊑★
            bSeal ℕ⊑Y)
          tagY-ty ℕ⊑★)
        bR₇ ℕ⊑★)
      (proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = R₇})))) ℕ⊑ℕ

  R₇-blames : ΔR ⊢ R₇ -→ blame 0 ∣ none
  R₇-blames = justStep refl

  five-never-blames : ∀ {ℓ} → ¬ (empty ⊢ $ 5 -→* blame ℓ)
  five-never-blames (st then r) = proj₁ irreducible (V-simple S-$) st

  -- the same pair refutes CastRedexNoBlame (STATEMENTS-CORE M26) for the
  -- ★-embedded relation: both sides values, the right's cast redex
  -- (TagUntagBad-⟪⟫) blames
  vR₇ᵢ : Value ((sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫)
  vR₇ᵢ = V-fresh (V-⟪⟫ (S-cast (V-simple S-$) I-tag) I-seal) refl

  castRedexNoBlame-fails :
    Value ($ 5) × Value ((sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩)
                           ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫)
    × (W₃★ ∣ [] ⊢ $ 5 ⊑ R₇ ∶ ℕ⊑ℕ) × (ΔR ⊢ R₇ -→ blame 0 ∣ none)
  castRedexNoBlame-fails = V-simple S-$ , vR₇ᵢ , five⊑R₇ , R₇-blames

  ---------------------------------------------------------------------
  -- (c) uniqueness survives: the index is `_⊢_⊑_` itself

  ⊑ᵂ★-unique : ∀ {Δ Δ′} {W : World★ Δ Δ′} {A A′}
    → (p q : A ⊑ᵂ★⟨ W ⟩ A′) → p ≡ q
  ⊑ᵂ★-unique ⟦ p ⟧ ⟦ q ⟧ with PI.⊑-unique p q
  ⊑ᵂ★-unique ⟦ p ⟧ ⟦ q ⟧ | refl = refl

  ---------------------------------------------------------------------
  -- (d) the right embedding is no longer a renaming

  embᴿ★-not-renaming :
    ¬ (Σ[ ρ ∈ Renameᵗ ] (∀ A → embᴿ★ Wi3★ A ≡ renameᵗ ρ A))
  embᴿ★-not-renaming (ρ , h) with h (` 0)
  embᴿ★-not-renaming (ρ , h) | ()
