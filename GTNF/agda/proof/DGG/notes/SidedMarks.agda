module proof.DGG.notes.SidedMarks where

-- File Charter:
--   * THE PROPOSAL CHECKED HERE ("sided marks", Jeremy 2026-10-05): a
--     name's mark is DETERMINED BY ITS SIDEDNESS, as type imprecision
--     already has it (`∀⊑∀` uses `extᵐ`, `∀⊑` uses `instᵐ`): a center
--     name in the right image is X⊑X, a left-only name is X⊑★.  This
--     reverses design.md D11 (marks chosen at the binder, fixed below)
--     and D15 (a rejoined name keeps its mark).  Findings in
--     SidedMarks.md.  NOT a Def module, not imported by All.agda;
--     nothing outside this file and its .md is edited.
--   * ENCODING (§1): marks are a FUNCTION of the two embeddings.
--     `Sidedᵐ ηᴸ ηᴿ` says: both images ⇒ X⊑X, left image only ⇒ X⊑★,
--     right image only ⇒ X⊑X (so "X⊑★ iff no right preimage").  Given
--     the keep/skip pattern, `Sidedᵐ` has exactly one mark list, so μ is
--     derived data.  It is required wherever a world is checked
--     (`WfWorld`, and the conversion worlds of the two conversion
--     premises); `Interior`/`ConversionInterior` lose their mark fields.
--     The key consequence is one line: `right-mark` (a right-image name
--     is never X⊑★).
--   * LOCAL COPY.  The world layer (ImprecisionWorld §1–§8),
--     ConversionImprecision and TermImprecision (its 15 rules, same
--     constructor names) are copied from git HEAD 46f04f4f, because the
--     real files are being edited concurrently.  The copy is
--     PARAMETERIZED by a `Policy` (§2): `d11` is HEAD's relation
--     (mark fields, `Joint`), `sided` the proposal.  Type imprecision
--     `_⊢_⊑_` (Imprecision.agda) is UNCHANGED and imported.
--   * §3 type-level lemmas: `⊑var`, the clash lemma (a right type that
--     has ★ where another has a variable, both above one left type,
--     forces an X⊑★ mark on that variable), `bad-cast`: under sided
--     marks a right-only cast `⊑cast` of a name tag `X!`, a name check
--     `X?`, or an arrow of them, is NEVER derivable.
--   * §4 one master non-derivability lemma `no-rel` (left forms `LftA`,
--     right forms `RBad`).
--   * §5 Example P4 (= cambridge Cf from its second block): the initial
--     pair is related (`p4-init`); blocks 2–4 are not (`p4-B2..4`);
--     THE MULTI-STEP SIMULATION FAILS: the left's state after Beta,
--     TyBeta is unrelated to EVERY state the right can reach
--     (`p4-multisim-fails`, via `in-trace`: reachable states are the
--     run's states, by determinism).
--   * §6 corpus: Cg (`cg-multisimback-fails`: the right's Inst, TyBeta
--     cannot be caught up), C12 (`c12-multisim-fails`), C12/C13/C14 B1
--     (the gen layer) not derivable; K (§6b, every opening pair, the
--     joined names at X⊑X) and C2 X0 (§6c, both sides gen-wrapped)
--     derive.
--   * §7 the SimBackBlame counterexample: `L₆ ⊑ R₇` is derivable in
--     `d11` WITHOUT any conversion premise (one-sided boundaries), so
--     restricting `conv-unseal⊑id★` alone does not remove it; it is NOT
--     derivable in any sided world (`cex-unrelated`).  Hunt probe H1
--     (hide, rebind, escape): unrelated (`h1-unrelated`).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length; head; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction using (InstX; inst-Λ; inst-gen; inst-∀; inst-⟪⟫)
open import Imprecision
  using (VarImp; X⊑X; X⊑★; ImpEnv; extᵐ; instᵐ; _⊢_⊑_;
         ★⊑★; ι⊑ι; ⇒⊑⇒; ∀⊑∀; ⇒⊑★; ι⊑★; ∀⊑; ∀★⊑★; ∀⊑★; bot-elim; bot⊑★)
import Imprecision as I

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. The world layer (copy of ImprecisionWorld at HEAD, §1–§8)
------------------------------------------------------------------------

infix 4 _↪_
data _↪_ : TyCtx → ImpEnv → Set where
  []↪  : [] ↪ []
  keep : ∀ {α m Δ Ω} → Δ ↪ Ω → (α ∷ Δ) ↪ (m ∷ Ω)
  skip : ∀ {m Δ Ω} → Δ ↪ Ω → Δ ↪ (m ∷ Ω)

emb : ∀ {η Ω} → η ↪ Ω → Renameᵗ
emb []↪      X       = X
emb (keep ι) zero    = zero
emb (keep ι) (suc X) = suc (emb ι X)
emb (skip ι) X       = suc (emb ι X)

relabel : ∀ {η Ω} (f : RVar → RVar) → η ↪ Ω → map f η ↪ Ω
relabel f []↪      = []↪
relabel f (keep ι) = keep (relabel f ι)
relabel f (skip ι) = skip (relabel f ι)

RepRel : Set
RepRel = List (RVar × RVar)

infix 4 _∋ᵨ_⇔_
data _∋ᵨ_⇔_ : RepRel → RVar → RVar → Set where
  here⇔  : ∀ {ϱ α β} → ((α , β) ∷ ϱ) ∋ᵨ α ⇔ β
  there⇔ : ∀ {ϱ α β π} → ϱ ∋ᵨ α ⇔ β → (π ∷ ϱ) ∋ᵨ α ⇔ β

sucᴸ sucᴿ suc² : RVar × RVar → RVar × RVar
sucᴸ (α , β) = suc α , β
sucᴿ (α , β) = α , suc β
suc² (α , β) = suc α , suc β

shiftᴸ shiftᴿ shift² : RepRel → RepRel
shiftᴸ = map sucᴸ
shiftᴿ = map sucᴿ
shift² = map suc²

record World (Δ Δ′ : Ctxᵗ) : Set where
  constructor world
  field
    μʷ  : ImpEnv
    ηᴸʷ : names Δ ↪ μʷ
    ηᴿʷ : names Δ′ ↪ μʷ
    ϱᵍʷ : RepRel
    ϱˡʷ : RepRel
open World public

Paired : World Δ Δ′ → RVar → RVar → Set
Paired W α β = (ϱᵍʷ W ∋ᵨ α ⇔ β) ⊎ (ϱˡʷ W ∋ᵨ α ⇔ β)

Joins : World Δ Δ′ → ℕ → ℕ → Set
Joins W X X′ = emb (ηᴸʷ W) X ≡ emb (ηᴿʷ W) X′

∅ʷ : World empty empty
∅ʷ = world [] []↪ []↪ [] []

embᴸ : World Δ Δ′ → Ty → Ty
embᴸ W = renameᵗ (emb (ηᴸʷ W))

embᴿ : World Δ Δ′ → Ty → Ty
embᴿ W = renameᵗ (emb (ηᴿʷ W))

infix 4 _⊑ᵂ⟨_⟩_
_⊑ᵂ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ᵂ⟨ W ⟩ A′ = μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′

infixl 6 _⊕_
_⊕_ : World Δ Δ′ → VarImp → World (underΛ Δ) (underΛ Δ′)
world μ η η′ ϱᵍ ϱˡ ⊕ m =
  world (m ∷ μ) (keep (relabel suc η)) (keep (relabel suc η′))
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ)

infixl 6 _⊕ᴸ
_⊕ᴸ : World Δ Δ′ → World (underΛ Δ) Δ′
world μ η η′ ϱᵍ ϱˡ ⊕ᴸ =
  world (X⊑★ ∷ μ) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ)

infixl 6 _⊕⁺_^_
_⊕⁺_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ ⊕⁺ m ^ β =
  world (m ∷ μ) (keep (relabel suc η)) (keep η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ)

infixl 6 _⊕ʳ_^_
_⊕ʳ_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World Δ (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ ⊕ʳ m ^ β = world (m ∷ μ) (skip η) (keep η′) ϱᵍ ϱˡ

data Join↪ {η : TyCtx}
    : ∀ {η′ μ} → η ↪ μ → η′ ↪ μ → (zero ∷ map suc η) ↪ μ → ℕ → Set where
  join-here : ∀ {β η′ μ m} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
    → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
  join-there : ∀ {β η′ μ m k} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
      {ι⁺ : (zero ∷ map suc η) ↪ μ}
    → Join↪ ι ι′ ι⁺ k
    → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

data Open1 {Δ Δ′ : Ctxᵗ}
    : World Δ Δ′ → ℕ → World (underΛ Δ) Δ′ → Set where
  open1 : ∀ {μ ϱᵍ ϱˡ k β} {ι : names Δ ↪ μ} {ι′ : names Δ′ ↪ μ}
      {ι⁺ : names (underΛ Δ) ↪ μ}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → Open1 (world μ ι ι′ ϱᵍ ϱˡ) k
            (world μ ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ))

open-⊕ : ∀ {W : World Δ Δ′} {m β}
  → Δ′ ∋rep β := ★ → Open1 (W ⊕ʳ m ^ β) 0 (W ⊕⁺ m ^ β)
open-⊕ hβ = open1 join-here here hβ

underν² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
underν² R R′ (world μ η η′ ϱᵍ ϱˡ) =
  world μ (relabel suc η) (relabel suc η′)
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ)

record CtxImpEntry (W : World Δ Δ′) : Set where
  constructor ctx-imp
  field
    tyᴸ  : Ty
    tyᴿ  : Ty
    impʷ : tyᴸ ⊑ᵂ⟨ W ⟩ tyᴿ
open CtxImpEntry public

CtxImp : World Δ Δ′ → Set
CtxImp W = List (CtxImpEntry W)

lhs : {W : World Δ Δ′} → CtxImp W → List Ty
lhs = map tyᴸ

rhs : {W : World Δ Δ′} → CtxImp W → List Ty
rhs = map tyᴿ

infix 4 _∋ʷ_⦂_
data _∋ʷ_⦂_ {W : World Δ Δ′} : CtxImp W → ℕ → CtxImpEntry W → Set where
  Zʷ : ∀ {γ e} → (e ∷ γ) ∋ʷ zero ⦂ e
  Sʷ : ∀ {γ e e′ x} → γ ∋ʷ x ⦂ e → (e′ ∷ γ) ∋ʷ suc x ⦂ e

data LiftCtx {W : World Δ Δ′} (m : VarImp)
    : CtxImp W → CtxImp (W ⊕ m) → Set where
  lift-[] : LiftCtx m [] []
  lift-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtx m γ γ′
    → LiftCtx m (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ A′) p′ ∷ γ′)

data LiftCtxᴸ {W : World Δ Δ′} : CtxImp W → CtxImp (W ⊕ᴸ) → Set where
  liftᴸ-[] : LiftCtxᴸ [] []
  liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
    → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

-- HEAD's `Joint` (D11): no skip/skip; a left-only name is X⊑★; a name in
-- both images names paired rep. vars, at ANY (shared) mark
data Joint (P : RVar → RVar → Set)
    : ∀ {η η′ Ω} → η ↪ Ω → η′ ↪ Ω → Set where
  joint[]    : Joint P []↪ []↪
  both       : ∀ {α β m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → P α β → Joint P ι ι′
    → Joint P (keep {α = α} {m = m} ι) (keep {α = β} {m = m} ι′)
  left-only  : ∀ {α η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → Joint P ι ι′
    → Joint P (keep {α = α} {m = X⊑★} ι) (skip {m = X⊑★} ι′)
  right-only : ∀ {β m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → Joint P ι ι′
    → Joint P (skip {m = m} ι) (keep {α = β} {m = m} ι′)

-- THE PROPOSAL: marks determined by sidedness.  A center name in the
-- right image is X⊑X; a center name in the left image only is X⊑★.
-- (A center name in neither image, never produced by `Joint`, is
-- unconstrained; conversion worlds do not check `Joint`.)
data Sidedᵐ : ∀ {η η′ Ω} → η ↪ Ω → η′ ↪ Ω → Set where
  s[]     : Sidedᵐ []↪ []↪
  s-both  : ∀ {α β η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} → Sidedᵐ ι ι′
    → Sidedᵐ (keep {α = α} {m = X⊑X} ι) (keep {α = β} {m = X⊑X} ι′)
  s-left  : ∀ {α η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} → Sidedᵐ ι ι′
    → Sidedᵐ (keep {α = α} {m = X⊑★} ι) (skip {m = X⊑★} ι′)
  s-right : ∀ {β η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} → Sidedᵐ ι ι′
    → Sidedᵐ (skip {m = X⊑X} ι) (keep {α = β} {m = X⊑X} ι′)
  s-none  : ∀ {m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} → Sidedᵐ ι ι′
    → Sidedᵐ (skip {m = m} ι) (skip {m = m} ι′)

-- THE ONE-LINE CONSEQUENCE: a right-image name is never X⊑★ (for any
-- position, in range or not)
right-mark : ∀ {η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} {X′ m}
  → Sidedᵐ ι ι′ → Ω ∋ˡ emb ι′ X′ := m → m ≡ X⊑X
right-mark s[] ()
right-mark {X′ = zero} (s-both s) here = refl
right-mark {X′ = suc X′} (s-both s) (there h) = right-mark s h
right-mark (s-left s) (there h) = right-mark s h
right-mark {X′ = zero} (s-right s) here = refl
right-mark {X′ = suc X′} (s-right s) (there h) = right-mark s h
right-mark (s-none s) (there h) = right-mark s h

-- and a name with no right preimage is X⊑★: the marks are DERIVED
-- from the keep/skip pattern
left-mark : ∀ {η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} {X m}
  → Sidedᵐ ι ι′ → Ω ∋ˡ emb ι X := m
  → (∀ {X′} → emb ι X ≢ emb ι′ X′) → m ≡ X⊑★
left-mark s[] () _
left-mark {X = zero} (s-both s) here n = ⊥-elim (n {zero} refl)
left-mark {X = suc X} (s-both s) (there h) n =
  left-mark s h (λ {X′} e → n {suc X′} (cong suc e))
left-mark {X = zero} (s-left s) here n = refl
left-mark {X = suc X} (s-left s) (there h) n =
  left-mark s h (λ {X′} e → n {X′} (cong suc e))
left-mark (s-right s) (there h) n =
  left-mark s h (λ {X′} e → n {suc X′} (cong suc e))
left-mark (s-none s) (there h) n =
  left-mark s h (λ {X′} e → n {X′} (cong suc e))

sided-relabel : ∀ {η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω} (f : RVar → RVar)
  → Sidedᵐ ι ι′ → Sidedᵐ (relabel f ι) ι′
sided-relabel f s[]         = s[]
sided-relabel f (s-both s)  = s-both (sided-relabel f s)
sided-relabel f (s-left s)  = s-left (sided-relabel f s)
sided-relabel f (s-right s) = s-right (sided-relabel f s)
sided-relabel f (s-none s)  = s-none (sided-relabel f s)

Sid : World Δ Δ′ → Set
Sid W = Sidedᵐ (ηᴸʷ W) (ηᴿʷ W)

sid-⊕ᴸ : ∀ {W : World Δ Δ′} → Sid W → Sid (W ⊕ᴸ)
sid-⊕ᴸ {W = world μ η η′ ϱᵍ ϱˡ} s = s-left (sided-relabel suc s)

-- Representation imprecision (D23), unchanged
data RepImp (W : World Δ Δ′) : ImpEnv → Ty → Ty → Set
infix 4 RepImp
syntax RepImp W μ R R′ = μ ⊢ R ⊑ᴿ⟨ W ⟩ R′

data RepImp W where
  ★⊑★ : ∀ {μ} → μ ⊢ ★ ⊑ᴿ⟨ W ⟩ ★
  ι⊑ι : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ι
  X⊑X : ∀ {μ X m} → μ ∋ˡ X := m → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ` X
  α⊑β : ∀ {μ α β} → Paired W α β
    → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ` (length μ + β)
  ⇒⊑⇒ : ∀ {μ R R′ S S′}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ S ⊑ᴿ⟨ W ⟩ S′
    → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ R′ ⇒ S′
  ∀⊑∀ : ∀ {μ R R′} → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ `∀ R′
  ⇒⊑★ : ∀ {μ R S}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ S ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ ★
  ι⊑★ : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ★
  X⊑★ : ∀ {μ X} → μ ∋ˡ X := X⊑★ → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ★
  α⊑★ : ∀ {μ α} → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ★
  ∀⊑  : ∀ {μ R R′} → NonVar R → 0 ∈ᵗ R
    → instᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ⇑ᵗ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ R′
  ∀★⊑★ : ∀ {μ} → μ ⊢ `∀ ★ ⊑ᴿ⟨ W ⟩ ★
  ∀⊑★ : ∀ {μ R} → NonStar R → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ★
    → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ ★
  bot-elim : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ `∀ ★
  bot⊑★ : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ ★

data Agree (W : World Δ Δ′) (α β : RVar) : Set where
  abst-abst : reps Δ ∋ʳ α := abstR → reps Δ′ ∋ʳ β := abstR
    → Agree W α β
  abst-★    : reps Δ ∋ʳ α := abstR → Δ′ ∋rep β := ★
    → Agree W α β
  rep-rep   : ∀ {R R′}
    → Δ ∋rep α := R → Δ′ ∋rep β := R′
    → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′
    → Agree W α β

NamedUniqueᴸ : World Δ Δ′ → Set
NamedUniqueᴸ {Δ} {Δ′} W = ∀ {α α′ β}
  → names Δ ∋ᵅ α → names Δ ∋ᵅ α′ → names Δ′ ∋ᵅ β
  → Paired W α β → Paired W α′ β → α ≡ α′

NamedUniqueᴿ : World Δ Δ′ → Set
NamedUniqueᴿ {Δ} {Δ′} W = ∀ {α β β′}
  → names Δ ∋ᵅ α → names Δ′ ∋ᵅ β → names Δ′ ∋ᵅ β′
  → Paired W α β → Paired W α β′ → β ≡ β′

AtMostOneName : TyCtx → Set
AtMostOneName ns = ∀ {α α′} → ns ∋ᵅ α → ns ∋ᵅ α′ → α ≡ α′

≤1-[] : AtMostOneName []
≤1-[] (_ , ()) _

≤1-∷[] : ∀ {γ} → AtMostOneName (γ ∷ [])
≤1-∷[] (_ , here) (_ , here) = refl
≤1-∷[] (_ , here) (_ , there ())
≤1-∷[] (_ , there ()) _

namedᴸ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ) → NamedUniqueᴸ W
namedᴸ-≤1 W h a a′ _ _ _ = h a a′

namedᴿ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ′) → NamedUniqueᴿ W
namedᴿ-≤1 W h _ b b′ _ _ = h b b′

-- HEAD's mark fields of `Interior` and `ConversionInterior` (D11, D15),
-- as separate records so that a policy can keep or drop them
record D11Marks (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᵢ : World Δᵢ Δ′ᵢ) : Set where
  constructor d11-marks
  field
    mark-left : ∀ {X Xₑ m}
      → Δᵢ ∋tv X → toExt Θ X ≡ just Xₑ
      → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
      → μʷ Wᵢ ∋ˡ emb (ηᴸʷ Wᵢ) X := m
    mark-right : ∀ {X′ X′ₑ m}
      → Δ′ᵢ ∋tv X′ → toExt Θ′ X′ ≡ just X′ₑ
      → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
      → μʷ Wᵢ ∋ˡ emb (ηᴿʷ Wᵢ) X′ := m

record D11CMarks (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᶜ : World Δᶜ Δ′ᶜ) : Set where
  constructor d11-cmarks
  field
    conv-mark-left : ∀ {X Xₑ α m}
      → Δᶜ ∋ᵗ X := α → Δ ∋ᵗ Xₑ := α
      → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
      → μʷ Wᶜ ∋ˡ emb (ηᴸʷ Wᶜ) X := m
    conv-mark-right : ∀ {X′ X′ₑ β m}
      → Δ′ᶜ ∋ᵗ X′ := β → Δ′ ∋ᵗ X′ₑ := β
      → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
      → μʷ Wᶜ ∋ˡ emb (ηᴿʷ Wᶜ) X′ := m

------------------------------------------------------------------------
-- 1b. Conversion imprecision (copy of ConversionImprecision at HEAD).
-- Its ★ clauses read `μ(X) = X⊑★` of a LEFT name; under `sided` that
-- already means the name is left-only (`right-mark`), so the clauses
-- need no change: they apply to left-only names only.
------------------------------------------------------------------------

mutual
  data MidImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
      : Mid → Mid → Set where
    conv-id⊑id : ∀ {A A′} → A ⊑ᵂ⟨ W ⟩ A′ → MidImp W (id A) (id A′)
    conv-↦⊑↦ : ∀ {s s′ c c′} → ConvImp W s s′ → ConvImp W c c′
      → MidImp W (s ↦ c) (s′ ↦ c′)
    conv-∀⊑∀ : ∀ {c c′} → ConvImp (W ⊕ X⊑X) c c′
      → MidImp W (`∀ c) (`∀ c′)
    conv-∀⊑ : ∀ {c g′} → ConvImp (W ⊕ᴸ) c ⌞ g′ ⌟ → MidImp W (`∀ c) g′

  data TailImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
      : Tail → Tail → Set where
    conv-mid⊑mid : ∀ {g g′} → MidImp W g g′ → TailImp W (mid g) (mid g′)
    conv-seal⊑seal : ∀ {X X′} → Joins W X X′
      → TailImp W (seal X) (seal X′)
    conv-⨾seal⊑⨾seal : ∀ {t t′ X X′} → TailImp W t t′ → Joins W X X′
      → TailImp W (t ⨾seal X) (t′ ⨾seal X′)
    conv-seal⊑id★ : ∀ {X} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → TailImp W (seal X) (mid (id ★))
    conv-⨾seal⊑ : ∀ {t t′ X} → TailImp W t t′
      → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → TailImp W (t ⨾seal X) t′

  data ConvImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
      : Conv → Conv → Set where
    conv-tail⊑tail : ∀ {t t′} → TailImp W t t′
      → ConvImp W (tail t) (tail t′)
    conv-unseal⊑unseal : ∀ {X X′} → Joins W X X′
      → ConvImp W (unseal X) (unseal X′)
    conv-unseal⨾⊑unseal⨾ : ∀ {X X′ c c′} → Joins W X X′ → ConvImp W c c′
      → ConvImp W (unseal X ⨾ c) (unseal X′ ⨾ c′)
    conv-unseal⊑id★ : ∀ {X} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → ConvImp W (unseal X) ⌞ id ★ ⌟
    conv-unseal⨾⊑ : ∀ {X c c′} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → ConvImp W c c′
      → ConvImp W (unseal X ⨾ c) c′

------------------------------------------------------------------------
-- 1c. Side-premise bundles (copy of TermImprecision §1 at HEAD)
------------------------------------------------------------------------

data Lit : Term → Ty → Set where
  lit-$     : ∀ {n} → Lit ($ n) `ℕ
  lit-true  : Lit `true `𝔹
  lit-false : Lit `false `𝔹

data CastTy (Δ : Ctxᵗ) (μ : ModeEnv) (p : Coercion) (B A : Ty) : Set where
  cast-ty : Δ ∣ μ ⊢ᵖ p ∶ B ⟹ A → length μ ≡ length (names Δ)
    → CastTy Δ μ p B A

data NuTy (Δ : Ctxᵗ) (A C : Ty) (c : Conv) (B : Ty) : Set where
  nu-ty : ∀ {R Δᵢ Δᶜ Cₑ}
    → Δ ⊢ᵗ A
    → Δ ⊢ᶜ A ~ R
    → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
    → Δᶜ ⊢ c ∶ C ⇝ Cₑ
    → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ
    → Δ ⊢ᵗ B
    → NuTy Δ A C c B

data BdyTy (Δ : Ctxᵗ) (Θ : Boundary) (Δᵢ : Ctxᵗ) (Bᵢ : Ty) (c : Conv)
    (Bₑ : Ty) : Set where
  bdy-ty : ∀ {Δᶜ Cᵢ Cₑ}
    → BoundaryWf Δ Θ Δᵢ Δᶜ
    → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
    → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
    → Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ
    → Δ ⊢ᵗ Bₑ
    → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ

cast-inv : ∀ {Γ M μ p A} → Δ ∣ Γ ⊢ M ⟨ μ ∣ p ⟩ ⦂ A
  → Σ[ B ∈ Ty ] ((Δ ∣ Γ ⊢ M ⦂ B) × CastTy Δ μ p B A)
cast-inv (⊢cast ⊢M ⊢p len) = _ , ⊢M , cast-ty ⊢p len

ν-inv : ∀ {Γ A L c B} → Δ ∣ Γ ⊢ ν A · L ⟨ c ⟩ ⦂ B
  → Σ[ C ∈ Ty ] ((Δ ∣ Γ ⊢ L ⦂ `∀ C) × NuTy Δ A C c B)
ν-inv (⊢ν wA rA ⊢L mw ⊢c eq wB) = _ , ⊢L , nu-ty wA rA mw ⊢c eq wB

⟪⟫-inv : ∀ {Γ M Θ c Bₑ} → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Bᵢ ∈ Ty ]
      ((Δᵢ ∣ [] ⊢ M ⦂ Bᵢ) × BdyTy Δ Θ Δᵢ Bᵢ c Bₑ)
⟪⟫-inv (boundary mw ⊢M ⊢c eqᵢ eqₑ wB) =
  _ , _ , ⊢M , bdy-ty mw ⊢c eqᵢ eqₑ wB

------------------------------------------------------------------------
-- 2. Policies and the relation (copy of TermImprecision §2 at HEAD,
-- parameterized by where marks come from)
------------------------------------------------------------------------

record Policy : Set₁ where
  field
    IMarks  : ∀ {Δ Δ′ Δᵢ Δ′ᵢ} → World Δ Δ′ → Boundary → Boundary
      → World Δᵢ Δ′ᵢ → Set
    CMarks  : ∀ {Δ Δ′ Δᶜ Δ′ᶜ} → World Δ Δ′ → Boundary → Boundary
      → World Δᶜ Δ′ᶜ → Set
    JointP  : ∀ {Δ Δ′} → World Δ Δ′ → Set
    CJointP : ∀ {Δ Δ′} → World Δ Δ′ → Set

-- HEAD (D11, D15): marks copied into interiors, chosen when fresh
d11 : Policy
d11 = record
  { IMarks  = D11Marks
  ; CMarks  = D11CMarks
  ; JointP  = λ W → Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
  ; CJointP = λ _ → ⊤
  }

-- THE PROPOSAL: no mark is copied or chosen; every checked world has
-- its marks determined by sidedness
sided : Policy
sided = record
  { IMarks  = λ _ _ _ _ → ⊤
  ; CMarks  = λ _ _ _ _ → ⊤
  ; JointP  = λ W → Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W) × Sid W
  ; CJointP = Sid
  }

module Rel (P : Policy) where
  open Policy P

  record Interior (W : World Δ Δ′) (Θ Θ′ : Boundary)
      (Wᵢ : World Δᵢ Δ′ᵢ) : Set where
    constructor interior-world
    field
      int-left  : Δ ⊢ⁱ Θ ⇒ Δᵢ
      int-right : Δ′ ⊢ⁱ Θ′ ⇒ Δ′ᵢ
      same-ϱᵍ : ϱᵍʷ Wᵢ ≡ ϱᵍʷ W
      same-ϱˡ : ϱˡʷ Wᵢ ≡ ϱˡʷ W
      join-cont : ∀ {X X′ Xₑ X′ₑ}
        → Δᵢ ∋tv X → Δ′ᵢ ∋tv X′
        → toExt Θ X ≡ just Xₑ → toExt Θ′ X′ ≡ just X′ₑ
        → (Joins Wᵢ X X′ → Joins W Xₑ X′ₑ)
          × (Joins W Xₑ X′ₑ → Joins Wᵢ X X′)
      join-fresh : ∀ {X X′ α β}
        → Δᵢ ∋ᵗ X := α → Δ′ᵢ ∋ᵗ X′ := β
        → Fresh Θ X ⊎ Fresh Θ′ X′
        → (Joins Wᵢ X X′ → Paired W α β)
          × (Paired W α β → Joins Wᵢ X X′)
      int-marks : IMarks W Θ Θ′ Wᵢ

  record ConversionInterior (W : World Δ Δ′) (Θ Θ′ : Boundary)
      (Wᶜ : World Δᶜ Δ′ᶜ) : Set where
    constructor conversion-interior-world
    field
      conv-left  : Δ ⊢ᶜ Θ ⇒ Δᶜ
      conv-right : Δ′ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
      conv-same-ϱᵍ : ϱᵍʷ Wᶜ ≡ ϱᵍʷ W
      conv-same-ϱˡ : ϱˡʷ Wᶜ ≡ ϱˡʷ W
      conv-join-cont : ∀ {X X′ Xₑ X′ₑ α β}
        → Δᶜ ∋ᵗ X := α → Δ′ᶜ ∋ᵗ X′ := β
        → Δ ∋ᵗ Xₑ := α → Δ′ ∋ᵗ X′ₑ := β
        → (Joins Wᶜ X X′ → Joins W Xₑ X′ₑ)
          × (Joins W Xₑ X′ₑ → Joins Wᶜ X X′)
      conv-join-fresh : ∀ {X X′ α β}
        → Δᶜ ∋ᵗ X := α → Δ′ᶜ ∋ᵗ X′ := β
        → (names Δ ∌ʳ α) ⊎ (names Δ′ ∌ʳ β)
        → (Joins Wᶜ X X′ → Paired W α β)
          × (Paired W α β → Joins Wᶜ X X′)
      conv-marks : CMarks W Θ Θ′ Wᶜ

  record WfWorld (W : World Δ Δ′) : Set where
    constructor wf-world
    field
      wf-joint  : JointP W
      wf-agree  : ∀ {α β} → Paired W α β → Agree W α β
      wf-namedᴸ : NamedUniqueᴸ W
      wf-namedᴿ : NamedUniqueᴿ W
  open WfWorld public

  NuConversionImp : ∀ {Δ Δ′ A A′ C C′ c c′ B B′}
    → (W : World Δ Δ′)
    → NuTy Δ A C c B → NuTy Δ′ A′ C′ c′ B′ → Set
  NuConversionImp {c = c} {c′ = c′} W
    (nu-ty {R = R} {Δᶜ = Δᶜ} wA rA mw ⊢c eq wB)
    (nu-ty {R = R′} {Δᶜ = Δ′ᶜ} wA′ rA′ mw′ ⊢c′ eq′ wB′) =
    Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
      (ConversionInterior (underν² R R′ W) TyBetaBoundary TyBetaBoundary Wᶜ
      × CJointP Wᶜ × ConvImp Wᶜ c c′)

  BdyConversionImp : ∀ {Δ Δ′ Δᵢ Δ′ᵢ Θ Θ′}
      {Aᵢ A′ᵢ c c′ A A′}
    → (W : World Δ Δ′)
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → Set
  BdyConversionImp {Θ = Θ} {Θ′ = Θ′} {c = c} {c′ = c′} W
    (bdy-ty {Δᶜ = Δᶜ} mw ⊢c eqᵢ eqₑ wB)
    (bdy-ty {Δᶜ = Δ′ᶜ} mw′ ⊢c′ eq′ᵢ eq′ₑ wB′) =
    Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
      (ConversionInterior W Θ Θ′ Wᶜ × CJointP Wᶜ × ConvImp Wᶜ c c′)

  data Opens {Δ′ : Ctxᵗ} (Θ′ : Boundary)
      : ∀ {Δ Δ⁺} → World Δ Δ′ → Term → Ty → World Δ⁺ Δ′ → Term → Ty
      → Set where
    open-none : ∀ {Δ} {W : World Δ Δ′} {M A}
      → Opens Θ′ W M A W M A
    open-∀ : ∀ {Δ Δ⁺ k} {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
        {W⁺ : World Δ⁺ Δ′} {V N M₀ A A₀}
      → NonVar A
      → 0 ∈ᵗ A
      → Value V
      → Δ ∣ [] ⊢ V ⦂ `∀ A
      → InstX V N
      → Fresh Θ′ k
      → Open1 W k W₁
      → Opens Θ′ W₁ N A W⁺ M₀ A₀
      → Opens Θ′ W V (`∀ A) W⁺ M₀ A₀

  infix 3 _∣_⊢_⊑_∶_

  data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) (γ : CtxImp W)
      : Term → Term → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

    x⊑x : ∀ {x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
      → γ ∋ʷ x ⦂ ctx-imp A A′ p
      → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

    κ⊑κ : ∀ {k ι}
      → Lit k ι
      → (p : ι ⊑ᵂ⟨ W ⟩ ι)
      → W ∣ γ ⊢ k ⊑ k ∶ p

    ƛ⊑ƛ : ∀ {N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → Δ ⊢ᵗ A
      → Δ′ ⊢ᵗ A′
      → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
      → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

    ·⊑· : ∀ {L L′ M M′ A A′ B B′}
        {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
      → W ∣ γ ⊢ M ⊑ M′ ∶ pA
      → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

    blame⊑ : ∀ {ℓ M′ A A′}
      → Δ ⊢ᵗ A
      → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
      → (p : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

    cast⊑cast : ∀ {M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ μ c B A
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    cast⊑ : ∀ {M M′ μ c B A A′} {p : B ⊑ᵂ⟨ W ⟩ A′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ μ c B A
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

    ⊑cast : ∀ {M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ M ⊑ M′ ∶ p
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    Λ⊑Λ : ∀ {γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
      → LiftCtx X⊑X γ γ′
      → Value V
      → Value V′
      → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
      → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

    Λ⊑ : ∀ {γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′}
      → NonVar A
      → 0 ∈ᵗ A
      → LiftCtxᴸ γ γ′
      → Value V
      → W ⊕ᴸ ∣ γ′ ⊢ V ⊑ M′ ∶ r
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

    ν⊑ν : ∀ {L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
      → W ∣ γ ⊢ L ⊑ L′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ A′
      → (n : NuTy Δ A C c B)
      → (n′ : NuTy Δ′ A′ C′ c′ B′)
      → NuConversionImp W n n′
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

    ν⊑ : ∀ {L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ M′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ ★
      → NuTy Δ A C c B
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

    ⟪⟫⊑⟪⟫ : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
        {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
      → Interior W Θ Θ′ Wᵢ
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
      → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
      → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
      → BdyConversionImp W b b′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

    ⟪⟫⊑ : ∀ {Δᵢ} {Wᵢ : World Δᵢ Δ′}
        {M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
      → Interior W Θ [] Wᵢ
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
      → BdyTy Δ Θ Δᵢ Aᵢ c A
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

    ⊑⟪⟫ : ∀ {Δ′ᵢ Δ⁺} {Wᵢ : World Δ Δ′ᵢ} {Wᵢ⁺ : World Δ⁺ Δ′ᵢ}
        {M M₀ M′ Θ′ c′ A A₀ A′ᵢ A′} {r : A₀ ⊑ᵂ⟨ Wᵢ⁺ ⟩ A′ᵢ}
      → Interior W [] Θ′ Wᵢ
      → Opens Θ′ Wᵢ M A Wᵢ⁺ M₀ A₀
      → WfWorld Wᵢ⁺
      → Wᵢ⁺ ∣ [] ⊢ M₀ ⊑ M′ ∶ r
      → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

module D = Rel d11
module S = Rel sided

------------------------------------------------------------------------
-- 3. Type-level lemmas: no type is below both ★ and a right variable,
-- unless that variable is marked X⊑★
------------------------------------------------------------------------

-- only a variable is below a variable (∀⊑ needs `NonVar`)
⊑var : ∀ {μ A k} → μ ⊢ A ⊑ ` k → A ≡ ` k
⊑var I.X⊑X = refl
⊑var (∀⊑ nv _ d) with ⊑var d
⊑var (∀⊑ () _ d) | refl

var⊑★ : ∀ {μ k} → μ ⊢ ` k ⊑ ★ → μ ∋ˡ k := X⊑★
var⊑★ (I.X⊑★ h) = h

-- `Clash k B C`: at some position, one of B, C has ★ and the other the
-- variable k (B the source of a right cast, C its target)
data Clash (k : ℕ) : Ty → Ty → Set where
  c★v : Clash k ★ (` k)
  cv★ : Clash k (` k) ★
  c⇒ˡ : ∀ {B₁ B₂ C₁ C₂} → Clash k B₁ C₁ → Clash k (B₁ ⇒ B₂) (C₁ ⇒ C₂)
  c⇒ʳ : ∀ {B₁ B₂ C₁ C₂} → Clash k B₂ C₂ → Clash k (B₁ ⇒ B₂) (C₁ ⇒ C₂)

clash-swap : ∀ {k B C} → Clash k B C → Clash k C B
clash-swap c★v     = cv★
clash-swap cv★     = c★v
clash-swap (c⇒ˡ c) = c⇒ˡ (clash-swap c)
clash-swap (c⇒ʳ c) = c⇒ʳ (clash-swap c)

clash-ren : ∀ {k B C} (ρ : Renameᵗ) → Clash k B C
  → Clash (ρ k) (renameᵗ ρ B) (renameᵗ ρ C)
clash-ren ρ c★v     = c★v
clash-ren ρ cv★     = cv★
clash-ren ρ (c⇒ˡ c) = c⇒ˡ (clash-ren ρ c)
clash-ren ρ (c⇒ʳ c) = c⇒ʳ (clash-ren ρ c)

there⁻ : ∀ {A : Set} {x y : A} {xs i} → (y ∷ xs) ∋ˡ suc i := x → xs ∋ˡ i := x
there⁻ (there h) = h

-- THE CLASH LEMMA (pure type imprecision): if one left type is below
-- both B and C, and B, C clash at k, then k is marked X⊑★.  The left
-- type may be a ∀ (both by ∀⊑): the clash moves under `instᵐ`.
clash : ∀ {μ A B C k} → μ ⊢ A ⊑ B → μ ⊢ A ⊑ C → Clash k B C
  → μ ∋ˡ k := X⊑★
clash d e c★v with ⊑var e
clash d e c★v | refl = var⊑★ d
clash d e cv★ with ⊑var d
clash d e cv★ | refl = var⊑★ e
clash (⇒⊑⇒ d₁ d₂) (⇒⊑⇒ e₁ e₂) (c⇒ˡ c) = clash d₁ e₁ c
clash (⇒⊑⇒ d₁ d₂) (⇒⊑⇒ e₁ e₂) (c⇒ʳ c) = clash d₂ e₂ c
clash (∀⊑ _ _ d) (∀⊑ _ _ e) c = there⁻ (clash d e (clash-ren suc c))

-- coercions whose source and target clash: a name tag `X!`, a name
-- check `X?`, and arrows with one of them inside
data BadCo : Coercion → Set where
  b-tag : ∀ {X} → BadCo ((` X) !)
  b-chk : ∀ {X ℓ} → BadCo ((` X) ？ ℓ)
  b-dom : ∀ {p q} → BadCo p → BadCo (p ↦ᵖ q)
  b-cod : ∀ {p q} → BadCo q → BadCo (p ↦ᵖ q)

bad-clash : ∀ {Δ μ c B A} → Δ ∣ μ ⊢ᵖ c ∶ B ⟹ A → BadCo c
  → ∃[ X ] Clash X B A
bad-clash (⊢tag ()) b-tag
bad-clash (⊢tag-var {X = X} _ _ _) b-tag = X , cv★
bad-clash (⊢check ()) b-chk
bad-clash (⊢check-var {X = X} _ _ _) b-chk = X , c★v
bad-clash (⊢fun dp dq) (b-dom b) with bad-clash dp b
... | X , c = X , c⇒ˡ (clash-swap c)
bad-clash (⊢fun dp dq) (b-cod b) with bad-clash dq b
... | X , c = X , c⇒ʳ c

-- UNDER SIDED MARKS, A RIGHT-ONLY CAST OF A NAME TAG OR CHECK IS NEVER
-- RELATED: `⊑cast`'s premise index p and conclusion index q share the
-- left type, so they force an X⊑★ mark on a right-image name
bad-cast : ∀ {Δ Δ′} {V : World Δ Δ′} {μ′ c′ A B′ A′}
  → Sid V → CastTy Δ′ μ′ c′ B′ A′ → BadCo c′
  → A ⊑ᵂ⟨ V ⟩ B′ → A ⊑ᵂ⟨ V ⟩ A′ → ⊥
bad-cast {V = V} s (cast-ty ⊢c _) b p q with bad-clash ⊢c b
... | X , c with right-mark s (clash p q (clash-ren (emb (ηᴿʷ V)) c))
... | ()

-- the left casts that may face a bad right cast in `cast⊑cast`: their
-- source and target are atomic, so no clash survives
data GoodL : Coercion → Set where
  g-id★ : GoodL (idᵖ ★)
  g-ℕ!  : GoodL (`ℕ !)
  g-ℕ?  : ∀ {ℓ} → GoodL (`ℕ ？ ℓ)

data Atomic : Ty → Set where
  at-★ : Atomic ★
  at-ℕ : Atomic `ℕ
  at-𝔹 : Atomic `𝔹

atomic⊑ : ∀ {μ A B} → Atomic A → μ ⊢ A ⊑ B → Atomic B
atomic⊑ at-★ ★⊑★          = at-★
atomic⊑ at-ℕ (ι⊑ι _)      = at-ℕ
atomic⊑ at-ℕ (ι⊑★ _)      = at-★
atomic⊑ at-𝔹 (ι⊑ι _)      = at-𝔹
atomic⊑ at-𝔹 (ι⊑★ _)      = at-★

no-clash : ∀ {k B C} → Atomic B → Atomic C → ¬ Clash k B C
no-clash a () c★v
no-clash () a′ cv★
no-clash () a′ (c⇒ˡ c)
no-clash () a′ (c⇒ʳ c)

good-atomic : ∀ {Δ μ c B A} → GoodL c → CastTy Δ μ c B A
  → Atomic B × Atomic A
good-atomic g-id★ (cast-ty (⊢id _ _) _)  = at-★ , at-★
good-atomic g-ℕ!  (cast-ty (⊢tag _) _)   = at-ℕ , at-★
good-atomic g-ℕ?  (cast-ty (⊢check _) _) = at-★ , at-ℕ

emb-atomic : ∀ {ρ B} → Atomic B → Atomic (renameᵗ ρ B)
emb-atomic at-★ = at-★
emb-atomic at-ℕ = at-ℕ
emb-atomic at-𝔹 = at-𝔹

-- a good left cast against a bad right cast (`cast⊑cast`)
cc-bad : ∀ {Δ Δ′} {V : World Δ Δ′} {μ μ′ c c′ B A B′ A′}
  → GoodL c → BadCo c′ → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
  → B ⊑ᵂ⟨ V ⟩ B′ → A ⊑ᵂ⟨ V ⟩ A′ → ⊥
cc-bad {V = V} g b ct (cast-ty ⊢c′ _) p q with good-atomic g ct
... | aB , aA with bad-clash ⊢c′ b
... | X , c =
  no-clash (atomic⊑ (emb-atomic aB) p) (atomic⊑ (emb-atomic aA) q)
    (clash-ren (emb (ηᴿʷ V)) c)

------------------------------------------------------------------------
-- 4. The master non-derivability lemma (sided relation)
------------------------------------------------------------------------

-- left terms that never pass a bad right cast: λ, literals,
-- applications (by their function), boundaries, Λ, ν, and good casts
data LftA : Term → Set where
  la-ƛ    : ∀ {A N} → LftA (ƛ A ∙ N)
  la-$    : ∀ {n} → LftA ($ n)
  la-·    : ∀ {L M} → LftA L → LftA (L · M)
  la-⟪⟫   : ∀ {M Θ d} → LftA M → LftA (M ⟪ Θ , d ⟫)
  la-Λ    : ∀ {V} → LftA V → LftA (Λ V)
  la-ν    : ∀ {A L c} → LftA L → LftA (ν A · L ⟨ c ⟩)
  la-cast : ∀ {M μ c} → LftA M → GoodL c → LftA (M ⟨ μ ∣ c ⟩)

-- right terms whose head path reaches a bad cast: through good or bad
-- casts, boundaries, and functions of applications
data RBad : Term → Set where
  rb-cast  : ∀ {U μ c} → BadCo c → RBad (U ⟨ μ ∣ c ⟩)
  rb-gcast : ∀ {R μ c} → RBad R → RBad (R ⟨ μ ∣ c ⟩)
  rb-⟪⟫    : ∀ {R Θ d} → RBad R → RBad (R ⟪ Θ , d ⟫)
  rb-·     : ∀ {F A} → RBad F → RBad (F · A)

-- InstX keeps the left form (it opens a Λ, or reaches through a
-- boundary; a good cast is not instantiable)
instx-lft : ∀ {M N} → LftA M → InstX M N → LftA N
instx-lft (la-Λ l) (inst-Λ _) = l
instx-lft (la-⟪⟫ l) (inst-⟪⟫ _ i) = la-⟪⟫ (instx-lft l i)
instx-lft (la-cast l ()) (inst-gen _)
instx-lft (la-cast l ()) (inst-∀ _ _)

module _ where
  open S

  opens-lft : ∀ {Δ Δ⁺ Δ′} {Θ′} {W : World Δ Δ′} {W⁺ : World Δ⁺ Δ′}
      {M A M₀ A₀}
    → LftA M → Opens Θ′ W M A W⁺ M₀ A₀ → LftA M₀
  opens-lft l open-none = l
  opens-lft l (open-∀ _ _ _ _ i _ _ os) = opens-lft (instx-lft l i) os

  wf-sid : ∀ {Δ Δ′} {W : World Δ Δ′} → WfWorld W → Sid W
  wf-sid wf = proj₂ (wf-joint wf)

  -- NO DERIVATION, in any sided world, relates a left `LftA` term to a
  -- right `RBad` term: every path down reaches the bad cast through
  -- `⊑cast` (refuted by `bad-cast`) or `cast⊑cast` against a good left
  -- cast (refuted by `cc-bad`); every world on the way is sided
  -- (boundary rules check WfWorld, `Λ⊑` adds a left-only X⊑★ name)
  no-rel : ∀ {Δ Δ′} {V : World Δ Δ′} {γ : CtxImp V} {M R A A′}
      {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LftA M → RBad R → Sid V → ¬ (V ∣ γ ⊢ M ⊑ R ∶ q)
  no-rel {V = V} l (rb-cast b) s (⊑cast {p = p} d ct q) =
    bad-cast {V = V} s ct b p q
  no-rel l (rb-gcast r) s (⊑cast d ct q) = no-rel l r s d
  no-rel {V = V} (la-cast l g) (rb-cast b) s
    (cast⊑cast {p = p} d ct ct′ q) = cc-bad {V = V} g b ct ct′ p q
  no-rel (la-cast l g) (rb-gcast r) s (cast⊑cast d _ _ _) = no-rel l r s d
  no-rel (la-cast l g) r s (cast⊑ d _ _) = no-rel l r s d
  no-rel (la-· l) (rb-· r) s (·⊑· d _) = no-rel l r s d
  no-rel {V = V} (la-Λ l) r s (Λ⊑ _ _ _ _ d _) =
    no-rel l r (sid-⊕ᴸ {W = V} s) d
  no-rel (la-ν l) r s (ν⊑ d _ _ _) = no-rel l r s d
  no-rel (la-⟪⟫ l) (rb-⟪⟫ r) s (⟪⟫⊑⟪⟫ _ wf d _ _ _ _) =
    no-rel l r (wf-sid wf) d
  no-rel (la-⟪⟫ l) r s (⟪⟫⊑ _ wf d _ _) = no-rel l r (wf-sid wf) d
  no-rel l (rb-⟪⟫ r) s (⊑⟪⟫ _ os wf d _ _) =
    no-rel (opens-lft l os) r (wf-sid wf) d

------------------------------------------------------------------------
-- 5. Runs, reachability, and Example P4 (= cambridge Cf)
------------------------------------------------------------------------

module Runs where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval
    using (eval; Trace; stop; illtyped; _◅⟨_⟩_; Final; value; blamed;
           no-redex; out-of-fuel; evalTerms; traceTerms; step; StepResult)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
  open import proof.TypeSafety.Determinism using (det)
  open import proof.TypeSafety.Irreducible using (irreducible)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  import Data.List.Relation.Unary.All as All

  justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
    → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
  justStep {r = r} _ = proj₂ (proj₂ r)

  -- a run that ends at a value or at blame
  EndsVB : ∀ {Δ A M} → Trace Δ A M → Set
  EndsVB (stop (value _))   = ⊤
  EndsVB (stop (blamed _))  = ⊤
  EndsVB (stop no-redex)    = ⊥
  EndsVB (stop out-of-fuel) = ⊥
  EndsVB (illtyped _)       = ⊥
  EndsVB (_ ◅⟨ _ ⟩ tr)      = EndsVB tr

  -- EVERY STATE REACHABLE FROM M IS A STATE OF ITS RUN (determinism)
  in-trace : ∀ {Δ A M N} (tr : Trace Δ A M) → Δ ∣ [] ⊢ M ⦂ A
    → EndsVB tr → Δ ⊢ M -→* N → N ∈ traceTerms tr
  in-trace (stop f) ⊢M e done = here refl
  in-trace (illtyped _) ⊢M e done = here refl
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e done = here refl
  in-trace (stop (value v)) ⊢M e (st then r) =
    ⊥-elim (proj₁ irreducible v st)
  in-trace (stop (blamed refl)) ⊢M e (st then r) =
    ⊥-elim (proj₂ irreducible st)
  in-trace (stop no-redex) ⊢M () (st then r)
  in-trace (stop out-of-fuel) ⊢M () (st then r)
  in-trace (illtyped _) ⊢M () (st then r)
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) with det ⊢M st st′
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) | refl , refl =
    there (in-trace tr ⊢M′ e r)

  all-reach : ∀ {Δ A M N} {P : Term → Set} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
    → EndsVB (eval k M ⊢M) → All P (evalTerms k ⊢M)
    → Δ ⊢ M -→* N → P N
  all-reach k ⊢M e a r = All.lookup a (in-trace (eval k _ ⊢M) ⊢M e r)

open Runs public using (justStep; EndsVB; in-trace; all-reach)

module P4 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_; done; _then_)
  open import examples.ImprecisionExamples using (L4; R4; L4-⊢; R4-⊢)
  open S

  idX : Term
  idX = ƛ (` 0) ∙ ` 0

  revX : Conv
  revX = reveal 0 (` 0 ⇒ ` 0)

  Θ₀ : Boundary
  Θ₀ = bind 0 0 ∷ []

  ∀X⇒X : Ty
  ∀X⇒X = `∀ (` 0 ⇒ ` 0)

  -- P4's left state 2 (after Beta, TyBeta) is P1's L1′
  L1′ : Term
  L1′ = (idX ⟪ Θ₀ , revX ⟫) · $ 5

  L-run : empty ⊢ L4 -→* L1′
  L-run = justStep refl then justStep refl then done

  -- `Unrel L R`: no sided world relates L to R
  Unrel : Term → Term → Set
  Unrel L R = ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′} → Sid W → ¬ (W ∣ γ ⊢ L ⊑ R ∶ p)

  ---------------------------------------------------------------------
  -- THE INITIAL PAIR IS RELATED (sided): the argument by ⊑cast (gen)
  -- over Λ⊑ (Y left-only at X⊑★, as sidedness gives); the body by
  -- ν⊑ν with the two ν-bound rep. vars paired in the conversion world

  ConvCtx₀ : Ty → Ctxᵗ
  ConvCtx₀ R = (bindR R ∷ []) ∣ (0 ∷ [])

  conv₀ : ∀ {R} → allocate R empty ⊢ᶜ Θ₀ ⇒ ConvCtx₀ R
  conv₀ = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

  Wν : ∀ {R R′} → World (ConvCtx₀ R) (ConvCtx₀ R′)
  Wν = world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ [])

  Wν-conv : ∀ {R R′} → ConversionInterior (underν² R R′ ∅ʷ) Θ₀ Θ₀ Wν
  Wν-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-marks      = tt
    }

  revX⊑revX : ∀ {Δ Δ′} {W : World Δ Δ′} → Joins W 0 0 → ConvImp W revX revX
  revX⊑revX j =
    conv-tail⊑tail
      (conv-mid⊑mid
        (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                   (conv-unseal⊑unseal j)))

  ∀id⊑★ : ∀ {Δ Δ′} (W : World Δ Δ′) → ∀X⇒X ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
  ∀id⊑★ W = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (I.X⊑★ here) (I.X⊑★ here))

  ∀id⊑∀id : ∀ {Δ Δ′} (W : World Δ Δ′) → ∀X⇒X ⊑ᵂ⟨ W ⟩ ∀X⇒X
  ∀id⊑∀id W = ∀⊑∀ (⇒⊑⇒ I.X⊑X I.X⊑X)

  νbody : Term
  νbody = ν `ℕ · ` 0 ⟨ revX ⟩

  νbody-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νbody-ty = proj₂ (proj₂ (ν-inv {Γ = ∀X⇒X ∷ []}
    (tc {Δ = empty} {Γ = ∀X⇒X ∷ []} {M = νbody})))

  genArg : Term
  genArg = (ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩

  genArg-ty : CastTy empty [] (genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)))
    (★ ⇒ ★) ∀X⇒X
  genArg-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = genArg})))

  R4-is : R4 ≡ (ƛ ∀X⇒X ∙ (νbody · $ 5)) · genArg
  R4-is = refl

  p4-init : ∅ʷ ∣ [] ⊢ L4 ⊑ R4 ∶ ι⊑ι base-ℕ
  p4-init =
    ·⊑·
      (ƛ⊑ƛ {pA = ∀id⊑∀id ∅ʷ} tf tf
        (·⊑·
          (ν⊑ν (x⊑x Zʷ) (ι⊑ι base-ℕ) νbody-ty νbody-ty
            (Wν , Wν-conv , s-both s[] , revX⊑revX refl)
            (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
          (κ⊑κ lit-$ (ι⊑ι base-ℕ))))
      (⊑cast
        (Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = I.X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
        genArg-ty (∀id⊑∀id ∅ʷ))

  ---------------------------------------------------------------------
  -- Small non-derivability lemmas for the right states that hold no
  -- bad cast

  -- right terms that are literals under boundaries
  data RLit : Term → Set where
    rl-$   : ∀ {n} → RLit ($ n)
    rl-⟪⟫  : ∀ {R Θ d} → RLit R → RLit (R ⟪ Θ , d ⟫)

  no-app-lit : ∀ {Δ Δ′} {V : World Δ Δ′} {γ : CtxImp V} {L M R A A′}
      {q : A ⊑ᵂ⟨ V ⟩ A′}
    → RLit R → ¬ (V ∣ γ ⊢ L · M ⊑ R ∶ q)
  no-app-lit rl-$ ()
  no-app-lit (rl-⟪⟫ r) (⊑⟪⟫ _ open-none _ d _ _) = no-app-lit r d
  no-app-lit (rl-⟪⟫ r) (⊑⟪⟫ _ (open-∀ _ _ _ _ () _ _ _) _ _ _ _)

  -- the right's function is a λ whose body is an application
  no-ƛapp : ∀ {Δ Δ′} {V : World Δ Δ′} {γ : CtxImp V} {Θ d M C P Q N A A′}
      {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ (idX ⟪ Θ , d ⟫) · M ⊑ (ƛ C ∙ (P · Q)) · N ∶ q)
  no-ƛapp (·⊑· (⟪⟫⊑ _ _ (ƛ⊑ƛ _ _ ()) _ _) _)

  -- the right's function is a ν
  no-νapp : ∀ {Δ Δ′} {V : World Δ Δ′} {γ : CtxImp V} {Θ d M B L c N A A′}
      {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ (idX ⟪ Θ , d ⟫) · M ⊑ (ν B · L ⟨ c ⟩) · N ∶ q)
  no-νapp (·⊑· (⟪⟫⊑ _ _ () _ _) _)

  nth : List Term → ℕ → Term
  nth []       _       = $ 0
  nth (x ∷ xs) zero    = x
  nth (x ∷ xs) (suc n) = nth xs n

  Ls Rs : List Term
  Ls = evalTerms 11 L4-⊢
  Rs = evalTerms 17 R4-⊢

  L1′-state : nth Ls 2 ≡ L1′
  L1′-state = refl

  lft₂ : LftA L1′
  lft₂ = la-· (la-⟪⟫ la-ƛ)

  ---------------------------------------------------------------------
  -- design.md §12.4's P4 blocks 2, 3, 4 (cambridge Cf B1, B2, B3) are
  -- NOT derivable in any sided world: each needs `⊑cast` of the right's
  -- gen wrapper `X! → X?` or of its `X?` at the both-sided X

  p4-B2 : Unrel (nth Ls 2) (nth Rs 2)
  p4-B2 s = no-rel lft₂ (rb-· (rb-⟪⟫ (rb-cast (b-dom b-tag)))) s

  p4-B3 : Unrel (nth Ls 3) (nth Rs 4)
  p4-B3 s = no-rel (la-⟪⟫ (la-· la-ƛ)) (rb-⟪⟫ (rb-cast b-chk)) s

  p4-B4 : Unrel (nth Ls 4) (nth Rs 6)
  p4-B4 s = no-rel (la-⟪⟫ (la-⟪⟫ la-$)) (rb-⟪⟫ (rb-cast b-chk)) s

  ---------------------------------------------------------------------
  -- THE MULTI-STEP SIMULATION FAILS ON P4 (sided): the initial pair is
  -- related, the left runs Beta, TyBeta to L1′, and NO state the right
  -- can reach is related to L1′, in any sided world

  allR : All (Unrel L1′) Rs
  allR =
      (λ s → no-ƛapp)
    ∷ (λ s → no-νapp)
    ∷ (λ s → no-rel lft₂ (rb-· (rb-⟪⟫ (rb-cast (b-dom b-tag)))) s)
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-· (rb-cast (b-dom b-tag)))) s)
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-cast b-chk)) s)
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-cast b-chk)) s)
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-cast b-chk)) s)
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-cast b-chk)) s)
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-cast b-chk)) s)
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-cast b-chk)) s)
    ∷ (λ s → no-app-lit (rl-⟪⟫ (rl-⟪⟫ rl-$)))
    ∷ (λ s → no-app-lit (rl-⟪⟫ rl-$))
    ∷ (λ s → no-app-lit rl-$)
    ∷ []

  p4-multisim-fails :
    (∅ʷ ∣ [] ⊢ L4 ⊑ R4 ∶ ι⊑ι base-ℕ)
    × (empty ⊢ L4 -→* L1′)
    × (∀ {R′} → empty ⊢ R4 -→* R′ → Unrel L1′ R′)
  p4-multisim-fails =
    p4-init , L-run , all-reach {P = Unrel L1′} 17 R4-⊢ tt allR

------------------------------------------------------------------------
-- 6. The corpus: the gen layer (Cg, C12, C13, C14)
------------------------------------------------------------------------

module Corpus where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_; done; _then_)
  open import examples.CambridgeExamples
    using (I; I★; genI; instI; dyn; Cg-L; Cg-R; Cg-L-⊢; Cg-R-⊢;
           C12-L; C12-R; C12-L-⊢; C12-R-⊢; C13-R-⊢; C14-R-⊢)
  open S
  open P4
    using (idX; revX; Θ₀; ∀X⇒X; L1′; Unrel; Wν; Wν-conv; revX⊑revX;
           ∀id⊑★; ∀id⊑∀id; no-νapp; no-app-lit; RLit; rl-$; rl-⟪⟫; nth;
           lft₂)

  ℕ⊑★ : ∀ {μ} → μ ⊢ `ℕ ⊑ ★
  ℕ⊑★ = ι⊑★ base-ℕ

  five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
    → W ∣ γ ⊢ $ 5 ⊑ dyn 5 ∶ ℕ⊑★
  five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

  νL : Term
  νL = ν `ℕ · Λ idX ⟨ revX ⟩

  νL-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νL-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = νL})))

  ---------------------------------------------------------------------
  -- Cg ("gen then inst on the right only"): the initial pair is related
  -- (sided), the right runs Inst, TyBeta to Cg-R₂, and NO left state is
  -- related to Cg-R₂: the multi-step backward simulation fails

  genI-ty : CastTy empty [] genI (★ ⇒ ★) ∀X⇒X
  genI-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = I★ ⟨ [] ∣ genI ⟩})))

  instI∘genI-ty : CastTy empty [] instI ∀X⇒X (★ ⇒ ★)
  instI∘genI-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = I★ ⟨ [] ∣ genI ⟩ ⟨ [] ∣ instI ⟩})))

  cg-b0 : ∅ʷ ∣ [] ⊢ Cg-L ⊑ Cg-R ∶ ℕ⊑★
  cg-b0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑cast
            (Λ⊑ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = I.X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
            genI-ty (∀id⊑∀id ∅ʷ))
          instI∘genI-ty (∀id⊑★ ∅ʷ))
        ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

  CgR₂ : Term
  CgR₂ = nth (evalTerms 21 Cg-R-⊢) 2

  Cg-R-run : empty ⊢ Cg-R -→* CgR₂
  Cg-R-run = justStep refl then justStep refl then done

  -- Cg-R₂ = (([+X^α] ([−X^α] I★ ⟨…⟩)⟨X! → X?⟩ ⟨−X → +X⟩)⟨id★ → id★⟩) 5★
  rbCg : RBad CgR₂
  rbCg = rb-· (rb-gcast (rb-⟪⟫ (rb-cast (b-dom b-tag))))

  allLg : All (λ L → Unrel L CgR₂) (evalTerms 10 Cg-L-⊢)
  allLg =
      (λ s → no-rel (la-· (la-ν (la-Λ la-ƛ))) rbCg s)   -- X0 (cg-x0)
    ∷ (λ s → no-rel lft₂ rbCg s)                         -- B1
    ∷ (λ s → no-rel (la-⟪⟫ (la-· la-ƛ)) rbCg s)
    ∷ (λ s → no-rel (la-⟪⟫ (la-⟪⟫ la-$)) rbCg s)
    ∷ (λ s → no-rel (la-⟪⟫ la-$) rbCg s)
    ∷ (λ s → no-rel la-$ rbCg s)
    ∷ []

  cg-multisimback-fails :
    (∅ʷ ∣ [] ⊢ Cg-L ⊑ Cg-R ∶ ℕ⊑★)
    × (empty ⊢ Cg-R -→* CgR₂)
    × (∀ {L′} → empty ⊢ Cg-L -→* L′ → Unrel L′ CgR₂)
  cg-multisimback-fails =
    cg-b0 , Cg-R-run , all-reach {P = λ L → Unrel L CgR₂} 10 Cg-L-⊢ tt allLg

  ---------------------------------------------------------------------
  -- C12 (`inst` then `gen` on the right, under the source ν): the
  -- initial pair is related (sided), the left runs TyBeta to L1′, and
  -- NO state the right can reach is related to L1′ (its B1 pair is the
  -- gen layer, `p12-B1`): the multi-step forward simulation fails

  ΛI⊑ΛI : ∅ʷ ∣ [] ⊢ I ⊑ I ∶ ∀id⊑∀id ∅ʷ
  ΛI⊑ΛI = Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
    (ƛ⊑ƛ {pA = I.X⊑X} tf tf (x⊑x Zʷ)) (∀id⊑∀id ∅ʷ)

  instI-ty : CastTy empty [] instI ∀X⇒X (★ ⇒ ★)
  instI-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩})))

  genI∘instI-ty : CastTy empty [] genI (★ ⇒ ★) ∀X⇒X
  genI∘instI-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩})))

  C12-ν : Term
  C12-ν = ν `ℕ · (I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩) ⟨ revX ⟩

  C12-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C12-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C12-ν})))

  c12-b0 : ∅ʷ ∣ [] ⊢ C12-L ⊑ C12-R ∶ ι⊑ι base-ℕ
  c12-b0 =
    ·⊑·
      (ν⊑ν (⊑cast (⊑cast ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ))
              genI∘instI-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty C12-ν-ty
        (Wν , Wν-conv , s-both s[] , revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  C12-L-run : empty ⊢ C12-L -→* L1′
  C12-L-run = justStep refl then done

  allR12 : All (Unrel L1′) (evalTerms 24 C12-R-⊢)
  allR12 =
      (λ s → no-νapp)
    ∷ (λ s → no-νapp)
    ∷ (λ s → no-νapp)
    ∷ (λ s → no-rel lft₂ (rb-· (rb-⟪⟫ (rb-cast (b-dom b-tag)))) s)  -- B1
    ∷ (λ s → no-rel lft₂ (rb-⟪⟫ (rb-· (rb-cast (b-dom b-tag)))) s)
    ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk ∷ chk
    ∷ (λ s → no-app-lit (rl-⟪⟫ (rl-⟪⟫ rl-$)))
    ∷ (λ s → no-app-lit (rl-⟪⟫ rl-$))
    ∷ (λ s → no-app-lit rl-$)
    ∷ []
    where
    chk : ∀ {U μ Θ d ℓ X}
      → Unrel L1′ ((U ⟨ μ ∣ (` X) ？ ℓ ⟩) ⟪ Θ , d ⟫)
    chk s = no-rel lft₂ (rb-⟪⟫ (rb-cast b-chk)) s

  c12-multisim-fails :
    (∅ʷ ∣ [] ⊢ C12-L ⊑ C12-R ∶ ι⊑ι base-ℕ)
    × (empty ⊢ C12-L -→* L1′)
    × (∀ {R′} → empty ⊢ C12-R -→* R′ → Unrel L1′ R′)
  c12-multisim-fails =
    c12-b0 , C12-L-run , all-reach {P = Unrel L1′} 24 C12-R-⊢ tt allR12

  ---------------------------------------------------------------------
  -- C12, C13, C14 B1: the left's L1′ against one, two, three gen layers
  -- (TermImprecisionRebaseExamples `c12-b1`, `c13-b1`, `c14-b1`, which
  -- relate them at a both-sided name marked X⊑★): NOT derivable

  c12-B1 : Unrel L1′ (nth (evalTerms 24 C12-R-⊢) 3)
  c12-B1 s = no-rel lft₂ (rb-· (rb-⟪⟫ (rb-cast (b-dom b-tag)))) s

  c13-B1 : Unrel L1′ (nth (evalTerms 29 C13-R-⊢) 4)
  c13-B1 s =
    no-rel lft₂ (rb-· (rb-gcast (rb-⟪⟫ (rb-cast (b-dom b-tag))))) s

  c14-B1 : Unrel L1′ (nth (evalTerms 38 C14-R-⊢) 5)
  c14-B1 s = no-rel lft₂ (rb-· (rb-⟪⟫ (rb-cast (b-dom b-tag)))) s

------------------------------------------------------------------------
-- 6b. Counterexample K (design.md D26) under sided marks: every pair
-- derives.  HEAD already uses X⊑X for the joined names (the opened
-- binder Y, the rejoined X), which is what sidedness forces; the right
-- name Y bound to β:=★ is X⊑X while right-only, and stays X⊑X when the
-- opening joins it (Open1 does not touch μ).
------------------------------------------------------------------------

module K where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I; instI)
  open S
  open P4 using (idX; revX; Θ₀; ∀X⇒X; ∀id⊑★)

  KK : Term
  KK = Λ I

  cId cK : Conv
  cId = ⌞ ⌞ id (` 0) ⌟ ↦ ⌞ id (` 0) ⌟ ⌟
  cK  = ⌞ `∀ cId ⌟

  id★↦ : Coercion
  id★↦ = idᵖ ★ ↦ᵖ idᵖ ★

  VL Nk Rarg₃ Bm RF : Term
  VL    = I ⟪ Θ₀ , cK ⟫
  Nk    = idX ⟪ bind 1 1 ∷ [] , cId ⟫
  Rarg₃ = (Nk ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩
  Bm    = idX ⟪ bind 1 1 ∷ bind 0 0 ∷ [] , revX ⟫
  RF    = Bm ⟨ [] ∣ id★↦ ⟩

  LK LK₁ RK RK₁ RK₂ RK₃ RK₄ : Term
  LK  = (ƛ ∀X⇒X ∙ ` 0) · (ν `ℕ · KK ⟨ cK ⟩)
  LK₁ = (ƛ ∀X⇒X ∙ ` 0) · VL
  RK  = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩)
  RK₁ = (ƛ (★ ⇒ ★) ∙ ` 0) · (VL ⟨ [] ∣ instI ⟩)
  RK₂ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν ★ · VL ⟨ revX ⟩) ⟨ [] ∣ id★↦ ⟩)
  RK₃ = (ƛ (★ ⇒ ★) ∙ ` 0) · Rarg₃
  RK₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · RF

  LK-⊢ : empty ∣ [] ⊢ LK ⦂ ∀X⇒X
  LK-⊢ = tc

  RK-⊢ : empty ∣ [] ⊢ RK ⦂ ★ ⇒ ★
  RK-⊢ = tc

  LK-states : evalTerms 20 LK-⊢ ≡ LK ∷ LK₁ ∷ VL ∷ []
  LK-states = refl

  RK-states : evalTerms 20 RK-⊢ ≡ RK ∷ RK₁ ∷ RK₂ ∷ RK₃ ∷ RK₄ ∷ RF ∷ []
  RK-states = refl

  ΔL ΔRk ΔLX ΔRX : Ctxᵗ
  ΔL  = allocate `ℕ empty
  ΔRk = allocate ★ ΔL
  ΔLX = (abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
  ΔRX = (bindR ★ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

  vVL : Value VL
  vVL = V-⟪⟫ (S-Λ (V-simple S-ƛ)) I-all

  -- the world after the right's Inst TyBeta: (αᴸ, αᴿ) global
  Wk : World ΔL ΔRk
  Wk = world [] []↪ []↪ ((0 , 1) ∷ []) []

  PwK : World (underΛ ΔL) (reps ΔRk ∣ (0 ∷ []))
  PwK = Wk ⊕⁺ X⊑X ^ 0

  agreeP : ∀ {α β} → Paired PwK α β → Agree PwK α β
  agreeP (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agreeP (inj₁ (there⇔ ()))
  agreeP (inj₂ here⇔) = abst-★ r-here r-here
  agreeP (inj₂ (there⇔ ()))

  PwK-wf : WfWorld PwK
  PwK-wf = wf-world (both (inj₂ here⇔) joint[] , s-both s[]) agreeP
    (namedᴸ-≤1 PwK ≤1-∷[]) (namedᴿ-≤1 PwK ≤1-∷[])

  Θ₀-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ []) ⊢ⁱ Θ₀ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  Θ₀-int = interior
    (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  IntK-ro : Interior Wk [] Θ₀ (Wk ⊕ʳ X⊑X ^ 0)
  IntK-ro = record
    { int-left   = interior changes[]
    ; int-right  = Θ₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; int-marks  = tt
    }

  ΘX : Boundary
  ΘX = bind 1 1 ∷ []

  bindX-int : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ⁱ ΘX
        ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  bindX-int = interior (changes∷ changes[]
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  bindX-conv : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ᶜ ΘX
        ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  bindX-conv = conversion (conv-bind (_ , there here) conv[]
    (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

  WX : World ΔLX ΔRX
  WX = world (X⊑X ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))
         ((1 , 1) ∷ []) ((0 , 0) ∷ [])

  WX-int : Interior PwK ΘX ΘX WX
  WX-int = record
    { int-left   = bindX-int
    ; int-right  = bindX-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
        ; (_ , here) (_ , there here) _ ()
        ; (_ , here) (_ , there (there ())) _ _
        ; (_ , there here) _ () _
        ; (_ , there (there ())) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) here _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there (there ())) _
        ; (there here) (there (there ())) _
        ; (there (there ())) _ _
        }
    ; int-marks  = tt
    }

  WX-conv : ConversionInterior PwK ΘX ΘX WX
  WX-conv = record
    { conv-left       = bindX-conv
    ; conv-right      = bindX-conv
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ
        { here here here here → (λ _ → refl) , (λ _ → refl)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there here) _ (there ())
        ; here (there (there ())) _ _
        ; (there here) _ (there ()) _
        ; (there (there ())) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) here _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there (there ())) _
        ; (there here) (there (there ())) _
        ; (there (there ())) _ _
        }
    ; conv-marks      = tt
    }

  uniqᴸX : ∀ {α α′ β} → Paired WX α β → Paired WX α′ β → α ≡ α′
  uniqᴸX (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴸX (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniqᴸX (inj₁ (there⇔ ())) _
  uniqᴸX (inj₂ here⇔) (inj₂ here⇔) = refl
  uniqᴸX (inj₂ here⇔) (inj₂ (there⇔ ()))
  uniqᴸX (inj₂ (there⇔ ())) _
  uniqᴸX (inj₁ here⇔) (inj₂ (there⇔ ()))
  uniqᴸX (inj₂ here⇔) (inj₁ (there⇔ ()))

  uniqᴿX : ∀ {α β β′} → Paired WX α β → Paired WX α β′ → β ≡ β′
  uniqᴿX (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴿX (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniqᴿX (inj₁ (there⇔ ())) _
  uniqᴿX (inj₂ here⇔) (inj₂ here⇔) = refl
  uniqᴿX (inj₂ here⇔) (inj₂ (there⇔ ()))
  uniqᴿX (inj₂ (there⇔ ())) _
  uniqᴿX (inj₁ here⇔) (inj₂ (there⇔ ()))
  uniqᴿX (inj₂ here⇔) (inj₁ (there⇔ ()))

  agreeX : ∀ {α β} → Paired WX α β → Agree WX α β
  agreeX (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agreeX (inj₁ (there⇔ ()))
  agreeX (inj₂ here⇔) = abst-★ r-here r-here
  agreeX (inj₂ (there⇔ ()))

  -- sided: both names in both images, X⊑X
  WX-wf : WfWorld WX
  WX-wf = wf-world
    (both (inj₂ here⇔) (both (inj₁ here⇔) joint[]) , s-both (s-both s[]))
    agreeX (λ _ _ _ → uniqᴸX) (λ _ _ _ → uniqᴿX)

  instVL : InstX VL Nk
  instVL = inst-⟪⟫ (S-Λ (V-simple S-ƛ)) (inst-Λ (V-simple S-ƛ))

  VL-⊢ : ΔL ∣ [] ⊢ VL ⦂ ∀X⇒X
  VL-⊢ = tc

  bNL : BdyTy (underΛ ΔL) ΘX ΔLX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
  bNL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = underΛ ΔL} {M = Nk}))))

  bNR : BdyTy (reps ΔRk ∣ (0 ∷ [])) ΘX ΔRX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
  bNR = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = reps ΔRk ∣ (0 ∷ [])} {M = Nk}))))

  bOutK : BdyTy ΔRk Θ₀ (reps ΔRk ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bOutK = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Nk ⟪ Θ₀ , revX ⟫}))))

  id★↦ᴿk-ty : CastTy ΔRk [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦ᴿk-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  cId⊑cId : ∀ {Δ Δ′} {W : World Δ Δ′} → ` 0 ⊑ᵂ⟨ W ⟩ ` 0
    → ConvImp W cId cId
  cId⊑cId x = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
    where
    i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id x))

  openVLₖ : Opens Θ₀ (Wk ⊕ʳ X⊑X ^ 0) VL ∀X⇒X PwK Nk (` 0 ⇒ ` 0)
  openVLₖ =
    open-∀ nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL refl (open-⊕ r-here) open-none

  Nk⊑Nk : PwK ∣ [] ⊢ Nk ⊑ Nk ∶ ⇒⊑⇒ I.X⊑X I.X⊑X
  Nk⊑Nk =
    ⟪⟫⊑⟪⟫ WX-int WX-wf (ƛ⊑ƛ {pA = I.X⊑X} tf tf (x⊑x Zʷ)) bNL bNR
      (WX , WX-conv , s-both (s-both s[]) , cId⊑cId I.X⊑X)
      (⇒⊑⇒ I.X⊑X I.X⊑X)

  -- before the right's Merge (RK₃)
  VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
  VL⊑Rarg₃ =
    ⊑cast (⊑⟪⟫ IntK-ro openVLₖ PwK-wf Nk⊑Nk bOutK (∀id⊑★ Wk))
      id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk
  lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

  -- after the right's Merge (RK₄, RF): the opening at the merged Θ₂
  Θ₂ : Boundary
  Θ₂ = bind 1 1 ∷ bind 0 0 ∷ []

  int-Θ₂ : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ⁱ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  int-Θ₂ = interior
    (changes∷ (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))
      (step-bind (_ , there here) (fresh∷ (λ ()) fresh[])
        (ins-there ins-here)))

  bBm : BdyTy ΔRk Θ₂ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bBm = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Bm}))))

  -- inside the merged `+Y^β, +X^αᴿ`: both right names right-only, at
  -- X⊑X (sidedness: a right-image name)
  WiR : World ΔL ΔRX
  WiR = world (X⊑X ∷ X⊑X ∷ []) (skip (skip []↪)) (keep (keep []↪))
          ((0 , 1) ∷ []) []

  -- the opened world: the left's opened binder joins Y (β:=★), X⊑X
  WoK : World (underΛ ΔL) ΔRX
  WoK = world (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))
          ((1 , 1) ∷ []) ((0 , 0) ∷ [])

  IntK-Θ₂ : Interior Wk [] Θ₂ WiR
  IntK-Θ₂ = record
    { int-left   = interior changes[]
    ; int-right  = int-Θ₂
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; int-marks  = tt
    }

  openK : Open1 WiR 0 WoK
  openK = open1 join-here here r-here

  openVL : Opens Θ₂ WiR VL ∀X⇒X WoK Nk (` 0 ⇒ ` 0)
  openVL = open-∀ nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL refl openK open-none

  agreeO : ∀ {α β} → Paired WoK α β → Agree WoK α β
  agreeO (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agreeO (inj₁ (there⇔ ()))
  agreeO (inj₂ here⇔) = abst-★ r-here r-here
  agreeO (inj₂ (there⇔ ()))

  -- sided: the joined Y at X⊑X, the right-only X at X⊑X
  WoK-wf : WfWorld WoK
  WoK-wf = wf-world
    (both (inj₂ here⇔) (right-only joint[]) , s-both (s-right s[]))
    agreeO (λ _ _ _ → uniqᴸX) (λ _ _ _ → uniqᴿX)

  -- inside the left's inner `+X^αᴸ` (left-only): X rejoins the right's
  -- X through (αᴸ, αᴿ); under sidedness it is X⊑X, as in HEAD
  IntK-X : Interior WoK ΘX [] WX
  IntK-X = record
    { int-left   = bindX-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
        ; (_ , here) (_ , there here) refl refl → (λ ()) , (λ ())
        ; (_ , here) (_ , there (there ())) _ _
        ; (_ , there here) _ () _
        ; (_ , there (there ())) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there here) (inj₁ ()) ; here (there here) (inj₂ ())
        ; (there here) here _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; _ (there (there ())) _
        ; (there (there ())) _ _
        }
    ; int-marks  = tt
    }

  Nk⊑idX : WoK ∣ [] ⊢ Nk ⊑ idX ∶ ⇒⊑⇒ I.X⊑X I.X⊑X
  Nk⊑idX =
    ⟪⟫⊑ IntK-X WX-wf (ƛ⊑ƛ {pA = I.X⊑X} tf tf (x⊑x Zʷ)) bNL (⇒⊑⇒ I.X⊑X I.X⊑X)

  -- K'S FINAL PAIR, under sided marks
  VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
  VL⊑RF = ⊑cast (⊑⟪⟫ IntK-Θ₂ openVL WoK-wf Nk⊑idX bBm (∀id⊑★ Wk))
    id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
  lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

------------------------------------------------------------------------
-- 6c. C2's right-led block X0 (both sides gen-wrapped; D26 opening at
-- X⊑X, the two gen wrappers matched by `cast⊑cast`): derives under
-- sided marks, unchanged.  (In the pending-openings encoding it needs
-- the pending name at X⊑★, which sidedness forbids; SidedMarks.md.)
------------------------------------------------------------------------

module C2 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples
    using (I★; genI; dyn; C2-L; Cg-R-⊢)
  open S
  open P4 using (idX; revX; Θ₀; ∀X⇒X; ∀id⊑★; nth)
  open Corpus using (ℕ⊑★; five⊑; CgR₂)
  open K using (id★↦)

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  id★→ : Conv
  id★→ = tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))

  tagX↦ : Coercion
  tagX↦ = (` 0) ! ↦ᵖ (` 0) ？ 0

  I★⁻ I★gen Bg I★genI : Term
  I★⁻    = I★ ⟪ unb₀ , id★→ ⟫
  I★gen  = I★⁻ ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩
  Bg     = I★gen ⟪ Θ₀ , revX ⟫
  I★genI = I★ ⟨ [] ∣ genI ⟩

  CgR₂-is : CgR₂ ≡ (Bg ⟨ [] ∣ K.id★↦ ⟩) · dyn 5
  CgR₂-is = refl

  ΔR ΔRₓ : Ctxᵗ
  ΔR  = allocate ★ empty
  ΔRₓ = reps ΔR ∣ (0 ∷ [])

  Bg-ty : BdyTy ΔR Θ₀ ΔRₓ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  Bg-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = Bg}))))

  I★⁻ᴿ-ty : BdyTy ΔRₓ unb₀ ΔR (★ ⇒ ★) id★→ (★ ⇒ ★)
  I★⁻ᴿ-ty =
    proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★⁻}))))

  I★⁻ᴸ-ty : BdyTy (underΛ empty) unb₀ (reps (underΛ empty) ∣ [])
    (★ ⇒ ★) id★→ (★ ⇒ ★)
  I★⁻ᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = underΛ empty} {M = I★⁻}))))

  tagᴿ-ty : CastTy ΔRₓ (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᴿ-ty =
    proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★gen})))

  tagᴸ-ty : CastTy (underΛ empty) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᴸ-ty =
    proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = underΛ empty} {M = I★gen})))

  id★↦ᴿ-ty : CastTy ΔR [] K.id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦ᴿ-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  I★genI-⊢ : empty ∣ [] ⊢ I★genI ⦂ ∀X⇒X
  I★genI-⊢ = tc

  C2-L-ν : Term
  C2-L-ν = ν `ℕ · I★genI ⟨ revX ⟩

  C2-L-is : C2-L ≡ C2-L-ν · $ 5
  C2-L-is = refl

  C2-L-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C2-L-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C2-L-ν})))

  W₃ : World empty ΔR
  W₃ = world [] []↪ []↪ [] []

  int₀ : ∀ {R} → allocate R empty ⊢ⁱ Θ₀ ⇒ ((bindR R ∷ []) ∣ (0 ∷ []))
  int₀ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  int-ro₃ : Interior W₃ [] Θ₀ (W₃ ⊕ʳ X⊑X ^ 0)
  int-ro₃ = record
    { int-left   = interior changes[]
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; int-marks  = tt
    }

  W2⁺ : World (underΛ empty) ΔRₓ
  W2⁺ = W₃ ⊕⁺ X⊑X ^ 0

  W2⁻ : World (reps (underΛ empty) ∣ []) ΔR
  W2⁻ = world [] []↪ []↪ [] ((0 , 0) ∷ [])

  unbind₀-int : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ unb₀ ⇒ ((b ∷ Ξ) ∣ [])
  unbind₀-int = interior (changes∷ changes[]
    (step-unbind (_ , here) del-here fresh[]))

  W2⁻-int : Interior W2⁺ unb₀ unb₀ W2⁻
  W2⁻-int = record
    { int-left   = unbind₀-int
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; int-marks  = tt
    }

  W2⁺-conv : ConversionInterior W2⁺ unb₀ unb₀ W2⁺
  W2⁺-conv = record
    { conv-left       = conversion (conv-unbind (_ , here) conv[])
    ; conv-right      = conversion (conv-unbind (_ , here) conv[])
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there ()) _ _
        ; (there ()) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-marks      = tt
    }

  agree⁺ : ∀ {α β} → Paired W2⁺ α β → Agree W2⁺ α β
  agree⁺ (inj₁ ())
  agree⁺ (inj₂ here⇔) = abst-★ r-here r-here
  agree⁺ (inj₂ (there⇔ ()))

  agree⁻ : ∀ {α β} → Paired W2⁻ α β → Agree W2⁻ α β
  agree⁻ (inj₁ ())
  agree⁻ (inj₂ here⇔) = abst-★ r-here r-here
  agree⁻ (inj₂ (there⇔ ()))

  W2⁺-wf : WfWorld W2⁺
  W2⁺-wf = wf-world (both (inj₂ here⇔) joint[] , s-both s[]) agree⁺
    (namedᴸ-≤1 W2⁺ ≤1-∷[]) (namedᴿ-≤1 W2⁺ ≤1-∷[])

  W2⁻-wf : WfWorld W2⁻
  W2⁻-wf = wf-world (joint[] , s[]) agree⁻
    (namedᴸ-≤1 W2⁻ ≤1-[]) (namedᴿ-≤1 W2⁻ ≤1-[])

  id★→⊑id★→ : ∀ {Δ Δ′} {W : World Δ Δ′} → ConvImp W id★→ id★→
  id★→⊑id★→ =
    conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
    where
    i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ★⊑★))

  c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ CgR₂ ∶ ℕ⊑★
  c2-x0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑⟪⟫ int-ro₃
            (open-∀ nv-⇒ (∈-⇒ˡ ∈-var)
              (V-simple (S-cast (V-simple S-ƛ) I-gen)) I★genI-⊢
              (inst-gen (V-simple S-ƛ)) refl (open-⊕ r-here) open-none)
            W2⁺-wf
            (cast⊑cast
              (⟪⟫⊑⟪⟫ W2⁻-int W2⁻-wf
                (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ))
                I★⁻ᴸ-ty I★⁻ᴿ-ty
                (W2⁺ , W2⁺-conv , s-both s[] , id★→⊑id★→)
                (⇒⊑⇒ ★⊑★ ★⊑★))
              tagᴸ-ty tagᴿ-ty (⇒⊑⇒ I.X⊑X I.X⊑X))
            Bg-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        ℕ⊑★ C2-L-ν-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

------------------------------------------------------------------------
-- 7. The SimBackBlame counterexample (PendingOpenings §5d)
------------------------------------------------------------------------

module Cex where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_)
  open P4 using (idX; Θ₀; Unrel; nth)

  5★ : Term
  5★ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  ℕ? : Coercion
  ℕ? = `ℕ ？ 0

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  sealed5 : Term
  sealed5 = 5★ ⟪ unb₀ , tail (seal 0) ⟫

  --   L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  --   R₀  ((ΛX. λx:X. x⟨X!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  L₀ R₀ L₆ R₇ : Term
  L₀ = ((Λ idX ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)) ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  R₀ = ((Λ (ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩))
          ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  L₆ = ((sealed5 ⟪ Θ₀ , unseal 0 ⟫) ⟨ [] ∣ idᵖ ★ ⟩) ⟨ [] ∣ ℕ? ⟩
  R₇ = ((sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫) ⟨ [] ∣ ℕ? ⟩

  L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
  L₀-⊢ = tc

  R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ `ℕ
  R₀-⊢ = tc

  L₆-state : nth (evalTerms 30 L₀-⊢) 6 ≡ L₆
  L₆-state = refl

  R₇-state : nth (evalTerms 30 R₀-⊢) 7 ≡ R₇
  R₇-state = refl

  ΔR ΔRᵢ : Ctxᵗ
  ΔR  = allocate ★ empty
  ΔRᵢ = (bindR ★ ∷ []) ∣ (0 ∷ [])

  R₇-blames : ΔR ⊢ R₇ -→ blame 0 ∣ none
  R₇-blames = justStep refl

  L₆-⊢ : ΔR ∣ [] ⊢ L₆ ⦂ `ℕ
  L₆-⊢ = tc

  NotBlame : Term → Set
  NotBlame M = ∀ {ℓ} → M ≡ blame ℓ → ⊥

  L₆-never-blames : ∀ {ℓ} → ¬ (ΔR ⊢ L₆ -→* blame ℓ)
  L₆-never-blames r = all-reach {P = NotBlame} 20 L₆-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  ---------------------------------------------------------------------
  -- (a) IN HEAD'S RELATION (`d11`) THE PAIR IS DERIVABLE WITHOUT ANY
  -- CONVERSION PREMISE: the left's `+X` by `⟪⟫⊑` (X left-only, X⊑★),
  -- the right's `+X` by `⊑⟪⟫` (X rejoins through (α, α) and KEEPS X⊑★,
  -- D15), then `⊑cast` of the right's `X!` at X ⊑ ★.  So restricting
  -- `conv-unseal⊑id★` to left-only names does not remove the
  -- counterexample.

  module InD11 where
    open D

    Wαα : World ΔR ΔR
    Wαα = world [] []↪ []↪ ((0 , 0) ∷ []) []

    Wl : World ΔRᵢ ΔR
    Wl = world (X⊑★ ∷ []) (keep []↪) (skip []↪) ((0 , 0) ∷ []) []

    Wj : World ΔRᵢ ΔRᵢ
    Wj = world (X⊑★ ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

    agree★ : ∀ {Δ₀ Δ₀′} {W : World Δ₀ Δ₀′} → Δ₀ ∋rep 0 := ★
      → Δ₀′ ∋rep 0 := ★ → ϱᵍʷ W ≡ (0 , 0) ∷ [] → ϱˡʷ W ≡ []
      → ∀ {α β} → Paired W α β → Agree W α β
    agree★ l r refl refl (inj₁ here⇔) = rep-rep l r ★⊑★
    agree★ l r refl refl (inj₁ (there⇔ ()))
    agree★ l r refl refl (inj₂ ())

    Wαα-wf : WfWorld Wαα
    Wαα-wf = wf-world joint[] (agree★ r-here r-here refl refl)
      (namedᴸ-≤1 Wαα ≤1-[]) (namedᴿ-≤1 Wαα ≤1-[])

    Wl-wf : WfWorld Wl
    Wl-wf = wf-world (left-only joint[]) (agree★ r-here r-here refl refl)
      (namedᴸ-≤1 Wl ≤1-∷[]) (namedᴿ-≤1 Wl ≤1-[])

    Wj-wf : WfWorld Wj
    Wj-wf = wf-world (both (inj₁ here⇔) joint[])
      (agree★ r-here r-here refl refl)
      (namedᴸ-≤1 Wj ≤1-∷[]) (namedᴿ-≤1 Wj ≤1-∷[])

    int₀ : ∀ {R} → allocate R empty ⊢ⁱ Θ₀ ⇒ ((bindR R ∷ []) ∣ (0 ∷ []))
    int₀ = interior
      (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

    unbind₀-int : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ unb₀ ⇒ ((b ∷ Ξ) ∣ [])
    unbind₀-int = interior (changes∷ changes[]
      (step-unbind (_ , here) del-here fresh[]))

    unbind₀-conv : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ unb₀
      ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
    unbind₀-conv = conversion (conv-unbind (_ , here) conv[])

    -- the left's +X alone: X left-only (mark X⊑★)
    IntL : Interior Wαα Θ₀ [] Wl
    IntL = record
      { int-left   = int₀
      ; int-right  = interior changes[]
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , ()) _ _ }
      ; join-fresh = λ { _ () _ }
      ; int-marks  = d11-marks
          (λ { (_ , here) () _ ; (_ , there ()) _ _ })
          (λ { (_ , ()) _ _ })
      }

    -- the right's +X then: X rejoins (α, α) and keeps X⊑★ (mark-left)
    IntR : Interior Wl [] Θ₀ Wj
    IntR = record
      { int-left   = interior changes[]
      ; int-right  = int₀
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
      ; join-fresh = λ
          { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; int-marks  = d11-marks
          (λ { (_ , here) refl here → here ; (_ , there ()) _ _ })
          (λ { (_ , here) () _ ; (_ , there ()) _ _ })
      }

    Wj-unb : Interior Wj unb₀ unb₀ Wαα
    Wj-unb = record
      { int-left   = unbind₀-int
      ; int-right  = unbind₀-int
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { (_ , ()) _ _ _ }
      ; join-fresh = λ { () _ _ }
      ; int-marks  = d11-marks (λ { (_ , ()) _ _ }) (λ { (_ , ()) _ _ })
      }

    Wj-conv-self : ConversionInterior Wj unb₀ unb₀ Wj
    Wj-conv-self = record
      { conv-left       = unbind₀-conv
      ; conv-right      = unbind₀-conv
      ; conv-same-ϱᵍ    = refl
      ; conv-same-ϱˡ    = refl
      ; conv-join-cont  = λ
          { here here here here → (λ j → j) , (λ j → j)
          ; here here here (there ())
          ; here here (there ()) _
          ; here (there ()) _ _
          ; (there ()) _ _ _
          }
      ; conv-join-fresh = λ
          { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
          ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; conv-marks      = d11-cmarks
          (λ { here here m → m ; here (there ()) _ ; (there ()) _ _ })
          (λ { here here m → m ; here (there ()) _ ; (there ()) _ _ })
      }

    bSeal : BdyTy ΔRᵢ unb₀ ΔR ★ (tail (seal 0)) (` 0)
    bSeal = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
      (tc {Δ = ΔRᵢ} {M = sealed5}))))

    bL₆ : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
    bL₆ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
      (tc {Δ = ΔR} {M = sealed5 ⟪ Θ₀ , unseal 0 ⟫}))))

    bR₇ : BdyTy ΔR Θ₀ ΔRᵢ ★ ⌞ id ★ ⌟ ★
    bR₇ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
      (tc {Δ = ΔR} {M = (sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩)
                          ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫}))))

    tagX-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) ((` 0) !) (` 0) ★
    tagX-ty = proj₂ (proj₂ (cast-inv {Γ = []}
      (tc {Δ = ΔRᵢ} {M = sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩})))

    id★-ty : CastTy ΔR [] (idᵖ ★) ★ ★
    id★-ty = cast-ty (⊢id atom-★ wf-★) refl

    ℕ?-ty : CastTy ΔR [] ℕ? ★ `ℕ
    ℕ?-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = R₇})))

    five★⊑ : Wαα ∣ [] ⊢ 5★ ⊑ 5★ ∶ ★⊑★
    five★⊑ = cast⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ))
      (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★

    sealed⊑sealed : Wj ∣ [] ⊢ sealed5 ⊑ sealed5 ∶ I.X⊑X
    sealed⊑sealed =
      ⟪⟫⊑⟪⟫ Wj-unb Wαα-wf five★⊑ bSeal bSeal
        (Wj , Wj-conv-self , tt , conv-tail⊑tail (conv-seal⊑seal refl))
        I.X⊑X

    -- THE ONE-SIDED DERIVATION (no conversion is compared anywhere but
    -- the inner seal ⊑ seal)
    L₆⊑R₇ : Wαα ∣ [] ⊢ L₆ ⊑ R₇ ∶ ι⊑ι base-ℕ
    L₆⊑R₇ =
      cast⊑cast
        (cast⊑
          (⟪⟫⊑ IntL Wl-wf
            (⊑⟪⟫ IntR open-none Wj-wf
              (⊑cast sealed⊑sealed tagX-ty (I.X⊑★ here))
              bR₇ (I.X⊑★ here))
            bL₆ ★⊑★)
          id★-ty ★⊑★)
        ℕ?-ty ℕ?-ty (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- (b) UNDER SIDED MARKS THE PAIR IS NOT DERIVABLE, in any sided
  -- world: after the right's `+X` rejoins, X is X⊑X, and `⊑cast` of
  -- the right's `X!` needs X ⊑ ★ (`bad-cast`)

  cex-unrelated : Unrel L₆ R₇
  cex-unrelated s =
    no-rel
      (la-cast (la-cast (la-⟪⟫ (la-⟪⟫ (la-cast la-$ g-ℕ!))) g-id★) g-ℕ?)
      (rb-gcast (rb-⟪⟫ (rb-cast b-tag))) s

  ---------------------------------------------------------------------
  -- (c) HUNT, probe H1 ("hide, then escape"): the right hides X (−X),
  -- rebinds it (+X) with an `id(★)` conversion so that its X-tag
  -- escapes, and the escaped tag reaches `ℕ?` outside: the right
  -- blames, the left (which unseals) reaches 5.  P4's right state 6
  -- has the same inner shape, but there the tag is re-checked by `X?`.
  -- Under sided marks the pair is unrelated by the same lemma.

  LH RH : Term
  LH = (sealed5 ⟪ Θ₀ , unseal 0 ⟫) ⟨ [] ∣ ℕ? ⟩
  RH = ((((sealed5 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫)
          ⟪ unb₀ , ⌞ id ★ ⌟ ⟫) ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫) ⟨ [] ∣ ℕ? ⟩

  LH-⊢ : ΔR ∣ [] ⊢ LH ⦂ `ℕ
  LH-⊢ = tc

  RH-⊢ : ΔR ∣ [] ⊢ RH ⦂ `ℕ
  RH-⊢ = tc

  last : List Term → Term
  last []           = $ 0
  last (x ∷ [])     = x
  last (x ∷ y ∷ xs) = last (y ∷ xs)

  LH-ends : last (evalTerms 20 LH-⊢) ≡ $ 5
  LH-ends = refl

  RH-ends : last (evalTerms 20 RH-⊢) ≡ blame 0
  RH-ends = refl

  h1-unrelated : Unrel LH RH
  h1-unrelated s =
    no-rel (la-cast (la-⟪⟫ (la-⟪⟫ (la-cast la-$ g-ℕ!))) g-ℕ?)
      (rb-gcast (rb-⟪⟫ (rb-⟪⟫ (rb-⟪⟫ (rb-cast b-tag))))) s
