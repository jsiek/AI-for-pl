module proof.DGG.notes.HiddenNames where

-- File Charter:
--   * THE REPAIR CHECKED HERE ("hidden names", SidedMarks.md §6 and
--     ModeCondition.md §5; Jeremy, 2026-10-05).  A world records HOW a
--     name became one-sided.  The right embedding passes a center name
--     either by `skip` (the left name is PLAIN left-only: born so) or by
--     `hide` (the right HID a both-sided name with its own `−X`); the
--     left embedding likewise.  A continuing name that a fresh
--     other-side name rejoins KEEPS its mark when it was joined or
--     hidden (D15), and becomes X⊑X when it was plain (born one-sided).
--     The ★ conversion clauses (`conv-seal⊑id★`, `conv-unseal⊑id★`,
--     `conv-⨾seal⊑`, `conv-unseal⨾⊑`) additionally require the name to
--     be LEFT-ONLY in the conversion world.  Findings in HiddenNames.md.
--   * LOCAL COPY OF GIT HEAD ce2da4b6+ (design.md D27: pending names
--     are the field `πʷ` of `World`).  The world layer
--     (ImprecisionWorld), ConversionImprecision and the 15 rules of
--     TermImprecision are copied with exactly these changes:
--       - `_↪_` gets a fourth constructor `hide` (a `skip` that records
--         a hiding); `emb`/`relabel` treat it as `skip`;
--       - `St`, `statusAt`, `stᴿ`/`stᴸ`, `markStep`, `StOK`, `NotHid`
--         (§1); `Joint` gets `hidden-r`/`hidden-l` (§4);
--       - `Interior`: `mark-left`/`mark-right` return the status step
--         and the stepped mark; new fields `fresh-left`/`fresh-right`;
--         `ConversionInterior`'s marks step likewise (§3);
--       - the four ★ clauses take `LeftOnly` (§5).
--     The rule set itself (§6) is HEAD's, verbatim.  The side-premise
--     bundles (`Lit`, `CastTy`, `NuTy`, `BdyTy`) and the pending-name
--     side relations (`CastClaim`, `BdyClaim`, `Carried`, `Push`) are
--     world-free and imported from HEAD's TermImprecision.
--   * SYMMETRIC.  The rule above is applied on BOTH sides.  The
--     asymmetric reading (only a left name rejoined by a right `+X`)
--     does not remove the counterexample C1: a right-first derivation
--     (right `+X` born right-only at a chosen X⊑★, then the left's `+X`
--     rejoins and keeps it by `mark-right`) relates L₆ ⊑ R₇ in HEAD with
--     no ★ conversion clause and no left-only rejoin (§12, `C1.InHEAD`).
--   * SECTIONS.  §1-§6 the local copy; §7-§9 HEAD's TermImprecision
--     (P1/P2/P3/P6), Rebase (C12-C14, Cg, C2, Ch) and Regression (K)
--     examples, ported; §10 P4, all blocks; §11, §14, §16 facts for the
--     negative proofs (index shapes, left/right types, the invariant
--     `Good`, `no-S`); §12 C1 unrelated (`c1-unrelated`); §15 C3
--     unrelated (`c3-unrelated`); §17 C2 unrelated (`c2-unrelated`);
--     §13, §19, §24 NEW counterexamples C4, C4g (pops at X⊑★; C4 also
--     in HEAD); §18 Cg B1; §20 C18b B7 (two hidden names); §21-§22
--     reduction closure (status composition at a Merge; P4's right
--     Merge/IdDyn states); §23 InteriorMerge false as stated.
--   * NOT a Def module, not imported by All.agda; nothing outside this
--     file and its .md is edited.  LEFT is the more precise side.

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length; head; drop; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
  using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
  using (RepRel; _∋ᵨ_⇔_; here⇔; there⇔; sucᴸ; sucᴿ; suc²;
         shiftᴸ; shiftᴿ; shift²; _⊳_; OpenImp)
open import TermImprecision
  using (Lit; lit-$; lit-true; lit-false;
         CastTy; cast-ty; NuTy; nu-ty; BdyTy; bdy-ty;
         cast-inv; ν-inv; ⟪⟫-inv;
         CastClaim; cc-plain; cc-∀; cc-gen;
         ForallConv; fc-[]; fc-∷; BdyClaim; bc-plain; bc-∀;
         Carried; ca-[]; ca-∷; Push; push; push-none)
open import proof.ImprecisionWorld using (AtMostOneName; ≤1-[]; ≤1-∷[])

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Embeddings, with the hidden case, and the status of a center name
------------------------------------------------------------------------

-- `hide` passes a center name this side does not see, like `skip`, but
-- records that this side HID it (an unbind of a both-sided name)
infix 4 _↪_
data _↪_ : TyCtx → ImpEnv → Set where
  []↪  : [] ↪ []
  keep : ∀ {α m Δ Ω} → Δ ↪ Ω → (α ∷ Δ) ↪ (m ∷ Ω)
  skip : ∀ {m Δ Ω} → Δ ↪ Ω → Δ ↪ (m ∷ Ω)
  hide : ∀ {m Δ Ω} → Δ ↪ Ω → Δ ↪ (m ∷ Ω)

emb : ∀ {η Ω} → η ↪ Ω → Renameᵗ
emb []↪      X       = X
emb (keep ι) zero    = zero
emb (keep ι) (suc X) = suc (emb ι X)
emb (skip ι) X       = suc (emb ι X)
emb (hide ι) X       = suc (emb ι X)

relabel : ∀ {η Ω} (f : RVar → RVar) → η ↪ Ω → map f η ↪ Ω
relabel f []↪      = []↪
relabel f (keep ι) = keep (relabel f ι)
relabel f (skip ι) = skip (relabel f ι)
relabel f (hide ι) = hide (relabel f ι)

-- how an embedding passes a center position: it sees it (`joined`
-- when read from the other side), skips it (`plain`), or hid it
data St : Set where
  joined plain hidden : St

statusAt : ∀ {η Ω} → η ↪ Ω → ℕ → St
statusAt []↪      _       = plain
statusAt (keep ι) zero    = joined
statusAt (skip ι) zero    = plain
statusAt (hide ι) zero    = hidden
statusAt (keep ι) (suc c) = statusAt ι c
statusAt (skip ι) (suc c) = statusAt ι c
statusAt (hide ι) (suc c) = statusAt ι c

-- THE MARK RULE: a plain one-sided name that the other side rejoins
-- becomes X⊑X; every other continuing name keeps its mark (D15)
markStep : St → St → VarImp → VarImp
markStep plain  joined m = X⊑X
markStep plain  plain  m = m
markStep plain  hidden m = m
markStep joined _      m = m
markStep hidden _      m = m

-- the allowed status steps of a continuing name: a joined name may be
-- hidden (the other side unbinds its partner) and a hidden or plain
-- one may be rejoined; nothing becomes plain from joined/hidden, and a
-- plain name is never hidden
StOK : St → St → Set
StOK joined joined = ⊤
StOK joined hidden = ⊤
StOK joined plain  = ⊥
StOK hidden joined = ⊤
StOK hidden hidden = ⊤
StOK hidden plain  = ⊥
StOK plain  joined = ⊤
StOK plain  plain  = ⊤
StOK plain  hidden = ⊥

-- a name whose status does not change keeps its mark
keepMark : ∀ {μ : List VarImp} {c m} (s : St)
  → μ ∋ˡ c := m → μ ∋ˡ c := markStep s s m
keepMark joined h = h
keepMark plain  h = h
keepMark hidden h = h

-- a name a boundary introduces is never hidden
NotHid : St → Set
NotHid hidden = ⊥
NotHid joined = ⊤
NotHid plain  = ⊤

------------------------------------------------------------------------
-- 2. Worlds (HEAD's record, unchanged) and the statuses of names
------------------------------------------------------------------------

record World (Δ Δ′ : Ctxᵗ) : Set where
  constructor world
  field
    μʷ  : ImpEnv
    ηᴸʷ : names Δ ↪ μʷ
    ηᴿʷ : names Δ′ ↪ μʷ
    ϱᵍʷ : RepRel
    ϱˡʷ : RepRel
    πʷ  : List ℕ
open World public

Paired : World Δ Δ′ → RVar → RVar → Set
Paired W α β = (ϱᵍʷ W ∋ᵨ α ⇔ β) ⊎ (ϱˡʷ W ∋ᵨ α ⇔ β)

Joins : World Δ Δ′ → ℕ → ℕ → Set
Joins W X X′ = emb (ηᴸʷ W) X ≡ emb (ηᴿʷ W) X′

-- the right's view of left name X, the left's view of right name X′
stᴿ : World Δ Δ′ → ℕ → St
stᴿ W X = statusAt (ηᴿʷ W) (emb (ηᴸʷ W) X)

stᴸ : World Δ Δ′ → ℕ → St
stᴸ W X′ = statusAt (ηᴸʷ W) (emb (ηᴿʷ W) X′)

∅ʷ : World empty empty
∅ʷ = world [] []↪ []↪ [] [] []

embᴸ : World Δ Δ′ → Ty → Ty
embᴸ W = renameᵗ (emb (ηᴸʷ W))

embᴿ : World Δ Δ′ → Ty → Ty
embᴿ W = renameᵗ (emb (ηᴿʷ W))

infix 4 _⊑ᵂ⟨_⟩_
_⊑ᵂ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ᵂ⟨ W ⟩ A′ =
  OpenImp (μʷ W) (map (emb (ηᴿʷ W)) (πʷ W)) (emb (ηᴸʷ W)) A (embᴿ W A′)

-- world operations (HEAD's, verbatim)
infixl 6 _⊕_ _⊕ᴿ_
_⊕_ : World Δ Δ′ → VarImp → World (underΛ Δ) (underΛ Δ′)
world μ η η′ ϱᵍ ϱˡ π ⊕ m =
  world (m ∷ μ) (keep (relabel suc η)) (keep (relabel suc η′))
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc π)

infixl 6 _⊕ᴸ
_⊕ᴸ : World Δ Δ′ → World (underΛ Δ) Δ′
world μ η η′ ϱᵍ ϱˡ π ⊕ᴸ =
  world (X⊑★ ∷ μ) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) π

_⊕ᴿ_ : World Δ Δ′ → VarImp → World Δ (underΛ Δ′)
world μ η η′ ϱᵍ ϱˡ π ⊕ᴿ m =
  world (m ∷ μ) (skip η) (keep (relabel suc η′))
        (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ) (map suc π)

infixl 6 _⊕⁺_^_
_⊕⁺_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ π ⊕⁺ m ^ β =
  world (m ∷ μ) (keep (relabel suc η)) (keep η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) (map suc π)

infixl 6 _⊕ʳ_^_
_⊕ʳ_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World Δ (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ π ⊕ʳ m ^ β =
  world (m ∷ μ) (skip η) (keep η′) ϱᵍ ϱˡ (map suc π)

data Join↪ {η : TyCtx}
    : ∀ {η′ μ} → η ↪ μ → η′ ↪ μ → (zero ∷ map suc η) ↪ μ → ℕ → Set where
  join-here : ∀ {β η′ μ m} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
    → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
  join-there : ∀ {β η′ μ m k} {ι : η ↪ μ} {ι′ : η′ ↪ μ}
      {ι⁺ : (zero ∷ map suc η) ↪ μ}
    → Join↪ ι ι′ ι⁺ k
    → Join↪ (skip {m = m} ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

data Open1 {Δ Δ′ : Ctxᵗ} : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  open1 : ∀ {μ ϱᵍ ϱˡ k π β} {ι : names Δ ↪ μ} {ι′ : names Δ′ ↪ μ}
      {ι⁺ : names (underΛ Δ) ↪ μ}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → Open1 (world μ ι ι′ ϱᵍ ϱˡ (k ∷ π))
            (world μ ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) π)

open-⊕ : ∀ {W : World Δ Δ′} {m β}
  → Δ′ ∋rep β := ★
  → Open1 (record (W ⊕ʳ m ^ β) { πʷ = 0 ∷ map suc (πʷ W) }) (W ⊕⁺ m ^ β)
open-⊕ hβ = open1 join-here here hβ

underν² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
underν² R R′ (world μ η η′ ϱᵍ ϱˡ π) =
  world μ (relabel suc η) (relabel suc η′)
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) π

------------------------------------------------------------------------
-- 3. The interior world and the conversion-context world
------------------------------------------------------------------------

-- HEAD's `Interior`, with the marks of continuing names stepped by
-- their status (`markStep`, `StOK`) and fresh names not hidden.
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
    -- a continuing name: its status steps (`StOK`), and its mark steps:
    -- kept, except a PLAIN one-sided name rejoined, which is X⊑X
    mark-left : ∀ {X Xₑ m}
      → Δᵢ ∋tv X → toExt Θ X ≡ just Xₑ
      → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
      → StOK (stᴿ W Xₑ) (stᴿ Wᵢ X)
        × (μʷ Wᵢ ∋ˡ emb (ηᴸʷ Wᵢ) X := markStep (stᴿ W Xₑ) (stᴿ Wᵢ X) m)
    mark-right : ∀ {X′ X′ₑ m}
      → Δ′ᵢ ∋tv X′ → toExt Θ′ X′ ≡ just X′ₑ
      → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
      → StOK (stᴸ W X′ₑ) (stᴸ Wᵢ X′)
        × (μʷ Wᵢ ∋ˡ emb (ηᴿʷ Wᵢ) X′ := markStep (stᴸ W X′ₑ) (stᴸ Wᵢ X′) m)
    -- a name the boundary introduces is joined or plain, never hidden
    fresh-left  : ∀ {X} → Δᵢ ∋tv X → Fresh Θ X → NotHid (stᴿ Wᵢ X)
    fresh-right : ∀ {X′} → Δ′ᵢ ∋tv X′ → Fresh Θ′ X′ → NotHid (stᴸ Wᵢ X′)
open Interior public

-- HEAD's `ConversionInterior`, the marks stepped as in `Interior`
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
    conv-mark-left : ∀ {X Xₑ α m}
      → Δᶜ ∋ᵗ X := α → Δ ∋ᵗ Xₑ := α
      → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
      → μʷ Wᶜ ∋ˡ emb (ηᴸʷ Wᶜ) X := markStep (stᴿ W Xₑ) (stᴿ Wᶜ X) m
    conv-mark-right : ∀ {X′ X′ₑ β m}
      → Δ′ᶜ ∋ᵗ X′ := β → Δ′ ∋ᵗ X′ₑ := β
      → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
      → μʷ Wᶜ ∋ˡ emb (ηᴿʷ Wᶜ) X′ := markStep (stᴸ W X′ₑ) (stᴸ Wᶜ X′) m
open ConversionInterior public

------------------------------------------------------------------------
-- 4. Term contexts and well-formedness (HEAD's, with two Joint cases)
------------------------------------------------------------------------

record CtxImpEntry {ns ns′ : TyCtx} (μ : ImpEnv) (ηᴸ : ns ↪ μ)
    (ηᴿ : ns′ ↪ μ) : Set where
  constructor ctx-imp
  field
    tyᴸ  : Ty
    tyᴿ  : Ty
    impʷ : μ ⊢ renameᵗ (emb ηᴸ) tyᴸ ⊑ renameᵗ (emb ηᴿ) tyᴿ
open CtxImpEntry public

Entries : ∀ {ns ns′} (μ : ImpEnv) → ns ↪ μ → ns′ ↪ μ → Set
Entries μ ηᴸ ηᴿ = List (CtxImpEntry μ ηᴸ ηᴿ)

CtxImp : World Δ Δ′ → Set
CtxImp W = Entries (μʷ W) (ηᴸʷ W) (ηᴿʷ W)

lhs : ∀ {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ} → Entries μ ηᴸ ηᴿ → List Ty
lhs = map tyᴸ

rhs : ∀ {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ} → Entries μ ηᴸ ηᴿ → List Ty
rhs = map tyᴿ

infix 4 _∋ʷ_⦂_
data _∋ʷ_⦂_ {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ}
    : Entries μ ηᴸ ηᴿ → ℕ → CtxImpEntry μ ηᴸ ηᴿ → Set where
  Zʷ : ∀ {γ e} → (e ∷ γ) ∋ʷ zero ⦂ e
  Sʷ : ∀ {γ e e′ x} → γ ∋ʷ x ⦂ e → (e′ ∷ γ) ∋ʷ suc x ⦂ e

data LiftCtx {ns ns′ μ} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ} (m : VarImp)
    : Entries μ ηᴸ ηᴿ
    → Entries (m ∷ μ) (keep {α = zero} (relabel suc ηᴸ))
              (keep {α = zero} (relabel suc ηᴿ))
    → Set where
  lift-[] : LiftCtx m [] []
  lift-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtx m γ γ′
    → LiftCtx m (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ A′) p′ ∷ γ′)

data LiftCtxᴸ {ns ns′ ns₁ μ μ₁} {ηᴸ : ns ↪ μ} {ηᴿ : ns′ ↪ μ}
    {ηᴸ₁ : ns₁ ↪ μ₁} {ηᴿ₁ : ns′ ↪ μ₁}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
  liftᴸ-[] : LiftCtxᴸ [] []
  liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
    → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

-- The two embeddings jointly.  NEW: a center name the left sees and
-- the right HID (`hidden-r`, X⊑★ as a left-only name), and one the
-- right sees and the left hid (`hidden-l`, any mark as a right-only
-- name).
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
  hidden-r   : ∀ {α η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → Joint P ι ι′
    → Joint P (keep {α = α} {m = X⊑★} ι) (hide {m = X⊑★} ι′)
  hidden-l   : ∀ {β m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → Joint P ι ι′
    → Joint P (hide {m = m} ι) (keep {α = β} {m = m} ι′)

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

NoNamedPartner : World Δ Δ′ → RVar → Set
NoNamedPartner {Δ} W β = ∀ {α} → names Δ ∋ᵅ α → ¬ Paired W α β

RightOnly : World Δ Δ′ → ℕ → Set
RightOnly {Δ = Δ} W k = ∀ {X} → Δ ∋tv X → ¬ Joins W X k

PendingOK : World Δ Δ′ → ℕ → Set
PendingOK {Δ′ = Δ′} W k =
  Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k
    × (μʷ W ∋ˡ emb (ηᴿʷ W) k := X⊑★) × NoNamedPartner W β

record WfWorld (W : World Δ Δ′) : Set where
  constructor wf-world
  field
    wf-joint : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
    wf-agree : ∀ {α β} → Paired W α β → Agree W α β
    wf-namedᴸ : NamedUniqueᴸ W
    wf-namedᴿ : NamedUniqueᴿ W
    wf-pending  : All (PendingOK W) (πʷ W)
    wf-distinct : AllPairs _≢_ (πʷ W)
open WfWorld public

namedᴸ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ) → NamedUniqueᴸ W
namedᴸ-≤1 W h a a′ _ _ _ = h a a′

namedᴿ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ′) → NamedUniqueᴿ W
namedᴿ-≤1 W h _ b b′ _ _ = h b b′

------------------------------------------------------------------------
-- 5. Conversion imprecision (HEAD's; the ★ clauses read LEFT-ONLY)
------------------------------------------------------------------------

-- a left name no right name of the (conversion) world joins
LeftOnly : World Δ Δ′ → ℕ → Set
LeftOnly {Δ′ = Δ′} W X = ∀ {X′} → Δ′ ∋tv X′ → ¬ Joins W X X′

mutual
  data MidImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Mid → Mid → Set where
    conv-id⊑id : ∀ {A A′} → μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′
      → MidImp W (id A) (id A′)
    conv-↦⊑↦ : ∀ {s s′ c c′} → ConvImp W s s′ → ConvImp W c c′
      → MidImp W (s ↦ c) (s′ ↦ c′)
    conv-∀⊑∀ : ∀ {c c′} → ConvImp (W ⊕ X⊑X) c c′
      → MidImp W (`∀ c) (`∀ c′)
    conv-∀⊑ : ∀ {c g′} → ConvImp (W ⊕ᴸ) c ⌞ g′ ⌟
      → MidImp W (`∀ c) g′

  data TailImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Tail → Tail → Set where
    conv-mid⊑mid : ∀ {g g′} → MidImp W g g′
      → TailImp W (mid g) (mid g′)
    conv-seal⊑seal : ∀ {X X′} → Joins W X X′
      → TailImp W (seal X) (seal X′)
    conv-⨾seal⊑⨾seal : ∀ {t t′ X X′} → TailImp W t t′ → Joins W X X′
      → TailImp W (t ⨾seal X) (t′ ⨾seal X′)
    -- RESTRICTED: X is left-only in the conversion world
    conv-seal⊑id★ : ∀ {X} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → LeftOnly W X
      → TailImp W (seal X) (mid (id ★))
    conv-⨾seal⊑ : ∀ {t t′ X} → TailImp W t t′
      → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★ → LeftOnly W X
      → TailImp W (t ⨾seal X) t′

  data ConvImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) : Conv → Conv → Set where
    conv-tail⊑tail : ∀ {t t′} → TailImp W t t′
      → ConvImp W (tail t) (tail t′)
    conv-unseal⊑unseal : ∀ {X X′} → Joins W X X′
      → ConvImp W (unseal X) (unseal X′)
    conv-unseal⨾⊑unseal⨾ : ∀ {X X′ c c′} → Joins W X X′ → ConvImp W c c′
      → ConvImp W (unseal X ⨾ c) (unseal X′ ⨾ c′)
    -- RESTRICTED: X is left-only in the conversion world
    conv-unseal⊑id★ : ∀ {X} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → LeftOnly W X
      → ConvImp W (unseal X) ⌞ id ★ ⌟
    conv-unseal⨾⊑ : ∀ {X c c′} → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
      → LeftOnly W X → ConvImp W c c′
      → ConvImp W (unseal X ⨾ c) c′

NuConversionImp : ∀ {Δ Δ′ A A′ C C′ c c′ B B′}
  → (W : World Δ Δ′)
  → NuTy Δ A C c B → NuTy Δ′ A′ C′ c′ B′ → Set
NuConversionImp {c = c} {c′ = c′} W
  (nu-ty {R = R} {Δᶜ = Δᶜ} wA rA mw ⊢c eq wB)
  (nu-ty {R = R′} {Δᶜ = Δ′ᶜ} wA′ rA′ mw′ ⊢c′ eq′ wB′) =
  Σ[ Wᶜ ∈ World Δᶜ Δ′ᶜ ]
    (ConversionInterior (underν² R R′ W) TyBetaBoundary TyBetaBoundary Wᶜ
    × ConvImp Wᶜ c c′)

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
    (ConversionInterior W Θ Θ′ Wᶜ × ConvImp Wᶜ c c′)

------------------------------------------------------------------------
-- 6. The relation: HEAD's 15 rules (D27), verbatim
------------------------------------------------------------------------

data Claim : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  claim-fresh : ∀ {Ω ϱᵍ ϱˡ} {ηᴸ : names Δ ↪ Ω} {ηᴿ : names Δ′ ↪ Ω}
    → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in Claim W (W ⊕ᴸ)
  claim-pop   : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
    → Open1 W W₁ → Claim W W₁

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ}
    : (W : World Δ Δ′) → CtxImp W → Term → Term
    → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ k ι}
    → Lit k ι
    → (p : ι ⊑ᵂ⟨ W ⟩ ι)
    → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A
    → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ L L′ M M′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  blame⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ ℓ M′ A A′}
    → Δ ⊢ᵗ A
    → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
    → (p : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {W : World Δ Δ′} {πₚ γ M M′ μ c B A A′}
      {p : B ⊑ᵂ⟨ record W { πʷ = πₚ } ⟩ A′}
    → CastClaim M c (πʷ W) πₚ
    → record W { πʷ = πₚ } ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ μ c B A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  ⊑cast : ∀ {W : World Δ Δ′} {γ M M′ μ′ c′ A B′ A′}
      {p : A ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′
    → Value V
    → Value V′
    → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  Λ⊑ : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {γ γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W₁ ⟩ B′}
    → Claim W W₁
    → NonVar A
    → 0 ∈ᵗ A
    → LiftCtxᴸ γ γ′
    → Value V
    → W₁ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  ν⊑ν : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B)
    → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ ★
    → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in
      ∀ {Δᵢ Δ′ᵢ Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ}
    → let Wᵢ = world {Δᵢ} {Δ′ᵢ} Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ [] in
      ∀ {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
    → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ
    → BdyClaim M c (πʷ W) (πʷ Wᵢ)
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {γ M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → Push Θ′ M (πʷ W) (πʷ Wᵢ)
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

infix 3 _∣_⊢_⊑_∶⟨_,_⟩_
_∣_⊢_⊑_∶⟨_,_⟩_ : ∀ {Δ Δ′} (W : World Δ Δ′) → CtxImp W → Term → Term
  → (A A′ : Ty) → A ⊑ᵂ⟨ W ⟩ A′ → Set
W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩ p = _∣_⊢_⊑_∶_ W γ M M′ {A} {A′} p

------------------------------------------------------------------------
-- 7. HEAD's TermImprecisionExamples (P1, P2, P3, P6), ported: imports
-- replaced, and each `Interior` gets its two `fresh-*` fields
------------------------------------------------------------------------

module TIE where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.ImprecisionExamples
    using (L1; R1; L1-⊢; R1-⊢; R2; L3-⊢; R3-⊢; L6; R6; L6-⊢; R6-⊢)

  ------------------------------------------------------------------------
  -- Shared pieces
  ------------------------------------------------------------------------

  idX : Term
  idX = ƛ (` 0) ∙ ` 0

  revX : Conv
  revX = reveal 0 (` 0 ⇒ ` 0)

  ℕ⊑★ : ∀ {μ} → μ ⊢ `ℕ ⊑ ★
  ℕ⊑★ = ι⊑★ base-ℕ

  5⟨ℕ!⟩ : Term
  5⟨ℕ!⟩ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  -- the argument `5 ⊑ 5⟨ℕ!⟩` at ℕ ⊑ ★, in any world whose right side has
  -- no names (the cast carries `[]`)
  five⊑ : ∀ {Δ Ξ′ Ω ϱᵍ ϱˡ} {ηᴸ : names Δ ↪ Ω} {ηᴿ : [] ↪ Ω}
    → let W = world {Δ} {Ξ′ ∣ []} Ω ηᴸ ηᴿ ϱᵍ ϱˡ [] in ∀ {γ : CtxImp W}
    → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
  five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

  ∀X⇒X : Ty
  ∀X⇒X = `∀ (` 0 ⇒ ` 0)

  ------------------------------------------------------------------------
  -- P1, initial pair
  ------------------------------------------------------------------------

  νL νR : Term
  νL = ν `ℕ · Λ idX ⟨ revX ⟩
  νR = ν ★ · Λ idX ⟨ revX ⟩

  νL-⊢ : empty ∣ [] ⊢ νL ⦂ `ℕ ⇒ `ℕ
  νL-⊢ = tc

  νR-⊢ : empty ∣ [] ⊢ νR ⦂ ★ ⇒ ★
  νR-⊢ = tc

  νL-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νL-ty = proj₂ (proj₂ (ν-inv νL-⊢))

  νR-ty : NuTy empty ★ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  νR-ty = proj₂ (proj₂ (ν-inv νR-⊢))

  ------------------------------------------------------------------------
  -- P1, after both TyBetas
  ------------------------------------------------------------------------

  Θ₀ : Boundary
  Θ₀ = bind 0 0 ∷ []

  L1′ R1′ : Term
  L1′ = (idX ⟪ Θ₀ , revX ⟫) · $ 5
  R1′ = (idX ⟪ Θ₀ , revX ⟫) · 5⟨ℕ!⟩

  L1′-state : head (drop 1 (evalTerms 10 L1-⊢)) ≡ just L1′
  L1′-state = refl

  R1′-state : head (drop 1 (evalTerms 11 R1-⊢)) ≡ just R1′
  R1′-state = refl

  ΔL ΔR ΔLᵢ ΔRᵢ : Ctxᵗ
  ΔL = allocate `ℕ empty
  ΔR = allocate ★ empty
  ΔLᵢ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])
  ΔRᵢ = (bindR ★ ∷ []) ∣ (0 ∷ [])

  ConvCtx₀ : Ty → Ctxᵗ
  ConvCtx₀ R = (bindR R ∷ []) ∣ (0 ∷ [])

  conv₀ : ∀ {R} → allocate R empty ⊢ᶜ Θ₀ ⇒ ConvCtx₀ R
  conv₀ = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

  -- The ν-conversion world has one both-sided name and the ν-bound pair
  -- in ϱˡ, not ϱᵍ.
  Wν : ∀ {R R′} → World (ConvCtx₀ R) (ConvCtx₀ R′)
  Wν = world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ []) []

  Wν-conv : ∀ {R R′}
    → ConversionInterior (underν² R R′ ∅ʷ) Θ₀ Θ₀ Wν
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
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  revX⊑revX : ∀ {Δ Δ′} {W : World Δ Δ′}
    → Joins W 0 0 → ConvImp W revX revX
  revX⊑revX j =
    conv-tail⊑tail
      (conv-mid⊑mid
        (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                   (conv-unseal⊑unseal j)))

  νLR-conv : NuConversionImp ∅ʷ νL-ty νR-ty
  νLR-conv = Wν , Wν-conv , revX⊑revX refl

  p1-init : ∅ʷ ∣ [] ⊢ L1 ⊑ R1 ∶ ℕ⊑★
  p1-init =
    ·⊑· (ν⊑ν (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
                (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
             ℕ⊑★ νL-ty νR-ty νLR-conv (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  -- the exterior world: no names; the two store rep. vars paired (ϱᵍ)
  W₁ : World ΔL ΔR
  W₁ = world [] []↪ []↪ ((0 , 0) ∷ []) [] []

  -- the interior world: X both-sided at X⊑X
  Wᵢ₁ : World ΔLᵢ ΔRᵢ
  Wᵢ₁ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  int₀ : ∀ {R} → allocate R empty ⊢ⁱ Θ₀ ⇒ ((bindR R ∷ []) ∣ (0 ∷ []))
  int₀ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  Wᵢ₁-int : Interior W₁ Θ₀ Θ₀ Wᵢ₁
  Wᵢ₁-int = record
    { int-left   = int₀
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    }

  Wᵢ₁-conv : ConversionInterior W₁ Θ₀ Θ₀ Wᵢ₁
  Wᵢ₁-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
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

  bL bR : Term
  bL = idX ⟪ Θ₀ , revX ⟫
  bR = bL

  bL-⊢ : ΔL ∣ [] ⊢ bL ⦂ `ℕ ⇒ `ℕ
  bL-⊢ = tc

  bR-⊢ : ΔR ∣ [] ⊢ bR ⦂ ★ ⇒ ★
  bR-⊢ = tc

  bL-ty : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bL-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv bL-⊢)))

  bR-ty : BdyTy ΔR Θ₀ ΔRᵢ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bR-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv bR-⊢)))

  bLR-conv : BdyConversionImp W₁ bL-ty bR-ty
  bLR-conv = Wᵢ₁ , Wᵢ₁-conv , revX⊑revX refl

  Wᵢ₁-wf : WfWorld Wᵢ₁
  Wᵢ₁-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 Wᵢ₁ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₁ ≤1-∷[]) [] []
    where
    agree : ∀ {α β} → Paired Wᵢ₁ α β → Agree Wᵢ₁ α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  p1-tybeta : W₁ ∣ [] ⊢ L1′ ⊑ R1′ ∶ ℕ⊑★
  p1-tybeta =
    ·⊑· (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
                (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bL-ty bR-ty bLR-conv
                (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  ------------------------------------------------------------------------
  -- P2, after the left's TyBeta (a left-only boundary)
  ------------------------------------------------------------------------

  R2-state : R2 ≡ (ƛ ★ ∙ ` 0) · 5⟨ℕ!⟩
  R2-state = refl

  W₂ : World ΔL empty
  W₂ = world [] []↪ []↪ [] [] []

  -- X is left-only, so its mark is X⊑★
  Wᵢ₂ : World ΔLᵢ empty
  Wᵢ₂ = world (X⊑★ ∷ []) (keep []↪) (skip []↪) [] [] []

  Wᵢ₂-int : Interior W₂ Θ₀ [] Wᵢ₂
  Wᵢ₂-int = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    ; fresh-right = λ { (_ , ()) _ }
    }

  Wᵢ₂-wf : WfWorld Wᵢ₂
  Wᵢ₂-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 Wᵢ₂ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₂ ≤1-[]) [] []
    where
    agree : ∀ {α β} → Paired Wᵢ₂ α β → Agree Wᵢ₂ α β
    agree (inj₁ ())
    agree (inj₂ ())

  p2-tybeta : W₂ ∣ [] ⊢ L1′ ⊑ R2 ∶ ℕ⊑★
  p2-tybeta =
    ·⊑· (⟪⟫⊑ Wᵢ₂-int bc-plain (Wᵢ₂-wf)
                (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) bL-ty
                (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  ------------------------------------------------------------------------
  -- P3, after the right's Inst, TyBeta and Beta, before the left's
  -- TyBeta: ⊑⟪⟫ pushes the Inst boundary's name and Λ⊑ pops it (D27;
  -- before D26, ∀⊑⟪+⟫; D26: an opening) to relate the left Λ to the right's
  -- Inst boundary
  ------------------------------------------------------------------------

  R3′ : Term
  R3′ = ((idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ ★ ⟩) · 5⟨ℕ!⟩

  L3′-state : head (drop 1 (evalTerms 11 L3-⊢)) ≡ just L1
  L3′-state = refl

  R3′-state : head (drop 3 (evalTerms 16 R3-⊢)) ≡ just R3′
  R3′-state = refl

  W₃ : World empty ΔR
  W₃ = world [] []↪ []↪ [] [] []

  -- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★)
  ∀id⊑★ : ∀X⇒X ⊑ᵂ⟨ W₃ ⟩ (★ ⇒ ★)
  ∀id⊑★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  ΛidX-⊢ : empty ∣ [] ⊢ Λ idX ⦂ ∀X⇒X
  ΛidX-⊢ = tc

  -- the Inst boundary `+X^α` (α:=★ at rep. var 0) alone: X is a
  -- right-only name, with the mark m chosen here (D11), and PUSHED: the
  -- interior world has the pending name 0 (D27)
  int-ro₃ : ∀ {m} → Interior W₃ [] Θ₀ (record (W₃ ⊕ʳ m ^ 0) { πʷ = 0 ∷ [] })
  int-ro₃ = record
    { int-left   = interior changes[]
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    }

  -- inside the Inst boundary: X right-only at X⊑★, and PENDING (D27): it
  -- is bound to the ★ rep. var αᴿ and has no named left partner
  Wi₃-wf : WfWorld (record (W₃ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] })
  Wi₃-wf = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 (W₃ ⊕ʳ X⊑★ ^ 0) ≤1-[]) (namedᴿ-≤1 (W₃ ⊕ʳ X⊑★ ^ 0) ≤1-∷[])
    ((0 , here , r-here , (λ { (_ , ()) }) , here , (λ { (_ , ()) })) ∷ [])
    ([] ∷ [])

  vΛidX : Value (Λ idX)
  vΛidX = V-simple (S-Λ (V-simple S-ƛ))

  -- THE CORE: ⊑⟪⟫ PUSHES the boundary's name X (the left is a value);
  -- Λ⊑ POPS it: the left binder joins X, its abstract rep. var paired
  -- lexically with αᴿ:=★ (`open-⊕`: the popped world is `W₃ ⊕⁺ X⊑★ ^ 0`);
  -- then ƛ⊑ƛ at X ⊑ X
  core₃ : W₃ ∣ [] ⊢ Λ idX ⊑ idX ⟪ Θ₀ , revX ⟫ ∶ ∀id⊑★
  core₃ =
    ⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vΛidX)) Wi₃-wf
      (Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[]
        (V-simple S-ƛ) (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (⇒⊑⇒ X⊑X X⊑X))
      bR-ty ∀id⊑★

  p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
  p3-inst =
    ·⊑· (ν⊑ (⊑cast core₃
                   (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl)
                   ∀id⊑★)
            ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑

  ------------------------------------------------------------------------
  -- P6, the initial ν pair and the state after both TyBetas
  ------------------------------------------------------------------------

  ∀6L ∀6R : Ty
  ∀6L = `∀ (` 0 ⇒ `ℕ)
  ∀6R = `∀ (` 0 ⇒ ★)

  ∀6L⊑∀6R : ∀6L ⊑ᵂ⟨ ∅ʷ ⟩ ∀6R
  ∀6L⊑∀6R = ∀⊑∀ (⇒⊑⇒ X⊑X ℕ⊑★)

  c6L c6R : Conv
  c6L = reveal 0 (` 0 ⇒ `ℕ)
  c6R = reveal 0 (` 0 ⇒ ★)

  ν6L ν6R : Term
  ν6L = ν `𝔹 · ` 0 ⟨ c6L ⟩
  ν6R = ν `𝔹 · ` 0 ⟨ c6R ⟩

  ν6L-⊢ : empty ∣ ∀6L ∷ [] ⊢ ν6L ⦂ `𝔹 ⇒ `ℕ
  ν6L-⊢ = tc

  ν6R-⊢ : empty ∣ ∀6R ∷ [] ⊢ ν6R ⦂ `𝔹 ⇒ ★
  ν6R-⊢ = tc

  ν6L-ty : NuTy empty `𝔹 (` 0 ⇒ `ℕ) c6L (`𝔹 ⇒ `ℕ)
  ν6L-ty = proj₂ (proj₂ (ν-inv ν6L-⊢))

  ν6R-ty : NuTy empty `𝔹 (` 0 ⇒ ★) c6R (`𝔹 ⇒ ★)
  ν6R-ty = proj₂ (proj₂ (ν-inv ν6R-⊢))

  c6⊑ : ∀ {Δ Δ′} {W : World Δ Δ′}
    → Joins W 0 0 → ConvImp W c6L c6R
  c6⊑ j =
    conv-tail⊑tail
      (conv-mid⊑mid
        (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                   (conv-tail⊑tail
                     (conv-mid⊑mid (conv-id⊑id ℕ⊑★)))))

  ν6-conv : NuConversionImp ∅ʷ ν6L-ty ν6R-ty
  ν6-conv = Wν , Wν-conv , c6⊑ refl

  p6-init-ν : ∅ʷ ∣ ctx-imp ∀6L ∀6R ∀6L⊑∀6R ∷ []
    ⊢ ν6L ⊑ ν6R ∶ ⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★
  p6-init-ν =
    ν⊑ν (x⊑x Zʷ) (ι⊑ι base-𝔹) ν6L-ty ν6R-ty ν6-conv
         (⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★)

  Δ6 Δ6ᵢ : Ctxᵗ
  Δ6 = allocate `𝔹 empty
  Δ6ᵢ = ConvCtx₀ `𝔹

  W₆ : World Δ6 Δ6
  W₆ = world [] []↪ []↪ ((0 , 0) ∷ []) [] []

  Wᵢ₆ : World Δ6ᵢ Δ6ᵢ
  Wᵢ₆ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  int₆ : Δ6 ⊢ⁱ Θ₀ ⇒ Δ6ᵢ
  int₆ = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  Wᵢ₆-int : Interior W₆ Θ₀ Θ₀ Wᵢ₆
  Wᵢ₆-int = record
    { int-left   = int₆
    ; int-right  = int₆
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    }

  Wᵢ₆-wf : WfWorld Wᵢ₆
  Wᵢ₆-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 Wᵢ₆ ≤1-∷[]) (namedᴿ-≤1 Wᵢ₆ ≤1-∷[]) [] []
    where
    agree : ∀ {α β} → Paired Wᵢ₆ α β → Agree Wᵢ₆ α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑ι base-𝔹)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wᵢ₆-conv : ConversionInterior W₆ Θ₀ Θ₀ Wᵢ₆
  Wᵢ₆-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
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

  body6L body6R : Term
  body6L = ƛ (` 0) ∙ $ 7
  body6R = body6L ⟨ X∼X ∷ [] ∣ idᵖ (` 0) ↦ᵖ (`ℕ !) ⟩

  b6L b6R : Term
  b6L = body6L ⟪ Θ₀ , c6L ⟫
  b6R = body6R ⟪ Θ₀ , c6R ⟫

  L6′ R6′ : Term
  L6′ = b6L · `true
  R6′ = b6R · `true

  L6′-state : head (drop 2 (evalTerms 10 L6-⊢)) ≡ just L6′
  L6′-state = refl

  R6′-state : head (drop 2 (evalTerms 13 R6-⊢)) ≡ just R6′
  R6′-state = refl

  body6R-⊢ : Δ6ᵢ ∣ [] ⊢ body6R ⦂ ` 0 ⇒ ★
  body6R-⊢ = tc

  body6R-ty : CastTy Δ6ᵢ (X∼X ∷ []) (idᵖ (` 0) ↦ᵖ (`ℕ !))
                           (` 0 ⇒ `ℕ) (` 0 ⇒ ★)
  body6R-ty = proj₂ (proj₂ (cast-inv body6R-⊢))

  b6L-⊢ : Δ6 ∣ [] ⊢ b6L ⦂ `𝔹 ⇒ `ℕ
  b6L-⊢ = tc

  b6R-⊢ : Δ6 ∣ [] ⊢ b6R ⦂ `𝔹 ⇒ ★
  b6R-⊢ = tc

  b6L-ty : BdyTy Δ6 Θ₀ Δ6ᵢ (` 0 ⇒ `ℕ) c6L (`𝔹 ⇒ `ℕ)
  b6L-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv b6L-⊢)))

  b6R-ty : BdyTy Δ6 Θ₀ Δ6ᵢ (` 0 ⇒ ★) c6R (`𝔹 ⇒ ★)
  b6R-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv b6R-⊢)))

  b6-conv : BdyConversionImp W₆ b6L-ty b6R-ty
  b6-conv = Wᵢ₆ , Wᵢ₆-conv , c6⊑ refl

  p6-tybeta : W₆ ∣ [] ⊢ L6′ ⊑ R6′ ∶ ℕ⊑★
  p6-tybeta =
    ·⊑·
      (⟪⟫⊑⟪⟫ Wᵢ₆-int Wᵢ₆-wf
        (⊑cast
          (ƛ⊑ƛ {pA = X⊑X} {pB = ι⊑ι base-ℕ}
            tf tf (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
          body6R-ty (⇒⊑⇒ X⊑X ℕ⊑★))
        b6L-ty b6R-ty b6-conv (⇒⊑⇒ (ι⊑ι base-𝔹) ℕ⊑★))
      (κ⊑κ lit-true (ι⊑ι base-𝔹))

------------------------------------------------------------------------
-- 8. HEAD's TermImprecisionRebaseExamples (C12, C13, C14, Cg, C2, Ch),
-- ported.  CHANGE: the left-only worlds that a RIGHT `−X` produces
-- (`Wcᴸ`, `Wg⁻`) are HIDDEN (`hide`, Joint `hidden-r`), so the right
-- `+X^β` that rejoins c keeps c⊑★ (`Wc-bindᴿ`: hidden → joined)
------------------------------------------------------------------------

module Rebase where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples
  open import TermSubst using (crossΛᴹ)
  open import examples.ImprecisionExamples using (L1)
  open TIE
    using (idX; revX; ℕ⊑★; five⊑; Θ₀; L1′; ΔL; ΔR; ΔLᵢ; ΔRᵢ;
           W₁; Wᵢ₁; Wᵢ₁-int; Wᵢ₁-conv; Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv;
           revX⊑revX; νL-ty; Wν; Wν-conv; W₃; R3′; p3-inst; int-ro₃;
           core₃; Wi₃-wf; vΛidX)

  -- Pieces shared by the blocks
  ------------------------------------------------------------------------

  -- `id(★) → id(★)` as a coercion and as a conversion
  id★↦ : Coercion
  id★↦ = idᵖ ★ ↦ᵖ idᵖ ★

  id★→ : Conv
  id★→ = tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))

  -- the gen wrapper's coercion `X! → X?ℓ0`
  tagX↦ : Coercion
  tagX↦ = (` 0) ! ↦ᵖ (` 0) ？ 0

  X⇒X⊑★⇒★ : ∀ {Δ Δ′} {W : World Δ Δ′} → μʷ W ∋ˡ emb (ηᴸʷ W) 0 := X⊑★
    → μʷ W ⊢ embᴸ W (` 0 ⇒ ` 0) ⊑ embᴿ W (★ ⇒ ★)
  X⇒X⊑★⇒★ m = ⇒⊑⇒ (X⊑★ m) (X⊑★ m)

  ℕ⇒ℕ : ∀ {Δ Δ′} (W : World Δ Δ′) → μʷ W ⊢ embᴸ W (`ℕ ⇒ `ℕ) ⊑ embᴿ W (`ℕ ⇒ `ℕ)
  ℕ⇒ℕ W = ⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)

  ------------------------------------------------------------------------
  -- D25 worlds: one left name c against a chain of right boundaries
  ------------------------------------------------------------------------

  -- C12–C14 B1.  The left is `[+X^αᴸ] (λx:X. x) ⟨−X → +X⟩` at
  -- ΔL = αᴸ:=ℕ.  The right nests `[+Y^β] ([−Y^β] … ⟨…⟩)⟨Y! → Y?ℓ0⟩` around
  -- the Inst boundary `[+X^αᴿ] (λx:X. x)`.  Every right `+_^β` names a
  -- right rep. var paired with αᴸ (D25), so c rejoins at each one; every
  -- right `−_^β` leaves c left-only at c⊑★ (D15).  The store pairing ϱ is
  -- global and the same in every world of the derivation.

  module _ {Ξ′ : RepCtx} {ϱ : RepRel} where

    -- outside: no names
    Wc⁰ : World ΔL (Ξ′ ∣ [])
    Wc⁰ = world [] []↪ []↪ ϱ [] []

    -- c both-sided, its right name at rep. var β
    Wc² : (β : RVar) → World ΔLᵢ (Ξ′ ∣ (β ∷ []))
    Wc² β = world (X⊑★ ∷ []) (keep []↪) (keep []↪) ϱ [] []

    -- c left-only
    Wcᴸ : World ΔLᵢ (Ξ′ ∣ [])
    Wcᴸ = world (X⊑★ ∷ []) (keep []↪) (hide []↪) ϱ [] []

    -- the matched TyBeta boundaries [+X^αᴸ] ∥ [+Y^0]
    Wc-bind² : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0 → Interior Wc⁰ Θ₀ Θ₀ (Wc² 0)
    Wc-bind² v p = record
      { int-left   = interior (changes∷ changes[]
                       (step-bind (_ , here) fresh[] ins-here))
      ; int-right  = interior (changes∷ changes[]
                       (step-bind v fresh[] ins-here))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
      ; join-fresh = λ { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
                       ; here (there ()) _ ; (there ()) _ _ }
      ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there ()) _ }
      ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
      }

    Wc-bind²-conv : Ξ′ ∋ʳ 0 → ϱ ∋ᵨ 0 ⇔ 0
      → ConversionInterior Wc⁰ Θ₀ Θ₀ (Wc² 0)
    Wc-bind²-conv v p = record
      { conv-left       =
          conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
      ; conv-right      = conversion (conv-bind v conv[] fresh[] ins-here)
      ; conv-same-ϱᵍ    = refl
      ; conv-same-ϱˡ    = refl
      ; conv-join-cont  = λ { _ _ () _ }
      ; conv-join-fresh = λ
          { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; conv-mark-left  = λ { _ () _ }
      ; conv-mark-right = λ { _ () _ }
      }

    -- a right-only −Y^β: c goes left-only, keeping c⊑★
    Wc-unbindᴿ : ∀ {β} → Ξ′ ∋ʳ β → Interior (Wc² β) [] (unbind 0 β ∷ []) Wcᴸ
    Wc-unbindᴿ v = record
      { int-left   = interior changes[]
      ; int-right  = interior (changes∷ changes[]
                       (step-unbind v del-here fresh[]))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , ()) _ _ }
      ; join-fresh = λ { _ () _ }
      ; mark-left  = λ { (_ , here) refl here → tt , here ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , ()) _ _ }
      ; fresh-left  = λ _ ()
      ; fresh-right = λ { (_ , ()) _ }
      }

    -- a right-only +X^β: c rejoins αᴸ, β's left partner named in scope (D25)
    Wc-bindᴿ : ∀ {β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
      → Interior Wcᴸ [] (bind 0 β ∷ []) (Wc² β)
    Wc-bindᴿ v p = record
      { int-left   = interior changes[]
      ; int-right  = interior (changes∷ changes[] (step-bind v fresh[] ins-here))
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
      ; join-fresh = λ
          { here here _ → (λ _ → inj₁ p) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; mark-left  = λ { (_ , here) refl here → tt , here ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      ; fresh-left  = λ _ ()
      ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
      }

  -- the types at these worlds
  c⊑★ᴸ : ∀ Ξ′ ϱ → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wcᴸ {Ξ′} {ϱ} ⟩ (★ ⇒ ★)
  c⊑★ᴸ Ξ′ ϱ = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

  c⊑★² : ∀ Ξ′ ϱ β → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} β ⟩ (★ ⇒ ★)
  c⊑★² Ξ′ ϱ β = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

  c⊑c² : ∀ Ξ′ ϱ β → (` 0 ⇒ ` 0) ⊑ᵂ⟨ Wc² {Ξ′} {ϱ} β ⟩ (` 0 ⇒ ` 0)
  c⊑c² Ξ′ ϱ β = ⇒⊑⇒ (X⊑X {X = 0}) (X⊑X {X = 0})

  -- the core `[+X^αᴿ] (λx:X. x) ⟨−X → +X⟩` against λx:X. x, and one
  -- gen layer `[+Y^β] ([−Y^β] M ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩` around a
  -- right term M, at the right context Ξ′ (the typing bundles are passed
  -- in, read off `tc` at each instance)
  core⊑ : ∀ {Ξ′ ϱ β} → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ′} {ϱ} β)
    → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → (Wcᴸ {Ξ′} {ϱ}) ∣ [] ⊢ idX ⊑ idX ⟪ bind 0 β ∷ [] , revX ⟫
        ∶ c⊑★ᴸ Ξ′ ϱ
  core⊑ {Ξ′} {ϱ} v p W²-wf b =
    ⊑⟪⟫ (Wc-bindᴿ v p) push-none (W²-wf)
      (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
      b (c⊑★ᴸ Ξ′ ϱ)

  -- the gen layer's right term, around M
  genLayer : RVar → Term → Term
  genLayer β M =
    (((M ⟨ [] ∣ id★↦ ⟩) ⟪ unbind 0 β ∷ [] , id★→ ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩)
      ⟪ bind 0 β ∷ [] , revX ⟫

  layer⊑ : ∀ {Ξ′ ϱ β M}
    → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ′} {ϱ} β)
    → WfWorld (Wcᴸ {Ξ′} {ϱ})
    → (Wcᴸ {Ξ′} {ϱ}) ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (β ∷ [])) (unbind 0 β ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (β ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → (Wcᴸ {Ξ′} {ϱ}) ∣ [] ⊢ idX ⊑ genLayer β M
        ∶ c⊑★ᴸ Ξ′ ϱ
  layer⊑ {Ξ′} {ϱ} {β} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b =
    ⊑⟪⟫ (Wc-bindᴿ v p) push-none (W²-wf)
      (⊑cast {A = ` 0 ⇒ ` 0}
        (⊑⟪⟫ (Wc-unbindᴿ v) push-none (Wᴸ-wf)
          (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ)) bᵤ (c⊑★² Ξ′ ϱ β))
        cₜ (c⊑c² Ξ′ ϱ β))
      b (c⊑★ᴸ Ξ′ ϱ)

  -- the outermost gen layer, matched with the left's TyBeta boundary
  outer⊑ : ∀ {Ξ′ ϱ M B′}
    → (v : Ξ′ ∋ʳ 0) → (p : ϱ ∋ᵨ 0 ⇔ 0)
    → WfWorld (Wc² {Ξ′} {ϱ} 0)
    → WfWorld (Wcᴸ {Ξ′} {ϱ})
    → (Wcᴸ {Ξ′} {ϱ}) ∣ [] ⊢ idX ⊑ M ∶ c⊑★ᴸ Ξ′ ϱ
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → (b : BdyTy (Ξ′ ∣ []) Θ₀ (Ξ′ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX B′)
    → BdyConversionImp (Wc⁰ {Ξ′} {ϱ}) bL-ty b
    → (q : (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ Wc⁰ {Ξ′} {ϱ} ⟩ B′)
    → (Wc⁰ {Ξ′} {ϱ}) ∣ [] ⊢ idX ⟪ Θ₀ , revX ⟫ ⊑ genLayer 0 M ∶ q
  outer⊑ {Ξ′} {ϱ} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b bc q =
    ⟪⟫⊑⟪⟫ (Wc-bind² v p) W²-wf
      (⊑cast {A = ` 0 ⇒ ` 0}
        (⊑⟪⟫ (Wc-unbindᴿ v) push-none (Wᴸ-wf)
          (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ)) bᵤ (c⊑★² Ξ′ ϱ 0))
        cₜ (c⊑c² Ξ′ ϱ 0))
      bL-ty b bc q

  ------------------------------------------------------------------------
  -- C12 B1: one left rep. var, two right partners (D25)
  ------------------------------------------------------------------------

  -- C12's state 3: the right has run Inst, TyBeta (αᴿ:=★) and the source
  -- TyBeta (βᴿ:=ℕ); βᴿ is rep. var 0, αᴿ is rep. var 1
  Ξ₁₂ : RepCtx
  Ξ₁₂ = bindR `ℕ ∷ bindR ★ ∷ []

  -- αᴸ (0) is paired with both βᴿ (0) and αᴿ (1)
  ϱ₁₂ : RepRel
  ϱ₁₂ = (0 , 0) ∷ (0 , 1) ∷ []

  B12x B12 : Term
  B12x = idX ⟪ bind 0 1 ∷ [] , revX ⟫
  B12  = genLayer 0 B12x

  C12-R₃ : Term
  C12-R₃ = B12 · $ 5

  C12-L₁-state : head (drop 1 (evalTerms 10 C12-L-⊢)) ≡ just L1′
  C12-L₁-state = refl

  C12-R₃-state : head (drop 3 (evalTerms 24 C12-R-⊢)) ≡ just C12-R₃
  C12-R₃-state = refl

  -- the right contexts: outside, and with the one name at rep. var β
  ΔR₁₂ : Ctxᵗ
  ΔR₁₂ = Ξ₁₂ ∣ []

  ΔR₁₂^ : RVar → Ctxᵗ
  ΔR₁₂^ β = Ξ₁₂ ∣ (β ∷ [])

  -- typing side premises, read off `tc`
  B12-ty : BdyTy ΔR₁₂ Θ₀ (ΔR₁₂^ 0) (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  B12-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂} {M = B12}))))

  B12x-ty : BdyTy ΔR₁₂ (bind 0 1 ∷ []) (ΔR₁₂^ 1) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  B12x-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂} {M = B12x}))))

  id★↦-ty : ∀ {Ξ} → CastTy (Ξ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  -- one gen layer's two inner pieces
  unbTerm tagTerm : RVar → Term → Term
  unbTerm β M = (M ⟨ [] ∣ id★↦ ⟩) ⟪ unbind 0 β ∷ [] , id★→ ⟫
  tagTerm β M = unbTerm β M ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

  B12ᵤ-ty : BdyTy (ΔR₁₂^ 0) (unbind 0 0 ∷ []) ΔR₁₂ (★ ⇒ ★) id★→ (★ ⇒ ★)
  B12ᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔR₁₂^ 0} {M = unbTerm 0 B12x}))))

  B12ₜ-ty : CastTy (ΔR₁₂^ 0) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B12ₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = ΔR₁₂^ 0} {M = tagTerm 0 B12x})))

  -- the worlds of the derivation
  W₁₂ : World ΔL ΔR₁₂
  W₁₂ = Wc⁰ {Ξ₁₂} {ϱ₁₂}

  -- WfWorld for the four worlds of c12-b1: outside; c both-sided naming
  -- (αᴸ, βᴿ); c left-only; c both-sided naming (αᴸ, αᴿ).  Each has
  -- ϱᵍ = ϱ₁₂ and ϱˡ = ∅.
  module Wf₁₂ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₂ ∣ nsR)
    W = world μ η η′ ϱ₁₂ [] []

    -- both pairs agree: ℕ ⊑ ℕ and ℕ ⊑ ★
    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())

  W₁₂-wf : WfWorld W₁₂
  W₁₂-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wf₁₂ [] []↪ []↪

  W₁₂²-wf : WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} 0)
  W₁₂²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] []
    where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₁₂ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₂} {ϱ₁₂})
  W₁₂ᴸ-wf = wf-world (hidden-r joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (hide []↪)

  W₁₂ˣ-wf : WfWorld (Wc² {Ξ₁₂} {ϱ₁₂} 1)
  W₁₂ˣ-wf = wf-world (both (inj₁ (there⇔ here⇔)) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] []
    where open Wf₁₂ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  c12-b1 : W₁₂ ∣ [] ⊢ L1′ ⊑ C12-R₃ ∶ ι⊑ι base-ℕ
  c12-b1 =
    ·⊑·
      (outer⊑ (_ , here) here⇔ W₁₂²-wf W₁₂ᴸ-wf
        (core⊑ (_ , there here) (there⇔ here⇔) W₁₂ˣ-wf B12x-ty)
        id★↦-ty B12ᵤ-ty B12ₜ-ty B12-ty
        (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₁₂))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- Shared pieces for the right-led blocks
  ------------------------------------------------------------------------

  -- ∀X.X→X ⊑ ★→★, by ∀⊑ (X left-only at X⊑★), in any world (the plain
  -- index, which is `_⊑ᵂ⟨_⟩_` at a world with no pending name)
  ∀id⊑★ : ∀ {Δ Δ′} (W : World Δ Δ′)
    → μʷ W ⊢ embᴸ W (`∀ (` 0 ⇒ ` 0)) ⊑ embᴿ W (★ ⇒ ★)
  ∀id⊑★ W = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  ∀id⊑∀id : ∀ {Δ Δ′} (W : World Δ Δ′)
    → μʷ W ⊢ embᴸ W (`∀ (` 0 ⇒ ` 0)) ⊑ embᴿ W (`∀ (` 0 ⇒ ` 0))
  ∀id⊑∀id W = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

  ★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → μʷ W ⊢ embᴸ W (★ ⇒ ★) ⊑ embᴿ W (★ ⇒ ★)
  ★⇒★ W = ⇒⊑⇒ ★⊑★ ★⊑★

  ℕ⇒ℕ⊑★⇒★ : ∀ {Δ Δ′} (W : World Δ Δ′) → μʷ W ⊢ embᴸ W (`ℕ ⇒ `ℕ) ⊑ embᴿ W (★ ⇒ ★)
  ℕ⇒ℕ⊑★⇒★ W = ⇒⊑⇒ ℕ⊑★ ℕ⊑★

  id★→⊑id★→ : ∀ {Δ Δ′} {W : World Δ Δ′} → ConvImp W id★→ id★→
  id★→⊑id★→ =
    conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
    where
    i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ★⊑★))

  -- `[−X^α] (λx:★. x) ⟨id(★) → id(★)⟩`: the gen value's crossed body, and
  -- the gen wrapper `(…)⟨X! → X?ℓ0⟩^[X:★∼X]` over it (on the left this is
  -- `inst_X` of the gen value, `inst-gen`; on the right it is what the
  -- right's TyBeta left inside its boundary)
  I★⁻ I★gen : Term
  I★⁻ = I★ ⟪ unbind 0 0 ∷ [] , id★→ ⟫
  I★gen = I★⁻ ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

  I★⁻-crossed : crossΛᴹ I★ (srcᵖ genI) ≡ I★⁻
  I★⁻-crossed = refl

  -- the right's state after Inst and TyBeta (αᴿ:=★), Cg-R = C2-R state 2
  Bg Cg-R₂ : Term
  Bg = I★gen ⟪ Θ₀ , revX ⟫
  Cg-R₂ = (Bg ⟨ [] ∣ id★↦ ⟩) · dyn 5

  Cg-R₂-state : head (drop 2 (evalTerms 21 Cg-R-⊢)) ≡ just Cg-R₂
  Cg-R₂-state = refl

  -- the right contexts: the exterior (αᴿ:=★ at rep. var 0), inside the
  -- Inst boundary `+X^αᴿ`, inside the gen value's `−X^αᴿ`
  ΔRₓ : Ctxᵗ
  ΔRₓ = reps ΔR ∣ (0 ∷ [])

  Bg-ty : BdyTy ΔR (bind 0 0 ∷ []) ΔRₓ (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  Bg-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = Bg}))))

  I★⁻ᴿ-ty : BdyTy ΔRₓ (unbind 0 0 ∷ []) ΔR (★ ⇒ ★) id★→ (★ ⇒ ★)
  I★⁻ᴿ-ty =
    proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★⁻}))))

  tagᴿ-ty : CastTy ΔRₓ (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᴿ-ty =
    proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRₓ} {M = I★gen})))

  id★↦ᴿ-ty : CastTy ΔR [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦ᴿ-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  ΛidX-⊢ : empty ∣ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
  ΛidX-⊢ = tc

  ------------------------------------------------------------------------
  -- Cg's right-led block X0 (D27: ⊑⟪⟫ pushes X at mark X⊑★, Λ⊑ pops it)
  ------------------------------------------------------------------------

  -- the popped world: the left Λ's abstract rep. var paired
  -- LEXICALLY with αᴿ:=★; the shared name at X⊑★ (chosen here, D11)
  Wg⁺ : World (underΛ empty) ΔRₓ
  Wg⁺ = W₃ ⊕⁺ X⊑★ ^ 0

  -- inside the right's −X^αᴿ: X is left-only, X⊑★
  Wg⁻ : World (underΛ empty) ΔR
  Wg⁻ = world (X⊑★ ∷ []) (keep []↪) (hide []↪) [] ((0 , 0) ∷ []) []

  Wg⁻-int : Interior Wg⁺ [] (unbind 0 0 ∷ []) Wg⁻
  Wg⁻-int = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) refl here → tt , here ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ _ ()
    ; fresh-right = λ { (_ , ()) _ }
    }

  -- WfWorld for the worlds of the lexical pair (aᴸ_ΛY, αᴿ:=★): the left
  -- member abstract, the right member at ★ (`abst-★`)
  module WfΛ★ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((abstR ∷ []) ∣ nsL) ((bindR ★ ∷ []) ∣ nsR)
    W = world μ η η′ [] ((0 , 0) ∷ []) []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ ())
    agree (inj₂ here⇔) = abst-★ r-here r-here
    agree (inj₂ (there⇔ ()))


  Wg⁺-wf : WfWorld Wg⁺
  Wg⁺-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] []
    where open WfΛ★ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  Wg⁻-wf : WfWorld Wg⁻
  Wg⁻-wf = wf-world (hidden-r joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open WfΛ★ (X⊑★ ∷ []) (keep []↪) (hide []↪)

  -- the pop's premise: the left's λx:X.x against the right's gen value,
  -- at the popped world Wg⁺ (the right's tag cast, then its −X^αᴿ)
  cg-body : record (W₃ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] } ∣ [] ⊢ I ⊑ I★gen
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  cg-body =
    Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (⊑cast
        (⊑⟪⟫ Wg⁻-int push-none (Wg⁻-wf)
          (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
          I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺} here))
        tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
      (⇒⊑⇒ X⊑X X⊑X)

  -- ⊑⟪⟫ pushes X, Λ⊑ pops it first; then the right's tag cast and −X
  cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
  cg-x0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vΛidX)) Wi₃-wf cg-body
            Bg-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
      five⊑

  ------------------------------------------------------------------------
  -- C2's right-led block X0 (D27: ⊑⟪⟫ pushes X, the left gen cast pops
  -- it, `cc-gen`)
  ------------------------------------------------------------------------

  I★genI : Term
  I★genI = I★ ⟨ [] ∣ genI ⟩

  I★genI-⊢ : empty ∣ [] ⊢ I★genI ⦂ `∀ (` 0 ⇒ ` 0)
  I★genI-⊢ = tc

  C2-L-ν : Term
  C2-L-ν = ν `ℕ · I★genI ⟨ revX ⟩

  C2-L-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C2-L-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C2-L-ν})))

  C2-L₀-is : C2-L ≡ C2-L-ν · $ 5
  C2-L₀-is = refl

  unbind₀-int : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ (unbind 0 0 ∷ [])
    ⇒ ((b ∷ Ξ) ∣ [])
  unbind₀-int = interior (changes∷ changes[]
    (step-unbind (_ , here) del-here fresh[]))

  unbind₀-conv : ∀ {b} {Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ (unbind 0 0 ∷ [])
    ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  unbind₀-conv = conversion (conv-unbind (_ , here) conv[])

  -- the right's `−X^αᴿ` alone: X goes away (the left has no name here)
  IntN : ∀ {m} → Interior (W₃ ⊕ʳ m ^ 0) [] (unbind 0 0 ∷ []) W₃
  IntN = record
    { int-left   = interior changes[]
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , ()) _ }
    }

  -- the conversion contexts skip the unbinds: they are the exterior
  unbind₀-conv-self : ∀ {b b′ Ξ Ξ′}
      {W : World ((b ∷ Ξ) ∣ (0 ∷ [])) ((b′ ∷ Ξ′) ∣ (0 ∷ []))}
    → ConversionInterior W (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W
  unbind₀-conv-self {W = W} = record
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
    ; conv-mark-left  = λ { here here m → keepMark (stᴿ W 0) m
                          ; here (there ()) _ ; (there ()) _ _ }
    ; conv-mark-right = λ { here here m → keepMark (stᴸ W 0) m
                          ; here (there ()) _ ; (there ()) _ _ }
    }

  W₃-wf : WfWorld W₃
  W₃-wf = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (namedᴸ-≤1 W₃ ≤1-[]) (namedᴿ-≤1 W₃ ≤1-[]) [] []

  vI★genI : Value I★genI
  vI★genI = V-simple (S-cast (V-simple S-ƛ) I-gen)

  genIᴸ-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genIᴸ-ty = proj₂ (proj₂ (cast-inv {Γ = []} I★genI-⊢))

  -- the left gen cast against the right's tag cast: ⊑cast first (Y ⊑ ★
  -- by the pending name's X⊑★), then cast⊑ POPS at the gen (`cc-gen`):
  -- the left's λx:★.x is related at the UNOPENED world W₃, against the
  -- right's `[−X^αᴿ] λx:★.x`
  c2-body : record (W₃ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] } ∣ [] ⊢ I★genI ⊑ I★gen
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  c2-body =
    ⊑cast
      (cast⊑ (cc-gen (V-simple S-ƛ))
        (⊑⟪⟫ IntN push-none (W₃-wf)
          (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ)) I★⁻ᴿ-ty (⇒⊑⇒ ★⊑★ ★⊑★))
        genIᴸ-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X)

  c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
  c2-x0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vI★genI)) Wi₃-wf c2-body
            Bg-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ W₃))
      five⊑

  ------------------------------------------------------------------------
  -- C2 B6 and B7 (D15: a multi-entry boundary, with its conversion
  -- premise)
  ------------------------------------------------------------------------

  -- the multi-entry scope (−X, +X): head last, so `unbind` acts first
  Θ⁻⁺ : Boundary
  Θ⁻⁺ = bind 0 0 ∷ unbind 0 0 ∷ []

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  -- `[−X^α] m ⟨−X⟩`, for the leaf m = 5 (left) or 5⟨ℕ!⟩ (right)
  seal-leaf : Term → Term
  seal-leaf m = m ⟪ unb₀ , tail (seal 0) ⟫

  tagX untagX : Coercion
  tagX   = (` 0) !
  untagX = (` 0) ？ 0

  C2-B6 C2-B7 : Term → Term
  C2-B6 m =
    (((seal-leaf m ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , tail (mid (id ★)) ⟫)
      ⟨ ★∼X ∷ [] ∣ untagX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  C2-B7 m =
    (((seal-leaf m ⟪ Θ⁻⁺ , tail (mid (id (` 0))) ⟫) ⟨ X∼★ ∷ [] ∣ tagX ⟩)
      ⟨ ★∼X ∷ [] ∣ untagX ⟩) ⟪ Θ₀ , unseal 0 ⟫

  C2-L₆-state : head (drop 6 (evalTerms 16 C2-L-⊢)) ≡ just (C2-B6 ($ 5))
  C2-L₆-state = refl

  C2-R₉-state : head (drop 9 (evalTerms 21 C2-R-⊢))
    ≡ just (C2-B6 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩)
  C2-R₉-state = refl

  C2-L₇-state : head (drop 7 (evalTerms 16 C2-L-⊢)) ≡ just (C2-B7 ($ 5))
  C2-L₇-state = refl

  C2-R₁₀-state : head (drop 10 (evalTerms 21 C2-R-⊢))
    ≡ just (C2-B7 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩)
  C2-R₁₀-state = refl

  -- the worlds: W₁ outside (ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)}), Wᵢ₁ inside the outer
  -- boundaries (X both-sided at X⊑X, chosen at B1); the final interior
  -- world of (−X, +X) ∥ (−X, +X) is Wᵢ₁ again (X continues, keeps X⊑X);
  -- inside the two −X, W₁ again (no names)
  Wᵢ₁-unb : Interior Wᵢ₁ unb₀ unb₀ W₁
  Wᵢ₁-unb = record
    { int-left   = unbind₀-int
    ; int-right  = unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , ()) _ }
    }

  W₁-wf : WfWorld W₁
  W₁-wf = wf-world joint[] agree (namedᴸ-≤1 W₁ ≤1-[]) (namedᴿ-≤1 W₁ ≤1-[]) [] []
    where
    agree : ∀ {α β} → Paired W₁ α β → Agree W₁ α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Θ⁻⁺-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ Θ⁻⁺ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  Θ⁻⁺-int = interior (changes∷
    (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))
    (step-bind (_ , here) fresh[] ins-here))

  Θ⁻⁺-conv : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ Θ⁻⁺ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  Θ⁻⁺-conv = conversion (conv-bind-live (_ , here)
    (conv-unbind (_ , here) conv[]) here)

  -- D15: X goes away and comes back within the entries; only the final
  -- interior world is given, and X keeps its mark
  Wᵢ₁-Θ⁻⁺ : Interior Wᵢ₁ Θ⁻⁺ Θ⁻⁺ Wᵢ₁
  Wᵢ₁-Θ⁻⁺ = record
    { int-left   = Θ⁻⁺-int
    ; int-right  = Θ⁻⁺-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ j → j) , (λ j → j)
        ; (_ , here) (_ , there ()) _ _
        ; (_ , there ()) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) refl m → tt , m ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) refl m → tt , m ; (_ , there ()) _ _ }
    ; fresh-left  = λ { (_ , here) () ; (_ , there ()) _ }
    ; fresh-right = λ { (_ , here) () ; (_ , there ()) _ }
    }

  Wᵢ₁-Θ⁻⁺-conv : ConversionInterior Wᵢ₁ Θ⁻⁺ Θ⁻⁺ Wᵢ₁
  Wᵢ₁-Θ⁻⁺-conv = record
    { conv-left       = Θ⁻⁺-conv
    ; conv-right      = Θ⁻⁺-conv
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
    ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    ; conv-mark-right = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    }

  -- typing side premises
  leafᴸ-ty : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  leafᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = seal-leaf ($ 5)}))))

  leafᴿ-ty : BdyTy ΔRᵢ unb₀ ΔR ★ (tail (seal 0)) (` 0)
  leafᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = seal-leaf (dyn 5)}))))

  tag-ty : ∀ {R} → CastTy ((bindR R ∷ []) ∣ (0 ∷ [])) (X∼★ ∷ []) tagX (` 0) ★
  tag-ty = cast-ty (⊢tag-var (_ , here) here tag-dyn) refl

  untag-ty : ∀ {R} → CastTy ((bindR R ∷ []) ∣ (0 ∷ [])) (★∼X ∷ []) untagX ★ (` 0)
  untag-ty = cast-ty (⊢check-var (_ , here) here check-dyn) refl

  -- B6's middle boundary `[−X, +X] (…)⟨X!⟩ ⟨id(★)⟩`
  mid6 : Term → Term
  mid6 m = (seal-leaf m ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , tail (mid (id ★)) ⟫

  mid6ᴸ-ty : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ ★ (tail (mid (id ★))) ★
  mid6ᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = mid6 ($ 5)}))))

  mid6ᴿ-ty : BdyTy ΔRᵢ Θ⁻⁺ ΔRᵢ ★ (tail (mid (id ★))) ★
  mid6ᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = mid6 (dyn 5)}))))

  -- B7's middle boundary `[−X, +X] (…) ⟨id(X)⟩`
  mid7 : Term → Term
  mid7 m = seal-leaf m ⟪ Θ⁻⁺ , tail (mid (id (` 0))) ⟫

  mid7ᴸ-ty : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0) (tail (mid (id (` 0)))) (` 0)
  mid7ᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = mid7 ($ 5)}))))

  mid7ᴿ-ty : BdyTy ΔRᵢ Θ⁻⁺ ΔRᵢ (` 0) (tail (mid (id (` 0)))) (` 0)
  mid7ᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = mid7 (dyn 5)}))))

  -- the outer boundary `[+X] (…) ⟨+X⟩`
  outᴸ-ty : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  outᴸ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C2-B6 ($ 5)}))))

  outᴿ-ty : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
  outᴿ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = C2-B6 (dyn 5)}))))

  id★ᴿ-ty : CastTy ΔR [] (idᵖ ★) ★ ★
  id★ᴿ-ty = cast-ty (⊢id atom-★ wf-★) refl

  X⊑X₀ : ` 0 ⊑ᵂ⟨ Wᵢ₁ ⟩ ` 0
  X⊑X₀ = X⊑X

  -- the leaf `[−X] 5 ⟨−X⟩ ⊑ [−X] 5⟨ℕ!⟩ ⟨−X⟩`, with `−X ⊑ −X`
  leaf⊑ : Wᵢ₁ ∣ [] ⊢ seal-leaf ($ 5) ⊑ seal-leaf (dyn 5) ∶ X⊑X₀
  leaf⊑ =
    ⟪⟫⊑⟪⟫ Wᵢ₁-unb W₁-wf five⊑ leafᴸ-ty leafᴿ-ty
      (Wᵢ₁ , unbind₀-conv-self , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  c2-b6 : W₁ ∣ [] ⊢ C2-B6 ($ 5) ⊑ C2-B6 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩ ∶ ℕ⊑★
  c2-b6 =
    ⊑cast
      (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
        (cast⊑cast
          (⟪⟫⊑⟪⟫ Wᵢ₁-Θ⁻⁺ Wᵢ₁-wf
            (cast⊑cast leaf⊑ tag-ty tag-ty ★⊑★)
            mid6ᴸ-ty mid6ᴿ-ty
            (Wᵢ₁ , Wᵢ₁-Θ⁻⁺-conv , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ★⊑★)))
            ★⊑★)
          untag-ty untag-ty X⊑X)
        outᴸ-ty outᴿ-ty
        (Wᵢ₁ , Wᵢ₁-conv , conv-unseal⊑unseal refl) ℕ⊑★)
      id★ᴿ-ty ℕ⊑★

  c2-b7 : W₁ ∣ [] ⊢ C2-B7 ($ 5) ⊑ C2-B7 (dyn 5) ⟨ [] ∣ idᵖ ★ ⟩ ∶ ℕ⊑★
  c2-b7 =
    ⊑cast
      (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
        (cast⊑cast
          (cast⊑cast
            (⟪⟫⊑⟪⟫ Wᵢ₁-Θ⁻⁺ Wᵢ₁-wf
              leaf⊑ mid7ᴸ-ty mid7ᴿ-ty
              (Wᵢ₁ , Wᵢ₁-Θ⁻⁺-conv ,
               conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id X⊑X)))
              X⊑X)
            tag-ty tag-ty ★⊑★)
          untag-ty untag-ty X⊑X)
        outᴸ-ty′ outᴿ-ty′
        (Wᵢ₁ , Wᵢ₁-conv , conv-unseal⊑unseal refl) ℕ⊑★)
      id★ᴿ-ty ℕ⊑★
    where
    outᴸ-ty′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
    outᴸ-ty′ = proj₂ (proj₂ (proj₂
      (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C2-B7 ($ 5)}))))
    outᴿ-ty′ : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
    outᴿ-ty′ = proj₂ (proj₂ (proj₂
      (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = C2-B7 (dyn 5)}))))

  ------------------------------------------------------------------------
  -- C13 B1 and C14 B1: two and three right partners (D25)
  ------------------------------------------------------------------------

  -- C13's state 4: two Inst/TyBeta pairs on the right, βᴿ:=★ (0) and
  -- αᴿ:=★ (1); the store pairing is ϱ₁₂ again, now ℕ ⊑ ★ twice
  Ξ₁₃ : RepCtx
  Ξ₁₃ = bindR ★ ∷ bindR ★ ∷ []

  C13-R₄ : Term
  C13-R₄ = (B12 ⟨ [] ∣ id★↦ ⟩) · dyn 5

  C13-R₄-state : head (drop 4 (evalTerms 29 C13-R-⊢)) ≡ just C13-R₄
  C13-R₄-state = refl

  B13-ty : BdyTy (Ξ₁₃ ∣ []) Θ₀ (Ξ₁₃ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  B13-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ []} {M = B12}))))

  B13x-ty : BdyTy (Ξ₁₃ ∣ []) (bind 0 1 ∷ []) (Ξ₁₃ ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX
    (★ ⇒ ★)
  B13x-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ []} {M = B12x}))))

  B13ᵤ-ty : BdyTy (Ξ₁₃ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ₁₃ ∣ []) (★ ⇒ ★) id★→
    (★ ⇒ ★)
  B13ᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ (0 ∷ [])} {M = unbTerm 0 B12x}))))

  B13ₜ-ty : CastTy (Ξ₁₃ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B13ₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = Ξ₁₃ ∣ (0 ∷ [])} {M = tagTerm 0 B12x})))

  W₁₃ : World ΔL (Ξ₁₃ ∣ [])
  W₁₃ = Wc⁰ {Ξ₁₃} {ϱ₁₂}

  module Wf₁₃ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₃ ∣ nsR)
    W = world μ η η′ ϱ₁₂ [] []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) =
      rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())


  W₁₃²-wf : ∀ {β}
    → ϱ₁₂ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ₁₃} {ϱ₁₂} β)
  W₁₃²-wf p = wf-world (both (inj₁ p) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] []
    where open Wf₁₃ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₁₃ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₃} {ϱ₁₂})
  W₁₃ᴸ-wf = wf-world (hidden-r joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wf₁₃ (X⊑★ ∷ []) (keep []↪) (hide []↪)

  c13-b1 : W₁₃ ∣ [] ⊢ L1′ ⊑ C13-R₄ ∶ ℕ⊑★
  c13-b1 =
    ·⊑·
      (⊑cast
        (outer⊑ (_ , here) here⇔ (W₁₃²-wf here⇔) W₁₃ᴸ-wf
          (core⊑ (_ , there here) (there⇔ here⇔)
            (W₁₃²-wf (there⇔ here⇔)) B13x-ty)
          id★↦-ty B13ᵤ-ty B13ₜ-ty B13-ty
          (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
          (ℕ⇒ℕ⊑★⇒★ W₁₃))
        id★↦-ty (ℕ⇒ℕ⊑★⇒★ W₁₃))
      five⊑

  -- C14's state 5: γᴿ:=ℕ (0) from the source ν, βᴿ:=★ (1) and αᴿ:=★ (2)
  -- from the two Inst/TyBeta pairs; αᴸ has three right partners
  Ξ₁₄ : RepCtx
  Ξ₁₄ = bindR `ℕ ∷ bindR ★ ∷ bindR ★ ∷ []

  ϱ₁₄ : RepRel
  ϱ₁₄ = (0 , 0) ∷ (0 , 1) ∷ (0 , 2) ∷ []

  B14x B14y B14 : Term
  B14x = idX ⟪ bind 0 2 ∷ [] , revX ⟫
  B14y = genLayer 1 B14x
  B14  = genLayer 0 B14y

  C14-R₅ : Term
  C14-R₅ = B14 · $ 5

  C14-R₅-state : head (drop 5 (evalTerms 38 C14-R-⊢)) ≡ just C14-R₅
  C14-R₅-state = refl

  B14-ty : BdyTy (Ξ₁₄ ∣ []) Θ₀ (Ξ₁₄ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  B14-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14}))))

  B14ᵤ-ty : BdyTy (Ξ₁₄ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ₁₄ ∣ []) (★ ⇒ ★) id★→
    (★ ⇒ ★)
  B14ᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (0 ∷ [])} {M = unbTerm 0 B14y}))))

  B14ₜ-ty : CastTy (Ξ₁₄ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B14ₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (0 ∷ [])} {M = tagTerm 0 B14y})))

  B14y-ty : BdyTy (Ξ₁₄ ∣ []) (bind 0 1 ∷ []) (Ξ₁₄ ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX
    (★ ⇒ ★)
  B14y-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14y}))))

  B14yᵤ-ty : BdyTy (Ξ₁₄ ∣ (1 ∷ [])) (unbind 0 1 ∷ []) (Ξ₁₄ ∣ []) (★ ⇒ ★) id★→
    (★ ⇒ ★)
  B14yᵤ-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (1 ∷ [])} {M = unbTerm 1 B14x}))))

  B14yₜ-ty : CastTy (Ξ₁₄ ∣ (1 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  B14yₜ-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ (1 ∷ [])} {M = tagTerm 1 B14x})))

  B14x-ty : BdyTy (Ξ₁₄ ∣ []) (bind 0 2 ∷ []) (Ξ₁₄ ∣ (2 ∷ [])) (` 0 ⇒ ` 0) revX
    (★ ⇒ ★)
  B14x-ty = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = Ξ₁₄ ∣ []} {M = B14x}))))

  W₁₄ : World ΔL (Ξ₁₄ ∣ [])
  W₁₄ = Wc⁰ {Ξ₁₄} {ϱ₁₄}

  -- WfWorld for the outer world and the three both-sided worlds of
  -- c14-b1: αᴸ is paired with γᴿ:=ℕ, βᴿ:=★ and αᴿ:=★
  module Wf₁₄ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξ₁₄ ∣ nsR)
    W = world μ η η′ ϱ₁₄ [] []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep r-here (r-there r-here) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ here⇔))) =
      rep-rep r-here (r-there (r-there r-here)) (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ (there⇔ (there⇔ ()))))
    agree (inj₂ ())


  W₁₄-wf : WfWorld W₁₄
  W₁₄-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wf₁₄ [] []↪ []↪

  W₁₄²-wf : ∀ {β} → ϱ₁₄ ∋ᵨ 0 ⇔ β → WfWorld (Wc² {Ξ₁₄} {ϱ₁₄} β)
  W₁₄²-wf p = wf-world (both (inj₁ p) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] []
    where open Wf₁₄ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₁₄ᴸ-wf : WfWorld (Wcᴸ {Ξ₁₄} {ϱ₁₄})
  W₁₄ᴸ-wf = wf-world (hidden-r joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wf₁₄ (X⊑★ ∷ []) (keep []↪) (hide []↪)

  c14-b1 : W₁₄ ∣ [] ⊢ L1′ ⊑ C14-R₅ ∶ ι⊑ι base-ℕ
  c14-b1 =
    ·⊑·
      (outer⊑ (_ , here) here⇔ (W₁₄²-wf here⇔) W₁₄ᴸ-wf
        (layer⊑ (_ , there here) (there⇔ here⇔)
          (W₁₄²-wf (there⇔ here⇔)) W₁₄ᴸ-wf
          (core⊑ (_ , there (there here)) (there⇔ (there⇔ here⇔))
            (W₁₄²-wf (there⇔ (there⇔ here⇔))) B14x-ty)
          id★↦-ty B14yᵤ-ty B14yₜ-ty B14y-ty)
        id★↦-ty B14ᵤ-ty B14ₜ-ty B14-ty
        (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₁₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- The initial blocks B0
  ------------------------------------------------------------------------

  instI-ty : CastTy empty [] instI (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instI-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩})))

  genI-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genI-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = I★genI})))

  instI∘genI-ty : CastTy empty [] instI (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instI∘genI-ty = proj₂ (proj₂
    (cast-inv {Γ = []} (tc {Δ = empty} {M = I★genI ⟨ [] ∣ instI ⟩})))

  genI∘instI-ty : CastTy empty [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genI∘instI-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩})))

  -- the left core Λ against the right core Λ: Λ⊑Λ pairs their abstract
  -- rep. vars lexically
  ΛI⊑ΛI : ∅ʷ ∣ [] ⊢ I ⊑ I ∶ (∀id⊑∀id ∅ʷ)
  ΛI⊑ΛI = Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
    (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ)) (∀id⊑∀id ∅ʷ)

  -- the premise world of Λ⊑Λ: (aᴸ_ΛY, aᴿ_ΛX) ∈ ϱˡ, both abstract
  ΛΛ-wf : WfWorld (∅ʷ ⊕ X⊑X)
  ΛΛ-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 (∅ʷ ⊕ X⊑X) ≤1-∷[]) (namedᴿ-≤1 (∅ʷ ⊕ X⊑X) ≤1-∷[]) [] []
    where
    agree : ∀ {α β} → Paired (∅ʷ ⊕ X⊑X) α β → Agree (∅ʷ ⊕ X⊑X) α β
    agree (inj₁ ())
    agree (inj₂ here⇔) = abst-abst r-here r-here
    agree (inj₂ (there⇔ ()))

  -- Ch B0: Λ⊑Λ under the right's inst cast; the left ν is one-sided
  ch-b0 : ∅ʷ ∣ [] ⊢ Ch-L ⊑ Ch-R ∶ ℕ⊑★
  ch-b0 =
    ·⊑· (ν⊑ (⊑cast ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ)) five⊑

  -- Cg B0: Λ⊑ (Y left-only at X⊑★) under the right's gen and inst casts
  cg-b0 : ∅ʷ ∣ [] ⊢ Cg-L ⊑ Cg-R ∶ ℕ⊑★
  cg-b0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (⊑cast
            (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
            genI-ty (∀id⊑∀id ∅ʷ))
          instI∘genI-ty (∀id⊑★ ∅ʷ))
        ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ))
      five⊑

  -- C2 B0: the two gen casts matched by cast⊑cast; the right's inst
  -- cast by ⊑cast; the left ν is one-sided
  c2-b0 : ∅ʷ ∣ [] ⊢ C2-L ⊑ C2-R ∶ ℕ⊑★
  c2-b0 =
    ·⊑·
      (ν⊑
        (⊑cast
          (cast⊑cast (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ)) genI-ty genI-ty (∀id⊑∀id ∅ʷ))
          instI∘genI-ty (∀id⊑★ ∅ʷ))
        ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ ∅ʷ))
      five⊑

  -- C12 B0: ν⊑ν (its two rep. vars paired lexically in the conversion
  -- world), the right's gen and inst casts by ⊑cast, Λ⊑Λ
  C12-ν : Term
  C12-ν = ν `ℕ · (I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩) ⟨ revX ⟩

  C12-R-is : C12-R ≡ C12-ν · $ 5
  C12-R-is = refl

  C12-ν-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C12-ν-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = C12-ν})))

  c12-b0 : ∅ʷ ∣ [] ⊢ C12-L ⊑ C12-R ∶ ι⊑ι base-ℕ
  c12-b0 =
    ·⊑·
      (ν⊑ν (⊑cast (⊑cast ΛI⊑ΛI instI-ty (∀id⊑★ ∅ʷ)) genI∘instI-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty C12-ν-ty (Wν , Wν-conv , revX⊑revX refl) (ℕ⇒ℕ ∅ʷ))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ------------------------------------------------------------------------
  -- Ch's right-led block X0 (= P3's block, push and pop) and Ch B1
  ------------------------------------------------------------------------

  Ch-R₂-state : head (drop 2 (evalTerms 15 Ch-R-⊢)) ≡ just R3′
  Ch-R₂-state = refl

  -- a push and a pop at X⊑★: (aᴸ_ΛY, αᴿ:=★) ∈ ϱˡ in the popped world
  -- W₃ ⊕⁺ X⊑★ ^ 0
  ch-x0 : W₃ ∣ [] ⊢ Ch-L ⊑ R3′ ∶ ℕ⊑★
  ch-x0 = p3-inst

  -- ch-x0's popped world is Wg⁺ (the same world as Cg's X0)
  ch-x0-world : W₃ ⊕⁺ X⊑★ ^ 0 ≡ Wg⁺
  ch-x0-world = refl

  -- Ch B1: after the left's TyBeta the lexical pair is global,
  -- ϱᵍ = {(αᴸ:=ℕ, αᴿ:=★)}
  Ch-L₁-state : head (drop 1 (evalTerms 10 Ch-L-⊢)) ≡ just L1′
  Ch-L₁-state = refl

  ch-b1 : W₁ ∣ [] ⊢ L1′ ⊑ R3′ ∶ ℕ⊑★
  ch-b1 =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
          (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
          bL-ty bR-ty bLR-conv (ℕ⇒ℕ⊑★⇒★ W₁))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₁))
      five⊑

  ------------------------------------------------------------------------
  -- C12's right-led block X0: ν⊑ν around P3's core (push X, pop X; D27)
  ------------------------------------------------------------------------

  -- C12's state 2: the right's Inst and TyBeta (αᴿ:=★) have run inside
  -- the source ν, which has not
  C12-ν₂ C12-R₂ : Term
  C12-ν₂ = ν `ℕ · ((idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ⟨ [] ∣ genI ⟩) ⟨ revX ⟩
  C12-R₂ = C12-ν₂ · $ 5

  C12-R₂-state : head (drop 2 (evalTerms 24 C12-R-⊢)) ≡ just C12-R₂
  C12-R₂-state = refl

  C12-ν₂-ty : NuTy ΔR `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  C12-ν₂-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = ΔR} {M = C12-ν₂})))

  genIᴿ-ty : CastTy ΔR [] genI (★ ⇒ ★) (`∀ (` 0 ⇒ ` 0))
  genIᴿ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔR} {M = (idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ⟨ [] ∣ genI ⟩})))

  -- the ν conversion world: the two ν-bound rep. vars paired lexically
  Wν₂ : World ((bindR `ℕ ∷ []) ∣ (0 ∷ [])) ((bindR `ℕ ∷ reps ΔR) ∣ (0 ∷ []))
  Wν₂ = world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ []) []

  Wν₂-conv : ConversionInterior (underν² `ℕ `ℕ W₃) Θ₀ Θ₀ Wν₂
  Wν₂-conv = record
    { conv-left       = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
    ; conv-right      = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
  c12-x0 =
    ·⊑·
      (ν⊑ν
        (⊑cast
          (⊑cast
            core₃
            id★↦ᴿ-ty (∀id⊑★ W₃))
          genIᴿ-ty (∀id⊑∀id W₃))
        (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl) (ℕ⇒ℕ W₃))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

------------------------------------------------------------------------
-- 9. HEAD's TermImprecisionRegressionExamples (K), §1-§4 ported (the
-- Evolve-based obligations of its §5 are not: they read HEAD's world).
-- IntX★ is a LEFT fresh name rejoining a PLAIN right-only name (X at
-- αᴿ:=ℕ): markStep gives X⊑X, which it already was
------------------------------------------------------------------------

module K where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I; instI)
  open TIE using (idX; revX; Θ₀; ΔL; ΔLᵢ; ∀X⇒X; int₀; conv₀; Wν; Wν-conv)
  open Rebase using (id★↦; ∀id⊑★; ∀id⊑∀id)

  ------------------------------------------------------------------------
  -- 1. The programs and their runs
  ------------------------------------------------------------------------

  --   L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
  --   R  (λf:★→★.    f) (K[ℕ]⟨inst⟩)

  KK : Term
  KK = Λ I

  cId cK : Conv
  cId = ⌞ ⌞ id (` 0) ⌟ ↦ ⌞ id (` 0) ⌟ ⌟
  cK  = ⌞ `∀ cId ⌟

  -- VL: the left's ∀-boundary value; Nk = inst_Y(VL); Bm: the merged
  -- boundary `[+Y^β, +X^αᴿ] λx:Y.x`
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

  -- the right's context after its Inst TyBeta (β:=★)
  ΔRk : Ctxᵗ
  ΔRk = allocate ★ ΔL

  vVL : Value VL
  vVL = V-⟪⟫ (S-Λ (V-simple S-ƛ)) I-all

  vRF : Value RF
  vRF = V-simple (S-cast (V-⟪⟫ S-ƛ I-fun) I-↦)

  ------------------------------------------------------------------------
  -- 2. The initial pairs (no pending name)
  ------------------------------------------------------------------------

  cId⊑cId : ∀ {Δ Δ′} {W : World Δ Δ′} → μʷ W ⊢ embᴸ W (` 0) ⊑ embᴿ W (` 0)
    → ConvImp W cId cId
  cId⊑cId x = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
    where
    i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id x))

  νK-ty : NuTy empty `ℕ ∀X⇒X cK ∀X⇒X
  νK-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = ν `ℕ · KK ⟨ cK ⟩})))

  instI₀-ty : CastTy empty [] instI ∀X⇒X (★ ⇒ ★)
  instI₀-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = (ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩})))

  νK-conv : NuConversionImp ∅ʷ νK-ty νK-ty
  νK-conv =
    Wν , Wν-conv , conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

  lk⊑rk : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅ʷ
  lk⊑rk =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ ∅ʷ} tf tf (x⊑x Zʷ))
      (⊑cast
        (ν⊑ν
          (Λ⊑Λ lift-[] (V-simple (S-Λ (V-simple S-ƛ)))
            (V-simple (S-Λ (V-simple S-ƛ)))
            (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
            (∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
          (ι⊑ι base-ℕ) νK-ty νK-ty νK-conv (∀id⊑∀id ∅ʷ))
        instI₀-ty (∀id⊑★ ∅ʷ))

  -- after both source TyBetas (α:=ℕ on each side, matched)
  Wk1 : World ΔL ΔL
  Wk1 = world [] []↪ []↪ ((0 , 0) ∷ []) [] []

  Wk1ᵢ : World ΔLᵢ ΔLᵢ
  Wk1ᵢ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  Wk1-wf : WfWorld Wk1
  Wk1-wf = wf-world joint[] agree (namedᴸ-≤1 Wk1 ≤1-[]) (namedᴿ-≤1 Wk1 ≤1-[])
    [] []
    where
    agree : ∀ {α β} → Paired Wk1 α β → Agree Wk1 α β
    agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wk1ᵢ-wf : WfWorld Wk1ᵢ
  Wk1ᵢ-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 Wk1ᵢ ≤1-∷[]) (namedᴿ-≤1 Wk1ᵢ ≤1-∷[]) [] []
    where
    agree : ∀ {α β} → Paired Wk1ᵢ α β → Agree Wk1ᵢ α β
    agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wk1ᵢ-int : Interior Wk1 Θ₀ Θ₀ Wk1ᵢ
  Wk1ᵢ-int = record
    { int-left   = int₀
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    }

  Wk1ᵢ-conv : ConversionInterior Wk1 Θ₀ Θ₀ Wk1ᵢ
  Wk1ᵢ-conv = record
    { conv-left       = conv₀
    ; conv-right      = conv₀
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

  cK⊑cK : ConvImp Wk1ᵢ cK cK
  cK⊑cK = conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

  bVL : BdyTy ΔL Θ₀ ΔLᵢ ∀X⇒X cK ∀X⇒X
  bVL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = VL}))))

  instI-ty : CastTy ΔL [] instI ∀X⇒X (★ ⇒ ★)
  instI-ty =
    proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔL} {M = VL ⟨ [] ∣ instI ⟩})))

  lk₁⊑rk₁ : Wk1 ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1
  lk₁⊑rk₁ =
    ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk1} tf tf (x⊑x Zʷ))
      (⊑cast
        (⟪⟫⊑⟪⟫ Wk1ᵢ-int Wk1ᵢ-wf
          (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
          bVL bVL (Wk1ᵢ , Wk1ᵢ-conv , cK⊑cK) (∀id⊑∀id Wk1))
        instI-ty (∀id⊑★ Wk1))

  ------------------------------------------------------------------------
  -- 3. The worlds and boundaries after the right's Inst TyBeta
  ------------------------------------------------------------------------

  -- the world after the right's Inst TyBeta: (αᴸ, αᴿ) global, β unpaired
  Wk : World ΔL ΔRk
  Wk = world [] []↪ []↪ ((0 , 1) ∷ []) [] []

  Wk-wf : WfWorld Wk
  Wk-wf = wf-world joint[] agree (namedᴸ-≤1 Wk ≤1-[]) (namedᴿ-≤1 Wk ≤1-[]) [] []
    where
    agree : ∀ {α β} → Paired Wk α β → Agree Wk α β
    agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Θ₀-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ []) ⊢ⁱ Θ₀ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
  Θ₀-int = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  -- the Inst boundary `+Y^β` alone: Y is introduced right-only, at X⊑★,
  -- and pushed (pending, D27)
  IntK-ro : Interior Wk [] Θ₀ (record (Wk ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] })
  IntK-ro = record
    { int-left   = interior changes[]
    ; int-right  = Θ₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    }

  -- inside the inner boundary `+X^α`: Y at 0, X at 1
  ΘX : Boundary
  ΘX = bind 1 1 ∷ []

  ΔLX ΔRX : Ctxᵗ
  ΔLX = (abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
  ΔRX = (bindR ★ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

  bindX-int : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ⁱ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  bindX-int = interior (changes∷ changes[]
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  -- the merged boundary `+Y^β, +X^αᴿ`
  Θ₂ : Boundary
  Θ₂ = bind 1 1 ∷ bind 0 0 ∷ []

  int-Θ₂ : ∀ {b₀ b₁ : RepBinding}
    → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ⁱ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
  int-Θ₂ = interior
    (changes∷ (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))
      (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  bNR : BdyTy (reps ΔRk ∣ (0 ∷ [])) ΘX ΔRX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
  bNR = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = reps ΔRk ∣ (0 ∷ [])} {M = Nk}))))

  bOutK : BdyTy ΔRk Θ₀ (reps ΔRk ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bOutK = proj₂ (proj₂ (proj₂
    (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Nk ⟪ Θ₀ , revX ⟫}))))

  bBm : BdyTy ΔRk Θ₂ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bBm = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Bm}))))

  id★↦ᴿk-ty : CastTy ΔRk [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦ᴿk-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  -- The worlds of the pending name Y (design.md D27).  Right names inside
  -- the merged `+Y^β, +X^αᴿ`: Y at 0 (β:=★, PENDING, X⊑★: `πʷ = 0 ∷ []`),
  -- X at 1 (αᴿ:=ℕ).

  -- inside Θ₂ (and inside the Inst boundary's inner `+X^αᴿ`): no left
  -- name, Y pending
  WiR★ : World ΔL ΔRX
  WiR★ = world (X⊑★ ∷ X⊑X ∷ []) (skip (skip []↪)) (keep (keep []↪))
           ((0 , 1) ∷ []) [] (0 ∷ [])

  -- inside the left's `+X^αᴸ` as well: X joined through (αᴸ, αᴿ)
  Wx★ : World ΔLᵢ ΔRX
  Wx★ = world (X⊑★ ∷ X⊑X ∷ []) (skip (keep []↪)) (keep (keep []↪))
          ((0 , 1) ∷ []) [] (0 ∷ [])

  -- after the pop of Y: the left binder Y joins the right's Y, its
  -- abstract rep. var paired lexically with β
  WX★ : World ΔLX ΔRX
  WX★ = world (X⊑★ ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))
          ((1 , 1) ∷ []) ((0 , 0) ∷ []) []

  openX★ : Open1 Wx★ WX★
  openX★ = open1 join-here here r-here

  IntΘ₂★ : Interior Wk [] Θ₂ WiR★
  IntΘ₂★ = record
    { int-left   = interior changes[]
    ; int-right  = int-Θ₂
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ
        { (_ , here) () _ ; (_ , there here) () _
        ; (_ , there (there ())) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there here) _ → tt
                      ; (_ , there (there ())) _ }
    }

  Wx-fresh : ∀ {X X′ α β}
    → ΔLᵢ ∋ᵗ X := α → ΔRX ∋ᵗ X′ := β
    → (Joins Wx★ X X′ → Paired WiR★ α β) × (Paired WiR★ α β → Joins Wx★ X X′)
  Wx-fresh here here = (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
  Wx-fresh here (there here) = (λ _ → inj₁ here⇔) , (λ _ → refl)
  Wx-fresh here (there (there ()))
  Wx-fresh (there ()) _

  IntX★ : Interior WiR★ Θ₀ [] Wx★
  IntX★ = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ a b _ → Wx-fresh a b
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ
        { (_ , here) refl m → tt , m
        ; (_ , there here) refl (there here) → tt , there here
        ; (_ , there (there ())) _ _ }
    ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    ; fresh-right = λ _ ()
    }

  -- the Inst boundary `+Y^β` alone (before the Merge), Y pending
  WiY★ : World ΔL (reps ΔRk ∣ (0 ∷ []))
  WiY★ = record (Wk ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] }

  -- the right's inner `+X^αᴿ` carries Y (toExt ΘX 0 = just 0)
  IntXc★ : Interior WiY★ [] ΘX WiR★
  IntXc★ = record
    { int-left   = interior changes[]
    ; int-right  = bindX-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ
        { (_ , here) refl here → tt , here ; (_ , there here) () _
        ; (_ , there (there ())) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , here) () ; (_ , there here) _ → tt
                      ; (_ , there (there ())) _ }
    }

  agreeₖ : ∀ {Δ₀ Δ₀′} {W : World Δ₀ Δ₀′} → Δ₀ ∋rep 0 := `ℕ
    → Δ₀′ ∋rep 1 := `ℕ → ϱᵍʷ W ≡ (0 , 1) ∷ [] → ϱˡʷ W ≡ []
    → ∀ {α β} → Paired W α β → Agree W α β
  agreeₖ l r refl refl (inj₁ here⇔) = rep-rep l r (ι⊑ι base-ℕ)
  agreeₖ l r refl refl (inj₁ (there⇔ ()))
  agreeₖ l r refl refl (inj₂ ())

  WiR★-wf : WfWorld WiR★
  WiR★-wf = wf-world (right-only (right-only joint[]))
    (agreeₖ r-here (r-there r-here) refl refl)
    (namedᴸ-≤1 WiR★ ≤1-[]) (λ { (_ , ()) _ _ _ _ })
    ((0 , here , r-here , (λ { (_ , ()) }) , here , (λ { (_ , ()) })) ∷ [])
    ([] ∷ [])

  uniqᴿx : NamedUniqueᴿ Wx★
  uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
  uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniqᴿx _ _ _ (inj₁ (there⇔ ())) _
  uniqᴿx _ _ _ (inj₂ ()) _
  uniqᴿx _ _ _ _ (inj₂ ())

  Wx★-wf : WfWorld Wx★
  Wx★-wf = wf-world (right-only (both (inj₁ here⇔) joint[]))
    (agreeₖ r-here (r-there r-here) refl refl)
    (namedᴸ-≤1 Wx★ ≤1-∷[]) uniqᴿx
    ((0 , here , r-here , (λ { (_ , here) () ; (_ , there ()) _ }) ,
      here ,
      (λ { (_ , here) (inj₁ (there⇔ ())) ; (_ , here) (inj₂ ())
         ; (_ , there ()) _ })) ∷ [])
    ([] ∷ [])

  WiY★-wf : WfWorld WiY★
  WiY★-wf = wf-world (right-only joint[])
    (agreeₖ r-here (r-there r-here) refl refl)
    (namedᴸ-≤1 WiY★ ≤1-[]) (namedᴿ-≤1 WiY★ ≤1-∷[])
    ((0 , here , r-here , (λ { (_ , ()) }) , here , (λ { (_ , ()) })) ∷ [])
    ([] ∷ [])

  ------------------------------------------------------------------------
  -- 4. The pairs with Y pending: push, pass, pop (design.md D27)
  ------------------------------------------------------------------------

  -- THE COMMON PREMISE: inside the right boundary, Y pending.  ⟪⟫⊑ passes
  -- Y into VL's boundary (cK = ∀Y.cId), Λ⊑ pops it, ƛ⊑ƛ at Y ⊑ Y
  VL⊑idX : WiR★ ∣ [] ⊢ VL ⊑ idX
    ∶⟨ ∀X⇒X , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  VL⊑idX =
    ⟪⟫⊑ IntX★ (bc-∀ (S-Λ (V-simple S-ƛ)) (fc-∷ fc-[])) Wx★-wf
      (Λ⊑ (claim-pop openX★) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
        (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (⇒⊑⇒ X⊑X X⊑X))
      bVL (⇒⊑⇒ X⊑X X⊑X)

  -- after the right's Merge (RK₄, RF): ⊑⟪⟫ at the merged Θ₂ PUSHES Y.
  -- THE FINAL ARGUMENT PAIR (unrelated before D26)
  VL⊑Bm : Wk ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
  VL⊑Bm =
    ⊑⟪⟫ IntΘ₂★ (push ca-[] (refl ∷ []) (inj₂ vVL)) WiR★-wf VL⊑idX bBm
      (∀id⊑★ Wk)

  VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
  VL⊑RF = ⊑cast VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
  lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

  -- before the Merge (RK₃), RIGHT-FIRST: ⊑⟪⟫ at Θ₀ pushes Y, the inner
  -- ⊑⟪⟫ at ΘX CARRIES it; the premise is VL⊑idX again
  VL⊑Nk : WiY★ ∣ [] ⊢ VL ⊑ Nk
    ∶⟨ ∀X⇒X , ` 0 ⇒ ` 0 ⟩ ⇒⊑⇒ X⊑X X⊑X
  VL⊑Nk =
    ⊑⟪⟫ IntXc★ (push (ca-∷ refl ca-[]) [] (inj₁ refl)) WiR★-wf VL⊑idX bNR
      (⇒⊑⇒ X⊑X X⊑X)

  VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
  VL⊑Rarg₃ =
    ⊑cast
      (⊑⟪⟫ IntK-ro (push ca-[] (refl ∷ []) (inj₂ vVL)) WiY★-wf VL⊑Nk bOutK
        (∀id⊑★ Wk))
      id★↦ᴿk-ty (∀id⊑★ Wk)

  lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk
  lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

  -- K NEEDS its push: with no pending name, the premise index of
  -- `VL ⊑ Bm` inside Θ₂ is empty (Y is right-only)
  no-push-K : ¬ (∀X⇒X ⊑ᵂ⟨ record WiR★ { πʷ = [] } ⟩ (` 0 ⇒ ` 0))
  no-push-K (∀⊑ _ _ (⇒⊑⇒ () _))

------------------------------------------------------------------------
-- 10. Example P4 (= cambridge Cf from its second block), every block,
-- ported from ModeCondition.P4 (D11 marks; pre-D27 rules adapted:
-- `push-none`, `claim-fresh`).  W₄ᴸ is HIDDEN: it is the world inside
-- the right's own `−X` of the both-sided X, so the J pair's rejoin
-- keeps X⊑★
------------------------------------------------------------------------

module P4 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.ImprecisionExamples using (L4; R4; L4-⊢; R4-⊢)

  nth : List Term → ℕ → Term
  nth []       _       = $ 0
  nth (x ∷ xs) zero    = x
  nth (x ∷ xs) (suc n) = nth xs n

  Ls Rs : List Term
  Ls = evalTerms 11 L4-⊢
  Rs = evalTerms 17 R4-⊢
  open TIE using (idX; revX; Θ₀; L1′; ΔL; ΔLᵢ; bL-ty; revX⊑revX; νL-ty;
                  Wν; Wν-conv)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; Wc-bindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; ℕ⇒ℕ; ∀id⊑★; ∀id⊑∀id; I★⁻; I★gen; Bg; tagX↦;
           id★→)
  open import examples.CambridgeExamples using (I★)

  νbody : Term
  νbody = ν `ℕ · ` 0 ⟨ revX ⟩

  νbody-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νbody-ty = proj₂ (proj₂ (ν-inv {Γ = TIE.∀X⇒X ∷ []}
    (tc {Δ = empty} {Γ = TIE.∀X⇒X ∷ []} {M = νbody})))

  genArg : Term
  genArg = (ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩

  genArg-ty : CastTy empty [] (genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)))
    (★ ⇒ ★) TIE.∀X⇒X
  genArg-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = genArg})))

  ---------------------------------------------------------------------
  -- The worlds.  Both sides allocate αᴸ:=ℕ, αᴿ:=ℕ (rep. var 0); the
  -- matched TyBetas pair them globally.  The boundary name X is
  -- both-sided at X⊑★ (`Wc² 0`), left-only after a right `−X`
  -- (`Wcᴸ`), and rejoins at the right's `+X` keeping X⊑★ (D15).

  Ξ₄ : RepCtx
  Ξ₄ = bindR `ℕ ∷ []

  ϱ₄ : RepRel
  ϱ₄ = (0 , 0) ∷ []

  W₄ : World ΔL ΔL
  W₄ = Wc⁰ {Ξ₄} {ϱ₄}

  W₄² : World ΔLᵢ ΔLᵢ
  W₄² = Wc² {Ξ₄} {ϱ₄} 0

  W₄ᴸ : World ΔLᵢ ΔL
  W₄ᴸ = Wcᴸ {Ξ₄} {ϱ₄}

  module Wf₄ {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World (Ξ₄ ∣ nsL) (Ξ₄ ∣ nsR)
    W = world μ η η′ ϱ₄ [] []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  W₄-wf : WfWorld W₄
  W₄-wf = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wf₄ [] []↪ []↪

  W₄²-wf : WfWorld W₄²
  W₄²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] []
    where open Wf₄ (X⊑★ ∷ []) (keep []↪) (keep []↪)

  W₄ᴸ-wf : WfWorld W₄ᴸ
  W₄ᴸ-wf = wf-world (hidden-r joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wf₄ (X⊑★ ∷ []) (keep []↪) (hide []↪)

  v₀ : Ξ₄ ∋ʳ 0
  v₀ = _ , here

  ---------------------------------------------------------------------
  -- Shared pieces: the sealed argument S = [−X^α] 5 ⟨−X⟩ on both sides

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  S : Term
  S = $ 5 ⟪ unb₀ , tail (seal 0) ⟫

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  unb-int : Interior W₄² unb₀ unb₀ W₄
  unb-int = record
    { int-left   = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , ()) _ }
    }

  unb-conv : ConversionInterior W₄² unb₀ unb₀ W₄²
  unb-conv = record
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
    ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    ; conv-mark-right = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    }

  bS : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S}))))

  S⊑S : W₄² ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑S = ⟪⟫⊑⟪⟫ unb-int W₄-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (W₄² , unb-conv , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- the left's λx:X. x against the right's λx:★. x (X left-only)
  idX⊑I★ : W₄ᴸ ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξ₄ ϱ₄
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  bI★⁻ : BdyTy ΔLᵢ unb₀ ΔL (★ ⇒ ★) id★→ (★ ⇒ ★)
  bI★⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★⁻}))))

  -- idX ⊑ [−X^α] (λx:★. x) ⟨id(★) → id(★)⟩ at X→X ⊑ ★→★ (X both-sided)
  idX⊑I★⁻ : W₄² ∣ [] ⊢ idX ⊑ I★⁻ ∶ c⊑★² Ξ₄ ϱ₄ 0
  idX⊑I★⁻ = ⊑⟪⟫ (Wc-unbindᴿ v₀) push-none W₄ᴸ-wf idX⊑I★ bI★⁻
    (c⊑★² Ξ₄ ϱ₄ 0)

  tagᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★gen})))

  ---------------------------------------------------------------------
  -- B1 (0, 0): the initial pair

  p4-B1 : ∅ʷ ∣ [] ⊢ L4 ⊑ R4 ∶ ι⊑ι base-ℕ
  p4-B1 =
    ·⊑·
      (ƛ⊑ƛ {pA = ∀id⊑∀id ∅ʷ} tf tf
        (·⊑·
          (ν⊑ν (x⊑x Zʷ) (ι⊑ι base-ℕ) νbody-ty νbody-ty
            (Wν , Wν-conv , revX⊑revX refl)
            (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
          (κ⊑κ lit-$ (ι⊑ι base-ℕ))))
      (⊑cast
        (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
        genArg-ty (∀id⊑∀id ∅ʷ))

  ---------------------------------------------------------------------
  -- (1, 1): after both Betas (cambridge Cf B0)

  νR₁ : Term
  νR₁ = ν `ℕ · genArg ⟨ revX ⟩

  νR₁-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νR₁-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = νR₁})))

  p4-B1′ : ∅ʷ ∣ [] ⊢ nth Ls 1 ⊑ nth Rs 1 ∶ ι⊑ι base-ℕ
  p4-B1′ =
    ·⊑·
      (ν⊑ν
        (⊑cast
          (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
          genArg-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty νR₁-ty
        (Wν , Wν-conv , revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B2 (2, 2): after both TyBetas.  The right's gen wrapper
  -- `X! → X?` at `^[X:★∼X]`, by ⊑cast at X→X ⊑ ★→★

  bBg : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bBg = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = Bg}))))

  p4-B2 : W₄ ∣ [] ⊢ nth Ls 2 ⊑ nth Rs 2 ∶ ι⊑ι base-ℕ
  p4-B2 =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
        (⊑cast idX⊑I★⁻ tagᵍ-ty (c⊑c² Ξ₄ ϱ₄ 0))
        bL-ty bBg (W₄² , Wc-bind²-conv v₀ here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B3 (3, 4): after the left's Wrap and the right's Wrap, CastFun.
  -- The right's X? at `^[X:★∼X]` and its argument's X! at `^[X:X∼★]`
  -- (CastFun flipped the environment), both by ⊑cast reading X ⊑ ★

  tagX : Coercion
  tagX = (` 0) !

  chkX : Coercion
  chkX = (` 0) ？ 0

  tagˣ-ty : CastTy ΔLᵢ (X∼★ ∷ []) tagX (` 0) ★
  tagˣ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = S ⟨ X∼★ ∷ [] ∣ tagX ⟩})))

  chkᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) chkX ★ (` 0)
  chkᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩})))

  -- the left's and the right's +X boundaries (conversion `unseal 0`)
  bUnsealL : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 4}))))

  bUnsealR : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealR = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 6}))))

  bUnsealL₃ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealL₃ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 3}))))

  bUnsealR₄ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealR₄ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 4}))))

  S⊑S! : W₄² ∣ [] ⊢ S ⊑ S ⟨ X∼★ ∷ [] ∣ tagX ⟩ ∶ X⊑★ here
  S⊑S! = ⊑cast S⊑S tagˣ-ty (X⊑★ here)

  p4-B3 : W₄ ∣ [] ⊢ nth Ls 3 ⊑ nth Rs 4 ∶ ι⊑ι base-ℕ
  p4-B3 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast {p = X⊑★ here} (·⊑· idX⊑I★⁻ S⊑S!) chkᵍ-ty X⊑X)
      bUnsealL₃ bUnsealR₄
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B4 (4, 6): after the left's Beta and the right's Wrap, Beta.  THE
  -- "J" PAIR (SidedMarks.md §4) is the premise `S ⊑ J`: X left-only
  -- after the right's −X, rejoined at the right's +X keeping X⊑★

  J : Term
  J = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ₀ , id★ᶜ ⟫

  bJ : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bJ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = J}))))

  bJ⁻ : BdyTy ΔLᵢ unb₀ ΔL ★ id★ᶜ ★
  bJ⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = J ⟪ unb₀ , id★ᶜ ⟫}))))

  -- the J pair (index X ⊑ ★, X left-only)
  S⊑J : W₄ᴸ ∣ [] ⊢ S ⊑ J ∶ X⊑★ here
  S⊑J = ⊑⟪⟫ (Wc-bindᴿ v₀ here⇔) push-none W₄²-wf S⊑S! bJ (X⊑★ here)

  p4-B4 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ nth Rs 6 ∶ ι⊑ι base-ℕ
  p4-B4 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast {p = X⊑★ here}
        (⊑⟪⟫ (Wc-unbindᴿ v₀) push-none W₄ᴸ-wf S⊑J bJ⁻ (X⊑★ here))
        chkᵍ-ty X⊑X)
      bUnsealL bUnsealR
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B5 (5, 11): after the Merges; the interiors have no name, the two
  -- conversions are id(ℕ)

  b5L : BdyTy ΔL (unbind 0 0 ∷ bind 0 0 ∷ []) ΔL `ℕ ⌞ id `ℕ ⌟ `ℕ
  b5L = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 5}))))

  b5R : BdyTy ΔL (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ [])
    ΔL `ℕ ⌞ id `ℕ ⌟ `ℕ
  b5R = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 11}))))

  bdy-wf : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ
    → Σ[ Δᶜ ∈ Ctxᵗ ] BoundaryWf Δ Θ Δᵢ Δᶜ
  bdy-wf (bdy-ty mw _ _ _ _) = _ , mw

  int5 : Interior W₄ (unbind 0 0 ∷ bind 0 0 ∷ [])
    (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ []) W₄
  int5 = record
    { int-left   = bw-interior (proj₂ (bdy-wf b5L))
    ; int-right  = bw-interior (proj₂ (bdy-wf b5R))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , ()) _ }
    }

  p4-B5 : W₄ ∣ [] ⊢ nth Ls 5 ⊑ nth Rs 11 ∶ ι⊑ι base-ℕ
  p4-B5 = ⟪⟫⊑⟪⟫ int5 W₄-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) b5L b5R
    (W₄² , conv5 , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))
    (ι⊑ι base-ℕ)
    where
    conv5 : ConversionInterior W₄ (unbind 0 0 ∷ bind 0 0 ∷ [])
      (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ []) W₄²
    conv5 = record
      { conv-left       = bw-conversion (proj₂ (bdy-wf b5L))
      ; conv-right      = bw-conversion (proj₂ (bdy-wf b5R))
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

  -- B6 (6, 12): 5 ⊑ 5
  p4-B6 : W₄ ∣ [] ⊢ nth Ls 6 ⊑ nth Rs 12 ∶ ι⊑ι base-ℕ
  p4-B6 = κ⊑κ lit-$ (ι⊑ι base-ℕ)


------------------------------------------------------------------------
-- 11. Facts for the non-derivability proofs
------------------------------------------------------------------------

lookup-unique : ∀ {A : Set} {xs : List A} {k a b}
  → xs ∋ˡ k := a → xs ∋ˡ k := b → a ≡ b
lookup-unique here      here       = refl
lookup-unique (there h) (there h′) = lookup-unique h h′

-- an embedded name in range sits at a center position its embedding
-- keeps
st-emb : ∀ {η Ω X β} (ι : η ↪ Ω) → η ∋ˡ X := β → statusAt ι (emb ι X) ≡ joined
st-emb (keep ι) here      = refl
st-emb (keep ι) (there h) = st-emb ι h
st-emb (skip ι) h         = st-emb ι h
st-emb (hide ι) h         = st-emb ι h

-- the embedding of an empty name list keeps no center position
st-[] : ∀ {Ω} (ι : [] ↪ Ω) c → statusAt ι c ≢ joined
st-[] []↪      c       ()
st-[] (skip ι) zero    ()
st-[] (hide ι) zero    ()
st-[] (skip ι) (suc c) = st-[] ι c
st-[] (hide ι) (suc c) = st-[] ι c

-- a name in range has a mark
emb-mark : ∀ {η Ω X β} (ι : η ↪ Ω) → η ∋ˡ X := β
  → Σ VarImp (λ m → Ω ∋ˡ emb ι X := m)
emb-mark (keep {m = m} ι) here = m , here
emb-mark (keep ι) (there h) with emb-mark ι h
... | m , l = m , there l
emb-mark (skip ι) h with emb-mark ι h
... | m , l = m , there l
emb-mark (hide ι) h with emb-mark ι h
... | m , l = m , there l

-- a fresh name with no partner side is plain
plain-of : ∀ {s} → NotHid s → s ≢ joined → s ≡ plain
plain-of {joined} _  nj = ⊥-elim (nj refl)
plain-of {plain}  _  _  = refl
plain-of {hidden} () _

-- THE REJOIN OF A PLAIN NAME IS X⊑X
rejoin : ∀ {μ : ImpEnv} {c m s s′} → s ≡ plain → s′ ≡ joined
  → μ ∋ˡ c := markStep s s′ m → μ ∋ˡ c := X⊑X
rejoin refl refl h = h

-- the index of a non-∀ left type has no pending name, and is then the
-- plain type imprecision
data NonForall : Ty → Set where
  nf-var : ∀ {X} → NonForall (` X)
  nf-ℕ   : NonForall `ℕ
  nf-𝔹   : NonForall `𝔹
  nf-★   : NonForall ★
  nf-⇒   : ∀ {A B} → NonForall (A ⇒ B)

openImp-[] : ∀ {μ cs ρ A B} → NonForall A → OpenImp μ cs ρ A B → cs ≡ []
openImp-[] {cs = []}    _      _  = refl
openImp-[] {cs = c ∷ cs} nf-var ()
openImp-[] {cs = c ∷ cs} nf-ℕ   ()
openImp-[] {cs = c ∷ cs} nf-𝔹   ()
openImp-[] {cs = c ∷ cs} nf-★   ()
openImp-[] {cs = c ∷ cs} nf-⇒   ()

map-[] : ∀ {A B : Set} {f : A → B} (xs : List A) → map f xs ≡ [] → xs ≡ []
map-[] []       _  = refl
map-[] (x ∷ xs) ()

π[] : ∀ {V : World Δ Δ′} {A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩ A′ → πʷ V ≡ []
π[] {V = V} {A} {A′} nf q =
  map-[] (πʷ V)
    (openImp-[] {μ = μʷ V} {ρ = emb (ηᴸʷ V)} {A = A} {B = embᴿ V A′} nf q)

plain-idx : ∀ {V : World Δ Δ′} {A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩ A′
  → μʷ V ⊢ embᴸ V A ⊑ embᴿ V A′
plain-idx {V = V} {A} {A′} nf q =
  subst (λ π → OpenImp (μʷ V) (map (emb (ηᴿʷ V)) π) (emb (ηᴸʷ V)) A
                 (embᴿ V A′))
        (π[] {V = V} {A′ = A′} nf q) q

-- the four index shapes the proofs refute or read
var⊑var : ∀ {μ a b} → μ ⊢ ` a ⊑ ` b → a ≡ b
var⊑var X⊑X = refl

var⊑★ : ∀ {μ a} → μ ⊢ ` a ⊑ ★ → μ ∋ˡ a := X⊑★
var⊑★ (X⊑★ h) = h

no-ℕ⊑var : ∀ {V : World Δ Δ′} {X} → ¬ (`ℕ ⊑ᵂ⟨ V ⟩ ` X)
no-ℕ⊑var {V = V} {X} q with plain-idx {V = V} {A′ = ` X} nf-ℕ q
... | ()

no-★⊑var : ∀ {V : World Δ Δ′} {X} → ¬ (★ ⊑ᵂ⟨ V ⟩ ` X)
no-★⊑var {V = V} {X} q with plain-idx {V = V} {A′ = ` X} nf-★ q
... | ()

no-var⊑ℕ : ∀ {V : World Δ Δ′} {X} → ¬ (` X ⊑ᵂ⟨ V ⟩ `ℕ)
no-var⊑ℕ {V = V} {X} q with plain-idx {V = V} {A′ = `ℕ} nf-var q
... | ()

no-plain-ℕ⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ `ℕ ⊑ ` a)
no-plain-ℕ⊑var ()

no-plain-★⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ ★ ⊑ ` a)
no-plain-★⊑var ()

no-★⊑ℕ : ∀ {V : World Δ Δ′} → ¬ (★ ⊑ᵂ⟨ V ⟩ `ℕ)
no-★⊑ℕ {V = V} q with plain-idx {V = V} {A′ = `ℕ} nf-★ q
... | ()

-- the left index type of a cast, a boundary, a literal: read off the
-- rule that peels it (the right rules keep the left index)
lty-cast : ∀ {V : World Δ Δ′} {γ M M′ μ c A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q → Σ[ B ∈ Ty ] CastTy Δ μ c B A
lty-cast (cast⊑cast _ ct _ _) = _ , ct
lty-cast (cast⊑ _ _ ct _)     = _ , ct
lty-cast (⊑cast d _ _)        = lty-cast d
lty-cast (⊑⟪⟫ _ _ _ d _ _)    = lty-cast d

lty-bdy : ∀ {V : World Δ Δ′} {γ M M′ Θ c A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Aᵢ ∈ Ty ] BdyTy Δ Θ Δᵢ Aᵢ c A
lty-bdy (⟪⟫⊑⟪⟫ _ _ _ b _ _ _) = _ , _ , b
lty-bdy (⟪⟫⊑ _ _ _ _ b _)     = _ , _ , b
lty-bdy (⊑cast d _ _)         = lty-bdy d
lty-bdy (⊑⟪⟫ _ _ _ d _ _)     = lty-bdy d

lty-$ : ∀ {V : World Δ Δ′} {γ n M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ $ n ⊑ M′ ∶ q → A ≡ `ℕ
lty-$ (κ⊑κ lit-$ _)       = refl
lty-$ (⊑cast d _ _)       = lty-$ d
lty-$ (⊑⟪⟫ _ _ _ d _ _)   = lty-$ d

-- coercion typings of the casts that occur
ct-id★ : ∀ {μ B A} → CastTy Δ μ (idᵖ ★) B A → (B ≡ ★) × (A ≡ ★)
ct-id★ (cast-ty (⊢id _ _) _) = refl , refl

ct-ℕ! : ∀ {μ B A} → CastTy Δ μ (`ℕ !) B A → (B ≡ `ℕ) × (A ≡ ★)
ct-ℕ! (cast-ty (⊢tag g-ℕ) _) = refl , refl

ct-ℕ? : ∀ {μ ℓ B A} → CastTy Δ μ (`ℕ ？ ℓ) B A → (B ≡ ★) × (A ≡ `ℕ)
ct-ℕ? (cast-ty (⊢check g-ℕ) _) = refl , refl

ct-X! : ∀ {μ X B A} → CastTy Δ μ ((` X) !) B A → (B ≡ ` X) × (A ≡ ★)
ct-X! (cast-ty (⊢tag ()) _)
ct-X! (cast-ty (⊢tag-var _ _ _) _) = refl , refl

-- the bind entry `+X^0` from a context with no name
Θ₀ : Boundary
Θ₀ = bind 0 0 ∷ []

bind₀-int : ∀ {Δ Δᵢ} → Δ ⊢ⁱ Θ₀ ⇒ Δᵢ → Δᵢ ∋ᵗ 0 := 0
bind₀-int (interior (changes∷ changes[] (step-bind _ _ ins-here))) = here

bind₀-conv : ∀ {R Δᶜ} → allocate R empty ⊢ᶜ Θ₀ ⇒ Δᶜ → Δᶜ ∋ᵗ 0 := 0
bind₀-conv c with conversion-functional c TIE.conv₀
... | refl = here

-- a ForallConv of a non-∀ conversion is empty
fc-unseal : ∀ {X k π} → ¬ ForallConv (unseal X) (k ∷ π)
fc-unseal ()

-- runs (SidedMarks.Runs, copied): every reachable state is a state of
-- the evalTerms run (determinism)
module Runs where
  open import examples.Eval
    using (eval; Trace; stop; illtyped; _◅⟨_⟩_; value; blamed;
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

  EndsVB : ∀ {Δ A M} → Trace Δ A M → Set
  EndsVB (stop (value _))   = ⊤
  EndsVB (stop (blamed _))  = ⊤
  EndsVB (stop no-redex)    = ⊥
  EndsVB (stop out-of-fuel) = ⊥
  EndsVB (illtyped _)       = ⊥
  EndsVB (_ ◅⟨ _ ⟩ tr)      = EndsVB tr

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

  NotBlame : Term → Set
  NotBlame N = ∀ {ℓ} → N ≡ blame ℓ → ⊥

  last : List Term → Term
  last []           = $ 0
  last (x ∷ [])     = x
  last (x ∷ y ∷ xs) = last (y ∷ xs)

------------------------------------------------------------------------
-- 12. C1 = the SimBackBlame counterexample L₆ ⊑ R₇ (PendingOpenings
-- §5d; SidedMarks/ModeCondition `Cex`): NOT DERIVABLE, in any world
-- over its typing contexts, at any index
------------------------------------------------------------------------

module C1 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_)
  open Runs
  open P4 using (nth)

  5★ : Term
  5★ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  ℕ? : Coercion
  ℕ? = `ℕ ？ 0

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  -- [−X^α] 5⟨ℕ!⟩ ⟨−X⟩, on both sides
  S : Term
  S = 5★ ⟪ unb₀ , tail (seal 0) ⟫

  -- the left spine and the right spine
  LB Lid L₆ RX RB R₇ : Term
  LB  = S ⟪ Θ₀ , unseal 0 ⟫
  Lid = LB ⟨ [] ∣ idᵖ ★ ⟩
  L₆  = Lid ⟨ [] ∣ ℕ? ⟩
  RX  = S ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩
  RB  = RX ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫
  R₇  = RB ⟨ [] ∣ ℕ? ⟩

  --   L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  --   R₀  ((ΛX. λx:X. x⟨X!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  L₀ R₀ : Term
  L₀ = ((Λ (ƛ (` 0) ∙ ` 0) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)) ⟩)
          · 5★) ⟨ [] ∣ ℕ? ⟩
  R₀ = ((Λ (ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩))
          ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

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

  L₆-⊢ : ΔR ∣ [] ⊢ L₆ ⦂ `ℕ
  L₆-⊢ = tc

  R₇-⊢ : ΔR ∣ [] ⊢ R₇ ⦂ `ℕ
  R₇-⊢ = tc

  R₇-blames : ΔR ⊢ R₇ -→ blame 0 ∣ none
  R₇-blames = justStep refl

  L₆-never-blames : ∀ {ℓ} → ¬ (ΔR ⊢ L₆ -→* blame ℓ)
  L₆-never-blames r = all-reach {P = NotBlame} 20 L₆-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  ---------------------------------------------------------------------
  -- the boundary typing of the left's `[+X^α] S ⟨+X⟩`: its interior
  -- name is 0 (at α), its interior type ` 0, its exterior type ★

  bdy-LB : ∀ {Δᵢ Aᵢ A} → BdyTy ΔR Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Δᵢ ∋ᵗ 0 := 0) × (Aᵢ ≡ ` 0) × (A ≡ ★)
  bdy-LB (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
    with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
  bdy-LB (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-★))
                 (_ , same-var here , same-var here)
                 (_ , same-★ , same-★) _) | refl | refl =
    here , refl , refl

  -- THE MATCHED BOUNDARIES `+X ⊑ +X` (conversions `+X` ⊑ `id(★)`)
  -- need X left-only in the conversion world, so the two αs are NOT
  -- paired
  matched-conv : ∀ {W : World ΔR ΔR} {Δᵢ Δ′ᵢ Aᵢ A′ᵢ A A′}
      (b : BdyTy ΔR Θ₀ Δᵢ Aᵢ (unseal 0) A)
      (b′ : BdyTy ΔR Θ₀ Δ′ᵢ A′ᵢ ⌞ id ★ ⌟ A′)
    → BdyConversionImp W b b′ → ¬ Paired W 0 0
  matched-conv (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _)
    (Wᶜ , ci , conv-unseal⊑id★ _ lo) pr =
    lo (_ , bind₀-conv (conv-right ci))
       (proj₂ (conv-join-fresh ci (bind₀-conv (conv-left ci))
                (bind₀-conv (conv-right ci)) (inj₁ fresh[])) pr)

  ---------------------------------------------------------------------
  -- left literals against the right spine

  no-$-RX : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ $ 5 ⊑ RX ∶ q)
  no-$-RX {V = V} (⊑cast {p = p} d ct _) with ct-X! ct | lty-$ d
  ... | refl , refl | refl = no-ℕ⊑var {V = V} p

  no-5★-RX : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ 5★ ⊑ RX ∶ q)
  no-5★-RX {V = V} (⊑cast {p = p} d ct _) with ct-X! ct | lty-cast d
  ... | refl , refl | _ , ct₀ with ct-ℕ! ct₀
  ... | refl , refl = no-★⊑var {V = V} p
  no-5★-RX (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ! ct | ct-X! ct′
  ... | refl , refl | refl , refl = no-plain-ℕ⊑var p
  no-5★-RX (cast⊑ _ d _ _) = no-$-RX d

  no-$-RB : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ $ 5 ⊑ RB ∶ q)
  no-$-RB (⊑⟪⟫ _ _ _ d _ _) = no-$-RX d

  no-5★-RB : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ 5★ ⊑ RB ∶ q)
  no-5★-RB (⊑⟪⟫ _ _ _ d _ _) = no-5★-RX d
  no-5★-RB (cast⊑ _ d _ _) = no-$-RB d

  no-$-R₇ : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ $ 5 ⊑ R₇ ∶ q)
  no-$-R₇ (⊑cast d _ _) = no-$-RB d

  no-5★-R₇ : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ 5★ ⊑ R₇ ∶ q)
  no-5★-R₇ (⊑cast d _ _) = no-5★-RB d
  no-5★-R₇ (cast⊑cast d _ _ _) = no-$-RB d
  no-5★-R₇ (cast⊑ _ d _ _) = no-$-R₇ d

  ---------------------------------------------------------------------
  -- THE DECISIVE PAIR: S against the right's `X!`.  ⊑cast needs the
  -- left's X joined with the right's X (`var⊑var`) at X⊑★ (`var⊑★`);
  -- the hypothesis H says that this never happens in the world at hand

  no-S-RX : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → A ≡ ` 0
    → (Joins V 0 0 → μʷ V ∋ˡ emb (ηᴸʷ V) 0 := X⊑★ → ⊥)
    → ¬ (V ∣ γ ⊢ S ⊑ RX ∶ q)
  no-S-RX {V = V} refl H (⊑cast {p = p} d ct q) with ct-X! ct
  ... | refl , refl =
    H (var⊑var (plain-idx {V = V} {A′ = ` 0} nf-var p))
      (var⊑★ (plain-idx {V = V} {A′ = ★} nf-var q))
  no-S-RX e H (⟪⟫⊑ _ _ _ d _ _) = no-5★-RX d

  -- the continuing left X in a world where a right `+X` rejoined it:
  -- it was PLAIN, so it is now X⊑X
  rejoined-left : ∀ {Δ₁ Δ₂ Δ₃} {V : World Δ₁ Δ₂} {Vj : World Δ₁ Δ₃}
    → Interior V [] Θ₀ Vj → Δ₁ ∋ᵗ 0 := 0 → stᴿ V 0 ≡ plain
    → Joins Vj 0 0 → μʷ Vj ∋ˡ emb (ηᴸʷ Vj) 0 := X⊑★ → ⊥
  rejoined-left {V = V} {Vj} I lh e₁ j h with emb-mark (ηᴸʷ V) lh
  ... | m , mk₀ with mark-left I (_ , lh) refl mk₀
  ... | _ , mk with lookup-unique h
        (rejoin e₁
          (subst (λ c → statusAt (ηᴿʷ Vj) c ≡ joined) (sym j)
            (st-emb (ηᴿʷ Vj) (bind₀-int (int-right I))))
          mk)
  ... | ()

  -- the continuing right X in a world where a left `+X` rejoined it
  rejoined-right : ∀ {Δ₁ Δ₂ Δ₃} {V : World Δ₁ Δ₂} {Vj : World Δ₃ Δ₂}
    → Interior V Θ₀ [] Vj → Δ₂ ∋ᵗ 0 := 0 → stᴸ V 0 ≡ plain
    → Joins Vj 0 0 → μʷ Vj ∋ˡ emb (ηᴸʷ Vj) 0 := X⊑★ → ⊥
  rejoined-right {V = V} {Vj} I rh e₁ j h with emb-mark (ηᴿʷ V) rh
  ... | m , mk₀ with mark-right I (_ , rh) refl mk₀
  ... | _ , mk with lookup-unique (subst (λ c → μʷ Vj ∋ˡ c := X⊑★) j h)
        (rejoin e₁
          (subst (λ c → statusAt (ηᴸʷ Vj) c ≡ joined) j
            (st-emb (ηᴸʷ Vj) (bind₀-int (int-left I))))
          mk)
  ... | ()

  ---------------------------------------------------------------------
  -- the left outside its boundary, against the right's `X!` (the right
  -- X right-only and plain): the left must enter `[+X^α]` to reach S,
  -- and its fresh X then rejoins the plain right X at X⊑X

  no-LB-RX : ∀ {Δ₂} {V : World ΔR Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Δ₂ ∋ᵗ 0 := 0 → stᴸ V 0 ≡ plain → ¬ (V ∣ γ ⊢ LB ⊑ RX ∶ q)
  no-LB-RX {V = V} rh e (⊑cast {p = p} d ct _) with ct-X! ct | lty-bdy d
  ... | refl , refl | _ , _ , b with bdy-LB b
  ... | _ , _ , refl = no-★⊑var {V = V} p
  no-LB-RX rh e (⟪⟫⊑ I _ _ d b _) with bdy-LB b
  ... | lh , refl , refl = no-S-RX refl (rejoined-right I rh e) d

  no-Lid-RX : ∀ {Δ₂} {V : World ΔR Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Δ₂ ∋ᵗ 0 := 0 → stᴸ V 0 ≡ plain → ¬ (V ∣ γ ⊢ Lid ⊑ RX ∶ q)
  no-Lid-RX {V = V} rh e (⊑cast {p = p} d ct _) with ct-X! ct | lty-cast d
  ... | refl , refl | _ , ct₀ with ct-id★ ct₀
  ... | _ , refl = no-★⊑var {V = V} p
  no-Lid-RX rh e (cast⊑cast {p = p} d ct ct′ _) with ct-id★ ct | ct-X! ct′
  ... | refl , _ | refl , _ = no-plain-★⊑var p
  no-Lid-RX rh e (cast⊑ _ d _ _) = no-LB-RX rh e d

  no-L₆-RX : ∀ {Δ₂} {V : World ΔR Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Δ₂ ∋ᵗ 0 := 0 → stᴸ V 0 ≡ plain → ¬ (V ∣ γ ⊢ L₆ ⊑ RX ∶ q)
  no-L₆-RX {V = V} rh e (⊑cast {p = p} d ct _) with ct-X! ct | lty-cast d
  ... | refl , refl | _ , ct₀ with ct-ℕ? ct₀
  ... | _ , refl = no-ℕ⊑var {V = V} p
  no-L₆-RX rh e (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ? ct | ct-X! ct′
  ... | refl , _ | refl , _ = no-plain-★⊑var p
  no-L₆-RX rh e (cast⊑ _ d _ _) = no-Lid-RX rh e d

  ---------------------------------------------------------------------
  -- the left inside its boundary (X plain left-only), against the
  -- right outside its own

  no-S-R₇ : ∀ {Δ₁} {V : World Δ₁ ΔR} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → A ≡ ` 0 → ¬ (V ∣ γ ⊢ S ⊑ R₇ ∶ q)
  no-S-R₇ {V = V} refl (⊑cast d ct q) with ct-ℕ? ct
  ... | _ , refl = no-var⊑ℕ {V = V} q
  no-S-R₇ _ (⟪⟫⊑ _ _ _ d _ _) = no-5★-R₇ d

  no-S-RB : ∀ {Δ₁} {V : World Δ₁ ΔR} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Δ₁ ∋ᵗ 0 := 0 → stᴿ V 0 ≡ plain → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ RB ∶ q)
  no-S-RB lh e eA (⊑⟪⟫ I _ _ d _ _) = no-S-RX eA (rejoined-left I lh e) d
  no-S-RB lh e eA (⟪⟫⊑ _ _ _ d _ _) = no-5★-RB d
  no-S-RB lh e eA (⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = no-5★-RX d

  ---------------------------------------------------------------------
  -- both outside

  no-LB-RB : ∀ {V : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ LB ⊑ RB ∶ q)
  no-LB-RB (⊑⟪⟫ {Wᵢ = Vr} I _ _ d _ _) =
    no-LB-RX r0 (plain-of (fresh-right I (_ , r0) refl) (st-[] (ηᴸʷ Vr) _)) d
    where r0 = bind₀-int (int-right I)
  no-LB-RB (⟪⟫⊑ {Wᵢ = Vl} I _ _ d b _) with bdy-LB b
  ... | lh , refl , refl =
    no-S-RB lh (plain-of (fresh-left I (_ , lh) refl) (st-[] (ηᴿʷ Vl) _))
      refl d
  no-LB-RB (⟪⟫⊑⟪⟫ I _ d b b′ bc _) with bdy-LB b
  ... | lh , refl , refl =
    no-S-RX refl
      (λ j _ → matched-conv b b′ bc
        (proj₁ (join-fresh I lh (bind₀-int (int-right I)) (inj₁ refl)) j))
      d

  no-Lid-RB : ∀ {V : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ Lid ⊑ RB ∶ q)
  no-Lid-RB (⊑⟪⟫ {Wᵢ = Vr} I _ _ d _ _) =
    no-Lid-RX r0 (plain-of (fresh-right I (_ , r0) refl) (st-[] (ηᴸʷ Vr) _)) d
    where r0 = bind₀-int (int-right I)
  no-Lid-RB (cast⊑ _ d _ _) = no-LB-RB d

  no-L₆-RB : ∀ {V : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ L₆ ⊑ RB ∶ q)
  no-L₆-RB (⊑⟪⟫ {Wᵢ = Vr} I _ _ d _ _) =
    no-L₆-RX r0 (plain-of (fresh-right I (_ , r0) refl) (st-[] (ηᴸʷ Vr) _)) d
    where r0 = bind₀-int (int-right I)
  no-L₆-RB (cast⊑ _ d _ _) = no-Lid-RB d

  no-LB-R₇ : ∀ {V : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ LB ⊑ R₇ ∶ q)
  no-LB-R₇ (⊑cast d _ _) = no-LB-RB d
  no-LB-R₇ (⟪⟫⊑ _ _ _ d b _) with bdy-LB b
  ... | _ , refl , refl = no-S-R₇ refl d

  no-Lid-R₇ : ∀ {V : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ Lid ⊑ R₇ ∶ q)
  no-Lid-R₇ (⊑cast d _ _) = no-Lid-RB d
  no-Lid-R₇ (cast⊑cast d _ _ _) = no-LB-RB d
  no-Lid-R₇ (cast⊑ _ d _ _) = no-LB-R₇ d

  -- C1 IS UNRELATED: every world over (ΔR, ΔR), every index
  c1-unrelated : ∀ {W : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ L₆ ⊑ R₇ ∶ q)
  c1-unrelated (⊑cast d _ _) = no-L₆-RB d
  c1-unrelated (cast⊑cast d _ _ _) = no-Lid-RB d
  c1-unrelated (cast⊑ _ d _ _) = no-Lid-R₇ d

  ---------------------------------------------------------------------
  -- WHY THE REPAIR MUST BE SYMMETRIC.  In HEAD's relation (D11, D15),
  -- C1 has a RIGHT-FIRST derivation that uses no ★ conversion clause
  -- and no rejoin of a left-only name: the right's `+X` makes X
  -- right-only at a chosen X⊑★ (fresh marks are free, D11), the left's
  -- `+X` then joins it and `mark-right` keeps X⊑★.  So the asymmetric
  -- reading of the repair (only a left name rejoined by a right `+X`
  -- steps to X⊑X) still relates C1.

  module InHEAD where
    import ImprecisionWorld as HW
    import ConversionImprecision as HC
    import TermImprecision as HT
    import proof.ImprecisionWorld as HP

    Wαα : HW.World ΔR ΔR
    Wαα = HW.world [] HW.[]↪ HW.[]↪ ((0 , 0) ∷ []) [] []

    -- the right's X alone: right-only, at the chosen X⊑★
    Wr : HW.World ΔR ΔRᵢ
    Wr = HW.world (X⊑★ ∷ []) (HW.skip HW.[]↪) (HW.keep HW.[]↪)
           ((0 , 0) ∷ []) [] []

    -- the left's X joined to it: X⊑★ KEPT (HEAD's mark-right)
    Wj : HW.World ΔRᵢ ΔRᵢ
    Wj = HW.world (X⊑★ ∷ []) (HW.keep HW.[]↪) (HW.keep HW.[]↪)
           ((0 , 0) ∷ []) [] []

    agree★ : ∀ {Δ₀ Δ₀′} {W : HW.World Δ₀ Δ₀′} → Δ₀ ∋rep 0 := ★
      → Δ₀′ ∋rep 0 := ★ → HW.ϱᵍʷ W ≡ (0 , 0) ∷ [] → HW.ϱˡʷ W ≡ []
      → ∀ {α β} → HW.Paired W α β → HW.Agree W α β
    agree★ l r refl refl (inj₁ here⇔) = HW.rep-rep l r HW.★⊑★
    agree★ l r refl refl (inj₁ (there⇔ ()))
    agree★ l r refl refl (inj₂ ())

    Wαα-wf : HW.WfWorld Wαα
    Wαα-wf = HW.wf-world HW.joint[] (agree★ r-here r-here refl refl)
      (HP.namedᴸ-≤1 Wαα ≤1-[]) (HP.namedᴿ-≤1 Wαα ≤1-[]) [] []

    Wr-wf : HW.WfWorld Wr
    Wr-wf = HW.wf-world (HW.right-only HW.joint[])
      (agree★ r-here r-here refl refl)
      (HP.namedᴸ-≤1 Wr ≤1-[]) (HP.namedᴿ-≤1 Wr ≤1-∷[]) [] []

    Wj-wf : HW.WfWorld Wj
    Wj-wf = HW.wf-world (HW.both (inj₁ here⇔) HW.joint[])
      (agree★ r-here r-here refl refl)
      (HP.namedᴸ-≤1 Wj ≤1-∷[]) (HP.namedᴿ-≤1 Wj ≤1-∷[]) [] []

    IntR : HW.Interior Wαα [] Θ₀ Wr
    IntR = record
      { int-left   = interior changes[]
      ; int-right  = TIE.int₀
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { (_ , ()) _ _ _ }
      ; join-fresh = λ { () _ _ }
      ; mark-left  = λ { (_ , ()) _ _ }
      ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      }

    IntL : HW.Interior Wr Θ₀ [] Wj
    IntL = record
      { int-left   = TIE.int₀
      ; int-right  = interior changes[]
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
      ; join-fresh = λ
          { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
      ; mark-right = λ { (_ , here) refl m → m ; (_ , there ()) _ _ }
      }

    Wj-unb : HW.Interior Wj unb₀ unb₀ Wαα
    Wj-unb = record
      { int-left   = Rebase.unbind₀-int
      ; int-right  = Rebase.unbind₀-int
      ; same-ϱᵍ    = refl
      ; same-ϱˡ    = refl
      ; join-cont  = λ { (_ , ()) _ _ _ }
      ; join-fresh = λ { () _ _ }
      ; mark-left  = λ { (_ , ()) _ _ }
      ; mark-right = λ { (_ , ()) _ _ }
      }

    Wj-conv-self : HW.ConversionInterior Wj unb₀ unb₀ Wj
    Wj-conv-self = record
      { conv-left       = Rebase.unbind₀-conv
      ; conv-right      = Rebase.unbind₀-conv
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
      ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                            ; (there ()) _ _ }
      ; conv-mark-right = λ { here here m → m ; here (there ()) _
                            ; (there ()) _ _ }
      }

    bS : BdyTy ΔRᵢ unb₀ ΔR ★ (tail (seal 0)) (` 0)
    bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = S}))))

    bLB : BdyTy ΔR Θ₀ ΔRᵢ (` 0) (unseal 0) ★
    bLB = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = LB}))))

    bRB : BdyTy ΔR Θ₀ ΔRᵢ ★ ⌞ id ★ ⌟ ★
    bRB = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = RB}))))

    tagX-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) ((` 0) !) (` 0) ★
    tagX-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = RX})))

    id★-ty : CastTy ΔR [] (idᵖ ★) ★ ★
    id★-ty = cast-ty (⊢id atom-★ wf-★) refl

    ℕ?-ty : CastTy ΔR [] ℕ? ★ `ℕ
    ℕ?-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = R₇})))

    five★⊑ : Wαα HT.∣ [] ⊢ 5★ ⊑ 5★ ∶ ★⊑★
    five★⊑ = HT.cast⊑cast (HT.κ⊑κ lit-$ (ι⊑ι base-ℕ))
      (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★

    S⊑S : Wj HT.∣ [] ⊢ S ⊑ S ∶ X⊑X
    S⊑S = HT.⟪⟫⊑⟪⟫ Wj-unb Wαα-wf five★⊑ bS bS
      (Wj , Wj-conv-self , HC.conv-tail⊑tail (HC.conv-seal⊑seal refl)) X⊑X

    -- THE RIGHT-FIRST DERIVATION (HEAD): ⊑⟪⟫ (X right-only, X⊑★),
    -- then ⟪⟫⊑ (X joined, X⊑★ kept), then ⊑cast of the right's X!
    L₆⊑R₇ : Wαα HT.∣ [] ⊢ L₆ ⊑ R₇ ∶ ι⊑ι base-ℕ
    L₆⊑R₇ =
      HT.cast⊑cast
        (HT.cast⊑ cc-plain
          (HT.⊑⟪⟫ IntR push-none Wr-wf
            (HT.⟪⟫⊑ IntL bc-plain Wj-wf
              (HT.⊑cast S⊑S tagX-ty (X⊑★ here))
              bLB ★⊑★)
            bRB ★⊑★)
          id★-ty ★⊑★)
        ℕ?-ty ℕ?-ty (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- the two interiors that the repair rejects: HEAD's left-first
  -- rejoin (SidedMarks `Cex.InD11.IntR`) and the right-first one above

  Wl Wr Wj : ∀ {m} → World _ _
  Wl {m} = world {ΔRᵢ} {ΔR} (m ∷ []) (keep []↪) (skip []↪) ((0 , 0) ∷ []) [] []
  Wr {m} = world {ΔR} {ΔRᵢ} (m ∷ []) (skip []↪) (keep []↪) ((0 , 0) ∷ []) [] []
  Wj {m} = world {ΔRᵢ} {ΔRᵢ} (m ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  left-first-rejected : ∀ {m} → ¬ Interior (Wl {m}) [] Θ₀ (Wj {X⊑★})
  left-first-rejected I with mark-left I (_ , here) refl here
  ... | _ , ()

  right-first-rejected : ∀ {m} → ¬ Interior (Wr {m}) Θ₀ [] (Wj {X⊑★})
  right-first-rejected I with mark-right I (_ , here) refl here
  ... | _ , ()

------------------------------------------------------------------------
-- 13. NEW COUNTEREXAMPLE C4 ("pop"): the hidden-names repair does not
-- touch pending names, and a POPPED name is joined at X⊑★ (PendingOK,
-- D27).  C1's own run, one block earlier on the right: the left has
-- not yet instantiated, the right has (Inst, TyBeta).  ⊑⟪⟫ PUSHES the
-- right's Inst name, Λ⊑ POPS it, and the right's source-scope tag
-- `x⟨X!⟩^[X:★∼X∼★]` is related by ⊑cast at the popped X⊑★.  No
-- conversion is compared (the push is one-sided), so the restricted ★
-- clauses do not apply either.
------------------------------------------------------------------------

module C4 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open C1 using (5★; ℕ?; L₀; R₀; L₀-⊢; R₀-⊢; ΔR; ΔRᵢ)
  open TIE using (W₃; int-ro₃; Wi₃-wf; vΛidX; idX)
  open Rebase using (∀id⊑★; id★↦)

  -- the right's body after its TyBeta, and the Inst boundary
  bodyR : Term
  bodyR = ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩)

  cE : Conv
  cE = tail (mid (tail (seal 0) ↦ ⌞ id ★ ⌟))

  RBp R₂ : Term
  RBp = bodyR ⟪ Θ₀ , cE ⟫
  R₂  = ((RBp ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  R₂-state : nth (evalTerms 30 R₀-⊢) 2 ≡ R₂
  R₂-state = refl

  R₂-⊢ : ΔR ∣ [] ⊢ R₂ ⦂ `ℕ
  R₂-⊢ = tc

  R₂-blames : last (evalTerms 20 R₂-⊢) ≡ blame 0
  R₂-blames = refl

  L₀-never-blames : ∀ {ℓ} → ¬ (empty ⊢ L₀ -→* blame ℓ)
  L₀-never-blames r = all-reach {P = NotBlame} 30 L₀-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  bRBp : BdyTy ΔR Θ₀ ΔRᵢ (` 0 ⇒ ★) cE (★ ⇒ ★)
  bRBp = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = RBp}))))

  tagX-ty : CastTy ΔRᵢ (★∼X∼★ ∷ []) ((` 0) !) (` 0) ★
  tagX-ty = cast-ty (⊢tag-var (_ , here) here tag-cross) refl

  instL-ty : CastTy empty [] (instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)))
    (`∀ (` 0 ⇒ ` 0)) (★ ⇒ ★)
  instL-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = empty} {M = Λ idX ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)) ⟩})))

  id★↦-ty : CastTy ΔR [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  ℕ?ᴸ-ty : CastTy empty [] ℕ? ★ `ℕ
  ℕ?ᴸ-ty = cast-ty (⊢check g-ℕ) refl

  ℕ?ᴿ-ty : CastTy ΔR [] ℕ? ★ `ℕ
  ℕ?ᴿ-ty = cast-ty (⊢check g-ℕ) refl

  -- the pop: the left's body against the right's body, the right's
  -- source-scope tag read at the popped name's X⊑★
  pop-body : record (W₃ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] } ∣ [] ⊢ Λ idX ⊑ bodyR
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ★ ⟩ ⇒⊑⇒ X⊑X (X⊑★ here)
  pop-body =
    Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (ƛ⊑ƛ {pA = X⊑X} tf tf (⊑cast (x⊑x Zʷ) tagX-ty (X⊑★ here)))
      (⇒⊑⇒ X⊑X (X⊑★ here))

  C4 : W₃ ∣ [] ⊢ L₀ ⊑ R₂ ∶ ι⊑ι base-ℕ
  C4 =
    cast⊑cast
      (·⊑·
        (cast⊑cast
          (⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vΛidX)) Wi₃-wf
            pop-body bRBp (∀id⊑★ W₃))
          instL-ty id★↦-ty (⇒⊑⇒ ★⊑★ ★⊑★))
        (cast⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ))
          (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★))
      ℕ?ᴸ-ty ℕ?ᴿ-ty (ι⊑ι base-ℕ)

  -- SimBackBlame FAILS: a related pair, the right blames, the left
  -- never does
  c4-cex : (W₃ ∣ [] ⊢ L₀ ⊑ R₂ ∶ ι⊑ι base-ℕ)
    × (last (evalTerms 20 R₂-⊢) ≡ blame 0)
    × (∀ {ℓ} → ¬ (empty ⊢ L₀ -→* blame ℓ))
  c4-cex = C4 , R₂-blames , L₀-never-blames

------------------------------------------------------------------------
-- 14. More index facts: the right type of a right cast, the left type
-- of a λ
------------------------------------------------------------------------

rty-cast : ∀ {V : World Δ Δ′} {γ M M′ μ′ c′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q → Σ[ B′ ∈ Ty ] CastTy Δ′ μ′ c′ B′ A′
rty-cast (cast⊑cast _ _ ct′ _) = _ , ct′
rty-cast (⊑cast _ ct _)        = _ , ct
rty-cast (cast⊑ _ d _ _)       = rty-cast d
rty-cast (⟪⟫⊑ _ _ _ d _ _)     = rty-cast d
rty-cast (Λ⊑ _ _ _ _ _ d _)    = rty-cast d
rty-cast (ν⊑ d _ _ _)          = rty-cast d
rty-cast (blame⊑ _ ⊢M′ _) with cast-inv ⊢M′
... | _ , _ , ct = _ , ct

lty-ƛ : ∀ {V : World Δ Δ′} {γ A₀ N M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ ƛ A₀ ∙ N ⊑ M′ ∶ q → Σ[ B ∈ Ty ] A ≡ A₀ ⇒ B
lty-ƛ (ƛ⊑ƛ _ _ _)       = _ , refl
lty-ƛ (⊑cast d _ _)     = lty-ƛ d
lty-ƛ (⊑⟪⟫ _ _ _ d _ _) = lty-ƛ d

no-var⇒⊑ℕ⇒ : ∀ {V : World Δ Δ′} {X B B′} → ¬ ((` X ⇒ B) ⊑ᵂ⟨ V ⟩ (`ℕ ⇒ B′))
no-var⇒⊑ℕ⇒ {V = V} {X} {B} {B′} q
  with plain-idx {V = V} {A′ = `ℕ ⇒ B′} (nf-⇒ {A = ` X} {B = B}) q
... | ⇒⊑⇒ () _

no-ℕ⇒⊑var⇒ : ∀ {V : World Δ Δ′} {X B B′} → ¬ ((`ℕ ⇒ B) ⊑ᵂ⟨ V ⟩ (` X ⇒ B′))
no-ℕ⇒⊑var⇒ {V = V} {X} {B} {B′} q
  with plain-idx {V = V} {A′ = ` X ⇒ B′} (nf-⇒ {A = `ℕ} {B = B}) q
... | ⇒⊑⇒ () _

------------------------------------------------------------------------
-- 15. C3 = ModeCondition's `Esc.esc-cex-early` (both after TyBeta):
-- NOT DERIVABLE, in any world, at any index.  Matched boundaries need
-- `+X ⊑ id(★)` at a name that `−X ⊑ −X` joins (restricted clause);
-- each one-sided order meets `X ⊑ ℕ` or `ℕ ⊑ X` in the function index.
------------------------------------------------------------------------

module C3 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I★)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open TIE using (idX; revX; ΔL)
  open Rebase using (I★⁻)

  genE genE-body : Coercion
  genE-body = ((` 0) !) ↦ᵖ idᵖ ★
  genE      = genᵖ genE-body

  cE : Conv
  cE = tail (mid (tail (seal 0) ↦ ⌞ id ★ ⌟))

  --  LE = ((ν X:=ℕ. ((ΛY. λx:Y. x) X) ⟨−X → +X⟩) 5)⟨ℕ!⟩⟨ℕ?ℓ0⟩
  --  RE = ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → id(★))⟩ X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
  LE RE : Term
  LE = (((ν `ℕ · Λ idX ⟨ revX ⟩) · $ 5) ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE = ((ν `ℕ · (I★ ⟨ [] ∣ genE ⟩) ⟨ cE ⟩) · $ 5) ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE-⊢ : empty ∣ [] ⊢ LE ⦂ `ℕ
  LE-⊢ = tc

  RE-⊢ : empty ∣ [] ⊢ RE ⦂ `ℕ
  RE-⊢ = tc

  LB₁ RB₁ LA RA LE₁ RE₁ : Term
  LB₁ = idX ⟪ Θ₀ , revX ⟫
  RB₁ = (I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩) ⟪ Θ₀ , cE ⟫
  LA  = LB₁ · $ 5
  RA  = RB₁ · $ 5
  LE₁ = (LA ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE₁ = RA ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE₁-state : nth (evalTerms 20 LE-⊢) 1 ≡ LE₁
  LE₁-state = refl

  RE₁-state : nth (evalTerms 30 RE-⊢) 1 ≡ RE₁
  RE₁-state = refl

  LE₁-⊢ : ΔL ∣ [] ⊢ LE₁ ⦂ `ℕ
  LE₁-⊢ = tc

  RE₁-⊢ : ΔL ∣ [] ⊢ RE₁ ⦂ `ℕ
  RE₁-⊢ = tc

  RE₁-blames : last (evalTerms 20 RE₁-⊢) ≡ blame 0
  RE₁-blames = refl

  LE₁-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₁ -→* blame ℓ)
  LE₁-never-blames r = all-reach {P = NotBlame} 20 LE₁-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  -- the matched conversions `−X → +X` ⊑ `−X → id(★)`: the seal needs X
  -- joined, the unseal needs X left-only (in ANY conversion world)
  matched-conv : ∀ {Δ₁ Δ₂} {W : World Δ₁ Δ₂} {Δᵢ Δ′ᵢ Aᵢ A′ᵢ A A′ Θ Θ′}
      (b : BdyTy Δ₁ Θ Δᵢ Aᵢ revX A) (b′ : BdyTy Δ₂ Θ′ Δ′ᵢ A′ᵢ cE A′)
    → ¬ BdyConversionImp W b b′
  matched-conv (bdy-ty _ _ _ _ _)
    (bdy-ty _ (conv-tail (conv-mid (conv-fun
       (conv-tail (conv-seal (_ , _ , l , _))) _))) _ _ _)
    (_ , _ , conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
       (conv-tail⊑tail (conv-seal⊑seal j)) (conv-unseal⊑id★ _ lo)))) =
    lo (_ , l) j

  ct-genE-body : ∀ {Δ₀ μ B A} → CastTy Δ₀ μ genE-body B A → A ≡ ` 0 ⇒ ★
  ct-genE-body (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-genE-body (cast-ty (⊢fun (⊢tag-var _ _ _) (⊢id _ _)) _) = refl

  -- the function pair, its domains both ℕ (read off the argument 5)
  no-fun : ∀ {V : World ΔL ΔL} {γ A A′ B B′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → A ≡ `ℕ ⇒ B → A′ ≡ `ℕ ⇒ B′ → ¬ (V ∣ γ ⊢ LB₁ ⊑ RB₁ ∶ q)
  no-fun _ _ (⟪⟫⊑⟪⟫ _ _ _ b b′ bc _) = matched-conv b b′ bc
  no-fun {V = V} eA refl (⟪⟫⊑ {Wᵢ = Vi} _ _ _ d _ _) with lty-ƛ d
  ... | _ , refl = no-var⇒⊑ℕ⇒ {V = Vi} (idx d)
    where
    idx : ∀ {V′ : World _ ΔL} {γ M M′ A₁ A₂} {r : A₁ ⊑ᵂ⟨ V′ ⟩ A₂}
      → V′ ∣ γ ⊢ M ⊑ M′ ∶ r → A₁ ⊑ᵂ⟨ V′ ⟩ A₂
    idx {r = r} _ = r
  no-fun refl _ (⊑⟪⟫ {Wᵢ = Vi} _ _ _ d _ _) with rty-cast d
  ... | _ , ct with ct-genE-body ct
  ... | refl = no-ℕ⇒⊑var⇒ {V = Vi} (idx d)
    where
    idx : ∀ {Δ₃} {V′ : World ΔL Δ₃} {γ M M′ A₁ A₂} {r : A₁ ⊑ᵂ⟨ V′ ⟩ A₂}
      → V′ ∣ γ ⊢ M ⊑ M′ ∶ r → A₁ ⊑ᵂ⟨ V′ ⟩ A₂
    idx {r = r} _ = r

  no-app : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ LA ⊑ RA ∶ q)
  no-app (·⊑· f (κ⊑κ lit-$ _)) = no-fun refl refl f

  no-LAℕ!-RA : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RA ∶ q)
  no-LAℕ!-RA (cast⊑ _ d _ _) = no-app d

  no-LE₁-RA : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ LE₁ ⊑ RA ∶ q)
  no-LE₁-RA (cast⊑ _ d _ _) = no-LAℕ!-RA d

  no-LA-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ LA ⊑ RE₁ ∶ q)
  no-LA-RE₁ (⊑cast d _ _) = no-app d

  no-LAℕ!-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RE₁ ∶ q)
  no-LAℕ!-RE₁ (cast⊑cast d _ _ _) = no-app d
  no-LAℕ!-RE₁ (⊑cast d _ _) = no-LAℕ!-RA d
  no-LAℕ!-RE₁ (cast⊑ _ d _ _) = no-LA-RE₁ d

  -- C3 IS UNRELATED: every world over (ΔL, ΔL), every index
  c3-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ LE₁ ⊑ RE₁ ∶ q)
  c3-unrelated (cast⊑cast d _ _ _) = no-LAℕ!-RA d
  c3-unrelated (⊑cast d _ _) = no-LE₁-RA d
  c3-unrelated (cast⊑ _ d _ _) = no-LAℕ!-RE₁ d

------------------------------------------------------------------------
-- 16. The invariant for the left's boundary name: `Good V` says that
-- the left name 0, if it is X⊑★, is PLAIN (left-only, born so).  Every
-- one-sided RIGHT boundary keeps it (`good-step`: the statuses and
-- marks of `Interior`); a right name tag `X!` cannot be related under
-- it (`no-S`).
------------------------------------------------------------------------

Good : World Δ Δ′ → Set
Good V = μʷ V ∋ˡ emb (ηᴸʷ V) 0 := X⊑★ → stᴿ V 0 ≡ plain

good-core : ∀ s s′ m → StOK s s′ → X⊑★ ≡ markStep s s′ m
  → (m ≡ X⊑★ → s ≡ plain) → s′ ≡ plain
good-core plain  plain  m _  _  _ = refl
good-core plain  joined m _  () _
good-core plain  hidden m () _  _
good-core joined joined m _  e  g with g (sym e)
... | ()
good-core joined hidden m _  e  g with g (sym e)
... | ()
good-core joined plain  m () _  _
good-core hidden joined m _  e  g with g (sym e)
... | ()
good-core hidden hidden m _  e  g with g (sym e)
... | ()
good-core hidden plain  m () _  _

good-step : ∀ {Δ₁ Δ₂ Δ₃ α Θ′} {V : World Δ₁ Δ₂} {V′ : World Δ₁ Δ₃}
  → Interior V [] Θ′ V′ → Δ₁ ∋ᵗ 0 := α → Good V → Good V′
good-step {V = V} {V′} I lh G h′ with emb-mark (ηᴸʷ V) lh
... | m , mk₀ with mark-left I (_ , lh) refl mk₀
... | ok , mk′ =
  good-core (stᴿ V 0) (stᴿ V′ 0) m ok (lookup-unique h′ mk′)
    (λ e → G (subst (λ m′ → μʷ V ∋ˡ emb (ηᴸʷ V) 0 := m′) e mk₀))

-- a joined center position is the image of a name in range
st-inv : ∀ {η Ω c} (ι : η ↪ Ω) → statusAt ι c ≡ joined
  → Σ ℕ (λ X → Σ RVar (λ β → (η ∋ˡ X := β) × (emb ι X ≡ c)))
st-inv []↪ ()
st-inv {c = zero} (keep ι) refl = 0 , _ , here , refl
st-inv {c = suc c} (keep ι) e with st-inv ι e
... | X , β , h , ee = suc X , β , there h , cong suc ee
st-inv {c = zero} (skip ι) ()
st-inv {c = suc c} (skip ι) e with st-inv ι e
... | X , β , h , ee = X , β , h , cong suc ee
st-inv {c = zero} (hide ι) ()
st-inv {c = suc c} (hide ι) e with st-inv ι e
... | X , β , h , ee = X , β , h , cong suc ee

-- the left's fresh name 0, the right names continuing and PLAIN: it
-- is Good (a rejoin of a plain right name is X⊑X)
good-fresh : ∀ {Δ₁ Δ₂ Δ₃ α Θ} {V : World Δ₁ Δ₂} {V′ : World Δ₃ Δ₂}
  → Interior V Θ [] V′ → Δ₃ ∋ᵗ 0 := α → Fresh Θ 0
  → (∀ {X′ β} → names Δ₂ ∋ˡ X′ := β → stᴸ V X′ ≡ plain) → Good V′
good-fresh {V = V} {V′} I lh fr P h′ = aux (stᴿ V′ 0) refl
  where
  aux : ∀ s → stᴿ V′ 0 ≡ s → stᴿ V′ 0 ≡ plain
  aux plain  e = e
  aux hidden e = ⊥-elim (subst NotHid e (fresh-left I (_ , lh) fr))
  aux joined e with st-inv (ηᴿʷ V′) e
  ... | X′ , β , rh , ee with emb-mark (ηᴿʷ V) rh
  ... | m , mk₀ with mark-right I (_ , rh) refl mk₀
  ... | _ , mk with lookup-unique (subst (λ c → μʷ V′ ∋ˡ c := X⊑★) (sym ee) h′)
        (rejoin (P rh)
          (subst (λ c → statusAt (ηᴸʷ V′) c ≡ joined) (sym ee)
            (st-emb (ηᴸʷ V′) lh))
          mk)
  ... | ()

-- the left's fresh name 0 against right names it cannot join: Good
good-matched : ∀ {Δ₁ Δ₂ Δᵢ Δ′ᵢ α Θ Θ′} {V : World Δ₁ Δ₂}
    {Vᵢ : World Δᵢ Δ′ᵢ}
  → Interior V Θ Θ′ Vᵢ → Δᵢ ∋ᵗ 0 := α → Fresh Θ 0
  → (∀ {X′ β} → names Δ′ᵢ ∋ˡ X′ := β → ¬ Paired V α β) → Good Vᵢ
good-matched {Vᵢ = Vᵢ} I lh fr P h′ = aux (stᴿ Vᵢ 0) refl
  where
  aux : ∀ s → stᴿ Vᵢ 0 ≡ s → stᴿ Vᵢ 0 ≡ plain
  aux plain  e = e
  aux hidden e = ⊥-elim (subst NotHid e (fresh-left I (_ , lh) fr))
  aux joined e with st-inv (ηᴿʷ Vᵢ) e
  ... | X′ , β , rh , ee =
    ⊥-elim (P rh (proj₁ (join-fresh I lh rh (inj₁ fr)) (sym ee)))

-- right terms whose spine (casts, boundaries) reaches a name tag
data Reach : Term → Set where
  r-tag  : ∀ {U μ k} → Reach (U ⟨ μ ∣ (` k) ! ⟩)
  r-cast : ∀ {R μ c} → Reach R → Reach (R ⟨ μ ∣ c ⟩)
  r-⟪⟫   : ∀ {R Θ d} → Reach R → Reach (R ⟪ Θ , d ⟫)

ct-X!′ : ∀ {μ X B A} → CastTy Δ μ ((` X) !) B A
  → (Δ ∋tv X) × (B ≡ ` X) × (A ≡ ★)
ct-X!′ (cast-ty (⊢tag ()) _)
ct-X!′ (cast-ty (⊢tag-var tv _ _) _) = tv , refl , refl

no-$ : ∀ {V : World Δ Δ′} {γ n R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → Reach R → ¬ (V ∣ γ ⊢ $ n ⊑ R ∶ q)
no-$ {V = V} r-tag (⊑cast {p = p} d ct _) with ct-X! ct | lty-$ d
... | refl , refl | refl = no-ℕ⊑var {V = V} p
no-$ (r-cast r) (⊑cast d _ _) = no-$ r d
no-$ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ d _ _) = no-$ r d

-- [−X^α] n ⟨−X⟩, the left's sealed literal (the left's only term of
-- variable type)
sealedN : ℕ → Term
sealedN n = $ n ⟪ unbind 0 0 ∷ [] , tail (seal 0) ⟫

-- THE INSIDE LEMMA: under Good, the left's sealed literal is related to
-- no right term whose spine reaches a name tag (a tag needs the left X
-- joined at X⊑★, which Good makes plain)
no-S : ∀ {Δ₁ Δ₂ α n} {V : World Δ₁ Δ₂} {γ R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → Δ₁ ∋ᵗ 0 := α → Good V → A ≡ ` 0 → Reach R
  → ¬ (V ∣ γ ⊢ sealedN n ⊑ R ∶ q)
no-S {V = V} lh G refl r-tag (⊑cast {p = p} d ct q) with ct-X!′ ct
... | (_ , rh) , refl , refl with
      var⊑var (plain-idx {V = V} {A′ = ` _} nf-var p)
... | j with G (var⊑★ (plain-idx {V = V} {A′ = ★} nf-var q))
... | e with trans (sym e)
               (subst (λ c → statusAt (ηᴿʷ V) c ≡ joined) (sym j)
                 (st-emb (ηᴿʷ V) rh))
... | ()
no-S lh G eA (r-cast r) (⊑cast d _ _) = no-S lh G eA r d
no-S lh G eA (r-⟪⟫ r) (⊑⟪⟫ I _ _ d _ _) = no-S lh (good-step I lh G) eA r d
no-S lh G eA (r-⟪⟫ r) (⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = no-$ r d
no-S lh G eA r (⟪⟫⊑ _ _ _ d _ _) = no-$ r d

-- matched `+X` boundaries whose conversions are `+X` ⊑ `id(★)`: the
-- two αs are not paired (any payloads)
matched-conv★ : ∀ {R R′} {W : World (allocate R empty) (allocate R′ empty)}
    {Δᵢ Δ′ᵢ Aᵢ A′ᵢ A A′}
    (b : BdyTy (allocate R empty) Θ₀ Δᵢ Aᵢ (unseal 0) A)
    (b′ : BdyTy (allocate R′ empty) Θ₀ Δ′ᵢ A′ᵢ ⌞ id ★ ⌟ A′)
  → BdyConversionImp W b b′ → ¬ Paired W 0 0
matched-conv★ (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _)
  (Wᶜ , ci , conv-unseal⊑id★ _ lo) pr =
  lo (_ , bind₀-conv (conv-right ci))
     (proj₂ (conv-join-fresh ci (bind₀-conv (conv-left ci))
              (bind₀-conv (conv-right ci)) (inj₁ fresh[])) pr)

------------------------------------------------------------------------
-- 17. C2 = ModeCondition's `Esc.esc-cex` (the late pair): NOT
-- DERIVABLE, in any world, at any index.  The left's X is PLAIN when
-- born (whatever the right has bound), every rejoin of a plain name is
-- X⊑X, a right `−X` hides it with X⊑X, the right's second `+X` rejoins
-- it with X⊑X; the matched orders compare `+X` with `id(★)`.
------------------------------------------------------------------------

module C2 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open TIE using (ΔL; ΔLᵢ)
  open C3 using (LE; RE; LE-⊢; RE-⊢)

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  S₄ LB₄ Lℕ LE₃ RX J RU RI RB₅ RE₅ : Term
  S₄  = sealedN 5
  LB₄ = S₄ ⟪ Θ₀ , unseal 0 ⟫
  Lℕ  = LB₄ ⟨ [] ∣ `ℕ ! ⟩
  LE₃ = Lℕ ⟨ [] ∣ `ℕ ？ 0 ⟩
  RX  = S₄ ⟨ X∼★ ∷ [] ∣ (` 0) ! ⟩
  J   = RX ⟪ Θ₀ , id★ᶜ ⟫
  RU  = J ⟪ unb₀ , id★ᶜ ⟫
  RI  = RU ⟨ ★∼X ∷ [] ∣ idᵖ ★ ⟩
  RB₅ = RI ⟪ Θ₀ , id★ᶜ ⟫
  RE₅ = RB₅ ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE₃-state : nth (evalTerms 20 LE-⊢) 3 ≡ LE₃
  LE₃-state = refl

  RE₅-state : nth (evalTerms 30 RE-⊢) 5 ≡ RE₅
  RE₅-state = refl

  -- J is P4 B4's J verbatim
  J-is-P4 : J ≡ P4.J
  J-is-P4 = refl

  LE₃-⊢ : ΔL ∣ [] ⊢ LE₃ ⦂ `ℕ
  LE₃-⊢ = tc

  RE₅-⊢ : ΔL ∣ [] ⊢ RE₅ ⦂ `ℕ
  RE₅-⊢ = tc

  RE₅-blames : last (evalTerms 20 RE₅-⊢) ≡ blame 0
  RE₅-blames = refl

  LE₃-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₃ -→* blame ℓ)
  LE₃-never-blames r = all-reach {P = NotBlame} 20 LE₃-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  bdy-LB₄ : ∀ {Δᵢ Aᵢ A} → BdyTy ΔL Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Δᵢ ∋ᵗ 0 := 0) × (Aᵢ ≡ ` 0) × (A ≡ `ℕ)
  bdy-LB₄ (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
    with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
  bdy-LB₄ (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-ℕ))
                  (_ , same-var here , same-var here)
                  (_ , same-ℕ , same-ℕ) _) | refl | refl =
    here , refl , refl

  int-bind : ∀ {Δ′ᵢ} → ΔL ⊢ⁱ Θ₀ ⇒ Δ′ᵢ → Δ′ᵢ ≡ ΔLᵢ
  int-bind i = interior-functional i TIE.int₀

  int-unb : ∀ {Δ′ᵢ} → ΔLᵢ ⊢ⁱ unb₀ ⇒ Δ′ᵢ → Δ′ᵢ ≡ ΔL
  int-unb i = interior-functional i Rebase.unbind₀-int

  -- the left terms outside the boundary: LB₄ under ground casts
  data LO : Term → Set where
    lo-B  : LO LB₄
    lo-ℕ! : ∀ {M} → LO M → LO (M ⟨ [] ∣ `ℕ ! ⟩)
    lo-ℕ? : ∀ {M} → LO M → LO (M ⟨ [] ∣ `ℕ ？ 0 ⟩)

  data G : Ty → Set where
    gℕ : G `ℕ
    g★ : G ★

  no-G⊑var : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {A X} → G A → ¬ (A ⊑ᵂ⟨ V ⟩ ` X)
  no-G⊑var {V = V} gℕ = no-ℕ⊑var {V = V}
  no-G⊑var {V = V} g★ = no-★⊑var {V = V}

  no-G⊑varᵖ : ∀ {μ : ImpEnv} {A a} → G A → ¬ (μ ⊢ A ⊑ ` a)
  no-G⊑varᵖ gℕ = no-plain-ℕ⊑var
  no-G⊑varᵖ g★ = no-plain-★⊑var

  lo-ty : ∀ {Δ₂} {V : World ΔL Δ₂} {γ M R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → V ∣ γ ⊢ M ⊑ R ∶ q → G A
  lo-ty lo-B d with lty-bdy d
  ... | _ , _ , b with bdy-LB₄ b
  ... | _ , _ , refl = gℕ
  lo-ty (lo-ℕ! _) d with lty-cast d
  ... | _ , ct with ct-ℕ! ct
  ... | _ , refl = g★
  lo-ty (lo-ℕ? _) d with lty-cast d
  ... | _ , ct with ct-ℕ? ct
  ... | _ , refl = gℕ

  -- the left's boundary entered with the right's names all plain
  enter : ∀ {Δ₂ Δᵢ} {V : World ΔL Δ₂} {Vᵢ : World Δᵢ Δ₂}
      {γ R A Aᵢ A′} {r : Aᵢ ⊑ᵂ⟨ Vᵢ ⟩ A′}
    → Interior V Θ₀ [] Vᵢ → BdyTy ΔL Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (∀ {X′ β} → names Δ₂ ∋ˡ X′ := β → stᴸ V X′ ≡ plain)
    → Reach R → ¬ (Vᵢ ∣ γ ⊢ S₄ ⊑ R ∶ r)
  enter I b P rr d with bdy-LB₄ b
  ... | lh , refl , refl = no-S lh (good-fresh I lh refl P) refl rr d

  noR : ∀ {A : Set} {X′ β} → names ΔL ∋ˡ X′ := β → A
  noR ()

  one : ∀ {V : World ΔL ΔLᵢ} → stᴸ V 0 ≡ plain
    → ∀ {X′ β} → names ΔLᵢ ∋ˡ X′ := β → stᴸ V X′ ≡ plain
  one e here = e

  rRX rJ rRU rRI rRB₅ rRE₅ : Reach _
  rRX  = r-tag {U = S₄} {μ = X∼★ ∷ []} {k = 0}
  rJ   = r-⟪⟫ {Θ = Θ₀} {d = id★ᶜ} rRX
  rRU  = r-⟪⟫ {Θ = unb₀} {d = id★ᶜ} rJ
  rRI  = r-cast {μ = ★∼X ∷ []} {c = idᵖ ★} rRU
  rRB₅ = r-⟪⟫ {Θ = Θ₀} {d = id★ᶜ} rRI
  rRE₅ = r-cast {μ = []} {c = `ℕ ？ 0} rRB₅

  ---------------------------------------------------------------------
  -- the stages of the right spine, the left outside its boundary

  o-RX : ∀ {V : World ΔL ΔLᵢ} {γ M A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → stᴸ V 0 ≡ plain → ¬ (V ∣ γ ⊢ M ⊑ RX ∶ q)
  o-RX {V = V} lo e (⊑cast {p = p} d ct _) with ct-X! ct
  ... | refl , refl = no-G⊑var {V = V} (lo-ty lo d) p
  o-RX (lo-ℕ! lo) e (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ! ct | ct-X! ct′
  ... | refl , _ | refl , _ = no-G⊑varᵖ gℕ p
  o-RX (lo-ℕ? lo) e (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ? ct | ct-X! ct′
  ... | refl , _ | refl , _ = no-G⊑varᵖ g★ p
  o-RX (lo-ℕ! lo) e (cast⊑ _ d _ _) = o-RX lo e d
  o-RX (lo-ℕ? lo) e (cast⊑ _ d _ _) = o-RX lo e d
  o-RX {V = V} lo-B e (⟪⟫⊑ I _ _ d b _) = enter I b (one {V = V} e) rRX d

  o-J : ∀ {V : World ΔL ΔL} {γ M A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → ¬ (V ∣ γ ⊢ M ⊑ J ∶ q)
  o-J lo (⊑⟪⟫ {Wᵢ = V′} I _ _ d _ _) with int-bind (int-right I)
  ... | refl =
    o-RX lo (plain-of (fresh-right I (_ , here) refl) (st-[] (ηᴸʷ V′) _)) d
  o-J (lo-ℕ! lo) (cast⊑ _ d _ _) = o-J lo d
  o-J (lo-ℕ? lo) (cast⊑ _ d _ _) = o-J lo d
  o-J lo-B (⟪⟫⊑ I _ _ d b _) = enter I b noR rJ d
  o-J lo-B (⟪⟫⊑⟪⟫ I _ d b b′ bc _) with bdy-LB₄ b | int-bind (int-right I)
  ... | lh , refl , refl | refl =
    no-S lh
      (good-matched I lh refl
        (λ { here pr → matched-conv★ b b′ bc pr }))
      refl rRX d

  o-RU : ∀ {V : World ΔL ΔLᵢ} {γ M A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → stᴸ V 0 ≡ plain → ¬ (V ∣ γ ⊢ M ⊑ RU ∶ q)
  o-RU lo e (⊑⟪⟫ I _ _ d _ _) with int-unb (int-right I)
  ... | refl = o-J lo d
  o-RU (lo-ℕ! lo) e (cast⊑ _ d _ _) = o-RU lo e d
  o-RU (lo-ℕ? lo) e (cast⊑ _ d _ _) = o-RU lo e d
  o-RU {V = V} lo-B e (⟪⟫⊑ I _ _ d b _) = enter I b (one {V = V} e) rRU d
  o-RU lo-B e (⟪⟫⊑⟪⟫ I _ d b _ _ _) with bdy-LB₄ b | int-unb (int-right I)
  ... | lh , refl , refl | refl =
    no-S lh (good-matched I lh refl noR) refl rJ d

  o-RI : ∀ {V : World ΔL ΔLᵢ} {γ M A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → stᴸ V 0 ≡ plain → ¬ (V ∣ γ ⊢ M ⊑ RI ∶ q)
  o-RI lo e (⊑cast d _ _) = o-RU lo e d
  o-RI (lo-ℕ! lo) e (cast⊑cast d _ _ _) = o-RU lo e d
  o-RI (lo-ℕ? lo) e (cast⊑cast d _ _ _) = o-RU lo e d
  o-RI (lo-ℕ! lo) e (cast⊑ _ d _ _) = o-RI lo e d
  o-RI (lo-ℕ? lo) e (cast⊑ _ d _ _) = o-RI lo e d
  o-RI {V = V} lo-B e (⟪⟫⊑ I _ _ d b _) = enter I b (one {V = V} e) rRI d

  o-RB₅ : ∀ {V : World ΔL ΔL} {γ M A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → ¬ (V ∣ γ ⊢ M ⊑ RB₅ ∶ q)
  o-RB₅ lo (⊑⟪⟫ {Wᵢ = V′} I _ _ d _ _) with int-bind (int-right I)
  ... | refl =
    o-RI lo (plain-of (fresh-right I (_ , here) refl) (st-[] (ηᴸʷ V′) _)) d
  o-RB₅ (lo-ℕ! lo) (cast⊑ _ d _ _) = o-RB₅ lo d
  o-RB₅ (lo-ℕ? lo) (cast⊑ _ d _ _) = o-RB₅ lo d
  o-RB₅ lo-B (⟪⟫⊑ I _ _ d b _) = enter I b noR rRB₅ d
  o-RB₅ lo-B (⟪⟫⊑⟪⟫ I _ d b b′ bc _) with bdy-LB₄ b | int-bind (int-right I)
  ... | lh , refl , refl | refl =
    no-S lh
      (good-matched I lh refl
        (λ { here pr → matched-conv★ b b′ bc pr }))
      refl rRI d

  o-RE₅ : ∀ {V : World ΔL ΔL} {γ M A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → ¬ (V ∣ γ ⊢ M ⊑ RE₅ ∶ q)
  o-RE₅ lo (⊑cast d _ _) = o-RB₅ lo d
  o-RE₅ (lo-ℕ! lo) (cast⊑cast d _ _ _) = o-RB₅ lo d
  o-RE₅ (lo-ℕ? lo) (cast⊑cast d _ _ _) = o-RB₅ lo d
  o-RE₅ (lo-ℕ! lo) (cast⊑ _ d _ _) = o-RE₅ lo d
  o-RE₅ (lo-ℕ? lo) (cast⊑ _ d _ _) = o-RE₅ lo d
  o-RE₅ lo-B (⟪⟫⊑ I _ _ d b _) = enter I b noR rRE₅ d

  -- C2 IS UNRELATED: every world over (ΔL, ΔL), every index
  c2-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ LE₃ ⊑ RE₅ ∶ q)
  c2-unrelated = o-RE₅ (lo-ℕ? (lo-ℕ! lo-B))

------------------------------------------------------------------------
-- 18. Cg B1 (cambridge Ex 1/20 after the left's catch-up TyBeta), not
-- mechanized under D11 before: matched `+X` boundaries (αᴸ:=ℕ against
-- the right's Inst αᴿ:=★, paired globally), X both-sided at X⊑★; the
-- right's gen wrapper `X! → X?` by ⊑cast; the right's own `−X` HIDES X
-- (Wcᴸ is hidden), where λx:X.x ⊑ λx:★.x reads X ⊑ ★
------------------------------------------------------------------------

module CgB1 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (Cg-L; Cg-L-⊢; I★)
  open TIE using (idX; revX; L1′; ΔL; ΔR; ΔLᵢ; bL-ty; revX⊑revX; five⊑)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; Cg-R₂; Cg-R₂-state; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty;
           id★↦ᴿ-ty; ℕ⇒ℕ⊑★⇒★)

  Ξg : RepCtx
  Ξg = bindR ★ ∷ []

  ϱg : RepRel
  ϱg = (0 , 0) ∷ []

  Cg-L₁-state : head (drop 1 (evalTerms 10 Cg-L-⊢)) ≡ just L1′
  Cg-L₁-state = refl

  module Wfg {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξg ∣ nsR)
    W = world μ η η′ ϱg [] []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wg²-wf : WfWorld (Wc² {Ξg} {ϱg} 0)
  Wg²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] []
    where open Wfg (X⊑★ ∷ []) (keep []↪) (keep []↪)

  Wgᴴ-wf : WfWorld (Wcᴸ {Ξg} {ϱg})
  Wgᴴ-wf = wf-world (hidden-r joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] []
    where open Wfg (X⊑★ ∷ []) (keep []↪) (hide []↪)

  idX⊑I★ : Wcᴸ {Ξg} {ϱg} ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξg ϱg
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  cg-b1 : Wc⁰ {Ξg} {ϱg} ∣ [] ⊢ L1′ ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
  cg-b1 =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ (Wc-bind² (_ , here) here⇔) Wg²-wf
          (⊑cast {A = ` 0 ⇒ ` 0}
            (⊑⟪⟫ (Wc-unbindᴿ (_ , here)) push-none Wgᴴ-wf idX⊑I★ I★⁻ᴿ-ty
              (c⊑★² Ξg ϱg 0))
            tagᴿ-ty (c⊑c² Ξg ϱg 0))
          bL-ty Bg-ty
          (Wc² 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
          (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
      five⊑

------------------------------------------------------------------------
-- 19. NEW COUNTEREXAMPLE C4g: C4 with a GEN-MODE tag, so the mode
-- condition of ModeCondition.md does not reject it either.  The right
-- is a gen-wrapped dynamic identity, instantiated: `X! → id(★)` at
-- `^[X:★∼X]`, the Inst boundary's conversion `−X → id(★)`.  The pop
-- (X⊑★, PendingOK) then the right's own `−X` (hidden, X⊑★).  This is
-- Cg X0's derivation (`Rebase.cg-body`) with the codomain `id(★)`.
------------------------------------------------------------------------

module C4g where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I★)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open C1 using (5★; ℕ?; L₀; L₀-⊢; ΔR)
  open C3 using (genE; genE-body; cE; RB₁)
  open C4 using (instL-ty; id★↦-ty; ℕ?ᴸ-ty; ℕ?ᴿ-ty; L₀-never-blames)
  open TIE using (W₃; int-ro₃; Wi₃-wf; vΛidX; idX)
  open Rebase
    using (∀id⊑★; id★↦; I★⁻; Wg⁺; Wg⁻; Wg⁻-int; Wg⁻-wf; I★⁻ᴿ-ty;
           X⇒X⊑★⇒★)

  R0g R2g : Term
  R0g = (((I★ ⟨ [] ∣ genE ⟩) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩)
          · 5★) ⟨ [] ∣ ℕ? ⟩
  R2g = ((RB₁ ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  R0g-⊢ : empty ∣ [] ⊢ R0g ⦂ `ℕ
  R0g-⊢ = tc

  R2g-state : nth (evalTerms 30 R0g-⊢) 2 ≡ R2g
  R2g-state = refl

  R2g-⊢ : ΔR ∣ [] ⊢ R2g ⦂ `ℕ
  R2g-⊢ = tc

  R2g-blames : last (evalTerms 30 R2g-⊢) ≡ blame 0
  R2g-blames = refl

  bRB₁ : BdyTy ΔR Θ₀ (reps ΔR ∣ (0 ∷ [])) (` 0 ⇒ ★) cE (★ ⇒ ★)
  bRB₁ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = RB₁}))))

  bodyᵍ-ty : CastTy (reps ΔR ∣ (0 ∷ [])) (★∼X ∷ []) genE-body (★ ⇒ ★)
    (` 0 ⇒ ★)
  bodyᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = reps ΔR ∣ (0 ∷ [])} {M = I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩})))

  pop-body : record (W₃ ⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] } ∣ [] ⊢ Λ idX
    ⊑ I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ★ ⟩ ⇒⊑⇒ X⊑X (X⊑★ here)
  pop-body =
    Λ⊑ (claim-pop (open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (⊑cast
        (⊑⟪⟫ Wg⁻-int push-none Wg⁻-wf
          (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
          I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺} here))
        bodyᵍ-ty (⇒⊑⇒ X⊑X (X⊑★ here)))
      (⇒⊑⇒ X⊑X (X⊑★ here))

  C4g : W₃ ∣ [] ⊢ L₀ ⊑ R2g ∶ ι⊑ι base-ℕ
  C4g =
    cast⊑cast
      (·⊑·
        (cast⊑cast
          (⊑⟪⟫ int-ro₃ (push ca-[] (refl ∷ []) (inj₂ vΛidX)) Wi₃-wf
            pop-body bRB₁ (∀id⊑★ W₃))
          instL-ty id★↦-ty (⇒⊑⇒ ★⊑★ ★⊑★))
        (cast⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ))
          (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★))
      ℕ?ᴸ-ty ℕ?ᴿ-ty (ι⊑ι base-ℕ)

  c4g-cex : (W₃ ∣ [] ⊢ L₀ ⊑ R2g ∶ ι⊑ι base-ℕ)
    × (last (evalTerms 30 R2g-⊢) ≡ blame 0)
    × (∀ {ℓ} → ¬ (empty ⊢ L₀ -→* blame ℓ))
  c4g-cex = C4g , R2g-blames , L₀-never-blames

  -- the push's boundary conversion `−X → id(★)` against the left's
  -- would-be `−X → +X` (the conversion the left's own Inst would
  -- produce): no conversion world relates them (C3.matched-conv's
  -- core); a push premise comparing them would kill C4 and C4g
  revX⋢cE : ∀ {Δ₁ Δ₂} {Wᶜ : World Δ₁ Δ₂} → Δ₂ ∋tv 0
    → ¬ ConvImp Wᶜ TIE.revX cE
  revX⋢cE tv (conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
    (conv-tail⊑tail (conv-seal⊑seal j)) (conv-unseal⊑id★ _ lo)))) =
    lo tv j

------------------------------------------------------------------------
-- 20. C18b B7 (cambridge Ex 18b, block (7,12)), not mechanized under
-- D11 before: TWO names at once.  Matched outer `(+Y,+X)`, both
-- both-sided at X⊑★ (chosen, D11); the right's `X?` reads X ⊑ ★; the
-- right's `(−Y,−X)` HIDES both (hidden-r twice); its `(+X,+Y)`
-- rejoins both (hidden → joined, marks kept); the right's `X!` reads
-- X ⊑ ★.  Center 0 is Y (rep. var 0 = β), center 1 is X (rep. var 1 = α).
------------------------------------------------------------------------

module C18bB7 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.Examples using (ℓ)
  open import examples.CambridgeExamples using (C18b-L-⊢; C18b-R-⊢)
  open P4 using (nth)

  Δ₀ Δ₂ : Ctxᵗ
  Δ₀ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ []
  Δ₂ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

  Θo Θh Θj ΘS : Boundary
  Θo = bind 1 1 ∷ bind 0 0 ∷ []
  Θh = unbind 0 1 ∷ unbind 0 0 ∷ []
  Θj = bind 0 0 ∷ bind 0 1 ∷ []
  ΘS = unbind 0 0 ∷ unbind 1 1 ∷ []

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  S2 J2 RH L7 R12 : Term
  S2  = $ 42 ⟪ ΘS , tail (seal 1) ⟫
  J2  = (S2 ⟨ flipᵐ ★∼X ∷ X∼★ ∷ [] ∣ (` 1) ! ⟩) ⟪ Θj , id★ᶜ ⟫
  RH  = J2 ⟪ Θh , id★ᶜ ⟫
  L7  = S2 ⟪ Θo , unseal 1 ⟫
  R12 = (RH ⟨ ★∼X ∷ ★∼X ∷ [] ∣ (` 1) ？ ℓ ⟩) ⟪ Θo , unseal 1 ⟫

  L7-state : nth (evalTerms 30 C18b-L-⊢) 7 ≡ L7
  L7-state = refl

  R12-state : nth (evalTerms 30 C18b-R-⊢) 12 ≡ R12
  R12-state = refl

  ϱ : RepRel
  ϱ = (0 , 0) ∷ (1 , 1) ∷ []

  W₀ : World Δ₀ Δ₀
  W₀ = world [] []↪ []↪ ϱ [] []

  -- both both-sided, X⊑★
  Wb : World Δ₂ Δ₂
  Wb = world (X⊑★ ∷ X⊑★ ∷ []) (keep (keep []↪)) (keep (keep []↪)) ϱ [] []

  -- both HIDDEN by the right
  Wh : World Δ₂ Δ₀
  Wh = world (X⊑★ ∷ X⊑★ ∷ []) (keep (keep []↪)) (hide (hide []↪)) ϱ [] []

  module Wf {nsL nsR : TyCtx} (μ : ImpEnv)
      (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

    W : World ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsL)
              ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsR)
    W = world μ η η′ ϱ [] []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep (r-there r-here) (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())

    diag : ∀ {α β} → Paired W α β → α ≡ β
    diag (inj₁ here⇔) = refl
    diag (inj₁ (there⇔ here⇔)) = refl
    diag (inj₁ (there⇔ (there⇔ ())))
    diag (inj₂ ())

    uniqᴸ : NamedUniqueᴸ W
    uniqᴸ _ _ _ p p′ = trans (diag p) (sym (diag p′))

    uniqᴿ : NamedUniqueᴿ W
    uniqᴿ _ _ _ p p′ = trans (sym (diag p)) (diag p′)

  W₀-wf : WfWorld W₀
  W₀-wf = wf-world joint[] agree uniqᴸ uniqᴿ [] []
    where open Wf [] []↪ []↪

  Wb-wf : WfWorld Wb
  Wb-wf = wf-world (both (inj₁ here⇔) (both (inj₁ (there⇔ here⇔)) joint[]))
    agree uniqᴸ uniqᴿ [] []
    where open Wf (X⊑★ ∷ X⊑★ ∷ []) (keep (keep []↪)) (keep (keep []↪))

  Wh-wf : WfWorld Wh
  Wh-wf = wf-world (hidden-r (hidden-r joint[])) agree uniqᴸ uniqᴿ [] []
    where open Wf (X⊑★ ∷ X⊑★ ∷ []) (keep (keep []↪)) (hide (hide []↪))

  -- the boundaries' interior contexts
  int-o : Δ₀ ⊢ⁱ Θo ⇒ Δ₂
  int-o = interior (changes∷ (changes∷ changes[]
    (step-bind (_ , here) fresh[] ins-here))
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  int-h : Δ₂ ⊢ⁱ Θh ⇒ Δ₀
  int-h = interior (changes∷ (changes∷ changes[]
    (step-unbind (_ , here) del-here (fresh∷ (λ ()) fresh[])))
    (step-unbind (_ , there here) del-here fresh[]))

  int-j : Δ₀ ⊢ⁱ Θj ⇒ Δ₂
  int-j = interior (changes∷ (changes∷ changes[]
    (step-bind (_ , there here) fresh[] ins-here))
    (step-bind (_ , here) (fresh∷ (λ ()) fresh[]) ins-here))

  int-S : Δ₂ ⊢ⁱ ΘS ⇒ Δ₀
  int-S = interior (changes∷ (changes∷ changes[]
    (step-unbind (_ , there here) (del-there del-here) (fresh∷ (λ ()) fresh[])))
    (step-unbind (_ , here) del-here fresh[]))

  -- the joins of the two fresh pairs: name i on each side, rep. var i
  pairs : ∀ {X X′ α β} → Δ₂ ∋ᵗ X := α → Δ₂ ∋ᵗ X′ := β
    → (Joins Wb X X′ → Paired W₀ α β) × (Paired W₀ α β → Joins Wb X X′)
  pairs here here = (λ _ → inj₁ here⇔) , (λ _ → refl)
  pairs here (there here) =
    (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
  pairs (there here) here =
    (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
  pairs (there here) (there here) = (λ _ → inj₁ (there⇔ here⇔)) , (λ _ → refl)

  -- the matched outer (+Y,+X): both fresh, both joined, X⊑★ chosen
  IntO : Interior W₀ Θo Θo Wb
  IntO = record
    { int-left   = int-o
    ; int-right  = int-o
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there here) _ () _ }
    ; join-fresh = λ a b _ → pairs a b
    ; mark-left  = λ { (_ , here) () _ ; (_ , there here) () _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there here) () _ }
    ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there here) _ → tt }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there here) _ → tt }
    }

  -- the right's (−Y,−X): both continuing left names become HIDDEN,
  -- marks kept
  IntH : Interior Wb [] Θh Wh
  IntH = record
    { int-left   = interior changes[]
    ; int-right  = int-h
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) refl here → tt , here
                     ; (_ , there here) refl (there here) → tt , there here }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ _ ()
    ; fresh-right = λ { (_ , ()) _ }
    }

  -- the right's (+X,+Y): both hidden names REJOIN, marks kept
  IntJ : Interior Wh [] Θj Wb
  IntJ = record
    { int-left   = interior changes[]
    ; int-right  = int-j
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there here) _ () }
    ; join-fresh = λ a b _ → pairs a b
    ; mark-left  = λ { (_ , here) refl here → tt , here
                     ; (_ , there here) refl (there here) → tt , there here }
    ; mark-right = λ { (_ , here) () _ ; (_ , there here) () _ }
    ; fresh-left  = λ _ ()
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there here) _ → tt }
    }

  -- the matched (−X,−Y) of the sealed literal: no names inside
  IntS : Interior Wb ΘS ΘS W₀
  IntS = record
    { int-left   = int-S
    ; int-right  = int-S
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , ()) _ }
    }

  conv-o : Δ₀ ⊢ᶜ Θo ⇒ Δ₂
  conv-o = conversion (conv-bind (_ , there here)
    (conv-bind (_ , here) conv[] fresh[] ins-here)
    (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

  conv-S : Δ₂ ⊢ᶜ ΘS ⇒ Δ₂
  conv-S = conversion (conv-unbind (_ , here)
    (conv-unbind (_ , there here) conv[]))

  ConvO : ConversionInterior W₀ Θo Θo Wb
  ConvO = record
    { conv-left       = conv-o
    ; conv-right      = conv-o
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ a b _ → pairs a b
    ; conv-mark-left  = λ { _ () _ }
    ; conv-mark-right = λ { _ () _ }
    }

  named₂ : ∀ {X α} → Δ₂ ∋ᵗ X := α → names Δ₂ ∌ʳ α → ⊥
  named₂ here         (fresh∷ n _)          = n refl
  named₂ (there here) (fresh∷ _ (fresh∷ n _)) = n refl

  ConvS : ConversionInterior Wb ΘS ΘS Wb
  ConvS = record
    { conv-left       = conv-S
    ; conv-right      = conv-S
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here (there here) here (there here) → (λ j → j) , (λ j → j)
        ; (there here) here (there here) here → (λ j → j) , (λ j → j)
        ; (there here) (there here) (there here) (there here) →
            (λ j → j) , (λ j → j)
        ; (there (there ())) _ _ _
        ; _ (there (there ())) _ _
        ; _ _ (there (there ())) _
        ; _ _ _ (there (there ()))
        }
    ; conv-join-fresh = λ
        { a _ (inj₁ f) → ⊥-elim (named₂ a f)
        ; _ b (inj₂ f) → ⊥-elim (named₂ b f)
        }
    ; conv-mark-left  = λ { here here m → m
                          ; (there here) (there here) m → m
                          ; here (there (there ())) _
                          ; (there (there ())) _ _ }
    ; conv-mark-right = λ { here here m → m
                          ; (there here) (there here) m → m
                          ; here (there (there ())) _
                          ; (there (there ())) _ _ }
    }

  bS : BdyTy Δ₂ ΘS Δ₀ `ℕ (tail (seal 1)) (` 1)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₂} {M = S2}))))

  bJ2 : BdyTy Δ₀ Θj Δ₂ ★ id★ᶜ ★
  bJ2 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = J2}))))

  bRH : BdyTy Δ₂ Θh Δ₀ ★ id★ᶜ ★
  bRH = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₂} {M = RH}))))

  bL7 : BdyTy Δ₀ Θo Δ₂ (` 1) (unseal 1) `ℕ
  bL7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = L7}))))

  bR12 : BdyTy Δ₀ Θo Δ₂ (` 1) (unseal 1) `ℕ
  bR12 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = R12}))))

  tag-ty : CastTy Δ₂ (flipᵐ ★∼X ∷ X∼★ ∷ []) ((` 1) !) (` 1) ★
  tag-ty = cast-ty (⊢tag-var (_ , there here) (there here) tag-dyn) refl

  chk-ty : CastTy Δ₂ (★∼X ∷ ★∼X ∷ []) ((` 1) ？ ℓ) ★ (` 1)
  chk-ty = cast-ty (⊢check-var (_ , there here) (there here) check-dyn) refl

  X★ : μʷ Wb ∋ˡ 1 := X⊑★
  X★ = there here

  S2⊑S2 : Wb ∣ [] ⊢ S2 ⊑ S2 ∶ X⊑X
  S2⊑S2 = ⟪⟫⊑⟪⟫ IntS W₀-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (Wb , ConvS , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- inside the rejoin: the right's X! at the rejoined X, X ⊑ ★
  inner : Wb ∣ [] ⊢ S2 ⊑ S2 ⟨ flipᵐ ★∼X ∷ X∼★ ∷ [] ∣ (` 1) ! ⟩ ∶ X⊑★ X★
  inner = ⊑cast S2⊑S2 tag-ty (X⊑★ X★)

  c18b-b7 : W₀ ∣ [] ⊢ L7 ⊑ R12 ∶ ι⊑ι base-ℕ
  c18b-b7 =
    ⟪⟫⊑⟪⟫ IntO Wb-wf
      (⊑cast {p = X⊑★ X★}
        (⊑⟪⟫ IntH push-none Wh-wf
          (⊑⟪⟫ IntJ push-none Wb-wf inner bJ2 (X⊑★ X★))
          bRH (X⊑★ X★))
        chk-ty X⊑X)
      bL7 bR12 (Wb , ConvO , conv-unseal⊑unseal refl) (ι⊑ι base-ℕ)

------------------------------------------------------------------------
-- 21. Reduction closure of the status data at a Merge (InteriorMerge's
-- core): two successive status steps of a continuing name compose to
-- one, with the composed mark, whenever the final world is well formed
-- (a hidden name is X⊑★, Joint `hidden-r`).  The one excluded path,
-- plain → joined → hidden, has the mark X⊑X at a hidden name, which no
-- well-formed world has.
------------------------------------------------------------------------

st-compose : ∀ s₁ s₂ s₃ m → StOK s₁ s₂ → StOK s₂ s₃
  → (s₃ ≡ hidden → markStep s₂ s₃ (markStep s₁ s₂ m) ≡ X⊑★)
  → StOK s₁ s₃ × (markStep s₂ s₃ (markStep s₁ s₂ m) ≡ markStep s₁ s₃ m)
st-compose joined joined joined m _ _ _ = tt , refl
st-compose joined joined hidden m _ _ _ = tt , refl
st-compose joined hidden joined m _ _ _ = tt , refl
st-compose joined hidden hidden m _ _ _ = tt , refl
st-compose hidden joined joined m _ _ _ = tt , refl
st-compose hidden joined hidden m _ _ _ = tt , refl
st-compose hidden hidden joined m _ _ _ = tt , refl
st-compose hidden hidden hidden m _ _ _ = tt , refl
st-compose plain  plain  plain  m _ _ _ = tt , refl
st-compose plain  plain  joined m _ _ _ = tt , refl
st-compose plain  joined joined m _ _ _ = tt , refl
st-compose plain  joined hidden m _ _ wf with wf refl
... | ()
st-compose joined plain  _      m () _ _
st-compose hidden plain  _      m () _ _
st-compose plain  hidden _      m () _ _
st-compose _      joined plain  m _ () _
st-compose _      hidden plain  m _ () _
st-compose _      plain  hidden m _ () _

------------------------------------------------------------------------
-- 22. Reduction closure on P4's run (SimBack evidence): the left at B4
-- (`[+X^α] S ⟨+X⟩`) is related to EVERY right state its Merge, IdDyn,
-- Merge, TagUntag steps produce (right states 7-10).  The merged
-- `[−X, +X]` is an unbind then a bind of X in ONE boundary: `toExt`
-- makes X continuing on both sides, so X stays joined at X⊑★
-- (joined → joined); after IdDyn the tag `X!` is outside, at the same
-- joined X⊑★.  (State 11, the final Merge, needs the left's own Merge:
-- B5.)
------------------------------------------------------------------------

module P4c where
  open import examples.TypeCheck using (tc; tf)
  open P4 using (nth; Ls; Rs; S; unb₀; id★ᶜ; tagX; chkX; tagˣ-ty; chkᵍ-ty;
                 bUnsealL; W₄; W₄²; W₄-wf; W₄²-wf; v₀; S⊑S; bS; bdy-wf;
                 Ξ₄; ϱ₄)
  open TIE using (ΔL; ΔLᵢ)
  open Rebase using (Θ⁻⁺; Θ⁻⁺-int; Wc-bind²; Wc-bind²-conv; unbind₀-int;
                     unbind₀-conv)

  Θ³ : Boundary
  Θ³ = unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ []

  Bm7 Bi8 S3 R7 R8 R9 R10 : Term
  Bm7 = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , id★ᶜ ⟫
  Bi8 = S ⟪ Θ⁻⁺ , ⌞ id (` 0) ⌟ ⟫
  S3  = $ 5 ⟪ Θ³ , tail (seal 0) ⟫
  R7  = (Bm7 ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R8  = ((Bi8 ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R9  = ((S3 ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R10 = S3 ⟪ Θ₀ , unseal 0 ⟫

  R7-state : nth Rs 7 ≡ R7
  R7-state = refl

  R8-state : nth Rs 8 ≡ R8
  R8-state = refl

  R9-state : nth Rs 9 ≡ R9
  R9-state = refl

  R10-state : nth Rs 10 ≡ R10
  R10-state = refl

  -- the right's [−X, +X] alone: X continuing on both sides, joined
  IntRR : Interior W₄² [] Θ⁻⁺ W₄²
  IntRR = record
    { int-left   = interior changes[]
    ; int-right  = Θ⁻⁺-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ j → j) , (λ j → j)
        ; (_ , here) (_ , there ()) _ _
        ; (_ , there ()) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) refl m → tt , m ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) refl m → tt , m ; (_ , there ()) _ _ }
    ; fresh-left  = λ _ ()
    ; fresh-right = λ { (_ , here) () ; (_ , there ()) _ }
    }

  bBm7 : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ ★ id★ᶜ ★
  bBm7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Bm7}))))

  bBi8 : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0) ⌞ id (` 0) ⌟ (` 0)
  bBi8 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Bi8}))))

  bS3 : BdyTy ΔLᵢ Θ³ ΔL `ℕ (tail (seal 0)) (` 0)
  bS3 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S3}))))

  bR7 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R7}))))

  bR8 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR8 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R8}))))

  bR9 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR9 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R9}))))

  bR10 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR10 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R10}))))

  -- the left's sealed 5 against the right's merged [−X, +X, −X] 5 ⟨−X⟩
  Int3 : Interior W₄² unb₀ Θ³ W₄
  Int3 = record
    { int-left   = unbind₀-int
    ; int-right  = bw-interior (proj₂ (bdy-wf bS3))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    ; mark-left  = λ { (_ , ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ { (_ , ()) _ }
    ; fresh-right = λ { (_ , ()) _ }
    }

  Conv3 : ConversionInterior W₄² unb₀ Θ³ W₄²
  Conv3 = record
    { conv-left       = unbind₀-conv
    ; conv-right      = bw-conversion (proj₂ (bdy-wf bS3))
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
    ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    ; conv-mark-right = λ { here here m → m ; here (there ()) _
                          ; (there ()) _ _ }
    }

  S⊑S3 : W₄² ∣ [] ⊢ S ⊑ S3 ∶ X⊑X
  S⊑S3 = ⟪⟫⊑⟪⟫ Int3 W₄-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS3
    (W₄² , Conv3 , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  outer : ∀ {M′} → (b′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ)
    → BdyConversionImp W₄ bUnsealL b′
    → W₄² ∣ [] ⊢ S ⊑ M′ ∶ X⊑X
    → W₄ ∣ [] ⊢ nth Ls 4 ⊑ M′ ⟪ Θ₀ , unseal 0 ⟫ ∶ ι⊑ι base-ℕ
  outer b′ bc d =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf d bUnsealL b′ bc (ι⊑ι base-ℕ)


  p4-R7 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R7 ∶ ι⊑ι base-ℕ
  p4-R7 = outer bR7
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast {p = X⊑★ here}
      (⊑⟪⟫ IntRR push-none W₄²-wf (⊑cast S⊑S tagˣ-ty (X⊑★ here)) bBm7
        (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R8 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R8 ∶ ι⊑ι base-ℕ
  p4-R8 = outer bR8
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast {p = X⊑★ here}
      (⊑cast {p = X⊑X} (⊑⟪⟫ IntRR push-none W₄²-wf S⊑S bBi8 X⊑X)
        tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R9 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R9 ∶ ι⊑ι base-ℕ
  p4-R9 = outer bR9
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast {p = X⊑★ here} (⊑cast {p = X⊑X} S⊑S3 tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R10 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R10 ∶ ι⊑ι base-ℕ
  p4-R10 = outer bR10
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl) S⊑S3

------------------------------------------------------------------------
-- 23. InteriorMerge (STATEMENTS-CORE M6) is FALSE AS STATED under the
-- repair: matched `+X ∥ +X` (X joined) followed by the right's `−X`
-- (X hidden) composes to `+X ∥ (+X, −X)`, where the left X is FRESH,
-- and a fresh name is never hidden (`fresh-left`).  The merged world
-- must have X plain: the statement needs a second interior world and
-- a status-lowering (hidden → plain) transport.
------------------------------------------------------------------------

module MergeCex where
  open C1 using (ΔR; ΔRᵢ; unb₀)

  Wαα : World ΔR ΔR
  Wαα = world [] []↪ []↪ ((0 , 0) ∷ []) [] []

  Wj : World ΔRᵢ ΔRᵢ
  Wj = world (X⊑★ ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) [] []

  Wh : World ΔRᵢ ΔR
  Wh = world (X⊑★ ∷ []) (keep []↪) (hide []↪) ((0 , 0) ∷ []) [] []

  I₁ : Interior Wαα Θ₀ Θ₀ Wj
  I₁ = record
    { int-left   = TIE.int₀
    ; int-right  = TIE.int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
    ; fresh-left  = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    ; fresh-right = λ { (_ , here) _ → tt ; (_ , there ()) _ }
    }

  I₂ : Interior Wj [] unb₀ Wh
  I₂ = record
    { int-left   = interior changes[]
    ; int-right  = Rebase.unbind₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    ; mark-left  = λ { (_ , here) refl here → tt , here ; (_ , there ()) _ _ }
    ; mark-right = λ { (_ , ()) _ _ }
    ; fresh-left  = λ _ ()
    ; fresh-right = λ { (_ , ()) _ }
    }

  merge-fails : ¬ Interior Wαα (Θ₀ ++ []) (unb₀ ++ Θ₀) Wh
  merge-fails I = fresh-left I (_ , here) refl

  InteriorMerge-cex :
    Interior Wαα Θ₀ Θ₀ Wj × Interior Wj [] unb₀ Wh
    × ¬ Interior Wαα ([] ++ Θ₀) (unb₀ ++ Θ₀) Wh
  InteriorMerge-cex = I₁ , I₂ , merge-fails

------------------------------------------------------------------------
-- 24. C4 also holds in HEAD's relation (TermImprecision, ce2da4b6+),
-- with HEAD's own example pieces (int-ro₃, Wi₃-wf, ∀id⊑★)
------------------------------------------------------------------------

module C4InHEAD where
  import ImprecisionWorld as HW
  import TermImprecision as HT
  import examples.TermImprecisionExamples as HE
  import examples.TermImprecisionRebaseExamples as HR
  open C4 using (bodyR; R₂; bRBp; tagX-ty; instL-ty; id★↦-ty; ℕ?ᴸ-ty;
                 ℕ?ᴿ-ty)
  open C1 using (L₀)

  pop-body : record (HE.W₃ HW.⊕ʳ X⊑★ ^ 0) { πʷ = 0 ∷ [] } HT.∣ []
    ⊢ Λ HE.idX ⊑ bodyR
    ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ★ ⟩ ⇒⊑⇒ X⊑X (X⊑★ here)
  pop-body =
    HT.Λ⊑ (HT.claim-pop (HW.open-⊕ r-here)) nv-⇒ (∈-⇒ˡ ∈-var) HW.liftᴸ-[]
      (V-simple S-ƛ)
      (HT.ƛ⊑ƛ {pA = X⊑X} tf tf (HT.⊑cast (HT.x⊑x HW.Zʷ) tagX-ty (X⊑★ here)))
      (⇒⊑⇒ X⊑X (X⊑★ here))
    where open import examples.TypeCheck using (tf)

  C4-HEAD : HE.W₃ HT.∣ [] ⊢ L₀ ⊑ R₂ ∶ ι⊑ι base-ℕ
  C4-HEAD =
    HT.cast⊑cast
      (HT.·⊑·
        (HT.cast⊑cast
          (HT.⊑⟪⟫ HE.int-ro₃ (push ca-[] (refl ∷ []) (inj₂ HE.vΛidX)) HE.Wi₃-wf
            pop-body bRBp (HR.∀id⊑★ HE.W₃))
          instL-ty id★↦-ty (⇒⊑⇒ ★⊑★ ★⊑★))
        (HT.cast⊑cast (HT.κ⊑κ lit-$ (ι⊑ι base-ℕ))
          (cast-ty (⊢tag g-ℕ) refl) (cast-ty (⊢tag g-ℕ) refl) ★⊑★))
      ℕ?ᴸ-ty ℕ?ᴿ-ty (ι⊑ι base-ℕ)
