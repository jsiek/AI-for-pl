module strong.CtxMorph where

-- Strong System F — the BOUNDARY'S CONTEXT MORPHISM and its well-formedness.
--
-- A boundary is  M ⟪ Θ , c ⟫  (strong.Terms) with ONE frame change.  THE
-- MORPHISM IS A PAIR (Jeremy, 2026-09-06), because its two halves are not
-- the same kind of thing:
--
--   Θ = morph B S
--     B : List Ty     the BINDS — a PARALLEL block of binders.  Each entry
--                is one fresh interior slot's representation, a type over
--                the exterior read OUTSIDE all of them (and outside every
--                lock the boundary itself performs); binds never see one
--                another.
--     S : List Change the SCOPE CHANGES — a SEQUENTIAL list of name-only
--                entries, applied head-LAST:
--                lock X   MASKS exterior slot X: the interior may not NAME
--                        it.  The entry is RETAINED on the type context —
--                        nothing is dropped and nothing is re-spelled, so
--                        there is no demotion.
--                unlock X UNMASKS exterior slot X; it claims nothing but
--                        that X IS masked where it acts (no vacuous
--                        unlocks).
--
-- The old interleaved `List MorphEnt` said neither thing: it made the
-- binds look sequential (a bind's rep was read past its own TAIL only) and
-- it let a lock sit between two binds, where it had no meaning.  The pair
-- says exactly what is true, and the list arithmetic that used to project
-- the two halves apart (`repsOf`, `scope-++` at a bind, …) is gone.
--
-- This module defines the morphism, the type contexts it induces
-- (`scope`, `unlockedScope`, `interior`, `convCtx`), their refinement
-- transports, the well-formedness judgement `Δ ⊢ᵐ Θ`, and the two
-- derived morphisms the reduction rules use: the DUAL of a crossed
-- boundary (`dual`, for Peel) and the SCOPE MOVE (`rewind`, `_⋉_`, for
-- IdPush and CancelR).  Terms and typing are in strong.Terms, which
-- re-exports this module.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length; drop)
open import Data.List.Properties using (≡-dec)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx

private
  variable
    Δ Δ′ : Ctxᵗ
    A B : Ty
    X Y : ℕ

------------------------------------------------------------------------
-- 1.  The boundary context morphism
------------------------------------------------------------------------

-- A SCOPE CHANGE carries a name only — an EXTERIOR index, unshifted by the
-- morphism's own binds.  That is the whole point of the redesign: no scope
-- change carries a representation.
data Change : Set where
  lock   : ℕ → Change        -- mask   exterior slot X
  unlock : ℕ → Change        -- unmask exterior slot X

record CtxMorph : Set where
  constructor morph
  field
    binds   : List Ty        -- PARALLEL: reps read outside all of them
    changes : List Change    -- SEQUENTIAL: applied head-LAST
open CtxMorph public

-- `numBinds` is the boundary's FRAME EXTENSION: the number of binders it
-- adds.  It is the only surviving list arithmetic; cmax/dropN have no
-- analogue, because conceal masks in place.
numBinds : CtxMorph → ℕ
numBinds Θ = length (binds Θ)

-- The masks (`lock`) and unmasks (`unlock`), applied in place, head-LAST.
applyChanges : List Change → Ctxᵗ → Ctxᵗ
applyChanges []             Δ = Δ
applyChanges (unlock X ∷ S) Δ = unmask X (applyChanges S Δ)
applyChanges (lock X ∷ S)   Δ = mask X (applyChanges S Δ)

-- The CONVERSION CONTEXT's slots: like `applyChanges` but WITHOUT the
-- conceal masks, so a `seal X` can resolve X at its binder.  This is
-- binder-syntactic lookup: the licence is read on the type context that
-- encloses the boundary, never inside it.
applyUnlocks : List Change → Ctxᵗ → Ctxᵗ
applyUnlocks []             Δ = Δ
applyUnlocks (unlock X ∷ S) Δ = unmask X (applyUnlocks S Δ)
applyUnlocks (lock X ∷ S)   Δ = applyUnlocks S Δ

-- THE TWO INDUCED CONTEXTS, at the morphism.
scope : CtxMorph → Ctxᵗ → Ctxᵗ
scope Θ Δ = applyChanges (changes Θ) Δ

unlockedScope : CtxMorph → Ctxᵗ → Ctxᵗ
unlockedScope Θ Δ = applyUnlocks (changes Θ) Δ

-- What replaces `intOf`: the same slot list, the interior mask, and the
-- binder extension.  Nothing is dropped and no rep is recomputed.
interior : CtxMorph → Ctxᵗ → Ctxᵗ
interior Θ Δ = pushBinds (binds Θ) (scope Θ Δ)

convCtx : CtxMorph → Ctxᵗ → Ctxᵗ
convCtx Θ Δ = pushBinds (binds Θ) (unlockedScope Θ Δ)

-- The interior type context is the conversion context with the changes'
-- locks on, so anything well formed inside is well formed on the
-- conversion context.
applyChanges⊑applyUnlocks : (S : List Change) (Δ : Ctxᵗ)
  → applyChanges S Δ ⊑ applyUnlocks S Δ
applyChanges⊑applyUnlocks []             Δ = ⊑-refl Δ
applyChanges⊑applyUnlocks (unlock X ∷ S) Δ =
  ⊑-updateAt unmaskEnt unmaskEnt-comm unmaskEnt-mono
    (applyChanges⊑applyUnlocks S Δ)
applyChanges⊑applyUnlocks (lock X ∷ S)   Δ =
  mask-⊑ X (applyChanges⊑applyUnlocks S Δ)

scope⊑unlockedScope : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scope Θ Δ ⊑ unlockedScope Θ Δ
scope⊑unlockedScope Θ Δ = applyChanges⊑applyUnlocks (changes Θ) Δ

interior⊑convCtx : (Θ : CtxMorph) (Δ : Ctxᵗ) → interior Θ Δ ⊑ convCtx Θ Δ
interior⊑convCtx Θ Δ =
  ⊑-pushBinds (binds Θ) (scope⊑unlockedScope Θ Δ)

-- The CONVERSION CONTEXT only ever ADDS nameability to the plain
-- exterior: `applyUnlocks` skips the locks, and an `unlock` merely
-- restores.  (`applyChanges` would not do — masking is what a lock is
-- for.)
Δ⊑applyUnlocks : (S : List Change) (Δ : Ctxᵗ) → Δ ⊑ applyUnlocks S Δ
Δ⊑applyUnlocks []             Δ = ⊑-refl Δ
Δ⊑applyUnlocks (unlock X ∷ S) Δ =
  ⊑-trans (Δ⊑applyUnlocks S Δ) (unmask-⊑ X (applyUnlocks S Δ))
Δ⊑applyUnlocks (lock X ∷ S)   Δ = Δ⊑applyUnlocks S Δ

Δ⊑unlockedScope : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊑ unlockedScope Θ Δ
Δ⊑unlockedScope Θ Δ = Δ⊑applyUnlocks (changes Θ) Δ

⊑-applyChanges : (S : List Change) → Δ ⊑ Δ′
  → applyChanges S Δ ⊑ applyChanges S Δ′
⊑-applyChanges []             ls = ls
⊑-applyChanges (unlock X ∷ S) ls =
  ⊑-updateAt unmaskEnt unmaskEnt-comm unmaskEnt-mono (⊑-applyChanges S ls)
⊑-applyChanges (lock X ∷ S)   ls =
  ⊑-updateAt maskEnt maskEnt-comm maskEnt-mono (⊑-applyChanges S ls)

⊑-applyUnlocks : (S : List Change) → Δ ⊑ Δ′
  → applyUnlocks S Δ ⊑ applyUnlocks S Δ′
⊑-applyUnlocks []             ls = ls
⊑-applyUnlocks (unlock X ∷ S) ls =
  ⊑-updateAt unmaskEnt unmaskEnt-comm unmaskEnt-mono (⊑-applyUnlocks S ls)
⊑-applyUnlocks (lock X ∷ S)   ls = ⊑-applyUnlocks S ls

⊑-scope : (Θ : CtxMorph) → Δ ⊑ Δ′ → scope Θ Δ ⊑ scope Θ Δ′
⊑-scope Θ ls = ⊑-applyChanges (changes Θ) ls

⊑-unlockedScope : (Θ : CtxMorph) → Δ ⊑ Δ′
  → unlockedScope Θ Δ ⊑ unlockedScope Θ Δ′
⊑-unlockedScope Θ ls = ⊑-applyUnlocks (changes Θ) ls

⊑-interior : (Θ : CtxMorph) → Δ ⊑ Δ′ → interior Θ Δ ⊑ interior Θ Δ′
⊑-interior Θ ls = ⊑-pushBinds (binds Θ) (⊑-scope Θ ls)

-- … and the same three transports for the LOCK-PRESERVING refinement,
-- the one a TERM travels along.
⊑ᵃ-applyChanges : (S : List Change) → Δ ⊑ᵃ Δ′
  → applyChanges S Δ ⊑ᵃ applyChanges S Δ′
⊑ᵃ-applyChanges []             ls = ls
⊑ᵃ-applyChanges (unlock X ∷ S) ls =
  ⊑ᵃ-updateAt unmaskEnt unmaskEnt-monoᵃ (⊑ᵃ-applyChanges S ls)
⊑ᵃ-applyChanges (lock X ∷ S)   ls =
  ⊑ᵃ-updateAt maskEnt maskEnt-monoᵃ (⊑ᵃ-applyChanges S ls)

⊑ᵃ-scope : (Θ : CtxMorph) → Δ ⊑ᵃ Δ′ → scope Θ Δ ⊑ᵃ scope Θ Δ′
⊑ᵃ-scope Θ ls = ⊑ᵃ-applyChanges (changes Θ) ls

⊑ᵃ-interior : (Θ : CtxMorph) → Δ ⊑ᵃ Δ′ → interior Θ Δ ⊑ᵃ interior Θ Δ′
⊑ᵃ-interior Θ ls = ⊑ᵃ-pushBinds (binds Θ) (⊑ᵃ-scope Θ ls)

⊑-convCtx : (Θ : CtxMorph) → Δ ⊑ Δ′ → convCtx Θ Δ ⊑ convCtx Θ Δ′
⊑-convCtx Θ ls = ⊑-pushBinds (binds Θ) (⊑-unlockedScope Θ ls)

------------------------------------------------------------------------
-- 2.  Boundary well-formedness
------------------------------------------------------------------------

-- THE JUDGEMENT IS A PAIR, BECAUSE THE MORPHISM IS.
--
-- THE CHANGES half is SEQUENTIAL — every premise is read on the frame the
-- entry acts on, in the order `applyChanges` applies the list (head-LAST).
-- For the tail S′ of the entry:
--
--   lock X    X is NAMEABLE in `applyChanges S′ Δ`  (you may only mask
--             what is visible; `Locked` is one mask deep BY
--             CONSTRUCTION now — strong.Ctx §1 — but the premise still
--             earns its keep: it is what makes `unmask ∘ mask` the
--             identity at the slot, `unmask-mask`, strong.Ctx §6b)
--   unlock X  X is LOCKED   in `applyChanges S′ Δ`  (`∋lk`: masked over a
--             nameable entry).  A VACUOUS UNLOCK — `↥X` at a slot the
--             frame leaves visible — IS REFUSED; it is the premise the
--             judgement used to drop, and the one the dual's restoring
--             `lock` needs (`mask-unmask`, strong.Ctx).
--
-- THE BINDS half is PARALLEL: every rep is a type over
-- `applyUnlocks S Δ` — the WHOLE change list's unmasks applied and ALL of
-- its locks lifted.  A rep is never blocked by the frame's own locks (it
-- is read where the CONVERSION is read, outside the masking the boundary
-- itself performs), and it may name whatever the frame unlocks, which is
-- what makes the scope move (`_⋉_`, §4 below) well formed.  Binds do not
-- see one another: the block is one simultaneous event.
--
-- Note the distinction the mask discipline forces: `unlock X`/`lock X`
-- NAME a masked index — that is a CHANGE, not a type — while `Δ ⊢ᵗ ` X`
-- at a masked slot is refused.  Tightness is about USE in a type, not
-- about mentioning the index in the context morphism.

-- The BINDS half, as a list judgement: every rep well formed, all on the
-- SAME type context (that is what "parallel" means).
infix 4 _⊢ʳ_
data _⊢ʳ_ : Ctxᵗ → List Ty → Set where
  rw[] : Δ ⊢ʳ []
  rw-b : ∀ {Bs} → Δ ⊢ᵗ A → Δ ⊢ʳ Bs → Δ ⊢ʳ (A ∷ Bs)

-- The CHANGES half, as a sequential judgement.
infix 4 _⊢ˢ_
data _⊢ˢ_ : Ctxᵗ → List Change → Set where
  sw[] : Δ ⊢ˢ []
  sw-l : ∀ {S} → applyChanges S Δ ∋tv X → Δ ⊢ˢ S → Δ ⊢ˢ (lock X ∷ S)
  sw-u : ∀ {S} → applyChanges S Δ ∋lk X → Δ ⊢ˢ S → Δ ⊢ˢ (unlock X ∷ S)

-- `Δ ⊢ᵐ Θ` — the context morphism Θ is WELL FORMED over Δ.  An infix
-- judgement in the family of `Δ ⊢ᵗ A` (strong.Ctx) and `Δ ⊢ c ∶ A ⇝ B`
-- (strong.Conversion).
infix 4 _⊢ᵐ_
record _⊢ᵐ_ (Δ : Ctxᵗ) (Θ : CtxMorph) : Set where
  constructor mw
  field
    mw-reps    : unlockedScope Θ Δ ⊢ʳ binds Θ
    mw-changes : Δ ⊢ˢ changes Θ
open _⊢ᵐ_ public

⊢ʳ-⊑ : ∀ {Bs} → Δ ⊑ Δ′ → Δ ⊢ʳ Bs → Δ′ ⊢ʳ Bs
⊢ʳ-⊑ ls rw[]        = rw[]
⊢ʳ-⊑ ls (rw-b w ws) = rw-b (⊑-wf ls w) (⊢ʳ-⊑ ls ws)

-- THE TERM TRANSPORT IS `_⊑ᵃ_`, NOT `_⊑_`.  An `unlock X` CLAIMS that X
-- is locked, and `le-mu` — the clause that re-exposes a concealed slot —
-- destroys the claim; `_⊑ᵃ_` (strong.Ctx §4b) is `_⊑_` without it.
⊢ˢ-⊑ᵃ : ∀ {S} → Δ ⊑ᵃ Δ′ → Δ ⊢ˢ S → Δ′ ⊢ˢ S
⊢ˢ-⊑ᵃ ls sw[] = sw[]
⊢ˢ-⊑ᵃ {S = lock X ∷ S}   ls (sw-l tv b) =
  sw-l (⊑-tv (⊑-applyChanges S (⊑ᵃ→⊑ ls)) tv) (⊢ˢ-⊑ᵃ ls b)
⊢ˢ-⊑ᵃ {S = unlock X ∷ S} ls (sw-u lk b) =
  sw-u (⊑ᵃ-lk (⊑ᵃ-applyChanges S ls) lk) (⊢ˢ-⊑ᵃ ls b)

⊢ᵐ-⊑ᵃ : ∀ {Θ} → Δ ⊑ᵃ Δ′ → Δ ⊢ᵐ Θ → Δ′ ⊢ᵐ Θ
⊢ᵐ-⊑ᵃ {Θ = Θ} ls (mw ws bs) =
  mw (⊢ʳ-⊑ (⊑-unlockedScope Θ (⊑ᵃ→⊑ ls)) ws) (⊢ˢ-⊑ᵃ ls bs)

------------------------------------------------------------------------
-- 3.  The dual of a crossed boundary
------------------------------------------------------------------------

-- THE DUAL, in full.  It mints ONLY scope changes — it has NO BINDS at
-- all: a `lock` for each of the crossed boundary's binders (the argument
-- may not see them) and an `unlock` for each of its conceals (the
-- argument came from outside, where they were nameable).  Nothing is
-- copied, nothing is guarded, nothing is demoted; the old design's `entᴳ`
-- has no analogue.
hideBinds : ℕ → List Change
hideBinds zero    = []
hideBinds (suc k) = lock k ∷ hideBinds k

-- THE DUAL IS AN INVERSE, AND AN INVERSE RUNS BACKWARDS (2026-09-06).
--
-- The mini-core DROPPED the `unlock` case, on the reading that an
-- `unlock` "claims nothing".  It claims plenty: it UNMASKS, and a dual
-- that does not re-mask hands the crossing argument a frame STRICTLY MORE
-- NAMEABLE than the exterior — `Peel` GAINS SCOPE, machine-checked in
-- proof/DualTightness.agda.  So `unlock X ↦ lock (n + X)`, and the
-- restoring `lock` is sound exactly because `sw-u` refuses a VACUOUS
-- unlock: `mask ∘ unmask` is the identity at a LOCKED slot
-- (`mask-unmask`, strong.Ctx) and nowhere else.
--
-- AND THE LIST IS REVERSED.  `applyChanges` applies its list HEAD-LAST, so
-- undoing it runs the entries BACK TO FRONT; a same-order dual is not an
-- inverse at a frame that toggles one slot twice (`S = ↥X ∷ ↧X ∷ []`,
-- which the judgement admits).  With both repairs the frame identity is
-- EXACT (proof/PeelDual, `interior-dual`): the crossing argument's frame
-- is the exterior itself, one bind prefix in, and it crosses by
-- `⊢rename` alone — no `⊢retag`, no `le-mu`.
dualScope : ℕ → List Change → List Change
dualScope n []             = []
dualScope n (unlock X ∷ S) = dualScope n S ++ (lock   (n + X) ∷ [])
dualScope n (lock X ∷ S)   = dualScope n S ++ (unlock (n + X) ∷ [])

dual : CtxMorph → CtxMorph
dual Θ =
  morph [] (hideBinds (numBinds Θ) ++ dualScope (numBinds Θ) (changes Θ))

-- (The old Cancel residue `repsOf→bind` — a frame that rebinds Θ₂'s
-- binders and nothing else — is GONE with the rule that wrote it: the
-- repaired CancelR keeps both frames and mints none.)

------------------------------------------------------------------------
-- 4.  THE SCOPE MOVE — the outer frame's locks go INTO the inner one
------------------------------------------------------------------------

-- JEREMY'S MOVE (2026-09-06).  CancelR and IdPush both SWAP the two
-- conversions: the inner boundary stops presenting the abstract name
-- `` ` Y `` and starts presenting Y's REP.  A rep is read on the outer
-- boundary's CONVERSION CONTEXT (its locks lifted), so it is nameable
-- there and NOT, in general, inside the outer boundary's own locks — that
-- was the wall (the old proof/PreserveObstruct §4).
--
-- The repair is not a side condition but a FRAME MOVE: the outer frame's
-- whole change list travels into the inner frame's TAIL, where
-- `applyChanges` applies it FIRST — exactly where it applied before — and
-- what stays outside is the frame with its own changes REWOUND
-- (`rewind Θ₂`), whose net effect on the exterior is its BIND BLOCK
-- alone.  The rep is then presented OUTSIDE the locks, where it is
-- nameable, and the locks still stand between the value and the world.
--
-- WHY THE UNLOCKS TRAVEL TOO.  `applyChanges` applies its list HEAD-LAST,
-- so moving only the LOCKS past a same-slot `unlock` reorders a
-- mask/unmask pair, and the value's frame is then not refined but
-- CORRUPTED — a slot it may name is masked in the contractum and was not
-- in the redex (`¬frame-locksOnly`, proof/MoveScope §4b, at the ⊢ᵐ-legal
-- `Θ₂ = morph [] (unlock 0 ∷ lock 0 ∷ [])`).  Moving the WHOLE list keeps
-- the order, and then the value's frame is preserved ON THE NOSE: the two
-- frame lemmas are EQUALITIES, no `⊢retag` appears in either case, and
-- there is no premise about Θ₂'s shape for Progress to supply.

-- The outer frame's changes, lifted past its own binders.
shiftScope : ℕ → List Change → List Change
shiftScope n []             = []
shiftScope n (unlock X ∷ S) = unlock (n + X) ∷ shiftScope n S
shiftScope n (lock X ∷ S)   = lock (n + X) ∷ shiftScope n S

-- WHAT IS LEFT OF THE OUTER FRAME: the frame with its OWN CHANGES
-- REWOUND.
--
-- `rewind Θ` is Θ with its inverse change list run on top, so its net
-- effect on the exterior is the BIND BLOCK ALONE:
--
--     scope    (rewind Θ) Δ ≡ Δ                     (given Δ ⊢ᵐ Θ)
--     interior (rewind Θ) Δ ≡ pushBinds (binds Θ) Δ
--
-- which is what makes the moved changes reproduce the redex's frame ON
-- THE NOSE (`interior-⋉-rewind`, proof/MoveScope) — no `⊢retag` and no
-- `le-mu` anywhere in the two cases.
--
-- IT IS NOT `morph (binds Θ) []`, AND THAT IS THE POINT.  Simply DELETING
-- Θ's changes has the same effect on the type context but loses the
-- frame's own `⊢ᵐ`: Θ's bind reps are read on `unlockedScope Θ Δ` and a
-- rep naming a slot Θ UNLOCKED is not well formed on the plain Δ.
-- Keeping the entries and rewinding them keeps every rep exactly where it
-- was read.  (`unlocksOf` alone — replaying only the unmasks the reps
-- need — loses both halves: `applyChanges` is then NOT the identity, and
-- the surviving unlock is VACUOUS wherever its own licensing lock was
-- dropped.  Both refuted in proof/RewindNorm §5.)
--
-- REWINDING IS IDEMPOTENT, AND IT HAD BETTER BE (2026-09-08).  The
-- replay `dualScope 0 S ++ S` DOUBLES the list, and the outer frame of a
-- scope move is rewound again on the next pass, so over a run the change
-- lists grow as `S , S ++ S , (S ++ S) ++ (S ++ S) , …` — the
-- `↥X , ↓X , ↥X , ↓X , …` blowup Examples §16 measures.  The doubling is
-- pure waste: `dualScope 0 S ++ S` is ALREADY a rewound list, and a
-- rewound list is already the identity on the frame
-- (`applyChanges-dualScope`) with the unmasks its reps need already on
-- it.  So `rewind` REPLAYS ONLY WHAT IS NOT ALREADY A REPLAY.
--
-- A list IS a replay when it is its own second half's dual replay.  The
-- test is decidable and the two branches are both trivial to discharge:
-- on `yes` the frame lemmas are the ORIGINAL frame's (`scope` is the
-- identity by `applyChanges-dualScope` at the second half, `⊢ᵐ` is Θ's
-- own — the reps are read on EXACTLY the same type context, so not even
-- a `⊢ʳ-⊑` step appears); on `no` they are the replay's, as before.

-- The SECOND HALF of a change list: the candidate Q in `S ≡ dualScope 0 Q ++ Q`.
half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

secondHalf : List Change → List Change
secondHalf S = drop (half (length S)) S

-- `S` IS A REPLAY: its first half rewinds its second.
Rewound : List Change → Set
Rewound S = dualScope 0 (secondHalf S) ++ secondHalf S ≡ S

_≟ᶜ_ : DecidableEquality Change
lock X   ≟ᶜ lock Y   with X ≟ℕ Y
... | yes refl = yes refl
... | no  ne   = no λ { refl → ne refl }
lock X   ≟ᶜ unlock Y = no λ()
unlock X ≟ᶜ lock Y   = no λ()
unlock X ≟ᶜ unlock Y with X ≟ℕ Y
... | yes refl = yes refl
... | no  ne   = no λ { refl → ne refl }

rewound? : (S : List Change) → Dec (Rewound S)
rewound? S = ≡-dec _≟ᶜ_ (dualScope 0 (secondHalf S) ++ secondHalf S) S

-- The decision is an EXPLICIT ARGUMENT, so that every lemma about the
-- rewound frame splits on it by ordinary pattern matching (no `with`
-- abstraction has to find the scrutinee under `rewind`).
rewindChanges : (S : List Change) → Dec (Rewound S) → List Change
rewindChanges S (yes _) = S
rewindChanges S (no  _) = dualScope 0 S ++ S

rewind : CtxMorph → CtxMorph
rewind Θ =
  morph (binds Θ) (rewindChanges (changes Θ) (rewound? (changes Θ)))

-- The inner frame, with the outer frame's changes moved in at its TAIL.
-- `numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁` DEFINITIONALLY: the move carries no
-- binder, and with the pair that is a fact about the constructor, not a
-- lemma about a filtered list.
infixl 5 _⋉_
_⋉_ : CtxMorph → CtxMorph → CtxMorph
Θ₁ ⋉ Θ₂ =
  morph (binds Θ₁) (changes Θ₁ ++ shiftScope (numBinds Θ₂) (changes Θ₂))
