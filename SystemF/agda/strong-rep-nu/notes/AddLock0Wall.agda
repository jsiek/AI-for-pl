module strong-rep-nu.notes.AddLock0Wall where

-- THE MODULE NAME IS A DATE-STAMPED PROPER NOUN.  `Change`'s two
-- constructors were renamed `lock`/`unlock` → `unbind`/`bind` on
-- 2026-09-23 (notes/DECISIONS.md); this file keeps the name the wall
-- was recorded under, and the live helper it is about is now
-- `strong-rep-nu.proof.AddUnbind0.addUnbind0-⊢`.

-- File Charter:
--   * THE WALL, and the record of the repair that answered it.  Found by
--     the stage-1 preservation assembly (2026-09-20): `TyPeelR-⟪⟫`
--     RE-SPELLED ITS MOVED CONVERSION IN THE WRONG NAME MAP.  A closed,
--     plain System F program — no boundary written by hand — lost its type
--     three steps in, so `AddUnbind0Typing` was FALSE and so was
--     `Preservation`.
--   * REPAIRED THE SAME DAY, with Jeremy's approval — the `Peel` repair of
--     2026-09-18, transplanted: the rule now NAMES the moved conversion
--     `s″`, carries the old and the moved conversion readings, and pins
--     the spelling with `SameConv`.  `strong-rep-nu.Reduction` carries the
--     repaired rule; `strong-rep-nu.proof.Progress` constructs its premises
--     outright (`addUnbind0-reading`); and the RESHAPED transport is PROVED
--     (`strong-rep-nu.proof.AddUnbind0`), which makes
-- `strong-rep-nu.Preservation`
--     unconditional.  See notes/DECISIONS.md, 2026-09-20.
--   * WHAT SURVIVES HERE, all still machine-checked: the source program
--     and its run (§1), the two conversion contexts that displace the new
--     ordinary name (§2), the untypeability of the state the OLD rule
--     reached (§3), the refutation of the OLD transport statement — stated
--     against a LOCAL copy of it, because the statement it came from no
--     longer exists (§4), and the repaired run on this very program, whose
--     third state is the old one with ONE conversion leaf changed (§5).
--
-- The local-copy device is the repo's usual one for a retired design:
-- `notes/CancelRShiftWall.agda` states the pre-2026-09-19 `CancelRCase`
-- locally in the same way, and `notes/ReUnlockWall.agda` the
-- pre-`conv-bind-live` conversion judgement, so that each refutation
-- stays a checked refutation rather than prose.
--
-- WHAT THE RULE SAID, BEFORE (strong-rep-nu.Reduction, until 2026-09-20).
-- `TyPeelR-⟪⟫` moves the inner boundary out by one new representation
-- binder and one new ordinary name, and re-spelled its three parts
-- SEPARATELY:
--
--     renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W   -- the interior term
--       ⟪ addUnbind0 (renᴮ² (ren² idᵗ suc) Θ′)        -- the frame
--       , `∀ (renᶜ (extᵗ suc) s′) ⟫                 -- the conversion
--
-- The first two are right, and still are.  `addUnbind0` APPENDS
-- `unbind 0 (numBinds Θ′)` to the change list, and a change list acts
-- head-LAST, so that unbind runs FIRST: in the INTERIOR reading it deletes
-- the new ordinary name before any of Θ′'s own changes run, which is
-- exactly what leaves every ordinary position of the moved term where it
-- was.
--
-- THE CONVERSION IS READ SOMEWHERE ELSE.  `env` checks it at the
-- boundary's CONVERSION context, and the conversion reading SKIPS unbinds
-- (`conv-unbind`, strong-rep-nu.Boundary §3) — that is the whole point of a
-- conversion context: it is the union of the names live anywhere along
-- the boundary scope.  So the new name is NOT deleted there, and every
-- `bind X α` of Θ′ then inserts at position X of a map that already
-- carries it.  The new name is therefore DISPLACED by Θ′'s binds, while
-- `renᶜ (extᵗ suc) s′` — which is `renᶜ suc` on the whole `` `∀ ``
-- conversion — assumes it landed at position ZERO.
--
-- ONE BIND IS ENOUGH, and `TyBeta` mints one: `inst Θ` appends
-- `bind 0 0`.  In the run below the moved boundary's conversion context
-- goes
--
--     (bindR `ℕ ∷ bindR `ℕ ∷ [])            ∣ (1 ∷ [])     -- before
--     (bindR `𝔹 ∷ bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (2 ∷ 0 ∷ []) -- after
--
-- (`conv-before` and `conv-after` in §2).  The new ordinary name lands at
-- position ONE, not zero: position 0 still names the `TyBeta` cell.
-- `renᶜ suc` moved the conversion's occurrences of position 1
-- — position 0 shifted under the `` `∀ `` — onto position 2, that is onto
-- the NEW cell, whose payload is the type argument `` `𝔹 ``.
-- `seal 1 ↦ unseal 1`, which converted `` ` 1 ⇒ ` 1 `` to `` `ℕ ⇒ `ℕ ``,
-- became `seal 2 ↦ unseal 2`, which converts `` ` 2 ⇒ ` 2 `` to
-- `` `𝔹 ⇒ `𝔹 ``; and `env`'s exterior alignment `SameTyExt` then had to
-- relate `` `∀ (`ℕ ⇒ `ℕ) `` to `` `∀ (`𝔹 ⇒ `𝔹) ``, which it cannot (§3).
--
-- WHY NO PREMISE REPAIRED IT.  The offending spelling was in the
-- CONTRACTUM, so no hypothesis on the redex could change it; and the
-- correct re-spelling is NOT A RENAMING AT ALL — where the new name ends
-- up depends on Θ′'s own binds.  This is precisely the defect the
-- crossing audit found for `Peel` on 2026-09-18 ("not merely a renumbering
-- of the same one", strong-rep-nu.Reduction).
--
-- THE REPAIR, AS INSTALLED (2026-09-20).  The rule NAMES the moved
-- spelling `s″` and carries, besides the two readings it already had, the
-- old boundary's conversion reading `Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ`, the instantiated
-- outer interior `Δ ⊢ⁱ inst R Θ ⇒ Δᵢ⁺`, the moved boundary's own
-- reading `Δᵢ⁺ ⊢ᶜ addUnbind0 (renᴮ² (ren² idᵗ suc) Θ′) ⇒ Δ″ᶜ`, and
--
--     SameConv (underΛ Δ″ᶜ) s″
--       (underΛ (renNameCtx (extN (numBinds Θ′) suc) Δ″ᶜ Δ′ᶜ)) s′
--
-- The old context is viewed through `renNameCtx`, that is through the
-- REPRESENTATION renaming the inserted binder makes: the ordinary
-- positions of `Δ′ᶜ` are kept, but each denotes `extN (numBinds Θ′) suc`
-- of the representation it denoted.  Without that view the premise is
-- unsatisfiable as soon as the old conversion context names a free
-- representation below the insertion — §6b of strong-rep-nu.Examples is the
-- witness.
--
-- WHAT SURVIVED OF THE DECOMPOSITION, and still does: the representation
-- half is fine and is proved elsewhere — the mover is `renᴹᴿ suc`, and
-- the head insertion is `repwk-cons₀` (strong-rep-nu.proof.Ctx §3).
-- The interior reading of `Θ′ ++ (unbind 0 0 ∷ [])` is the interior
-- reading of Θ′,
-- because the appended unbind deletes the new name first.  It was the
-- CONVERSION reading, and only it, that the rule got wrong.
--
-- WHAT THE STORE CHANGED (experiment 2, 2026-09-22,
-- notes/RepStoreSketch.md).  NOTHING ABOUT THIS WALL, which is the point
-- worth recording: the defect was always in the CONVERSION reading, and
-- the conversion reading is a name-map fact.  A boundary no longer
-- carries a bind block, so `numBinds Θ′` is gone and the three movers
-- collapse to one: the interior term moves by `renᴹᴿ suc`, the scope by
-- `renᴮᴿ suc`, and the frame is the snoc `Θ′ ++ (unbind 0 0 ∷ [])` rather
-- than an `addUnbind0` appending `unbind 0 (numBinds Θ′)`.  The run is the
-- SAME eight steps to the same shape, the displaced name is displaced by
-- the same one `bind`, and
-- the repaired leaf is still `seal 1 ↦ unseal 1` where the fixed
-- renaming wrote `seal 2 ↦ unseal 2`.  What moved is only WHERE the two
-- cells live: in the ambient store, so every scope below carries a
-- larger representation index (`bind 0 1` rather than `bind 0 0`,
-- and so on).

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; renameᵗ; extᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction
open import strong-rep-nu.TypeCheck
  using (tc; tk; tu; int!; conv!; sq!; wf!)
open import strong-rep-nu.Eval
  using (eval; report; repKept; traceEnd; eval-sound; Reaches; reaches)

------------------------------------------------------------------------
-- §1  A closed, plain source program, and its run
------------------------------------------------------------------------

--   Src = (((λf : ∀X. ℕ⇒ℕ. ΛX. λy:ℕ. f [𝔹])
--             · ((ΛY. ΛZ. λx:Y. x) [ℕ])) [ℕ]) · 0
--
-- The argument packages a polymorphic identity whose type MENTIONS the
-- outer binder, so `TyBeta` mints a `` `∀ `` conversion with a real
-- `seal`/`unseal` pair in it.  The function then carries that value
-- under a `Λ`, which wraps it in the binder's dual (`crossΛᴹ`) — a
-- SECOND `` `∀ `` boundary — and applies it to a type.  That application
-- is the `TyPeelR-⟪⟫` redex.
--
-- THE VALUE RESTRICTION (strong-rep-nu).  In strong-rep-var the body
-- of the `ΛX` was `f [𝔹]` itself and the redex fired UNDER the `Λ` by
-- `ξ-Λ`.  Here `⊢Λ` demands a value body and there is no `ξ-Λ`, so the
-- body is wrapped in a dummy `λy:ℕ`, and the program instantiates the
-- `Λ` at `ℕ` and applies the dummy to `0` to get the redex out from
-- under the binder.  The run is therefore eight steps, not four, and the
-- `TyPeelR-⟪⟫` redex is reached at the TOP LEVEL, inside the outer
-- `TyBeta` boundary, instead of under a `Λ`.  §2–§4 are unchanged: they
-- speak about the moved boundary and the state `bad`, which are the same
-- terms.

Vfun Pkg Use Src : Term
Vfun = Λ (ƛ (` 1) ∙ ` 0)
Pkg  = (Λ Vfun) ·[ `∀ (` 1 ⇒ ` 1) , `ℕ ]
Use  = ƛ (`∀ (`ℕ ⇒ `ℕ)) ∙ Λ (ƛ `ℕ ∙ ((` 1) ·[ `ℕ ⇒ `ℕ , `𝔹 ]))
Src  = ((Use · Pkg) ·[ `ℕ ⇒ (`ℕ ⇒ `ℕ) , `ℕ ]) · ($ 0)

Src-⊢ : empty ∣ [] ⊢ Src ⦂ `ℕ ⇒ `ℕ
Src-⊢ = tc

-- The outer `TyBeta` boundary, which every later state sits inside.  It
-- binds the cell `TyBeta` allocated — and WHICH address that is
-- depends on how many cells the run has allocated since, so the scope is
-- spelled once per state (experiment 2: the allocation shifts every
-- sibling's representation indices by one).
Outer₇ Outer₈ : Boundary
Outer₇ = (bind 0 1 ∷ [])
Outer₈ = (bind 0 2 ∷ [])

-- THE RUN, BEFORE (2026-09-20, the wall): `TyBeta`, then `Beta`, then
-- `TyPeelR-⟪⟫` — and the evaluator's own per-state check REJECTED the
-- third contractum, `repKept … ≡ false`.  That was only a checker's
-- verdict; §3 proves the state it stopped at untypeable, and §4 turns
-- that into the refutation of the transport statement.
--
-- THE RUN, AFTER: `TyBeta`, `Beta` (the crossing), then — the value
-- restriction's detour — `TyBeta`, `Peel`, `Drop$`, `Beta` to get the
-- redex out from under the `Λ`, then `TyPeelR-⟪⟫`, `TyPeelR-Λ`, and a
-- value — and every state type-checks.  The `true` inside `Reaches` IS
-- that record, and the `8 8` says: with fuel 8, exactly 8 steps to `Dst`.
-- `Dst` is strong-rep-var's endpoint with the `Λ` gone and the outer
-- `TyBeta` boundary around it.  The step COUNT is unchanged by the store.
Dst : Term
Dst =
  (((ƛ (` 1) ∙ ` 0)
        ⟪ (bind 1 3 ∷ unbind 1 1 ∷ bind 0 0 ∷ [])
        , seal 1 ↦ unseal 1 ⟫)
      ⟪ (unbind 1 2 ∷ bind 0 1 ∷ []) , id `ℕ ↦ id `ℕ ⟫)
    ⟪ Outer₈ , id `ℕ ↦ id `ℕ ⟫

Src-eval : Reaches 8 8 Src-⊢ Dst
Src-eval = reaches refl (V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-ƛ I-fun) I-fun) I-fun)

-- the same fact at the fuel the wall was measured with
run-keeps-the-type : repKept (report (eval 10 Src Src-⊢)) ≡ true
run-keeps-the-type = refl

------------------------------------------------------------------------
-- §2  The two conversion contexts, and the displaced name
------------------------------------------------------------------------

-- the inner boundary `TyBeta` minted, carried under the `Λ` by `Beta` —
-- which shifts it past the `Λ`'s own abstract cell
Θ′ : Boundary
Θ′ = renᴮᴿ suc TyBetaBoundary

Θ′-explicit : Θ′ ≡ (bind 0 1 ∷ [])
Θ′-explicit = refl

inner : Term
inner = Vfun ⟪ Θ′ , `∀ (seal 1 ↦ unseal 1) ⟫

-- its exterior, and the context it is moved to.  The store holds the two
-- cells the run has allocated by then; the move ALLOCATES a third — the
-- type argument's representation `` `𝔹 `` — at address 0, and
-- `inst` gives it the new ordinary name.
Δᵢ Δ⁺ : Ctxᵗ
Δᵢ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ []
Δ⁺ = (bindR `𝔹 ∷ bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ [])

⊢inner : Δᵢ ∣ [] ⊢ inner ⦂ `∀ (`ℕ ⇒ `ℕ)
⊢inner = tc

wf⁺ : WfCtx Δ⁺
wf⁺ = wf! Δ⁺

-- THE TWO CONVERSION CONTEXTS.  Before the move the boundary's own
-- conversion context names one representation variable; after it, two —
-- and the NEW one is at position 1, because the skipped `unbind 0 0` left
-- it in place and Θ′'s `bind` inserted in front of it.
--
-- Read one universe up, this is the representation renaming the repaired
-- rule carries: the allocated cell takes address 0 and everything below
-- it moves by `suc` — which is exactly the view `renNameCtx suc` takes
-- of `Δᶜ′` inside the repaired premise.  (Before the store the renaming
-- was `extN (numBinds Θ′) suc`, the bind block being exempt; there is no
-- bind block left to exempt.)
Δᶜ′ Δᶜ⁺ : Ctxᵗ
Δᶜ′ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (1 ∷ [])
Δᶜ⁺ = (bindR `𝔹 ∷ bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (2 ∷ 0 ∷ [])

conv-before : Δᵢ ⊢ᶜ Θ′ ⇒ Δᶜ′
conv-before = proj₂ (conv! Δᵢ Θ′)

AL : Boundary
AL = (renᴮᴿ suc Θ′ ++ (unbind 0 0 ∷ []))

AL-explicit : AL ≡ (bind 0 2 ∷ unbind 0 0 ∷ [])
AL-explicit = refl

conv-after : Δ⁺ ⊢ᶜ AL ⇒ Δᶜ⁺
conv-after = proj₂ (conv! Δ⁺ AL)

-- THE OLD CONTRACTUM.  `renᶜ (extᵗ suc)` moved `seal 1` to `seal 2`; the
-- repaired rule leaves it at `seal 1` (§5), which is what position 1 of
-- `underΛ Δᶜ⁺` still names.  The FRAMES AGREE — the wall was never about
-- the frame, and `AL` below is the scope both rules move to.
moved bad : Term
moved = Vfun ⟪ AL , `∀ (seal 2 ↦ unseal 2) ⟫
bad = (moved ·[ `ℕ ⇒ `ℕ , ` 0 ])
        ⟪ (unbind 1 1 ∷ bind 0 0 ∷ []) , id `ℕ ↦ id `ℕ ⟫

------------------------------------------------------------------------
-- §3  That state has no typing derivation
------------------------------------------------------------------------

-- The moved conversion reads the NEW cell, whose payload is `` `𝔹 ``.
sq2 : underΛ Δᶜ⁺ ∋ 2 := `𝔹
sq2 = proj₂ (sq! (underΛ Δᶜ⁺) 2)

⊢c⁺ : Δᶜ⁺ ⊢ `∀ (seal 2 ↦ unseal 2) ∶ `∀ (` 2 ⇒ ` 2) ⇝ `∀ (`𝔹 ⇒ `𝔹)
⊢c⁺ = tk

uq⁺ : Unique (names Δᶜ⁺)
uq⁺ = tu

-- The conversion context is a FUNCTION of the boundary scope and its
-- exterior, so `conv-after` IS the one `env` stored; the conversion's
-- types are then unique on it; and the exterior alignment asks for
-- `` `ℕ ⇒ `ℕ `` to read as the representation `` `𝔹 ⇒ `𝔹 ``.
no-moved : ¬ (Δ⁺ ∣ [] ⊢ moved ⦂ `∀ (`ℕ ⇒ `ℕ))
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
  with conversion-functional (bw-conversion mwΘ) conv-after
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl
  with conv-types-unique uq⁺ ⊢c ⊢c⁺
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl | refl , refl
  with sameₑ
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl | refl , refl
  | S , same-∀ (same-⇒ same-ℕ same-ℕ) , same-∀ (same-⇒ () q)

-- The pushed-in type application demands exactly the type the moved
-- boundary cannot have: its annotation is `renameᵗ (extᵗ suc) Bᵢ′`,
-- which here is `` `ℕ ⇒ `ℕ ``.  The instantiated outer scope is read at
-- the ALLOCATED exterior.
Δ₆ : Ctxᵗ
Δ₆ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ [])

int⁺ : allocate `𝔹 Δ₆ ⊢ⁱ (unbind 1 1 ∷ bind 0 0 ∷ []) ⇒ Δ⁺
int⁺ = proj₂ (int! (allocate `𝔹 Δ₆) ((unbind 1 1 ∷ bind 0 0 ∷ [])))

no-bad : ¬ (allocate `𝔹 Δ₆ ∣ [] ⊢ bad ⦂ `ℕ ⇒ `ℕ)
no-bad (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
  with interior-functional (bw-interior mwΘ) int⁺
no-bad (env mwΘ (⊢·[] ⊢L wA) ⊢c sameᵢ sameₑ wE) | refl = no-moved ⊢L

------------------------------------------------------------------------
-- §4  The RETIRED transport statement, refuted — a LOCAL statement
------------------------------------------------------------------------

-- `AddUnbind0Typing°` is `strong-rep-nu.proof.Preserve.AddUnbind0Typing`
-- AS IT STOOD on 2026-09-20 before the repair — the moved boundary's
-- typing, with the moved conversion FIXED at `renᶜ (extᵗ suc) s`.  It is
-- written out here rather than imported because the statement it came
-- from no longer exists, and a refutation that cannot be re-run is not
-- evidence.  The one line that matters is the contractum's conversion,
-- `` `∀ (renᶜ (extᵗ suc) s) ``.  (Its movers are written with the
-- store's `renᴹᴿ suc`/`renᴮᴿ suc`, which is what
-- `renᴹ² (ren² idᵗ (extN (numBinds Θ) suc))` and
-- `renᴮ² (ren² idᵗ suc)` became when the bind block went: the
-- refutation is about the conversion leaf either way.)
--
-- The live `strong-rep-nu.proof.Preserve.AddUnbind0Typing` was RESHAPED
-- with the rule: it receives the two conversion readings and the
-- `SameConv`, and names the moved spelling.  It is therefore not the
-- statement refuted here — and it is PROVED,
-- `strong-rep-nu.proof.AddUnbind0.addUnbind0-⊢`, so nothing below could
-- refute it.
AddUnbind0Typing° : Set
AddUnbind0Typing° = ∀ {Δ W Θ s A P}
  → WfCtx ((bindR P ∷ reps Δ) ∣
               (zero ∷ shiftReps (names Δ)))
  → Δ ∣ [] ⊢ W ⟪ Θ , `∀ s ⟫ ⦂ `∀ A
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
      ∣ [] ⊢
        (renᴹᴿ suc W
          ⟪ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ []))
          , `∀ (renᶜ (extᵗ suc) s) ⟫)
        ⦂ `∀ (renameᵗ (extᵗ suc) A)

-- §2 supplies the instance the run produced — Δ is the outer boundary's
-- interior, W is `Vfun`, Θ is the `TyBeta` scope, and P is the type
-- argument's representation `` `𝔹 `` — and §3 refutes its output.
no-addUnbind0° : ¬ AddUnbind0Typing°
no-addUnbind0° al =
  no-moved (al {Δ = Δᵢ} {W = Vfun} {Θ = Θ′}
               {s = seal 1 ↦ unseal 1} {A = `ℕ ⇒ `ℕ} {P = `𝔹}
               wf⁺ ⊢inner)

------------------------------------------------------------------------
-- §5  THE REPAIRED RULE, ON THIS CONFIGURATION
------------------------------------------------------------------------

-- The repaired rule fires here too — the wall was never about firing —
-- and it moves the SAME term across the SAME scope `AL`.  The one leaf
-- that changes is the conversion: `seal 1 ↦ unseal 1`, not
-- `seal 2 ↦ unseal 2`.  Position 1 of `underΛ Δᶜ⁺` still names the
-- `TyBeta` cell (§2), so the correct re-spelling here is the IDENTITY on
-- the conversion — which no fixed renaming delivers, because `renᶜ suc`
-- was forced on a boundary scope whose binds happen to insert nothing
-- in front of the new name.
moved-repaired good : Term
moved-repaired = Vfun ⟪ AL , `∀ (seal 1 ↦ unseal 1) ⟫
good = (moved-repaired ·[ `ℕ ⇒ `ℕ , ` 0 ])
         ⟪ (unbind 1 1 ∷ bind 0 0 ∷ []) , id `ℕ ↦ id `ℕ ⟫

-- THE SEVENTH STATE OF THE RUN, MEASURED (the third, in strong-rep-var).
-- This is the state §3 refutes, with that one leaf repaired, sitting in
-- the outer `TyBeta` boundary instead of under the `Λ`.
repaired-state : traceEnd (eval 7 Src Src-⊢)
  ≡ good ⟪ Outer₇ , id `ℕ ↦ id `ℕ ⟫
repaired-state = refl

-- and it is not the state §3 refutes
good≢bad : ¬ (good ≡ bad)
good≢bad ()

-- THE WALL NO LONGER REFUTES ANYTHING LIVE.  The retired §4(ii) went
-- `Preservation → Preservation* → no-state (pres* wf-empty Src-⊢ the-run)`
-- with `the-run : empty ⊢ Src -→* Λ bad` supplied by `eval-sound 10 Src-⊢`.
-- Under the repaired rule that run does not reach `bad`: it reaches
-- `Dst`, through `good`, and every state along the way type-checks
-- (`Src-eval`, §1).  So there is no closed program here refuting
-- `strong-rep-nu.Preservation.Preservation` — which is now an
-- UNCONDITIONAL theorem — and this file states none; the multi-step run
-- below ends where `Src-eval` says it does.
the-repaired-run : empty ⊢ Src -→* traceEnd (eval 10 Src Src-⊢)
the-repaired-run = eval-sound 10 Src-⊢
