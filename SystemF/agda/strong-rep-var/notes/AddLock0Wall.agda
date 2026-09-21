module strong-rep-var.notes.AddLock0Wall where

-- File Charter:
--   * THE WALL, and the record of the repair that answered it.  Found by
--     the stage-1 preservation assembly (2026-09-20): `TyPeelR-⟪⟫`
--     RE-SPELLED ITS MOVED CONVERSION IN THE WRONG NAME MAP.  A closed,
--     plain System F program — no boundary written by hand — lost its type
--     three steps in, so `AddLock0Typing` was FALSE and so was
--     `Preservation`.
--   * REPAIRED THE SAME DAY, with Jeremy's approval — the `Peel` repair of
--     2026-09-18, transplanted: the rule now NAMES the moved conversion
--     `s″`, carries the old and the moved conversion readings, and pins
--     the spelling with `SameConv`.  `strong-rep-var.Reduction` carries the
--     repaired rule; `strong-rep-var.proof.Progress` constructs its premises
--     outright (`addLock0-reading`); and the RESHAPED transport is PROVED
--     (`strong-rep-var.proof.AddLock0`), which makes
-- `strong-rep-var.Preservation`
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
-- pre-`conv-unlock-live` conversion judgement, so that each refutation
-- stays a checked refutation rather than prose.
--
-- WHAT THE RULE SAID, BEFORE (strong-rep-var.Reduction, until 2026-09-20).
-- `TyPeelR-⟪⟫` moves the inner boundary out by one new representation
-- binder and one new ordinary name, and re-spelled its three parts
-- SEPARATELY:
--
--     renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W   -- the interior term
--       ⟪ addLock0 (renᴮ² (ren² idᵗ suc) Θ′)        -- the frame
--       , `∀ (renᶜ (extᵗ suc) s′) ⟫                 -- the conversion
--
-- The first two are right, and still are.  `addLock0` APPENDS
-- `lock 0 (numBinds Θ′)` to the change list, and a change list acts
-- head-LAST, so that lock runs FIRST: in the INTERIOR reading it deletes
-- the new ordinary name before any of Θ′'s own changes run, which is
-- exactly what leaves every ordinary position of the moved term where it
-- was.
--
-- THE CONVERSION IS READ SOMEWHERE ELSE.  `env` checks it at the
-- boundary's CONVERSION context, and the conversion reading SKIPS locks
-- (`conv-lock`, strong-rep-var.CtxMorph §3) — that is the whole point of a
-- conversion context: it is the union of the names live anywhere along
-- the morphism.  So the new name is NOT deleted there, and every
-- `unlock X α` of Θ′ then inserts at position X of a map that already
-- carries it.  The new name is therefore DISPLACED by Θ′'s unlocks, while
-- `renᶜ (extᵗ suc) s′` — which is `renᶜ suc` on the whole `` `∀ ``
-- conversion — assumes it landed at position ZERO.
--
-- ONE UNLOCK IS ENOUGH, and `TyBeta` mints one: `instantiate R Θ` appends
-- `unlock 0 0`.  In the run below the moved boundary's conversion context
-- goes
--
--     (bindR `ℕ ∷ abstR ∷ [])             ∣ (0 ∷ [])       -- before
--     (bindR `ℕ ∷ bindR `𝔹 ∷ abstR ∷ [])  ∣ (0 ∷ 1 ∷ [])   -- after
--
-- (`conv-before` and `conv-after` in §2).  The new ordinary name lands at
-- position ONE, not zero: position 0 still names the `TyBeta` binder
-- `bindR `ℕ`.  `renᶜ suc` moved the conversion's occurrences of position 1
-- — position 0 shifted under the `` `∀ `` — onto position 2, that is onto
-- the NEW binder, whose payload is the type argument `` `𝔹 ``.
-- `seal 1 ↦ unseal 1`, which converted `` ` 1 ⇒ ` 1 `` to `` `ℕ ⇒ `ℕ ``,
-- became `seal 2 ↦ unseal 2`, which converts `` ` 2 ⇒ ` 2 `` to
-- `` `𝔹 ⇒ `𝔹 ``; and `env`'s exterior alignment `SameTyExt` then had to
-- relate `` `∀ (`ℕ ⇒ `ℕ) `` to `` `∀ (`𝔹 ⇒ `𝔹) ``, which it cannot (§3).
--
-- WHY NO PREMISE REPAIRED IT.  The offending spelling was in the
-- CONTRACTUM, so no hypothesis on the redex could change it; and the
-- correct re-spelling is NOT A RENAMING AT ALL — where the new name ends
-- up depends on Θ′'s own unlocks.  This is precisely the defect the
-- crossing audit found for `Peel` on 2026-09-18 ("not merely a renumbering
-- of the same one", strong-rep-var.Reduction).
--
-- THE REPAIR, AS INSTALLED (2026-09-20).  The rule NAMES the moved
-- spelling `s″` and carries, besides the two readings it already had, the
-- old boundary's conversion reading `Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ`, the instantiated
-- outer interior `Δ ⊢ⁱ instantiate R Θ ⇒ Δᵢ⁺`, the moved boundary's own
-- reading `Δᵢ⁺ ⊢ᶜ addLock0 (renᴮ² (ren² idᵗ suc) Θ′) ⇒ Δ″ᶜ`, and
--
--     SameConv (underΛ Δ″ᶜ) s″
--       (underΛ (renNameCtx (extN (numBinds Θ′) suc) Δ″ᶜ Δ′ᶜ)) s′
--
-- The old context is viewed through `renNameCtx`, that is through the
-- REPRESENTATION renaming the inserted binder makes: the ordinary
-- positions of `Δ′ᶜ` are kept, but each denotes `extN (numBinds Θ′) suc`
-- of the representation it denoted.  Without that view the premise is
-- unsatisfiable as soon as the old conversion context names a free
-- representation below the insertion — §6b of strong-rep-var.Examples is the
-- witness.
--
-- WHAT SURVIVED OF THE DECOMPOSITION, and still does: the representation
-- half is fine and is proved elsewhere — the mover is
-- `renᴹᴿ (extN (numBinds Θ′) suc)` by `renᴹ²-ord-id`/`renᴮ²-ord-id`, and
-- the head insertion is `repwk-cons₀` (strong-rep-var.proof.Ctx §3) pushed
-- through
-- `repwk-push`.  The interior reading of `addLock0 Θ′` is the interior
-- reading of Θ′, because the appended lock deletes the new name first.  It
-- was the CONVERSION reading, and only it, that the rule got wrong.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-var.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; renameᵗ; extᵗ)
open import strong-rep-var.Ctx
open import strong-rep-var.Conversion
open import strong-rep-var.CtxMorph
open import strong-rep-var.Terms
open import strong-rep-var.TermSubst
open import strong-rep-var.Reduction
open import strong-rep-var.TypeCheck using (tc)
open import strong-rep-var.Eval
  using (eval; report; repKept; traceEnd; eval-sound; Reaches; reaches)

------------------------------------------------------------------------
-- §1  A closed, plain source program, and its run
------------------------------------------------------------------------

--   Src = (λf : ∀X. ℕ⇒ℕ. ΛX. f [𝔹])
--           · ((ΛY. ΛZ. λx:Y. x) [ℕ])
--
-- The argument packages a polymorphic identity whose type MENTIONS the
-- outer binder, so `TyBeta` mints a `` `∀ `` conversion with a real
-- `seal`/`unseal` pair in it.  The function then carries that value
-- under a `Λ`, which wraps it in the binder's dual (`crossΛᴹ`) — a
-- SECOND `` `∀ `` boundary — and applies it to a type.  That application
-- is the `TyPeelR-⟪⟫` redex.

Vfun Pkg Use Src : Term
Vfun = Λ (ƛ (` 1) ∙ ` 0)
Pkg  = (Λ Vfun) ·[ `∀ (` 1 ⇒ ` 1) , `ℕ ]
Use  = ƛ (`∀ (`ℕ ⇒ `ℕ)) ∙ Λ ((` 0) ·[ `ℕ ⇒ `ℕ , `𝔹 ])
Src  = Use · Pkg

Src-⊢ : empty ∣ [] ⊢ Src ⦂ `∀ (`ℕ ⇒ `ℕ)
Src-⊢ = tc

-- THE RUN, BEFORE (2026-09-20, the wall): `TyBeta`, then `Beta`, then
-- `TyPeelR-⟪⟫` — and the evaluator's own per-state check REJECTED the
-- third contractum, `repKept … ≡ false`.  That was only a checker's
-- verdict; §3 proves the state it stopped at untypeable, and §4 turns
-- that into the refutation of the transport statement.
--
-- THE RUN, AFTER: the same three rules, then `TyPeelR-Λ`, then a value —
-- and every state type-checks.  The `true` inside `Reaches` IS that
-- record, and the `4 4` says: with fuel 4, exactly 4 steps to `Dst`.
Dst : Term
Dst =
  Λ (((ƛ (` 1) ∙ ` 0)
        ⟪ morph ((` 0) ∷ `ℕ ∷ [])
            (unlock 1 1 ∷ lock 1 2 ∷ unlock 0 0 ∷ [])
        , seal 1 ↦ unseal 1 ⟫)
      ⟪ morph (`𝔹 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
      , id `ℕ ↦ id `ℕ ⟫)

Src-eval : Reaches 4 4 Src-⊢ Dst
Src-eval = reaches refl (V-Λ (V-⟪⟫ (V-⟪⟫ V-ƛ I-fun) I-fun))

-- the same fact at the fuel the wall was measured with
run-keeps-the-type : repKept (report (eval 10 Src Src-⊢)) ≡ true
run-keeps-the-type = refl

------------------------------------------------------------------------
-- §2  The two conversion contexts, and the displaced name
------------------------------------------------------------------------

-- the inner boundary `TyBeta` minted, carried under the `Λ` by `Beta`
Θ′ : CtxMorph
Θ′ = renᴮ² (ren² (λ X → X) suc) TyBetaMorph

inner : Term
inner = Vfun ⟪ Θ′ , `∀ (seal 1 ↦ unseal 1) ⟫

-- its exterior, and the context it is moved to: one `bindR `𝔹` (the
-- type argument's representation) and one new ordinary name for it
Δᵢ Δ⁺ : Ctxᵗ
Δᵢ = (abstR ∷ []) ∣ []
Δ⁺ = (bindR `𝔹 ∷ abstR ∷ []) ∣ (0 ∷ [])

⊢inner : Δᵢ ∣ [] ⊢ inner ⦂ `∀ (`ℕ ⇒ `ℕ)
⊢inner = tc

wf⁺ : WfCtx Δ⁺
wf⁺ = wf-ctx (wf-bindR wfᴿ-𝔹 (wf-abstR wf-reps[])) vn
             (unique∷ fresh[] unique[])
  where
  vn : ValidNames (bindR `𝔹 ∷ abstR ∷ []) (0 ∷ [])
  vn here = bindR `𝔹 , here

-- THE TWO CONVERSION CONTEXTS.  Before the move the boundary's own
-- conversion context names one representation variable; after it, two —
-- and the NEW one is at position 1, because the skipped `lock 0 1` left
-- it in place and Θ′'s `unlock 0 0` inserted in front of it.
--
-- Read one universe up, this is the representation renaming the repaired
-- rule carries: Θ′'s own bind block occupies representation index 0 and is
-- untouched, while everything below it moves by `suc` — that is
-- `extN (numBinds Θ′) suc` with `numBinds Θ′ ≡ 1`, which is exactly the
-- view `renNameCtx` takes of `Δᶜ′` inside the repaired premise.
Δᶜ′ Δᶜ⁺ : Ctxᵗ
Δᶜ′ = (bindR `ℕ ∷ abstR ∷ []) ∣ (0 ∷ [])
Δᶜ⁺ = (bindR `ℕ ∷ bindR `𝔹 ∷ abstR ∷ []) ∣ (0 ∷ 1 ∷ [])

conv-before : Δᵢ ⊢ᶜ Θ′ ⇒ Δᶜ′
conv-before =
  conversion (conv-unlock (bindR `ℕ , here) conv[] fresh[] ins-here)

AL : CtxMorph
AL = addLock0 Θ′

conv-after : Δ⁺ ⊢ᶜ AL ⇒ Δᶜ⁺
conv-after =
  conversion
    (conv-unlock (bindR `ℕ , here)
      (conv-lock (bindR `𝔹 , there here) conv[])
      (fresh∷ (λ ()) fresh[])
      ins-here)

-- THE OLD CONTRACTUM.  `renᶜ (extᵗ suc)` moved `seal 1` to `seal 2`; the
-- repaired rule leaves it at `seal 1` (§5), which is what position 1 of
-- `underΛ Δᶜ⁺` still names.  The FRAMES AGREE — the wall was never about
-- the frame, and `AL` below is the frame both rules move to.
moved bad : Term
moved = Vfun ⟪ AL , `∀ (seal 2 ↦ unseal 2) ⟫
bad = (moved ·[ `ℕ ⇒ `ℕ , ` 0 ])
        ⟪ morph (`𝔹 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
        , id `ℕ ↦ id `ℕ ⟫

------------------------------------------------------------------------
-- §3  That state has no typing derivation
------------------------------------------------------------------------

-- The moved conversion reads the NEW binder, whose payload is `` `𝔹 ``.
sq2 : underΛ Δᶜ⁺ ∋ 2 := `𝔹
sq2 = 2 , `𝔹 , there (there here) , r-there-abst (r-there r-here)
    , same-𝔹

⊢c⁺ : Δᶜ⁺ ⊢ `∀ (seal 2 ↦ unseal 2) ∶ `∀ (` 2 ⇒ ` 2) ⇝ `∀ (`𝔹 ⇒ `𝔹)
⊢c⁺ = conv-all (conv-fun (conv-seal sq2) (conv-unseal sq2))

uq⁺ : Unique (names Δᶜ⁺)
uq⁺ = unique∷ (fresh∷ (λ ()) fresh[]) (unique∷ fresh[] unique[])

-- The conversion context is a FUNCTION of the morphism and its exterior,
-- so `conv-after` IS the one `env` stored; the conversion's types are
-- then unique on it; and the exterior alignment asks for `` `ℕ ⇒ `ℕ ``
-- to read as the representation `` `𝔹 ⇒ `𝔹 ``.
no-moved : ¬ (Δ⁺ ∣ [] ⊢ moved ⦂ `∀ (`ℕ ⇒ `ℕ))
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
  with conversion-functional (mw-conversion mwΘ) conv-after
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl
  with conv-types-unique uq⁺ ⊢c ⊢c⁺
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl | refl , refl
  with sameₑ
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl | refl , refl
  | S , same-∀ (same-⇒ same-ℕ same-ℕ) , same-∀ (same-⇒ () q)

-- The pushed-in type application demands exactly the type the moved
-- boundary cannot have: its annotation is `renameᵗ (extᵗ suc) Bᵢ′`,
-- which here is `` `ℕ ⇒ `ℕ ``.
int⁺ : underΛ empty ⊢ⁱ morph (`𝔹 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
         ⇒ Δ⁺
int⁺ =
  interior
    (changes∷ (changes∷ changes[]
                (step-unlock (bindR `𝔹 , here) (fresh∷ (λ ()) fresh[])
                             ins-here))
              (step-lock (abstR , there here) (del-there del-here)
                         (fresh∷ (λ ()) fresh[])))

no-bad : ¬ (underΛ empty ∣ [] ⊢ bad ⦂ `ℕ ⇒ `ℕ)
no-bad (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
  with interior-functional (mw-interior mwΘ) int⁺
no-bad (env mwΘ (⊢·[] ⊢L wA) ⊢c sameᵢ sameₑ wE) | refl = no-moved ⊢L

no-state : ¬ (empty ∣ [] ⊢ Λ bad ⦂ `∀ (`ℕ ⇒ `ℕ))
no-state (⊢Λ ⊢N) = no-bad ⊢N

------------------------------------------------------------------------
-- §4  The RETIRED transport statement, refuted — a LOCAL statement
------------------------------------------------------------------------

-- `AddLock0Typing°` is `strong-rep-var.proof.Preserve.AddLock0Typing` AS IT
-- STOOD
-- on 2026-09-20 before the repair — the moved boundary's typing, with the
-- moved conversion FIXED at `renᶜ (extᵗ suc) s`.  It is written out here
-- rather than imported because the rule that generated it no longer
-- exists, and a refutation that cannot be re-run is not evidence.  The one
-- line that matters is the contractum's conversion,
-- `` `∀ (renᶜ (extᵗ suc) s) ``.
--
-- The live `strong-rep-var.proof.Preserve.AddLock0Typing` was RESHAPED with
-- the
-- rule: it receives the two conversion readings and the `SameConv`, and
-- names the moved spelling.  It is therefore not the statement refuted
-- here — and it is PROVED, `strong-rep-var.proof.AddLock0.addLock0-⊢`, so
-- nothing
-- below could refute it.
AddLock0Typing° : Set
AddLock0Typing° = ∀ {Δ W Θ s A P}
  → WfCtx ((bindR P ∷ reps Δ) ∣
               (zero ∷ shiftNames (names Δ)))
  → Δ ∣ [] ⊢ W ⟪ Θ , `∀ s ⟫ ⦂ `∀ A
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))
      ∣ [] ⊢
        (renᴹ² (ren² (λ X → X) (extN (numBinds Θ) suc)) W
          ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ)
          , `∀ (renᶜ (extᵗ suc) s) ⟫)
        ⦂ `∀ (renameᵗ (extᵗ suc) A)

-- §2 supplies the instance the run produced — Δ is the outer boundary's
-- interior, W is `Vfun`, Θ is the `TyBeta` frame, and P is the type
-- argument's representation `` `𝔹 `` — and §3 refutes its output.
no-addLock0° : ¬ AddLock0Typing°
no-addLock0° al =
  no-moved (al {Δ = Δᵢ} {W = Vfun} {Θ = Θ′}
               {s = seal 1 ↦ unseal 1} {A = `ℕ ⇒ `ℕ} {P = `𝔹}
               wf⁺ ⊢inner)

------------------------------------------------------------------------
-- §5  THE REPAIRED RULE, ON THIS CONFIGURATION
------------------------------------------------------------------------

-- The repaired rule fires here too — the wall was never about firing —
-- and it moves the SAME term across the SAME frame `AL`.  The one leaf
-- that changes is the conversion: `seal 1 ↦ unseal 1`, not
-- `seal 2 ↦ unseal 2`.  Position 1 of `underΛ Δᶜ⁺` still names the
-- `TyBeta` binder `bindR `ℕ` (§2), so the correct re-spelling here is the
-- IDENTITY on the conversion — which no fixed renaming delivers, because
-- `renᶜ suc` was forced on a morphism whose unlocks happen to insert
-- nothing in front of the new name.
moved-repaired good : Term
moved-repaired = Vfun ⟪ AL , `∀ (seal 1 ↦ unseal 1) ⟫
good = (moved-repaired ·[ `ℕ ⇒ `ℕ , ` 0 ])
         ⟪ morph (`𝔹 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
         , id `ℕ ↦ id `ℕ ⟫

-- THE THIRD STATE OF THE RUN, MEASURED.  This is the state §3 refutes,
-- with that one leaf repaired.
repaired-state : traceEnd (eval 3 Src Src-⊢) ≡ Λ good
repaired-state = refl

-- and it is not the state §3 refutes
good≢bad : ¬ (good ≡ bad)
good≢bad ()

-- THE WALL NO LONGER REFUTES ANYTHING LIVE.  The retired §4(ii) went
-- `Preservation → Preservation* → no-state (pres* wf-empty Src-⊢ the-run)`
-- with `the-run : empty ⊢ Src -→* Λ bad` supplied by `eval-sound 10 Src-⊢`.
-- Under the repaired rule that run does not reach `Λ bad`: it reaches
-- `Dst`, through `Λ good`, and every state along the way type-checks
-- (`Src-eval`, §1).  So there is no closed program here refuting
-- `strong-rep-var.Preservation.Preservation` — which is now an UNCONDITIONAL
-- theorem — and this file states none; the multi-step run below ends where
-- `Src-eval` says it does.
the-repaired-run : empty ⊢ Src -→* traceEnd (eval 10 Src Src-⊢)
the-repaired-run = eval-sound 10 Src-⊢
