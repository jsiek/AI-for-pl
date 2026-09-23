module strong-rep-store.notes.CancelRReachabilityWitness where

-- File Charter:
--   * THE BEFORE/AFTER RECORD of the `CancelR` defect and its repair.
--   * BEFORE (2026-09-19, morning).  This module answered Jeremy's
--     question — "do you have an example source program that reduces to
--     the problematic configuration?" — with YES.  One CLOSED, PLAIN
--     System F program (no boundary, no boundary scope, no conversion anywhere
--     in the source) reduces in NINE steps to a `CancelR` redex whose
--     inner layer is read at a LARGER NAME MAP than its outer one (then:
--     `numBinds Θ₁ ≡ 1`) and whose cancelled binder's representation is
--     OPEN.  Under the OLD
--     rule the tenth step lost the type — `eval` recorded it as
--     `illtyped` — and the raw machine then STUCK after sixteen steps at
--     a non-value identity tower.  That closed repair path (b), the
--     invariant `numBinds Θ₁ ≡ 0`: it was false at a reachable redex.
--   * AFTER (2026-09-19, same day).  Repair (a) was approved by Jeremy
--     and installed in `strong-rep-store.Reduction`.  The first nine steps are
--     unchanged; the tenth now mints `mkId (` 2)` where it minted
--     `mkId (` 1)`, and the run COMPLETES: `Src-eval` below is
--     `Reaches 19 19 Src-⊢ ($ 7)`, every state along the way type
--     checked.  The two controls are unchanged.
--   * The BEFORE half is prose, not Agda: its equations were stated
--     against a constructor that no longer exists.  What made them true —
--     the incompatibility, and the old statement refuted against a
--     local copy of itself — is kept machine-checked in
--     `notes/CancelRShiftWall.agda`, and the narrative is
--     notes/DECISIONS.md (2026-09-19) and notes/CancelRReachability.md.
--   * Everything below is observed, not designed: the redex, its frames
--     and its contexts are read off `eval` and pinned by `refl`.
--
-- WHERE THE WALL'S UNREACHABILITY ARGUMENT WENT WRONG.  It said a bare
-- `seal X` conversion "is minted by exactly one rule — `Peel`, on the
-- crossing ARGUMENT — whose frame is `dual Θ`", and
-- `binds (dual Θ) ≡ []`.  `Peel` mints TWO boundaries, and only the
-- argument's carries the dual:
--
--       Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
--         -→ (V · (… ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫
--                   ^^^^^^^^^^^^^ binds nothing     ^^^ the ORIGINAL frame
--
-- The RESULT boundary keeps `Θ` and takes the CODOMAIN `t`.  If `t` is a
-- bare `seal`, that is a bare `seal` on whatever `Θ` binds.  And `Θ` binds
-- when the boundary was minted by `TyPeelR`: its conversion is
-- `instReveal 0 s` on `inst R Θ₀`, and
-- `instReveal X (seal Y) ≡ seal Y`, so a `seal` leaf of the crossed
-- `∀`-conversion survives onto a scope that unlocks one more cell than
-- the scope it crossed (before the store: `suc (numBinds Θ₀)` binds).
--
-- Both fire in this run, in that order (steps 7 and 8).  The `seal` leaf
-- itself is `TyBeta`'s `conceal 0` at the argument type `∀Z. Z ⇒ X`:
-- `conceal 0 (`∀ (` 0 ⇒ ` 1)) ≡ `∀ (id (` 0) ↦ seal 1)`.  No program in
-- `strong-rep-store.Examples` §§1–7 passes a `∀Z. … ⇒ X` — an argument whose
-- polymorphic type RETURNS the abstracted variable — so no run there ever
-- produced the leaf; `strong-rep-store.Examples` §8 is this program, merged in.
--
-- AND WHY THE OPEN REPRESENTATION.  The instantiation that mints the
-- cancelled binder is at a type VARIABLE of an ENCLOSING `Λ` (`[P]`, not
-- `[ℕ]`), which is what `strong-rep-store.Examples` §2c already does for
-- `IdPush`.  Its payload is then a representation VARIABLE.
--
-- WHAT THE STORE CHANGED (experiment 2, 2026-09-22,
-- notes/RepStoreSketch.md).  The run is the SAME: nineteen steps, the
-- same rules in the same order, the same `CancelR` at step ten, and the
-- same two minted spellings `mkId (` 2)` (inner) and `mkId (` 1)`
-- (outer).  What changed is WHERE the representations live.  A boundary
-- carries no bind block, so `numBinds` is gone and with it the SHIFT the
-- repair was about: the three cells this run allocates sit in the
-- AMBIENT store `bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []`, and every
-- frame of every state is read over it.  What survives of the defect is
-- its honest half — the inner layer is checked at a name map where the
-- cancelled seal sits at position TWO and the outer at one where it sits
-- at position ONE, so the one cell has two spellings (§5) — and the
-- premise is still carried for the reason `_⊢_≈_⊣_` has always existed:
-- two different NAME MAPS.  The SHIFT the repair was about is gone with
-- the bind block, and with it the refutation of the old premise; that
-- dissolution is recorded in notes/CancelRShiftWall.agda.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; _×_; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary
open import strong-rep-store.Terms
open import strong-rep-store.Reduction
open import strong-rep-store.TypeCheck using (tc; int!; conv!; sq!; tr)
open import strong-rep-store.Eval
  using (eval; traceEnd; traceCtx; eval-run; Reaches; reaches; reaches-run)

------------------------------------------------------------------------
-- 0. The route, in four identities
------------------------------------------------------------------------

-- Everything the header claims about HOW a bare `seal` reaches a frame
-- that binds is definitional, so it is checked rather than asserted.

-- the leaf `TyBeta` mints at the argument type `∀Z. Z ⇒ X`
conceal-at-∀-over-X : conceal 0 (`∀ (` 0 ⇒ ` 1)) ≡ `∀ (id (` 0) ↦ seal 1)
conceal-at-∀-over-X = refl

-- `TyPeelR`'s mint does not touch a `seal` leaf …
seal-survives-instReveal : ∀ {X Y} → instReveal X (seal Y) ≡ seal Y
seal-survives-instReveal = refl

-- … and the scope it lands on is read at a store with ONE MORE CELL:
-- `inst` names the freshly allocated address 0 and pushes the
-- crossed scope's own changes underneath it, in both universes.  (This
-- is what `numBinds (inst R Θ) ≡ suc (numBinds Θ)` said before
-- the store moved the bind onto the ambient context.)
inst-names-the-cell :
  inst [] ≡ (unlock 0 0 ∷ [])
inst-names-the-cell = refl

-- whereas `Peel`'s ARGUMENT frame — the one the wall module looked at —
-- changes no store at all.  Since experiment 2 NO boundary does: a
-- boundary changes NAMES only, which is `interior-reps`.
dual-keeps-the-store : ∀ {Θ Δ Δᵢ}
  → Δ ⊢ⁱ dual Θ ⇒ Δᵢ → reps Δᵢ ≡ reps Δ
dual-keeps-the-store = interior-reps

------------------------------------------------------------------------
-- 1. The source program — closed, plain, boundary-free
------------------------------------------------------------------------

--   Inner = ΛX. λf:(∀Z. Z ⇒ X). (f [ℕ]) · 7        : ∀X. (∀Z. Z⇒X) ⇒ X
--   Outer = ΛP. λp:P. (Inner [P]) · (ΛZ. λz:Z. p)  : ∀P. P ⇒ P
--   Src   = (Outer [ℕ]) · 7                        : ℕ
--
-- THE TWO INGREDIENTS, one per conjunct of the defect.
--
--   (i)  `Inner`'s argument has type `∀Z. Z ⇒ X` — polymorphic, and
--        RETURNING the abstracted variable.  `TyBeta` therefore conceals
--        at `X` UNDER a `∀` and to the RIGHT of an `⇒`, which is the one
--        way a `seal` leaf reaches the codomain of a `↦` under a `` `∀ ``.
--        `f [ℕ]` then fires `TyPeelR-Λ` (carrying that leaf onto a scope
--        that unlocks a freshly allocated cell) and `· 7` fires `Peel`
--        (installing it as the boundary's own conversion).  That is the
--        name-map disagreement of §5 (i) — before the store,
--        `numBinds Θ₁ ≡ 1`.
--
--   (ii) `Inner` is instantiated at `P`, an ENCLOSING `Λ`'s variable, so
--        the binder `CancelR` cancels has a representation VARIABLE for
--        its payload.  That is the OPEN representation.
--
-- Drop either one and the run completes even under the OLD rule — §6, and
-- the hunt log in notes/CancelRReachability.md.

Inner Outer Src : Term
Inner = Λ (ƛ (`∀ (` 0 ⇒ ` 1)) ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , `ℕ ]) · ($ 7)))
Outer = Λ (ƛ (` 0) ∙
             ((Inner ·[ (`∀ (` 0 ⇒ ` 1)) ⇒ ` 0 , ` 0 ])
                · (Λ (ƛ ` 0 ∙ (` 1)))))
Src   = (Outer ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

Src-⊢ : empty ∣ [] ⊢ Src ⦂ `ℕ
Src-⊢ = tc

------------------------------------------------------------------------
-- 2. AFTER — the complete, fully checked run
------------------------------------------------------------------------

-- THE HEADLINE.  With repair (a) installed, the program runs to a value
-- and no state loses the type.  `Reaches k n ⊢M V` says: with fuel k the
-- evaluator reaches V in exactly n steps, V is a value, and every
-- intermediate state type checked at `ℕ`.
--
-- The tail past the repaired `CancelR` is three `IdPush`es, a second
-- `CancelR`, and the `Drop$` tower.  Under the OLD rule step 10 was
-- recorded `illtyped` and the raw machine stuck at sixteen
-- (notes/RawRunProbe.agda).
Src-eval : Reaches 14 14 Src-⊢ ($ 7)
Src-eval = reaches refl V-$

Src-run : empty ⊢ Src -→* $ 7
Src-run = reaches-run Src-eval

------------------------------------------------------------------------
-- 3. The `CancelR` state the run still reaches, and what it produces now
------------------------------------------------------------------------

-- The first nine rules that fire are untouched by the repair:
--
--   TyBeta, Peel, Beta, TyBeta, Peel, Beta, TyPeelR-Λ, Peel, Beta,
--   and then CancelR.
--
-- Rendered (strong-rep-store.Show; α is a representation variable, X the
-- ordinary name for it), the ninth state is
--
--   ((((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Z , id X ⟫)
--       ⟪ ↥Z , ↓Y , seal Y ⟫)
--      ⟪ ↥Y , unseal Y ⟫)
--     ⟪ ↥X , unseal X ⟫
--
-- with the three cells the run allocated in the AMBIENT store,
--
--   Ξ = [ γ:=ℕ , β:=α , α:=ℕ ]
--
-- and `β:=α` is the OPEN payload: the binder `Y` names is represented by
-- the representation VARIABLE α, not by a closed type.  (Before the
-- store those three cells rode on the three frames, as `↑γ:=ℕ`,
-- `↑β:=α`, `↑α:=ℕ`.)

Θout Θ₁ Θ₂ : Boundary
Θout = (unlock 0 2 ∷ [])
Θ₁   = (lock 1 1 ∷ unlock 0 0 ∷ [])
Θ₂   = (unlock 0 1 ∷ [])

-- the cancelled value: 7 under two lock-only, bind-free layers
Vcr : Term
Vcr = (($ 7) ⟪ (lock 0 2 ∷ []) , seal 0 ⟫)
        ⟪ (lock 0 0 ∷ []) , id (` 1) ⟫

Redex Contractum : Term
Redex      = ((Vcr ⟪ Θ₁ , seal 1 ⟫) ⟪ Θ₂ , unseal 0 ⟫) ⟪ Θout , unseal 0 ⟫
Contractum = (Vcr ⟪ Θ₁ ++ Θ₂ , mkId (` 2) ⟫) ⟪ Θout , unseal 0 ⟫

-- what `eval` actually produces, at nine steps and at ten.  THE INNER
-- SPELLING IS THE WHOLE REPAIR: `mkId (` 2)`, the SHIFTED reading, where
-- the old rule minted `mkId (` 1)`.
redex-is-state-9 : traceEnd (eval 9 Src Src-⊢) ≡ Redex
redex-is-state-9 = refl

contractum-is-state-10 : traceEnd (eval 10 Src Src-⊢) ≡ Contractum
contractum-is-state-10 = refl

-- REACHABILITY, in the object language's own relation
src-→*-redex : empty ⊢ Src -→* Redex
src-→*-redex = eval-run 9 Src-⊢ redex-is-state-9

src-→*-contractum : empty ⊢ Src -→* Contractum
src-→*-contractum = eval-run 10 Src-⊢ contractum-is-state-10

------------------------------------------------------------------------
-- 4. The contexts the run built
------------------------------------------------------------------------

-- `Δ₉₀` is the context the RUN is at after nine steps: three cells
-- allocated, no ordinary name live at the top level.  (Before the store
-- it was `empty` throughout, because every cell rode on a frame.)
Δ₉₀ : Ctxᵗ
Δ₉₀ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ []

Δ₉₀-is-run-ctx : traceCtx (eval 9 Src Src-⊢) ≡ Δ₉₀
Δ₉₀-is-run-ctx = refl

-- `Δ₉` is the ambient of the `CancelR` — the interior of the outermost
-- boundary, the only one the redex sits inside.
Δ₉ : Ctxᵗ
Δ₉ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (2 ∷ [])

Δ₉-is-interior : proj₁ (int! Δ₉₀ Θout) ≡ Δ₉
Δ₉-is-interior = refl

-- `Δᶜ` is `Θ₂`'s conversion context, where the OUTER binder is read.
-- IT IS THE WALL'S `Δ*` ON THE NOSE (notes/CancelRShiftWall §1): a
-- store whose cell 1 is represented by a representation VARIABLE.
Δᶜ : Ctxᵗ
Δᶜ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (1 ∷ 2 ∷ [])

Δᶜ-is-conversion : proj₁ (conv! Δ₉ Θ₂) ≡ Δᶜ
Δᶜ-is-conversion = refl

-- `Δᵢ` is `Θ₂`'s INTERIOR, and `Δ₁ᶜ` is Θ₁'s conversion context read from
-- it.  These two are the readings repair (a) added to the rule, and the
-- second is where the cancelled seal's source is spelled.
Δᵢ Δ₁ᶜ : Ctxᵗ
Δᵢ  = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (1 ∷ 2 ∷ [])
Δ₁ᶜ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ 2 ∷ [])

Δᵢ-is-interior : proj₁ (int! Δ₉ Θ₂) ≡ Δᵢ
Δᵢ-is-interior = refl

Δ₁ᶜ-is-conversion : proj₁ (conv! Δᵢ Θ₁) ≡ Δ₁ᶜ
Δ₁ᶜ-is-conversion = refl

-- `Δᵣ` is where the INNER of the two minted layers sits: the interior of
-- the outer frame `rewind Θ₂`.  WITH THE STORE IT IS `Δ₉` ITSELF —
-- a rewound scope returns to its exterior and there is no bind block
-- left for it to sit inside (`rewind-interior`).
Δᵣ : Ctxᵗ
Δᵣ = Δ₉

Δᵣ-is-interior : proj₁ (int! Δ₉ (rewind Θ₂)) ≡ Δᵣ
Δᵣ-is-interior = refl

-- `Δ⋉ᶜ` is the merged frame's conversion context, read at `Δ₉` itself
-- (the rule's premise lost its `extendReps (binds Θ₂)` prefix with the
-- bind block) — and on this run it coincides with `Δ₁ᶜ`.
Δ⋉ᶜ : Ctxᵗ
Δ⋉ᶜ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ 2 ∷ [])

Δ⋉ᶜ-is-conversion : proj₁ (conv! Δ₉ (Θ₁ ++ Θ₂)) ≡ Δ⋉ᶜ
Δ⋉ᶜ-is-conversion = refl

------------------------------------------------------------------------
-- 5. The state IS a `CancelR` redex, BOTH conjuncts hold, and the
--    repaired premises deliver the SHIFTED spelling
------------------------------------------------------------------------

-- (i) THE TWO LAYERS ARE READ AT DIFFERENT NAME MAPS.  Before the store
-- this was `numBinds Θ₁ ≡ 1` — Θ₁'s conversion context lay one bind
-- block inside Θ₂'s.  The bind block is gone; the DISAGREEMENT is not.
-- Θ₁'s own conversion context holds one more ordinary name than Θ₂'s,
-- so the same representation has two different spellings there.
conjunct-i : names Δ₁ᶜ ≢ names Δᶜ
conjunct-i ()

-- (ii) THE CANCELLED BINDER'S REPRESENTATION IS OPEN.  The lookup
-- `Δᶜ ∋ 0 := A` returns `A ≡ ` 1`, whose representation is the VARIABLE
-- `` ` 2 `` (cell 1 of the store holds `bindR (` 0)`), not a closed type.
lookup-A : Δᶜ ∋ 0 := ` 1
lookup-A = proj₂ (sq! Δᶜ 0)

conjunct-ii-rep : Δᶜ ⊢ᶜ ` 1 ~ ` 2
conjunct-ii-rep = tr

-- THE PREMISES, and the step.  Nothing is assumed: each premise is
-- produced by the checker at the contexts §4 pinned.
cancel-int : Δ₉ ⊢ⁱ Θ₂ ⇒ Δᵢ
cancel-int = proj₂ (int! Δ₉ Θ₂)

cancel-Θ₁ : Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
cancel-Θ₁ = proj₂ (conv! Δᵢ Θ₁)

cancel-⋉ : Δ₉ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
cancel-⋉ = proj₂ (conv! Δ₉ (Θ₁ ++ Θ₂))

cancel-Θ₂ : Δ₉ ⊢ᶜ Θ₂ ⇒ Δᶜ
cancel-Θ₂ = proj₂ (conv! Δ₉ Θ₂)

-- THE PREMISE THE REPAIR CHANGED.  The cancelled `seal 1`'s SOURCE, read
-- where that conversion is typed, is `` ` 2 ``.  The old rule read
-- `` ` 1 `` at `Δᶜ` instead, and delivered `A′ ≡ ` 1`.
seal-source : Δ₁ᶜ ∋ 1 := ` 2
seal-source = proj₂ (sq! Δ₁ᶜ 1)

cancel-same : Δ⋉ᶜ ⊢ ` 2 ≈ ` 2 ⊣ Δ₁ᶜ
cancel-same = ` 2 , tr , tr

-- and `` ` 2 `` at `Δ⋉ᶜ` denotes exactly the representation the cancelled
-- binder has …
repaired-denotes : Δ⋉ᶜ ⊢ᶜ ` 2 ~ ` 2
repaired-denotes = tr

-- … and the OUTER layer's `A ≡ ` 1` is a DIFFERENT SPELLING of that one
-- representation, because it is read at a different name map: at `Δᶜ`
-- the cancelled binder sits at position 1, at `Δ⋉ᶜ` at position 2.  Two
-- spellings, one cell — which is why the rule carries a premise at all.
two-spellings : names Δ⋉ᶜ ≢ names Δᶜ
two-spellings ()

outer-spelling-denotes : Δᶜ ⊢ᶜ ` 1 ~ ` 2
outer-spelling-denotes = tr

inner-spelling-denotes : Δ⋉ᶜ ⊢ᶜ ` 2 ~ ` 2
inner-spelling-denotes = tr

cancel-value : Value Vcr
cancel-value = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv

cancel-step : Δ₉ ⊢ (Vcr ⟪ Θ₁ , seal 1 ⟫) ⟪ Θ₂ , unseal 0 ⟫
  -→ Vcr ⟪ Θ₁ ++ Θ₂ , mkId (` 2) ⟫ ∣ none
cancel-step =
  CancelR cancel-value cancel-int cancel-Θ₁ seal-source
          cancel-⋉ cancel-same

-- and the same step where the run takes it, under the outermost boundary
-- and at the context the run has reached
redex-step : Δ₉₀ ⊢ Redex -→ Contractum ∣ none
redex-step = ξ-⟪⟫ (proj₂ (int! Δ₉₀ Θout)) cancel-step

------------------------------------------------------------------------
-- 6. THE TWO CONTROLS — each conjunct alone was always harmless
------------------------------------------------------------------------

-- Removing either ingredient of §1 gives a program that reaches a
-- `CancelR` and RUNS TO A VALUE with no state losing its type — and did
-- so under the OLD rule too.  So it was the CONJUNCTION that broke
-- preservation, and the witness above is not an accident of the shape.
-- Both step counts are unchanged by the repair, which is the local
-- no-regression check.

-- CONTROL A — conjunct (i) only.  `Inner` instantiated at `ℕ` instead of
-- at an enclosing `Λ`'s variable.  Its `CancelR` still has
-- `numBinds Θ₁ ≡ 1` (the frame `↑β:=ℕ`), but the payload is CLOSED, so
-- `shiftBy 1` is invisible.
CtrlA : Term
CtrlA = (Inner ·[ (`∀ (` 0 ⇒ ` 1)) ⇒ ` 0 , `ℕ ]) · (Λ (ƛ ` 0 ∙ ($ 5)))

CtrlA-⊢ : empty ∣ [] ⊢ CtrlA ⦂ `ℕ
CtrlA-⊢ = tc

CtrlA-eval : Reaches 8 8 CtrlA-⊢ ($ 5)
CtrlA-eval = reaches refl V-$

CtrlA-run : empty ⊢ CtrlA -→* $ 5
CtrlA-run = reaches-run CtrlA-eval

-- CONTROL B — conjunct (ii) only.  The same enclosing `Λ` and the same
-- `[P]`, so the cancelled binder's payload is still the representation
-- VARIABLE α; but the crossing argument is FIRST ORDER (`ℕ ⇒ X`), so no
-- `TyPeelR` fires, the `seal` stays on the `Peel` dual frame, and the
-- `CancelR` has `numBinds Θ₁ ≡ 0`.
Inner′ Outer′ CtrlB : Term
Inner′ = Λ (ƛ (`ℕ ⇒ ` 0) ∙ ((` 0) · ($ 7)))
Outer′ = Λ (ƛ (` 0) ∙
              ((Inner′ ·[ (`ℕ ⇒ ` 0) ⇒ ` 0 , ` 0 ]) · (ƛ `ℕ ∙ (` 1))))
CtrlB  = (Outer′ ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

CtrlB-⊢ : empty ∣ [] ⊢ CtrlB ⦂ `ℕ
CtrlB-⊢ = tc

CtrlB-eval : Reaches 13 13 CtrlB-⊢ ($ 7)
CtrlB-eval = reaches refl V-$

CtrlB-run : empty ⊢ CtrlB -→* $ 7
CtrlB-run = reaches-run CtrlB-eval
