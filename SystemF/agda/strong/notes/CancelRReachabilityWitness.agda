module strong.notes.CancelRReachabilityWitness where

-- File Charter:
--   * THE BEFORE/AFTER RECORD of the `CancelR` defect and its repair.
--   * BEFORE (2026-09-19, morning).  This module answered Jeremy's
--     question — "do you have an example source program that reduces to
--     the problematic configuration?" — with YES.  One CLOSED, PLAIN
--     System F program (no boundary, no morphism, no conversion anywhere
--     in the source) reduces in NINE steps to a `CancelR` redex whose
--     inner frame BINDS a representation variable (`numBinds Θ₁ ≡ 1`) and
--     whose cancelled binder's representation is OPEN.  Under the OLD
--     rule the tenth step lost the type — `eval` recorded it as
--     `illtyped` — and the raw machine then STUCK after sixteen steps at
--     a non-value identity tower.  That closed repair path (b), the
--     invariant `numBinds Θ₁ ≡ 0`: it is false at a reachable redex.
--   * AFTER (2026-09-19, same day).  Repair (a) was approved by Jeremy
--     and installed in `strong.Reduction`.  The first nine steps are
--     unchanged; the tenth now mints `mkId (` 2)` where it minted
--     `mkId (` 1)`, and the run COMPLETES: `Src-eval` below is
--     `Reaches 19 19 Src-⊢ ($ 7)`, every state along the way type
--     checked.  The two controls are unchanged.
--   * The BEFORE half is now prose, not Agda: its equations were stated
--     against a constructor that no longer exists.  What made them true —
--     the shift incompatibility, and the old statement refuted against a
--     local copy of itself — is kept machine-checked in
--     `notes/CancelRShiftWall.agda`, and the narrative is
--     notes/DECISIONS.md (2026-09-19) and notes/CancelRReachability.md.
--   * Everything below is observed, not designed: the redex, its frames
--     and its contexts are read off `eval` and pinned by `refl`.
--
-- WHERE THE WALL'S UNREACHABILITY ARGUMENT WENT WRONG.  It said a bare
-- `seal X` conversion "is minted by exactly one rule — `Peel`, on the
-- crossing ARGUMENT — whose frame is `dualMorph Θ`", and
-- `binds (dualMorph Θ) ≡ []`.  `Peel` mints TWO boundaries, and only the
-- argument's carries the dual:
--
--       Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
--         -→ (V · (… ⟪ dualMorph Θ , s′ ⟫)) ⟪ Θ , t ⟫
--                   ^^^^^^^^^^^^^ binds nothing     ^^^ the ORIGINAL frame
--
-- The RESULT boundary keeps `Θ` and takes the CODOMAIN `t`.  If `t` is a
-- bare `seal`, that is a bare `seal` on whatever `Θ` binds.  And `Θ` binds
-- when the boundary was minted by `TyPeelR`: its conversion is
-- `instReveal 0 s` on `instantiate R Θ₀`, and
-- `instReveal X (seal Y) ≡ seal Y`, so a `seal` leaf of the crossed
-- `∀`-conversion survives onto a frame with `suc (numBinds Θ₀)` binds.
--
-- Both fire in this run, in that order (steps 7 and 8).  The `seal` leaf
-- itself is `TyBeta`'s `conceal 0` at the argument type `∀Z. Z ⇒ X`:
-- `conceal 0 (`∀ (` 0 ⇒ ` 1)) ≡ `∀ (id (` 0) ↦ seal 1)`.  No program in
-- the twelve-run suite or in `strong.Examples` passes a `∀Z. … ⇒ X` — an
-- argument whose polymorphic type RETURNS the abstracted variable — so no
-- run ever produced the leaf.
--
-- AND WHY THE OPEN REPRESENTATION.  The instantiation that mints the
-- cancelled binder is at a type VARIABLE of an ENCLOSING `Λ` (`[P]`, not
-- `[ℕ]`), which is what `strong.Examples` §1c already does for `IdPush`.
-- Its payload is then a representation VARIABLE, and `shiftBy 1` moves it.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; _×_; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.Reduction
open import strong.TypeCheck using (tc; int!; conv!; sq!; tr)
open import strong.Eval
  using (eval; traceEnd; eval-run; Reaches; reaches; reaches-run)

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

-- … and the frame it lands on binds one more than the frame it crossed
numBinds-instantiate : ∀ {R Θ}
  → numBinds (instantiate R Θ) ≡ suc (numBinds Θ)
numBinds-instantiate = refl

-- whereas `Peel`'s ARGUMENT frame — the one the wall module looked at —
-- binds nothing
numBinds-dual : ∀ {Θ} → numBinds (dualMorph Θ) ≡ 0
numBinds-dual = refl

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
--        `f [ℕ]` then fires `TyPeelR-Λ` (carrying that leaf onto a frame
--        that binds) and `· 7` fires `Peel` (installing it as the
--        boundary's own conversion).  That is `numBinds Θ₁ ≡ 1`.
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
Src-eval : Reaches 19 19 Src-⊢ ($ 7)
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
-- Rendered (strong.Show; α is a representation variable, X the ordinary
-- name for it), the ninth state is
--
--   ((((7 ⟪ ↓X , seal X ⟫) ⟪ ↓Z , id X ⟫)
--       ⟪ ↑γ:=ℕ , ↥Z , ↓Y , seal Y ⟫)
--      ⟪ ↑β:=α , ↥Y , unseal Y ⟫)
--     ⟪ ↑α:=ℕ , ↥X , unseal X ⟫
--
-- and `↑β:=α` is the OPEN payload: the binder `Y` names is represented by
-- the representation VARIABLE α, not by a closed type.

Θout Θ₁ Θ₂ : CtxMorph
Θout = morph (`ℕ ∷ []) (unlock 0 0 ∷ [])
Θ₁   = morph (`ℕ ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
Θ₂   = morph (` 0 ∷ []) (unlock 0 0 ∷ [])

-- the cancelled value: 7 under two lock-only, bind-free layers
Vcr : Term
Vcr = (($ 7) ⟪ morph [] (lock 0 2 ∷ []) , seal 0 ⟫)
        ⟪ morph [] (lock 0 0 ∷ []) , id (` 1) ⟫

Redex Contractum : Term
Redex      = ((Vcr ⟪ Θ₁ , seal 1 ⟫) ⟪ Θ₂ , unseal 0 ⟫) ⟪ Θout , unseal 0 ⟫
Contractum = ((Vcr ⟪ Θ₁ ⋉ Θ₂ , mkId (` 2) ⟫) ⟪ rewind Θ₂ , mkId (` 1) ⟫)
               ⟪ Θout , unseal 0 ⟫

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

-- `Δ₉` is the ambient of the `CancelR` — the interior of the outermost
-- boundary, the only one the redex sits inside.
Δ₉ : Ctxᵗ
Δ₉ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])

Δ₉-is-interior : proj₁ (int! empty Θout) ≡ Δ₉
Δ₉-is-interior = refl

-- `Δᶜ` is `Θ₂`'s conversion context, where the OUTER binder is read.
-- IT IS THE WALL'S `Δ*` ON THE NOSE (notes/CancelRShiftWall §1): a
-- representation context whose slot 0 is represented by slot 1.
Δᶜ : Ctxᵗ
Δᶜ = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

Δᶜ-is-conversion : proj₁ (conv! Δ₉ Θ₂) ≡ Δᶜ
Δᶜ-is-conversion = refl

-- `Δᵢ` is `Θ₂`'s INTERIOR, and `Δ₁ᶜ` is Θ₁'s conversion context read from
-- it.  These two are the readings repair (a) added to the rule, and the
-- second is where the cancelled seal's source is spelled.
Δᵢ Δ₁ᶜ : Ctxᵗ
Δᵢ  = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
Δ₁ᶜ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ 2 ∷ [])

Δᵢ-is-interior : proj₁ (int! Δ₉ Θ₂) ≡ Δᵢ
Δᵢ-is-interior = refl

Δ₁ᶜ-is-conversion : proj₁ (conv! Δᵢ Θ₁) ≡ Δ₁ᶜ
Δ₁ᶜ-is-conversion = refl

-- `Δᵣ` is where the INNER of the two minted layers sits: the interior of
-- the outer frame `rewind Θ₂`, which is `Δ₉` under `Θ₂`'s bind block.
Δᵣ : Ctxᵗ
Δᵣ = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (1 ∷ [])

Δᵣ-is-interior : proj₁ (int! Δ₉ (rewind Θ₂)) ≡ Δᵣ
Δᵣ-is-interior = refl

Δᵣ-is-extendReps : extendReps (binds Θ₂) Δ₉ ≡ Δᵣ
Δᵣ-is-extendReps = refl

-- `Δ⋉ᶜ` is the merged frame's conversion context, one bind block inside —
-- and on this run it coincides with `Δ₁ᶜ`.
Δ⋉ᶜ : Ctxᵗ
Δ⋉ᶜ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ 2 ∷ [])

Δ⋉ᶜ-is-conversion : proj₁ (conv! Δᵣ (Θ₁ ⋉ Θ₂)) ≡ Δ⋉ᶜ
Δ⋉ᶜ-is-conversion = refl

------------------------------------------------------------------------
-- 5. The state IS a `CancelR` redex, BOTH conjuncts hold, and the
--    repaired premises deliver the SHIFTED spelling
------------------------------------------------------------------------

-- (i) THE INNER FRAME BINDS.  Every `CancelR` the twelve runs reach has
-- `numBinds Θ₁ ≡ 0`; this one does not.
conjunct-i : numBinds Θ₁ ≡ 1
conjunct-i = refl

-- (ii) THE CANCELLED BINDER'S REPRESENTATION IS OPEN.  The lookup
-- `Δᶜ ∋ 0 := A` returns `A ≡ ` 1`, and `` ` 1 `` denotes the
-- representation VARIABLE `` ` 1 `` — so `shiftRep 1` moves it.
lookup-A : Δᶜ ∋ 0 := ` 1
lookup-A = proj₂ (sq! Δᶜ 0)

conjunct-ii-rep : Δᶜ ⊢ᶜ ` 1 ~ ` 1
conjunct-ii-rep = tr

conjunct-ii-open : shiftRep 1 (` 1) ≢ ` 1
conjunct-ii-open ()

-- THE PREMISES, and the step.  Nothing is assumed: each premise is
-- produced by the checker at the contexts §4 pinned.
cancel-int : Δ₉ ⊢ⁱ Θ₂ ⇒ Δᵢ
cancel-int = proj₂ (int! Δ₉ Θ₂)

cancel-Θ₁ : Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
cancel-Θ₁ = proj₂ (conv! Δᵢ Θ₁)

cancel-⋉ : Δᵣ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
cancel-⋉ = proj₂ (conv! Δᵣ (Θ₁ ⋉ Θ₂))

cancel-Θ₂ : Δ₉ ⊢ᶜ Θ₂ ⇒ Δᶜ
cancel-Θ₂ = proj₂ (conv! Δ₉ Θ₂)

-- THE PREMISE THE REPAIR CHANGED.  The cancelled `seal 1`'s SOURCE, read
-- where that conversion is typed, is `` ` 2 `` — the SHIFTED spelling.
-- The old rule read `` ` 1 `` at `Δᶜ` instead, and delivered `A′ ≡ ` 1`.
seal-source : Δ₁ᶜ ∋ 1 := ` 2
seal-source = proj₂ (sq! Δ₁ᶜ 1)

cancel-same : Δ⋉ᶜ ⊢ ` 2 ≈ ` 2 ⊣ Δ₁ᶜ
cancel-same = ` 2 , tr , tr

-- and `` ` 2 `` at `Δ⋉ᶜ` denotes exactly what the inner `env` asks for:
-- `shiftRep 1` of the representation `` ` 1 `` denotes at `Δᶜ`
repaired-denotes : Δ⋉ᶜ ⊢ᶜ ` 2 ~ shiftRep 1 (` 1)
repaired-denotes = tr

cancel-value : Value Vcr
cancel-value = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv

cancel-step : Δ₉ ⊢ (Vcr ⟪ Θ₁ , seal 1 ⟫) ⟪ Θ₂ , unseal 0 ⟫
  -→ (Vcr ⟪ Θ₁ ⋉ Θ₂ , mkId (` 2) ⟫) ⟪ rewind Θ₂ , mkId (` 1) ⟫
cancel-step =
  CancelR cancel-value cancel-int cancel-Θ₁ seal-source
          cancel-⋉ cancel-same cancel-Θ₂ lookup-A

-- and the same step where the run takes it, under the outermost boundary
redex-step : empty ⊢ Redex -→ Contractum
redex-step = ξ-⟪⟫ (proj₂ (int! empty Θout)) cancel-step

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

CtrlA-eval : Reaches 9 9 CtrlA-⊢ ($ 5)
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

CtrlB-eval : Reaches 17 17 CtrlB-⊢ ($ 7)
CtrlB-eval = reaches refl V-$

CtrlB-run : empty ⊢ CtrlB -→* $ 7
CtrlB-run = reaches-run CtrlB-eval
