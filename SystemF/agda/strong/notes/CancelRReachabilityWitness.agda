module strong.notes.CancelRReachabilityWitness where

-- File Charter:
--   * THE REACHABILITY ANSWER for the `CancelR` defect of
--     notes/CancelRShiftWall.agda (Jeremy's question, 2026-09-19: "do you
--     have an example source program that reduces to the problematic
--     configuration?").  YES.
--   * One CLOSED, PLAIN System F program — no boundary, no morphism, no
--     conversion anywhere in the source — reduces in NINE steps to a
--     `CancelR` redex whose inner frame BINDS a representation variable
--     (`numBinds Θ₁ ≡ 1`) and whose cancelled binder's representation is
--     OPEN (`` ` 1 ``, a representation VARIABLE).  The tenth step is the
--     `CancelR`, and its contractum has NO typing derivation.
--   * Everything here is observed, not designed: the redex, its frames and
--     its contexts are read off `eval`, and §2 pins them by `refl`.
--   * NOTHING IS REPAIRED.  A rule change is Jeremy's call.  §6 records,
--     machine-checked, that the SHIFTED spelling the wall module proposes
--     as repair (a) retypes this very contractum.
--
-- WHERE THE WALL'S REASONING WAS TOO NARROW.  notes/CancelRShiftWall says
-- a bare `seal X` conversion "is minted by exactly one rule — `Peel`, on
-- the crossing ARGUMENT — whose frame is `dualMorph Θ`", and
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
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; _×_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
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
  using (eval; traceEnd; eval-run; report; reported; Reaches; reaches;
         reaches-run)

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
-- Drop either one and the run completes — §7, and the hunt log in
-- notes/CancelRReachability.md.

Inner Outer Src : Term
Inner = Λ (ƛ (`∀ (` 0 ⇒ ` 1)) ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , `ℕ ]) · ($ 7)))
Outer = Λ (ƛ (` 0) ∙
             ((Inner ·[ (`∀ (` 0 ⇒ ` 1)) ⇒ ` 0 , ` 0 ])
                · (Λ (ƛ ` 0 ∙ (` 1)))))
Src   = (Outer ·[ ` 0 ⇒ ` 0 , `ℕ ]) · ($ 7)

Src-⊢ : empty ∣ [] ⊢ Src ⦂ `ℕ
Src-⊢ = tc

------------------------------------------------------------------------
-- 2. The state reduction reaches, and the state the next step produces
------------------------------------------------------------------------

-- The rules that fire, in order, are
--
--   TyBeta, Peel, Beta, TyBeta, Peel, Beta, TyPeelR-Λ, Peel, Beta,
--   and then CancelR, which loses the type.
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
Contractum = ((Vcr ⟪ Θ₁ ⋉ Θ₂ , mkId (` 1) ⟫) ⟪ rewind Θ₂ , mkId (` 1) ⟫)
               ⟪ Θout , unseal 0 ⟫

-- what `eval` actually produced, at nine steps and at ten
redex-is-state-9 : traceEnd (eval 9 Src Src-⊢) ≡ Redex
redex-is-state-9 = refl

contractum-is-state-10 : traceEnd (eval 10 Src Src-⊢) ≡ Contractum
contractum-is-state-10 = refl

-- REACHABILITY, in the object language's own relation
src-→*-redex : empty ⊢ Src -→* Redex
src-→*-redex = eval-run 9 Src-⊢ redex-is-state-9

src-→*-contractum : empty ⊢ Src -→* Contractum
src-→*-contractum = eval-run 10 Src-⊢ contractum-is-state-10

-- AND `eval` RECORDS IT AS A BREAK.  `report` returns `false` exactly
-- when some state lost the type; the `true` a `Reaches` asserts is
-- therefore unavailable for this run at any fuel past nine.
eval-broke-at-step-10 :
  report (eval 10 Src Src-⊢) ≡ reported Contractum 10 false
eval-broke-at-step-10 = refl

------------------------------------------------------------------------
-- 3. The contexts the run built
------------------------------------------------------------------------

-- `Δ₉` is the ambient of the `CancelR` — the interior of the outermost
-- boundary, the only one the redex sits inside.
Δ₉ : Ctxᵗ
Δ₉ = (bindR `ℕ ∷ []) ∣ (0 ∷ [])

Δ₉-is-interior : proj₁ (int! empty Θout) ≡ Δ₉
Δ₉-is-interior = refl

-- `Δᶜ` is `Θ₂`'s conversion context, where the cancelled binder is read.
-- IT IS THE WALL'S `Δ*` ON THE NOSE (notes/CancelRShiftWall §1): a
-- representation context whose slot 0 is represented by slot 1.
Δᶜ : Ctxᵗ
Δᶜ = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

Δᶜ-is-conversion : proj₁ (conv! Δ₉ Θ₂) ≡ Δᶜ
Δᶜ-is-conversion = refl

-- `Δᵣ` is where the INNER of the two minted layers sits: the interior of
-- the outer frame `rewind Θ₂`, which is `Δ₉` under `Θ₂`'s bind block.
Δᵣ : Ctxᵗ
Δᵣ = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (1 ∷ [])

Δᵣ-is-interior : proj₁ (int! Δ₉ (rewind Θ₂)) ≡ Δᵣ
Δᵣ-is-interior = refl

Δᵣ-is-extendReps : extendReps (binds Θ₂) Δ₉ ≡ Δᵣ
Δᵣ-is-extendReps = refl

-- `Δ⋉ᶜ` is the merged frame's conversion context, one bind block inside.
Δ⋉ᶜ : Ctxᵗ
Δ⋉ᶜ = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ 2 ∷ [])

Δ⋉ᶜ-is-conversion : proj₁ (conv! Δᵣ (Θ₁ ⋉ Θ₂)) ≡ Δ⋉ᶜ
Δ⋉ᶜ-is-conversion = refl

------------------------------------------------------------------------
-- 4. The state IS a `CancelR` redex, and BOTH conjuncts hold
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
-- produced by the checker at the contexts §3 pinned.
cancel-⋉ : Δᵣ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
cancel-⋉ = proj₂ (conv! Δᵣ (Θ₁ ⋉ Θ₂))

cancel-Θ₂ : Δ₉ ⊢ᶜ Θ₂ ⇒ Δᶜ
cancel-Θ₂ = proj₂ (conv! Δ₉ Θ₂)

-- THE PREMISE AT ISSUE, read the way the rule states it: `A′` denotes the
-- SAME representation as `A`, not the shifted one.
cancel-same : SameTy Δ⋉ᶜ (` 1) Δᶜ (` 1)
cancel-same = ` 1 , tr , tr

cancel-value : Value Vcr
cancel-value = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-idv

cancel-step : Δ₉ ⊢ (Vcr ⟪ Θ₁ , seal 1 ⟫) ⟪ Θ₂ , unseal 0 ⟫
  -→ (Vcr ⟪ Θ₁ ⋉ Θ₂ , mkId (` 1) ⟫) ⟪ rewind Θ₂ , mkId (` 1) ⟫
cancel-step = CancelR cancel-value cancel-⋉ cancel-same cancel-Θ₂ lookup-A

-- and the same step where the run takes it, under the outermost boundary
redex-step : empty ⊢ Redex -→ Contractum
redex-step = ξ-⟪⟫ (proj₂ (int! empty Θout)) cancel-step

------------------------------------------------------------------------
-- 5. The contractum has NO typing derivation
------------------------------------------------------------------------

-- The argument is the wall's, now at a REACHED configuration.  The outer
-- layer's `mkId (` 1)` pins the inner boundary's exterior type to the
-- representation `` ` 1 ``; the inner `env`'s `SameTyExt 1` then asks the
-- inner conversion's type to denote `shiftRep 1 (` 1) ≡ ` 2`, while the
-- inner `mkId (` 1)` denotes `` ` 1 `` at `Δ⋉ᶜ`.  A representation
-- reading is unique (`same-rep-unique`), and `` ` 1 ≢ ` 2 ``.
--
-- The refutation needs only the TWO layers `CancelR` minted, so it is
-- stated for an ARBITRARY exterior type: no choice of type for the pair
-- makes it typeable.

-- WHAT THE OUTER LAYER SAYS.  `` ` 1 `` names representation `` ` 1 ``
-- at `Δᶜ`, and nothing else can.
rep-of-1-at-Δᶜ : ∀ {R} → Δᶜ ⊢ᶜ ` 1 ~ R → R ≡ ` 1
rep-of-1-at-Δᶜ (same-var (there here)) = refl

-- WHAT THE INNER LAYER CANNOT SAY.  At `Δ⋉ᶜ` the name `` ` 1 `` still
-- denotes representation `` ` 1 ``, never the shifted `` ` 2 ``.  This is
-- the whole defect: the inner boundary's `SameTyExt 1` asks for `` ` 2 ``.
no-1-denotes-2 : ¬ (Δ⋉ᶜ ⊢ᶜ ` 1 ~ ` 2)
no-1-denotes-2 (same-var (there ()))

-- The inner of the two minted layers, at the exterior type the outer one
-- forces on it: `B` denotes `` ` 1 ``, so `SameTyExt 1` wants `` ` 2 ``.
no-inner-layer : ∀ {B}
  → Δᵣ ∣ [] ⊢ Vcr ⟪ Θ₁ ⋉ Θ₂ , mkId (` 1) ⟫ ⦂ B
  → Δᵣ ⊢ᶜ B ~ ` 1
  → ⊥
no-inner-layer (env mw⋉ ⊢V (conv-idv tv) sameᵢ′ (R , pₑ , q) wE′) pB
  with conversion-functional (mw-conversion mw⋉) cancel-⋉
no-inner-layer (env mw⋉ ⊢V (conv-idv tv) sameᵢ′ (R , pₑ , q) wE′) pB
  | refl with same-rep-unique pₑ pB
no-inner-layer (env mw⋉ ⊢V (conv-idv tv) sameᵢ′ (R , pₑ , q) wE′) pB
  | refl | refl = no-1-denotes-2 q

no-cancel-pair : ¬ (∃[ B ]
  (Δ₉ ∣ [] ⊢
     (Vcr ⟪ Θ₁ ⋉ Θ₂ , mkId (` 1) ⟫) ⟪ rewind Θ₂ , mkId (` 1) ⟫ ⦂ B))
no-cancel-pair (B , env mwR ⊢inner (conv-idv tv) (R₀ , pᵢ , sm) sameₑ wE)
  with conversion-functional (mw-conversion mwR)
         (proj₂ (conv! Δ₉ (rewind Θ₂)))
     | interior-functional (mw-interior mwR)
         (proj₂ (int! Δ₉ (rewind Θ₂)))
no-cancel-pair (B , env mwR ⊢inner (conv-idv tv) (R₀ , pᵢ , sm) sameₑ wE)
  | refl | refl with rep-of-1-at-Δᶜ sm
no-cancel-pair (B , env mwR ⊢inner (conv-idv tv) (R₀ , pᵢ , sm) sameₑ wE)
  | refl | refl | refl = no-inner-layer ⊢inner pᵢ

-- and therefore the whole state the run reached is untypeable
no-contractum : ¬ (empty ∣ [] ⊢ Contractum ⦂ `ℕ)
no-contractum (env mwO ⊢pair ⊢c sameᵢ sameₑ wE)
  with interior-functional (mw-interior mwO) (proj₂ (int! empty Θout))
no-contractum (env mwO ⊢pair ⊢c sameᵢ sameₑ wE) | refl =
  no-cancel-pair (_ , ⊢pair)

------------------------------------------------------------------------
-- 6. THE SHIFTED SPELLING RETYPES IT — repair (a), on this example
------------------------------------------------------------------------

-- notes/CancelRShiftWall proposes carrying the re-spelling premise against
-- the INNER boundary's own conversion context: `SameTy Δ⋉ᶜ A′ Δ₁ᶜ Aᵢ`,
-- with `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ` a new premise and `Aᵢ` the SOURCE of the
-- cancelled `seal X`.  On this run those are
--
--   Δᵢ  = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])   -- int Θ₂ Δ₉
--   Δ₁ᶜ = Δ⋉ᶜ                                            -- conv Θ₁ Δᵢ
--   Aᵢ  = ` 2                                            -- Δ₁ᶜ ∋ 1 := Aᵢ
--
-- so the repaired premise delivers `A′ ≡ ` 2` where the rule as stated
-- delivers `A′ ≡ ` 1`.  Both facts are checked here, and the contractum
-- built with `mkId (` 2)` IS well typed.

Δᵢ Δ₁ᶜ : Ctxᵗ
Δᵢ  = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
Δ₁ᶜ = Δ⋉ᶜ

Δᵢ-is-interior : proj₁ (int! Δ₉ Θ₂) ≡ Δᵢ
Δᵢ-is-interior = refl

Δ₁ᶜ-is-conversion : proj₁ (conv! Δᵢ Θ₁) ≡ Δ₁ᶜ
Δ₁ᶜ-is-conversion = refl

-- the source of the cancelled `seal 1`, read where that conversion is
-- typed: `` ` 2 ``, the SHIFTED spelling
seal-source : Δ₁ᶜ ∋ 1 := ` 2
seal-source = proj₂ (sq! Δ₁ᶜ 1)

-- the repaired premise, satisfied with `A′ ≡ ` 2`
repaired-reading : SameTy Δ⋉ᶜ (` 2) Δ₁ᶜ (` 2)
repaired-reading = ` 2 , tr , tr

-- and `` ` 2 `` at `Δ⋉ᶜ` denotes exactly what the inner `env` asked for:
-- `shiftRep 1` of the representation `` ` 1 `` denotes at `Δᶜ`
repaired-denotes : Δ⋉ᶜ ⊢ᶜ ` 2 ~ shiftRep 1 (` 1)
repaired-denotes = tr

RepairedContractum : Term
RepairedContractum =
  ((Vcr ⟪ Θ₁ ⋉ Θ₂ , mkId (` 2) ⟫) ⟪ rewind Θ₂ , mkId (` 1) ⟫)
    ⟪ Θout , unseal 0 ⟫

repaired-⊢ : empty ∣ [] ⊢ RepairedContractum ⦂ `ℕ
repaired-⊢ = tc

-- NOT INSTALLED.  `strong.Reduction` is unchanged; `redex-step` above is
-- the rule as it stands, and §5 refutes its contractum.

------------------------------------------------------------------------
-- 7. THE TWO CONTROLS — each conjunct alone is harmless
------------------------------------------------------------------------

-- Removing either ingredient of §1 gives a program that reaches a
-- `CancelR` and RUNS TO A VALUE with no state losing its type.  So it is
-- the CONJUNCTION that breaks preservation, exactly as the wall module
-- says, and the witness above is not an accident of the shape.

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
