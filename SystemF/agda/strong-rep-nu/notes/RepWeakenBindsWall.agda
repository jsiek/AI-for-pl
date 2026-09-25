module strong-rep-nu.notes.RepWeakenBindsWall where

-- THE REP-WEAKENING STATEMENT NEEDED ITS BIND BLOCK (2026-09-20).
--
-- WHAT THE STORE CHANGED (experiment 2, 2026-09-22,
-- notes/RepStoreSketch.md).  `RepWeakenTyping` is RETIRED: it was the
-- bind-block weakening `Wrap`'s crossing argument consumed, and a
-- boundary no longer HAS a bind block — `dual-interior` lands the
-- argument at the exterior itself, so `Wrap` moves it verbatim
-- (strong-rep-nu.proof.WrapDual).  The one weakening left is the
-- SIBLING SHIFT `⊢renᴿ` at `ρ = suc`, whose payload premise
-- (`repwk-alloc`, `Ξ ⊢ᴿ R`) is exactly the discipline this wall argued
-- for, now carried by the allocating rule's own `Δ ⊢ᶜ A ~ R`.
--
-- The wall is therefore kept as a RECORD, with LOCAL COPIES of the
-- retired bind-block machinery (§0) so that it states what it refuted
-- and nothing else depends on it.
--
-- `RepWeakenTyping` was simplified on 2026-09-20 to read
--
--     ∀ {Δ W A} (Rs : List Ty)
--       → Δ ∣ [] ⊢ W ⦂ A
--       → extendReps Rs Δ ∣ [] ⊢ renᴹᴿ (wkN (length Rs)) W ⦂ A
--
-- and in that form it is FALSE.  `extendReps Rs Δ` pushes the payloads
-- `Rs` onto the representation context WITHOUT checking them, but a
-- boundary inside `W` has to be RETYPED at the weakened context, and the
-- `boundary` rule stores a `BoundaryWf` whose `bw-exterior` field is a `WfCtx`
-- of that context — which demands `WfRepCtx`, i.e. that every stored
-- payload be well formed where it is written.
--
-- The counterexample is as small as the development allows.  Take the
-- closed, one-boundary program `β-seven` (strong-rep-nu.Terms §5) at
-- the context `TyBeta` leaves — `allocate `ℕ empty`, whose store holds
-- the one cell — and insert the single payload `` ` 1 ``, a
-- representation variable that one-cell store does not have.  (Before
-- the store the open payload was `` ` 0 `` at `empty`; the allocation
-- moved every index up by one, which is the whole experiment in one
-- character.)  The conclusion then asks for a term to be typed at a
-- context whose head binding is `bindR (` 1)`, and
-- `bindR `ℕ ∷ [] ⊢ᴿ ` 1` has no derivation: index 1 is neither local
-- (there are no local binders) nor free (the store has one entry).
--
-- THE REPAIR was the premise `reps Δ ⊢ᴮ Rs`, discharged at the one call
-- site — `Wrap`'s crossing argument — by `bw-binds` of the very boundary
-- being crossed.  Both the premise and that field went with the bind
-- block; the surviving discipline is `repwk-alloc`'s `Ξ ⊢ᴿ R`.

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (_+_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types using (Ty; `_; `ℕ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst using (renᴹᴿ)
open import strong-rep-nu.proof.TermSubst using (wkN)

------------------------------------------------------------------------
-- 0. Local copies of the retired bind-block machinery
------------------------------------------------------------------------

-- What `strong-rep-nu.Ctx` §9 held until the store landed: a bind
-- block pushed onto the representation context, earlier payloads
-- shifted past their tail, with every name-map entry moved up by the
-- block's width.
pushRepBinds₀ : List Ty → RepCtx → RepCtx
pushRepBinds₀ []       Ξ = Ξ
pushRepBinds₀ (R ∷ Rs) Ξ =
  bindR (shiftBy (length Rs) R) ∷ pushRepBinds₀ Rs Ξ

extendReps₀ : List Ty → Ctxᵗ → Ctxᵗ
extendReps₀ Rs (Ξ ∣ Δ) = pushRepBinds₀ Rs Ξ ∣ map (length Rs +_) Δ

------------------------------------------------------------------------
-- 1. The statement as it stood, without the bind-block premise
------------------------------------------------------------------------

RepWeakenTyping₀ : Set
RepWeakenTyping₀ = ∀ {Δ W A} (Rs : List Ty)
  → Δ ∣ [] ⊢ W ⦂ A
  → extendReps₀ Rs Δ ∣ [] ⊢ renᴹᴿ (wkN (length Rs)) W ⦂ A

------------------------------------------------------------------------
-- 2. The refutation
------------------------------------------------------------------------

-- One open payload: the representation variable 1, which the one-cell
-- store `allocate `ℕ empty` lacks.
openPayload : List Ty
openPayload = ` 1 ∷ []

-- WHAT THE STORE CHANGED, in one equation.  The weakening used to be
-- the IDENTITY on this program's frame — its one change sat inside the
-- boundary's own one-wide bind block, so `extᵗ (wkN 1) 0 ≡ 0`.  With the
-- store the change names an AMBIENT cell, and the weakening moves it.
renamed-frame : renᴹᴿ (wkN 1) β-seven
  ≡ ($ 7) ⟪ (bind 0 1 ∷ []) , ⌞ id `ℕ ⌟ ⟫
renamed-frame = refl

no-rep-weaken : ¬ RepWeakenTyping₀
no-rep-weaken rw with rw openPayload β-seven-⊢
no-rep-weaken rw | boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE
  with wf-reps (bw-exterior mwΘ)
no-rep-weaken rw | boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE
  | wf-bindR (wfᴿ-var (local-ref ())) wr
no-rep-weaken rw | boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE
  | wf-bindR (wfᴿ-var (free-ref (there ()))) wr
