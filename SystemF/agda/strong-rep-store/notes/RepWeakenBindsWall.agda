module strong-rep-store.notes.RepWeakenBindsWall where

-- THE REP-WEAKENING STATEMENT NEEDS ITS BIND BLOCK (2026-09-20).
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
-- `env` rule stores a `BoundaryWf` whose `bw-exterior` field is a `WfCtx` of
-- that context — which demands `WfRepCtx`, i.e. that every stored payload
-- be well formed where it is written.
--
-- The counterexample is as small as the development allows.  Take the
-- closed, one-boundary program `β-seven` (strong-rep-store.Terms §5) at the
-- EMPTY
-- context, and insert the single payload `` ` 0 `` — a representation
-- variable that the empty representation context does not have.  The
-- renamed term is `β-seven` itself: `renᴮᴿ (wkN 1) TyBetaBoundary` is
-- `TyBetaBoundary`, because the boundary scope's one change sits inside its own
-- one-wide bind block and `extᵗ (wkN 1) 0 ≡ 0`.  So the conclusion asks
-- for the SAME term to be typed at a context whose only representation
-- binding is `bindR (` 0)`, and `[] ⊢ᴿ ` 0` has no derivation: index 0 is
-- neither local (there are no local binders) nor free (the context is
-- empty).
--
-- THE REPAIR is the premise `reps Δ ⊢ᴮ Rs`, and it costs nothing: at the
-- one call site — `Peel`'s crossing argument, strong-rep-store.proof.PeelDual §3
-- —
-- it is `bw-binds` of the very boundary being crossed, already stored in
-- the redex's own typing derivation.  With it the statement is PROVED:
-- `strong-rep-store.proof.RepWeaken.rep-weaken-⊢`.

open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-store.Types using (Ty; `_; `ℕ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary
open import strong-rep-store.Terms
open import strong-rep-store.TermSubst using (renᴹᴿ; wkN)

------------------------------------------------------------------------
-- 1. The statement as it stood, without the bind-block premise
------------------------------------------------------------------------

RepWeakenTyping₀ : Set
RepWeakenTyping₀ = ∀ {Δ W A} (Rs : List Ty)
  → Δ ∣ [] ⊢ W ⦂ A
  → extendReps Rs Δ ∣ [] ⊢ renᴹᴿ (wkN (length Rs)) W ⦂ A

------------------------------------------------------------------------
-- 2. The refutation
------------------------------------------------------------------------

-- One open payload: the representation variable 0, which `empty` lacks.
openPayload : List Ty
openPayload = ` 0 ∷ []

-- The renaming really is the identity on this program's frame, so the
-- refutation is about the CONTEXT and nothing else.
renamed-is-the-same : renᴹᴿ (wkN 1) β-seven ≡ β-seven
renamed-is-the-same = refl

no-rep-weaken : ¬ RepWeakenTyping₀
no-rep-weaken rw with rw openPayload β-seven-⊢
no-rep-weaken rw | env mwΘ ⊢M ⊢c sameᵢ sameₑ wE
  with wf-reps (bw-exterior mwΘ)
no-rep-weaken rw | env mwΘ ⊢M ⊢c sameᵢ sameₑ wE
  | wf-bindR (wfᴿ-var (local-ref ())) wr
