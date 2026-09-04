module strong.ProgressDef where

-- The ONE progress obligation still open, after the Decision-6 install
-- (ACTIVE/INERT, 2026-09-04; notes/ParameterizedCastCalculi.md).
--
-- WHAT CLOSED.  RevealVarApp / RevealVarTApp — the two parameters this
-- module carried at the peel landing — are GONE, and so is the pair of
-- nested-wrapper parameters before them.  The value restriction
-- (`V-⟪⟫ : Value V → Inert Θ B₀ → Value (V ⟪ Θ , B₀ ⟫)`) dissolves them:
-- a wrapper that is a VALUE has an INERT face, and by `inert-ext` an
-- inert face keeps its head constructor when read outward, so a value of
-- ARROW type in function position has the SYNTACTIC ⇒ face Peel needs and
-- a value of ∀ type has the syntactic ∀ face TyWrap / TyPeel need (the
-- paper's `InertCross→`).  A reveal-variable face is ACTIVE, so such a
-- wrapper never reaches an elimination as a value at all: it steps first,
-- under ξ.  strong.Progress's app-steps / tapp-steps are therefore TOTAL.
--
-- WHAT REMAINS — the paper's `applyCast` TOTALITY, and nothing else.
-- Progress must show that every well-typed ACTIVE wrapper around a value
-- steps.  Three of the four active shapes are theorems in
-- strong.Progress:
--
--   base face ℕ   canon-ℕ says the body is a NUMERAL (a wrapper of type
--                 ℕ would need an ℕ-exporting inert face, and
--                 baseNotInert-ℕ says there is none), so Drop$ fires;
--   base face 𝔹   canon-𝔹 says there is NO value of type 𝔹 at all, so
--                 the shape is vacuous;
--   reveal-var    canon-var-conceal says the body is a wrapper whose own
--     face ` X    face is INERT (` Y with revs Θ₁ ≤ Y — a SEALED value),
--                 so Merge's redex shape is FORCED …
--
-- … and the fourth is this parameter: Merge's premise MergeOK must be
-- DERIVABLE at that forced shape.  Three instances are already fully
-- discharged (notes/old/CancelProbe.agda's a-MergeOK / p-MergeOK /
-- e-MergeOK, one per family α / β1 / β2, plus notes/InstallGauntlet §9i's
-- rv-merge).  IT IS NOT A THEOREM, AND NOT TRUE AS STATED: gauntlet §9l
-- exhibits a well-typed, non-value, non-stepping instance whose inner
-- boundary drops an AMBIENT slot the outer one does not reveal, so
-- MergeOK's first component (cmax Θ₁ ≤ revs Θ₂ — ⊕-γ's side condition)
-- is false there while components (2)–(5), and ⊕-γ's own conclusion,
-- all hold.  See §9l for the diagnosis and the indicated repair (weaken
-- MergeOK's component (1) to the internal-face equation it buys); until
-- that is ruled on, progress carries exactly this parameter.  See also
-- notes/DECISIONS.md "Decision 6 — CANCEL PROBE VERDICT" (3)–(4), where
-- this obligation is named THE CRUX.
--
-- The statement below is EXACTLY that residue and nothing more: the
-- hypotheses are the shape progress can actually produce (a value body,
-- an inert inner face, an active reveal-variable outer face, and the
-- redex's own typing at its own external face), and the conclusion is
-- MergeOK verbatim.

open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.List using ([])
open import strong.Types
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction using (Value; MergeOK)

-- APPLYCAST TOTALITY AT A REVEAL-VARIABLE FACE.  The redex is
--
--   (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫       revs Θ₁ ≤ Y ,  X < revs Θ₂
--
-- — a SEALED value inside an ACTIVE reveal-variable boundary, which is
-- the only shape strong.Progress reaches with no rule yet available.
-- Typing forces ρᵇ Θ₁ (` Y) ≡ ` X (the middle-type equation), so the
-- five MergeOK components have to come from the two (env) derivations'
-- own bwf / Scoped / ≼≈ / external-face content.
MergeDerivable : Set
MergeDerivable = ∀ {Δ : TCtx} {V : Term} {Θ₁ Θ₂ : BCtx} {X Y : ℕ}
  → Value V → revs Θ₁ ≤ Y → X < revs Θ₂
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ ⦂ substᵗ (ρᵇ Θ₂) (` X)
  → MergeOK Δ Θ₁ Θ₂ (` Y) (` X)
