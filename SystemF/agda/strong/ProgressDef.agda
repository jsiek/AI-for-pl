module strong.ProgressDef where

-- The progress obligation still open after the Decision-7 install
-- (2026-09-04; notes/DECISIONS.md "Decision 7", gauntlet §9l / §9m).
--
-- WHAT CLOSED EARLIER.  RevealVarApp / RevealVarTApp — the two parameters
-- this module carried at the peel landing — are GONE, and so is the pair of
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
-- … and the fourth is `MergeDerivable`: Merge's premise MergeOK must be
-- DERIVABLE at that forced shape.
--
-- WHAT DECISION 7 CLOSED, AND WHAT IT DID NOT.
--
-- Decision 7 replaced MergeOK's component (1) — the SCOPE side condition
-- `cmax Θ₁ ≤ revs Θ₂`, which is ⊕-γ's hypothesis — by the INTERNAL-FACE
-- EQUATION it was only ever used to buy.  At the reveal-variable redex
-- that component is now a THEOREM:
--
--   mid-var    the middle-type equation pins Y ≡ revs Θ₁ + X, so the
--              inner boundary type is Θ₁'s frame slot for the very
--              exterior index Θ₂ reveals;
--   ⊕-γ-var    at that slot the internal face composes with NO side
--              condition (⊕-γ-pt-lo: both the cancelled and the kept
--              branch land without ever comparing cmax Θ₁ to revs Θ₂).
--
-- So gauntlet §9l — the term that was well typed, not a value, and took
-- NO step — now STEPS (§9l's merge-p), and `merge-derivable` below
-- reduces the whole of MergeDerivable to the FOUR remaining components.
--
-- THE OBSTRUCTION MOVED, IT DID NOT VANISH.  MergeRest is still FALSE,
-- and gauntlet §9m is the machine-checked refutation — of MergeRest, of
-- MergeDerivable (¬MergeDerivable), and of PROGRESS itself (stuck-q).
-- The failing component is now the FIFTH, the EXTERNAL face, on a
-- CANCELLED slot:
--
--   Δq = X:=ℕ ;  Θ₂ = ↑X:=ℕ ;  Θ₁ = ↓X:=(` 0)
--   ((5 ⟪ ↓·:=ℕ , · ⟫) ⟪ Θ₁ , · ⟫) ⟪ Θ₂ , · ⟫  :  ℕ
--
-- Θ₁ conceals the very slot Θ₂ reveals, so the pair CANCELS and the
-- composite is EMPTY — but Θ₁'s rep is Δ's own variable (` 0), which is
-- ≈Δ̄-equal to Θ₂'s stored rep ℕ and NOT syntactically equal to it.
-- `bwf↓` licenses that conceal (its premise is `Reversal≈`, up to
-- unfolding — Decision 1's candidate (a″)), while MergeOK's external-face
-- component demands SYNTACTIC agreement, because preservation transports
-- the contractum's type by `subst`.  ≈ ⊄ ≡, and the merge is refused.
-- That gap is a DESIGN question, not an arithmetic one, and it is the
-- next ruling.  Two halves of the component are already settled:
--
--   ⊕-ρ-var-kept   (strong.BReduction) — a THEOREM: when Θ₁ does NOT
--                  conceal the revealed slot (cmax Θ₁ ≤ X) the external
--                  face composes with no side condition;
--   §9m            the CANCELLED branch (X < cmax Θ₁), REFUTED.
--
-- The statements below are EXACTLY that residue and nothing more.

open import Data.Nat using (ℕ; _+_; _<_; _≤_)
open import Data.Product using (_×_; _,_)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction
  using (Value; MergeOK; _⊕_; mrgB; _≼≈_;
         env-body; env-sc; mid-var; ⊕-γ-var)

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

-- THE RESIDUE (the Def-module split): MergeDerivable minus the component
-- Decision 7 discharged.  Components (2)–(5) of MergeOK, at the same
-- redex, in the same order.
MergeRest : Set
MergeRest = ∀ {Δ : TCtx} {V : Term} {Θ₁ Θ₂ : BCtx} {X Y : ℕ}
  → Value V → revs Θ₁ ≤ Y → X < revs Θ₂
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ ⦂ substᵗ (ρᵇ Θ₂) (` X)
  → (Δ ∣ intOf Δ (Θ₁ ⊕ Θ₂) ⊢ᵇ (Θ₁ ⊕ Θ₂))
  × Scoped (baseS (Θ₁ ⊕ Θ₂) Δ) (mrgB Θ₁ Θ₂ (` Y))
  × (intOf (intOf Δ Θ₂) Θ₁ ≼≈ intOf Δ (Θ₁ ⊕ Θ₂))
  × (substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ (` Y)) ≡ substᵗ (ρᵇ Θ₂) (` X))

-- … AND THE SPLIT IS MACHINE-CHECKED: component (1) is a theorem here.
-- `mid-var` pins the inner face's slot at revs Θ₁ + X, and `⊕-γ-var`
-- discharges the internal-face equation there with no side condition —
-- the whole of Decision 7, in two applications.
merge-derivable : MergeRest → MergeDerivable
merge-derivable rest {Δ} {V} {Θ₁} {Θ₂} {X} {Y} v ge lt ⊢W
  with mid-var {Δ} {V} {Θ₁} {Θ₂} {X} {Y} ge lt (env-body ⊢W)
merge-derivable rest {Δ} {V} {Θ₁} {Θ₂} {X} v ge lt ⊢W | refl =
    ⊕-γ-var Θ₁ Θ₂ X lt (env-sc (env-body ⊢W))
  , rest v ge lt ⊢W
