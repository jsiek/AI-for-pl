module strong.proof.WallGrounding where

-- WHERE THE WALL CAN BE GROUNDED — AND WHERE IT CANNOT.
--
-- proof/WallReach turns the wall into the type-context invariant
--
--     RepWf Ξ  =  ∀ {Y A} → Ξ ∋ Y := A → Ξ ⊢ᵗ A
--
-- and shows (§5) that `RepWf (intC Θ₂ Δ)` is EXACTLY the premise IdPush
-- and CancelR are missing.  The obvious next move is to GROUND it in the
-- typing rules by strengthening `Bwf`'s lock clause, so that
--
--     Bwf→RepWf : RepWf Δ → Bwf Δ Θ → RepWf (intC Θ Δ)
--
-- becomes a theorem.  THIS FILE REFUTES THAT MOVE, and says what the
-- right home for the condition is instead.
--
--   §1  THE TWO CONFIGURATIONS ARE THE SAME BOUNDARY.  The `¬IdPushCase`
--       witness (proof/PreserveObstruct §4) and the REACHABLE wrapper of
--       Examples §12's `run-L₀` have THE SAME exterior type context
--       `bind (` 0) ∷ bind ℕ ∷ []` and THE SAME frame `lock 1 ∷ []`.
--       They differ ONLY in their FACE — `unseal 0` (active) versus
--       `seal 1` (inert).  So NO condition on `Δ` and `Θ` alone — i.e.
--       no condition expressible in `Bwf Δ Θ` — can reject the first and
--       admit the second.
--
--   §2  THE REFUTATION, from the reachable side.  Any `Bwf→RepWf` makes
--       `⊢L₄` (Examples §12) underivable; `⊢L₃` is derivable and
--       `L₃ -→ L₄` is an ORDINARY TYBETA STEP, so preservation would
--       fail at TyBeta — the one boundary-minting rule that is currently
--       PROVEN (proof/Preserve.preserve-TyBeta).
--
--   §3  THE ROOT CAUSE, in one line: `RepWf (intC Θ ·)` is NOT MONOTONE
--       under knowledge refinement `_⊑_`, and it fails at exactly the
--       clause `le-ao : abst ⊑ᵉ bind A` — which is the refinement TyBeta
--       performs on its own contractum (`preserve-TyBeta`'s `refine`).
--       `Bwf` must be ⊑-stable, because `⊢retag` (strong.TermSubst)
--       transports a whole derivation along `_⊑_` via `Bwf-⊑`.  A wall
--       premise inside `Bwf` therefore breaks `Bwf-⊑`, hence `⊢retag`,
--       hence TyBeta.
--
--   §4  WHERE IT DOES BELONG.  The condition the rules need is about the
--       boundary that READS a rep back — the one carrying the ACTIVE
--       (`unseal`) face — and it is exactly
--
--         scp Θ Δ ⊢ᵗ Bₑ      ("the exterior type survives my own locks")
--
--       This is ⊑-STABLE (§4a), it DELIVERS `intC Θ Δ ⊢ᵗ A` (§4b), it
--       REJECTS the `¬IdPushCase` witness (§4c), and it is VACUOUS on
--       every lock-free frame — including every `Θ₂` on the `run-L₀` and
--       `run-D₀` runs (§4d).  It cannot live in `Bwf`; its home is the
--       `env` rule, where the face is in scope.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst using (⊢retag)
open import strong.Reduction
open import strong.proof.Preserve using (preserve-TyBeta)
open import strong.proof.WallReach
  using (RepWf; EntWf; RepWf-[]; RepWf-WΔ; ¬RepWf-WΞ; wf-liftN-prep)
open import strong.Examples
  using (QΔ₁; LΔ; LΞ; L₃; L₄; lstep₄; ⊢L₄; Δd; Θ2; Wd; ⊢Wd)
open import strong.proof.PreserveObstruct
  using (Δi; Θi; Ξi; Vi; Ri; ⊢Ri; step-i)

------------------------------------------------------------------------
-- §1  ONE BOUNDARY, TWO FACES
------------------------------------------------------------------------

-- The frame the wall is about.
Θw : CtxMorph
Θw = lock 1 ∷ []

-- `¬IdPushCase`'s exterior type context IS the reachable one.
_ : Δi ≡ LΔ
_ = refl

-- `¬IdPushCase`'s frame IS the reachable one.
_ : Θi ≡ Θw
_ = refl

-- … and so is the interior they both produce.
_ : intC Θw LΔ ≡ LΞ
_ = refl

_ : intC Θi Δi ≡ Ξi
_ = refl

-- THE ONLY DIFFERENCE IS THE FACE.  In `Ri` the frame `Θw` carries the
-- ACTIVE face `unseal 0`; in `L₄` the very same frame over the very same
-- type context carries the INERT face `seal 1`.
_ : Ri ≡ (Vi ⟪ [] , id (` 0) ⟫) ⟪ Θw , unseal 0 ⟫
_ = refl

_ : L₄ ≡ ((($ 7) ⟪ Θw , seal 1 ⟫) ⟪ bind (` 0) ∷ [] , id (` 1) ⟫)
           ⟪ bind `ℕ ∷ [] , unseal 0 ⟫
_ = refl

-- A `Bwf Δ Θ` premise sees Δ and Θ and NOTHING ELSE, so it either
-- accepts both boundaries or rejects both.
face-is-the-only-difference : (Δi ≡ LΔ) × (Θi ≡ Θw)
face-is-the-only-difference = refl , refl

------------------------------------------------------------------------
-- §2  THE REFUTATION
------------------------------------------------------------------------

-- The property the strengthened lock clause is supposed to buy.
BwfWall : Set
BwfWall = ∀ {Δ Θ} → RepWf Δ → Bwf Δ Θ → RepWf (intC Θ Δ)

-- Every typing of `L₄` contains the boundary `Bwf LΔ Θw` — the wrapper
-- three `env` nodes down, whose frame is `Θw`.  (The two enclosing
-- frames compute: `intC (bind ℕ ∷ []) [] ≡ QΔ₁` and
-- `intC (bind (` 0) ∷ []) QΔ₁ ≡ LΔ`.)
L₄-lock : [] ∣ [] ⊢ L₄ ⦂ `ℕ → Bwf LΔ Θw
L₄-lock (env _ (env _ (env bw _ _ _) _ _) _ _) = bw

-- THE REFUTATION, stated so that it bites BOTH ways: read left to right
-- it says a `Bwf`-level wall makes `L₄` untypeable; read with the
-- CURRENT `Bwf` (where `⊢L₄` exists) it says the wall is not a
-- consequence of `Bwf` at all.
wall-vs-L₄ : BwfWall → ¬ ([] ∣ [] ⊢ L₄ ⦂ `ℕ)
wall-vs-L₄ h ⊢L = ¬RepWf-WΞ (h RepWf-WΔ (L₄-lock ⊢L))

¬BwfWall : ¬ BwfWall
¬BwfWall h = wall-vs-L₄ h ⊢L₄

-- ── AND THE REDEX IT COMES FROM STILL TYPES ────────────────────────────

-- `L₃`'s wrapper sits over `abst ∷ QΔ₁`, where the locked slot is named
-- by NOTHING (slot 0 is Λ-bound, so it carries no rep at all).  The wall
-- ACCEPTS it.
_ : intC Θw (abst ∷ QΔ₁) ≡ abst ∷ blk (bind `ℕ) ∷ []
_ = refl

RepWf-L₃w : RepWf (intC Θw (abst ∷ QΔ₁))
RepWf-L₃w ez          = tt
RepWf-L₃w (es ez)     = tt
RepWf-L₃w (es (es ()))

⊢Lseal₇′ : (abst ∷ QΔ₁) ∣ [] ⊢ ($ 7) ⟪ Θw , seal 1 ⟫ ⦂ ` 1
⊢Lseal₇′ = env (bw-l (bind `ℕ , es ez , vis-b) bw[]) ⊢$
                (conv-seal (es ez)) (wf-var (bind `ℕ , es ez , vis-b))

⊢L₃-in : QΔ₁ ∣ [] ⊢ (Λ (($ 7) ⟪ Θw , seal 1 ⟫)) ·[ ` 1 , ` 0 ] ⦂ ` 0
⊢L₃-in = ⊢·[] (⊢Λ ⊢Lseal₇′) (wf-var (bind `ℕ , ez , vis-b))

⊢L₃ : [] ∣ [] ⊢ L₃ ⦂ `ℕ
⊢L₃ = env (bw-b wf-ℕ bw[]) ⊢L₃-in (conv-unseal ez) wf-ℕ

-- THE HEADLINE.  `L₃ -→ L₄` is `ξ-⟪⟫ (TyBeta …)` — an ordinary TyBeta,
-- the ONE boundary-minting rule whose preservation case is PROVEN.  So a
-- wall premise inside `Bwf` does not repair preservation; it BREAKS it,
-- at a rule that currently holds.
wall-vs-TyBeta : BwfWall
  → ¬ (∀ {Δ M M′ A} → Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A)
wall-vs-TyBeta h pr = wall-vs-L₄ h (pr ⊢L₃ lstep₄)

-- SHARPER: not merely "preservation" (which is false anyway while
-- CancelR/TyPeelR stand) but `preserve-TyBeta` ITSELF — a theorem today.
TyBetaCase : Set
TyBetaCase = ∀ {Δ N B A C}
  → Δ ∣ [] ⊢ (Λ N) ·[ B , A ] ⦂ C
    ---------------------------------------------
  → Δ ∣ [] ⊢ N ⟪ bind A ∷ [] , unsealAt 0 B ⟫ ⦂ C

-- it holds today …
tyBetaCase : TyBetaCase
tyBetaCase = preserve-TyBeta

-- … and the minted face at this redex is the id-layer.
_ : unsealAt 0 (` 1) ≡ id (` 1)
_ = refl

-- … but it CANNOT hold alongside a `Bwf`-level wall.
wall-vs-preserve-TyBeta : BwfWall → ¬ TyBetaCase
wall-vs-preserve-TyBeta h tb =
  wall-vs-L₄ h
    (env (bw-b wf-ℕ bw[]) (tb ⊢L₃-in) (conv-unseal ez) wf-ℕ)

------------------------------------------------------------------------
-- §3  THE ROOT CAUSE — the wall is not ⊑-STABLE
------------------------------------------------------------------------

-- TyBeta's own refinement (`preserve-TyBeta`'s `refine`): the slot the Λ
-- bound abstractly BECOMES an owner, under whatever locks the body
-- already contains.
refineᴸ : (abst ∷ QΔ₁) ⊑ LΔ
refineᴸ = le∷ le-ao (⊑-refl QΔ₁)

-- … and the wall does not survive it.  This is `le-ao`, the one `_⊑ᵉ_`
-- clause that INVENTS a rep: before the refinement the locked slot is
-- named by nothing, after it the fresh owner's rep names it.
wall-not-⊑-stable :
  ¬ (∀ {Δ Δ′} (Θ : CtxMorph) → Δ ⊑ Δ′ → RepWf (intC Θ Δ) → RepWf (intC Θ Δ′))
wall-not-⊑-stable h = ¬RepWf-WΞ (h Θw refineᴸ RepWf-L₃w)

-- WHY THAT IS FATAL FOR `Bwf`.  `Bwf-⊑` (strong.Terms) transports a
-- boundary along `_⊑_`, and `⊢retag` (strong.TermSubst) calls it on
-- EVERY wrapper of a retagged derivation.  `preserve-TyBeta` retags its
-- contractum along exactly `refineᴸ`'s shape.  A `Bwf` clause carrying a
-- non-⊑-stable premise makes `Bwf-⊑` unprovable, and `⊢retag` with it.
retag-needs-Bwf-⊑ : ∀ {Δ Δ′ Γ M A}
  → Δ ⊑ Δ′ → Δ ∣ Γ ⊢ M ⦂ A → Δ′ ∣ Γ ⊢ M ⦂ A
retag-needs-Bwf-⊑ = ⊢retag

------------------------------------------------------------------------
-- §4  THE CONDITION THAT DOES WORK — on the ACTIVE face's boundary
------------------------------------------------------------------------

-- What IdPush and CancelR actually need is `intC Θ₂ Δ ⊢ᵗ A` for the rep
-- `A` the ACTIVE face hands back.  For an `unseal`-faced `env` node that
-- rep IS `liftN (nbind Θ) Bₑ` (the exterior type, lifted), so the whole
-- requirement is that the boundary's OWN exterior type survives its OWN
-- locks:
Scoped : Ctxᵗ → CtxMorph → Ty → Set
Scoped Δ Θ Bₑ = scp Θ Δ ⊢ᵗ Bₑ

-- ── §4a  IT IS ⊑-STABLE — the property §3 denies the `Bwf` version ────
--
-- Masking is positional, so it commutes with refinement (`⊑-scp`), and
-- well-formedness is monotone (`⊑-wf`).  Nothing here depends on which
-- entries the refinement promotes.
Scoped-⊑ : ∀ {Δ Δ′ Bₑ} (Θ : CtxMorph)
  → Δ ⊑ Δ′ → Scoped Δ Θ Bₑ → Scoped Δ′ Θ Bₑ
Scoped-⊑ Θ ls w = ⊑-wf (⊑-scp Θ ls) w

-- ── §4b  IT DELIVERS THE MISSING PREMISE ──────────────────────────────
--
-- `wf-liftN-prep` (proof/WallReach §2) is the simultaneity step: a rep is
-- read in the PLAIN exterior and lifted past the owners bound inside.
Scoped→scoped : ∀ {Δ Bₑ} (Θ : CtxMorph)
  → Scoped Δ Θ Bₑ → intC Θ Δ ⊢ᵗ liftN (nbind Θ) Bₑ
Scoped→scoped Θ w = wf-liftN-prep (reps Θ) w

-- ── §4c  IT REJECTS THE `¬IdPushCase` WITNESS ─────────────────────────
--
-- `Ri`'s exterior type is `` ` 1 `` and its own frame locks slot 1.
¬Scoped-Ri : ¬ Scoped Δi Θi (` 1)
¬Scoped-Ri (wf-var (_ , es ez , ()))

-- ── §4d  IT IS VACUOUS ON EVERY LOCK-FREE FRAME ───────────────────────
--
-- `scp` is the identity on a frame that binds only, so a boundary that
-- locks nothing owes nothing.  Every `Θ₂` of every IdPush and CancelR
-- redex on Examples' `run-L₀`, `run-Q₀` and `run-D₀` is of this shape.
scp-binds : ∀ (Δ : Ctxᵗ) (A : Ty) → scp (bind A ∷ []) Δ ≡ Δ
scp-binds Δ A = refl

Scoped-bind : ∀ {Δ A Bₑ} → Δ ⊢ᵗ Bₑ → Scoped Δ (bind A ∷ []) Bₑ
Scoped-bind w = w

-- ── §4e  IT MUST NOT BE ASKED OF EVERY BOUNDARY ───────────────────────
--
-- PEEL'S OWN CROSSING WRAPPER VIOLATES IT.  Examples' `⊢Wd-crossed` is
-- typed at frame `dual Θ2` — which LOCKS Θ2's owners — with exterior type
-- V's domain `` ` 0 ⇒ ` 0 ``, a type that NAMES one of those owners.  So
-- `Scoped` cannot be a premise of EVERY `env` node; asking it universally
-- refutes the Peel case, which is PROVEN today (proof/PeelDual).
_ : scp (dual Θ2) (intC Θ2 Δd) ≡ blk (bind (` 0)) ∷ Δd
_ = refl

¬Scoped-crossing : ¬ Scoped (intC Θ2 Δd) (dual Θ2) (` 0 ⇒ ` 0)
¬Scoped-crossing (wf-⇒ (wf-var (_ , ez , ())) _)

-- ── §4f  WHAT WOULD HAVE SEPARATED THE THREE ──────────────────────────
--
-- The three boundaries this file has weighed are:
--
--   `L₄`'s wall wrapper  (`seal 1`)   REACHABLE, must be ADMITTED
--   Peel's crossing      (`s`)        PROVEN,    must be ADMITTED
--   `Ri`'s outer wrapper (`unseal 0`) UNSOUND,   must be REJECTED
--
-- The candidate that separated them asked `Scoped` at REVEAL boundaries
-- only, switching on the conversion judgment's POLARITY index — which
-- Jeremy's 2026-09-06 ruling RETIRED (strong.Conversion).  With no `p` on
-- an `env` node there is no face-conditioned premise to state, so this
-- branch of the search is closed along with the index; the surviving
-- candidate is the REP CHAIN of proof/ChainScoped, which reads the face's
-- NAME rather than a polarity, and is killed there by TyBeta's retag.
