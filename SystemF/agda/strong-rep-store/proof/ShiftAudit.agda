module strong-rep-store.proof.ShiftAudit where

-- THE SHIFT AUDIT — every place a rule MOVES A SUBTERM, checked against
-- FRAME EXACTNESS (Jeremy, 2026-09-08: "frame exactness is the main point
-- of Strong System F").
--
-- THE CRITERION.  Whenever a rule moves a subterm to a new position, the
-- subterm's TYPE CONTEXT at the new position must be EXACTLY its context
-- at the old position, up to
--
--   (i)  the movement past the binders it CROSSED, and
--   (ii) refinement `abstR → bindR R` of a representation variable it
--        could ALREADY name (TyBeta's reveal, TyPeelR's `instReveal`).
--
-- Any variable the subterm COULD NOT name before and CAN name after is a
-- FRAME LEAK, even when the subterm's shifted indices cannot reach it:
-- the frame must SAY THE TRUTH about what the subterm may name.
--
-- WHAT THE TWO UNIVERSES CHANGED (2026-09-19).  The frame identities
-- stopped being EQUATIONS BETWEEN COMPUTED CONTEXTS.  There is no
-- `interior Θ Δ` to write an equation about: a boundary scope RELATES an
-- exterior to an interior, and the audit's per-site facts are exactly the
-- transport lemmas of `strong-rep-store.Boundary` §3a — `dual-interior`
-- for Peel, `rewind-interior`/`merged-interior` for CancelR and IdPush.
-- So §2 and §6 CITE them rather than restating them.
--
-- WHAT THE STORE CHANGED (2026-09-22), AND WHY MOST OF THIS FILE IS
-- SHORTER.  A boundary scope carries no bind block, so THERE ARE NO
-- BINDS TO MOVE A SUBTERM PAST, and the audit's central question —
-- "does the moved subterm's frame gain a slot it could not name?" —
-- becomes vacuous at every site but one:
--
--   * `Peel` no longer renames its argument at all (§2).  The old
--     obligations `Peel-move-ordinary`, `Peel-move-represent`,
--     `Peel-frame-names` and `Peel-dual-numBinds` were about the bind
--     block the dual's interior used to carry; the dual's interior is
--     now the exterior ITSELF, so they are retired.
--   * `TyPeelR-⟪⟫` moves its boundary by the UNIFORM SIBLING SHIFT
--     `renᴹᴿ suc` (§3), not by an `extN (numBinds Θ′) suc` computed from
--     the crossed scope; `TyPeelR-⟪⟫-move-ordinary` survives in the form
--     that still says something — a representation renaming leaves every
--     ordinary annotation in place.
--   * `CancelR`/`IdPush` (§6) keep both frame identities, now stated at
--     the plain exterior.  `Move-outer-numBinds`/`Move-inner-numBinds`
--     are retired with `numBinds`.
--
-- WHAT THE STORE ADDED is §8: the congruences now SHIFT THE REDEX'S
-- SIBLINGS, and the shift has to be exactly the move the context makes.
-- That is the one new frame-exactness obligation of the experiment, and
-- it holds definitionally at both `Alloc`s.
--
--   §1  the site table (comment)
--   §2  Peel                  — EXACT, by `dual-interior`; NO shift
--   §3  the two TyPeelR clauses — the Λ clause shifts nothing; the
--       wrapper clause is the sibling shift plus one appended lock
--   §4  TERMINATION — the tower measure, and why the rejected repair
--       (wrap the moved value in the new binder's dual) stalls on it
--   §5  Beta                  — the `ƛ` and `Λ` crossings do not interfere
--   §6  CancelR / IdPush      — exact, inner AND outer
--   §7  Drop$ / Drop-true / Drop-false — vacuous
--   §8  the ξ rules           — the sibling shift IS the context move
--   §9  dead shift machinery
--
-- The verdict table, with the fix candidates and their hazards, is
-- notes/ShiftAudit.md.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.proof.TermSubst
open import strong-rep-store.Reduction
open import strong-rep-store.proof.Canonical using (canon-∀)

private
  variable
    Δ Δ′ Γᵗ : Ctxᵗ
    Γ : Ctx
    A B C : Ty
    X Y : ℕ
    Θ Θ₁ Θ₂ : Boundary

------------------------------------------------------------------------
-- §1  THE SITES
------------------------------------------------------------------------

-- Every place in the live development where a TERM is renamed, shifted or
-- substituted (`grep renᴹ² renᴹᴿ wkᴹ ⇑ᴹ renⁿ shiftᵐ crossΛᴹ substᵐ`):
--
--   RULES that move a subterm
--     Peel        `W`, verbatim, inside the frame
--                 `⟪ dual Θ , s′ ⟫`                  §2  EXACT
--     TyPeelR-Λ   `N ⟪ inst Θ , instReveal 0 s ⟫`     §3  EXACT
--     TyPeelR-⟪⟫  `renᴹᴿ suc` on the moved boundary, plus
--                 `++ (lock 0 0 ∷ [])` on its change list    §3  EXACT
--     TyBeta      `N ⟪ inst [] , reveal 0 B ⟫`
--                                                            §3  refinement
--     Beta        `N [ W ∶ A ]ᵐ`, i.e. `substᵐ`/`crossΛᴹ`     §5  EXACT
--     CancelR     `V ⟪ Θ₁ ++ Θ₂ , … ⟫ ⟪ rewind Θ₂ , … ⟫`       §6  EXACT
--     IdPush      (same two frames)                           §6  EXACT
--     Drop$ / Drop-true / Drop-false                          §7  vacuous
--     ξ-*         the SIBLINGS move, by `↑ᴹ[ δ ]`             §8  EXACT
--
--   TRANSPORTS, not rules (no term is moved by a reduction; these are the
--   lemmas the cases above are PROVED with, and each one's renaming or
--   reading argument is supplied at the site):
--     `⊢renᴿ`, `renᴹ²`, `renⁿ`, `⊢renⁿ`, `⊢weakenⁿ`,
--     `canon-renᴹ²`/`canon-renⁿ` (proof/Canonicity).

------------------------------------------------------------------------
-- §2  PEEL — the crossing argument's frame is the EXTERIOR ITSELF
------------------------------------------------------------------------

-- W's frame, before: `Δ`.  After: the dual's interior, which
-- `dual-interior` says is `Δ` — NOT ONE ORDINARY NAME AND NOT ONE
-- REPRESENTATION BINDER ADDED OR REMOVED.  Criterion (i) with nothing to
-- cross: EXACT, and the rule carries W verbatim.
Peel-frame : ∀ {Γᵢ : Ctxᵗ} (Θ : Boundary) (Γ : Ctxᵗ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ dual Θ ⇒ Γ
Peel-frame Θ Γ = dual-interior

-- … and Peel allocates nothing, so its siblings do not move either.
Peel-no-alloc : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Value V → Value W
  → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δ ⊢ⁱ Θ ⇒ Δᵢ
  → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ → SameConv Δᵈ s′ Δᶜ s
  → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
      -→ (V · (W ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫ ∣ none
Peel-no-alloc = Peel

------------------------------------------------------------------------
-- §3  THE TWO TYPEELR CLAUSES, AND TYBETA
------------------------------------------------------------------------

-- THE Λ CLAUSE MOVES NOTHING.  `N` already lives one `abstR` binder in
-- (`⊢Λ`), and the allocation REFINES that binder to `bindR R` in place
-- while `inst Θ` restores its ordinary name at position 0 (the
-- appended `unlock 0 0`).  So the frame move is criterion (ii) and there
-- is no renaming at all — the contractum mentions no `renᴹᴿ`.
TyPeelR-Λ-restores-name-0 : (Θ : Boundary)
  → ∃[ χ ] ((inst Θ) ≡ χ ++ (unlock 0 0 ∷ []))
TyPeelR-Λ-restores-name-0 Θ = _ , refl

-- TyBeta is the same refinement one `∀` out: the fresh cell is allocated
-- at index 0 and `inst []` gives it ordinary name 0.
TyBeta-restores-name-0 :
  (inst []) ≡ unlock 0 0 ∷ []
TyBeta-restores-name-0 = refl

-- THE WRAPPER CLAUSE.  The moved boundary crosses ONE freshly allocated
-- cell and ONE fresh ordinary name for it, and its appended `lock 0 0`
-- DELETES that ordinary name again.  So the move is the plain SIBLING
-- SHIFT — representation-only, `renᴹᴿ suc` — and the moved boundary's
-- ordinary indices keep their positions.  That is the whole of the
-- 2026-09-08 repair, restated in the universe that now carries it.
TyPeelR-⟪⟫-move-ordinary : (ρ : Renameᵗ) (L : Term) (B A : Ty)
  → renᴹᴿ ρ (L ·[ B , A ]) ≡ renᴹᴿ ρ L ·[ B , A ]
TyPeelR-⟪⟫-move-ordinary ρ L B A = refl

TyPeelR-⟪⟫-move-conversion : (ρ : Renameᵗ) (M : Term) (Θ : Boundary)
  (c : Conv) → renᴹᴿ ρ (M ⟪ Θ , c ⟫) ≡ renᴹᴿ ρ M ⟪ renᴮᴿ ρ Θ , c ⟫
TyPeelR-⟪⟫-move-conversion ρ M Θ c = refl

-- The appended lock names ordinary position 0 and the cell the
-- allocation just minted, which is representation index 0 — and it is
-- APPENDED, so it acts FIRST (the change list is read head-last).  Since
-- `Boundary = List Change` the rule WRITES that snoc, `Θ′ ++ (lock 0 0 ∷
-- [])`, so there is nothing left here to state: the old
-- `TyPeelR-⟪⟫-addLock0` was `refl` on one and the same list.

------------------------------------------------------------------------
-- §4  TERMINATION — THE TOWER MEASURE
------------------------------------------------------------------------

-- The wrapper clause's contractum contains
--
--    (… ⟪ … ++ (lock 0 0 ∷ []) , `∀ s″ ⟫) ·[ … , ` 0 ]
--
-- which IS again a redex.  It is not a regress, and the measure says why:
-- the number of nested boundaries above the `Λ`.
towerHeight : Term → ℕ
towerHeight (` x)          = 0
towerHeight ($ n)          = 0
towerHeight `true          = 0
towerHeight `false         = 0
towerHeight (ƛ A ∙ N)      = 0
towerHeight (L · M)        = 0
towerHeight (Λ N)          = 0
towerHeight (L ·[ B , A ]) = 0
towerHeight (M ⟪ Θ , c ⟫)  = suc (towerHeight M)

-- No renaming changes it — which is what makes the measure usable at all,
-- since both candidate repairs rename the moved value.
towerHeight-renᴹᴿ : (ρ : Renameᵗ) (M : Term)
  → towerHeight (renᴹᴿ ρ M) ≡ towerHeight M
towerHeight-renᴹᴿ ρ (` x)          = refl
towerHeight-renᴹᴿ ρ ($ n)          = refl
towerHeight-renᴹᴿ ρ `true          = refl
towerHeight-renᴹᴿ ρ `false         = refl
towerHeight-renᴹᴿ ρ (ƛ A ∙ N)      = refl
towerHeight-renᴹᴿ ρ (L · M)        = refl
towerHeight-renᴹᴿ ρ (Λ N)          = refl
towerHeight-renᴹᴿ ρ (L ·[ B , A ]) = refl
towerHeight-renᴹᴿ ρ (M ⟪ Θ , c ⟫)  =
  cong suc (towerHeight-renᴹᴿ ρ M)

-- … and neither does the sibling shift, at either `Alloc`.
towerHeight-↑ᴹ : (δ : Alloc) (M : Term)
  → towerHeight (↑ᴹ[ δ ] M) ≡ towerHeight M
towerHeight-↑ᴹ none    M = refl
towerHeight-↑ᴹ (new R) M = towerHeight-renᴹᴿ suc M

-- THE MEASURE STRICTLY DECREASES.  The ∀-value the contractum's inner
-- `·[]` instantiates is ONE BOUNDARY SHORTER than the one the redex's
-- `·[]` instantiated.
TyPeelR-⟪⟫-height : (W : Term) (Θ′ Θ : Boundary) (s′ s″ s : Conv)
  → towerHeight (renᴹᴿ suc W ⟪ (renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])) , `∀ s″ ⟫)
      ≡ towerHeight ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ∸ 1
TyPeelR-⟪⟫-height W Θ′ Θ s′ s″ s =
  cong suc (towerHeight-renᴹᴿ suc W)

-- THE REJECTED REPAIR STALLS AT THE SAME MEASURE.  Fix (a) — wrap the
-- moved value in the new binder's dual, with an identity conversion at
-- the value's own type — puts the ∀-value under a FRESH boundary, so the
-- height is the redex's height again: nothing is consumed.  THIS is the
-- difference between (a) and the installed clause: `TyPeelR-⟪⟫` CONSUMES
-- a boundary that was already there, (a) MINTS a new one.
fixA-height-stalls : (V : Term) (Θ : Boundary) (s : Conv) (Bᵢ : Ty)
  → towerHeight (renᴹᴿ suc V
                   ⟪ (lock 0 0 ∷ []) , mkId (`∀ Bᵢ) ⟫)
      ≡ towerHeight (V ⟪ Θ , `∀ s ⟫)
fixA-height-stalls V Θ s Bᵢ = cong suc (towerHeight-renᴹᴿ suc V)

-- AND IT IS SELF-FEEDING.  An identity conversion at a `∀` type is
-- NECESSARILY a `` `∀ `` conversion — `conv-id` wants a base type and
-- `conv-idv` a variable, so `mkId` has no other spelling — hence the
-- inserted layer is INERT `I-all`, hence the wrapped value sitting under
-- `·[ … ]` is ITSELF a TyPeelR redex.  Fix (a) does not converge: it
-- inserts one layer per step, forever.
mkId-∀ : (B : Ty) → mkId (`∀ B) ≡ `∀ (mkId B)
mkId-∀ B = refl

mkId-∀-inert : (B : Ty) → Inert (mkId (`∀ B))
mkId-∀-inert B = I-all

-- Values and inertness survive the renamings the rules perform, which is
-- what makes fix (a)'s regress feed itself and what lets the installed
-- clause fire again on its own contractum.
-- (`inert-renᶜ`, `value-renᴹ²` and `value-renᴹᴿ` moved to
-- strong-rep-store.proof.TermSubst §2, where the typing-transport lemmas
-- need them for `⊢Λ`'s value premise.)
value-↑ᴹ : ∀ {M} (δ : Alloc) → Value M → Value (↑ᴹ[ δ ] M)
value-↑ᴹ none    v = v
value-↑ᴹ (new R) v = value-renᴹᴿ suc v

-- WHERE THE DESCENT STOPS.  A `∀`-value of tower height 0 is a `Λ`
-- (`canon-∀` has no third shape), so once `TyPeelR-⟪⟫` has consumed the
-- tower it is `TyPeelR-Λ` that fires — and `TyPeelR-Λ` neither renames
-- nor locks anything (§3).  So the run is `height − 1` wrapper steps then
-- one Λ step, and never more.
canon-∀-height : ∀ {Δ V C} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → towerHeight V ≡ 0
  → Σ[ N ∈ Term ] (Value N × (V ≡ Λ N))
canon-∀-height v ⊢V eq with canon-∀ v ⊢V
canon-∀-height v ⊢V eq | inj₁ p = p
canon-∀-height v ⊢V ()
    | inj₂ (W , Θ′ , s′ , vW , refl)

-- … stated as the progress clause it decides, against the LIVE relation.
-- At tower height 0 the step is `TyPeelR-Λ`, which ALLOCATES the cell for
-- the type argument's representation — the contractum is named, and so is
-- the change.
progress-Λ-at-0 : ∀ {Δ Δᶜ V Θ s B A R C} → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → Δ ⊢ᶜ A ~ R
  → towerHeight V ≡ 0
    ----------------------------------------------------------------
  → Σ[ N ∈ Term ]
      ((V ≡ Λ N)
       × (Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
            -→ N ⟪ inst Θ , instReveal 0 s ⟫ ∣ new R))
progress-Λ-at-0 v (⊢·[] (env mwᵥ ⊢V ⊢c smᵢ smₑ wE) wA) rc pA eq
  with conv-all-inv ⊢c
progress-Λ-at-0 v (⊢·[] (env mwᵥ ⊢V ⊢c smᵢ smₑ wE) wA) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s with smᵢ
progress-Λ-at-0 v (⊢·[] (env mwᵥ ⊢V ⊢c smᵢ smₑ wE) wA) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s | _ , same-∀ pᵢ , same-∀ qᵢ
  with conversion-functional (bw-conversion mwᵥ) rc
progress-Λ-at-0 v (⊢·[] (env mwᵥ ⊢V ⊢c smᵢ smₑ wE) wA) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s | _ , same-∀ pᵢ , same-∀ qᵢ | refl
  with canon-∀-height v ⊢V eq
progress-Λ-at-0 v (⊢·[] (env mwᵥ ⊢V ⊢c smᵢ smₑ wE) wA) rc pA eq
  | A₀ , B₀ , refl , eqₑ , ⊢s | _ , same-∀ pᵢ , same-∀ qᵢ | refl
  | N , vN , refl = N , refl , TyPeelR-Λ vN rc ⊢s pA

------------------------------------------------------------------------
-- §5  BETA — the two crossings do not interfere
------------------------------------------------------------------------

-- THE `ƛ` CLAUSE.  A `ƛ` binds a TERM variable, so no type frame changes
-- and `shiftᴵ` must not touch the type side at all.  It does not: on a
-- value image it is the IDENTITY, which is correct because a value image
-- is TERM-CLOSED — and it stays term-closed, because `crossΛᴹ W A` is a
-- BOUNDARY and `env` types its interior at `Γ = []`.
Beta-ƛ-no-shift : ∀ {W A} → shiftᴵ (ival W A) ≡ ival W A
Beta-ƛ-no-shift = refl

Beta-ƛ-crossed-no-shift : ∀ {W A} → shiftᴵ (⇑ᴵ (ival W A)) ≡ ⇑ᴵ (ival W A)
Beta-ƛ-crossed-no-shift = refl

-- … and the two crossings DO NOT INTERFERE (design law: simultaneity).
-- Crossing a `ƛ` then a `Λ` is crossing a `Λ` then a `ƛ`, on the nose,
-- for EVERY image — which is what makes the two clauses of `substᵐ`
-- independent.
⇑ᴵ-shiftᴵ-comm : (i : Img) → ⇑ᴵ (shiftᴵ i) ≡ shiftᴵ (⇑ᴵ i)
⇑ᴵ-shiftᴵ-comm (ivar x)   = refl
⇑ᴵ-shiftᴵ-comm (ival W A) = refl

-- THE `Λ` CROSSING IS REP-ONLY, AND ITS LOCK IS WHAT MAKES IT SO.  A
-- value image crossing a `Λ` is weakened in the representation universe
-- and wrapped in `(lock 0 0 ∷ [])`, whose lock deletes the
-- ordinary name the `Λ` just bound.  So the image's ordinary indices keep
-- their positions — criterion (i) with nothing to shift.
Beta-Λ-crossing : ∀ {W A}
  → ⇑ᴵ (ival W A)
      ≡ ival (renᴹ² (ren² idᵗ suc) W
                ⟪ (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
             (⇑ᵗ A)
Beta-Λ-crossing = refl

-- Beta allocates nothing: the substitution moves no representation.
Beta-no-alloc : ∀ {Δ A N W} → Value W
  → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ ∣ none
Beta-no-alloc = Beta

------------------------------------------------------------------------
-- §6  CANCELR / IDPUSH — exact, inner AND outer
------------------------------------------------------------------------

-- THE INNER FRAME (the one V lives in) is preserved ON THE NOSE: the
-- merged frame's interior IS the inner frame's own.
Move-inner-frame : ∀ {Γ Γᵢ Γ₁ᵢ : Ctxᵗ} (Θ₁ Θ₂ : Boundary)
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ Θ₁ ⇒ Γ₁ᵢ
  → Γ ⊢ⁱ Θ₁ ++ Θ₂ ⇒ Γ₁ᵢ
Move-inner-frame Θ₁ Θ₂ = merged-interior

-- THE OUTER FRAME.  The outer boundary's interior — the position the
-- INNER BOUNDARY node occupies — becomes the plain exterior: the ordinary
-- changes have travelled inward, and the inner boundary REAPPLIES them
-- (`_++_` puts Θ₂'s change list at the tail of Θ₁'s, where the reading
-- runs it FIRST), which is exactly why the composite above holds.
-- Nothing else moves: both conversions are RE-MINTED (`mkId` / `unseal`),
-- not transported.
Move-outer-frame : ∀ {Γ Γᵢ : Ctxᵗ} (Θ₂ : Boundary)
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γ ⊢ⁱ rewind Θ₂ ⇒ Γ
Move-outer-frame Θ₂ = rewind-interior

-- … and the outer frame's CONVERSION context is Θ₂'s own, which is where
-- the redex's outer conversion was read.
Move-outer-conversion : ∀ {Γ Γᵢ Γᶜ : Ctxᵗ} (Θ₂ : Boundary)
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ₂ ⇒ Γᶜ
  → Γ ⊢ᶜ rewind Θ₂ ⇒ Γᶜ
Move-outer-conversion Θ₂ = rewind-conversion

-- V is not renamed at all — it retypes exactly where it was.  That is why
-- neither rule's contractum mentions a renaming, and neither allocates.

------------------------------------------------------------------------
-- §7  THE DROP RULES — the frame change in the OTHER direction, and why
--     it is vacuous
------------------------------------------------------------------------

-- `($ n) ⟪ Θ , id A ⟫ → $ n` moves the literal from the boundary scope's
-- interior OUT to Δ: Θ's locks are undone, so the new frame can be
-- STRICTLY MORE NAMEABLE.  That is a frame gain in the direction the
-- criterion also forbids — but it is VACUOUS, because a literal names no
-- type variable at all: `⊢$`, `⊢true` and `⊢false` type it at EVERY type
-- context and every term context.
Drop$-vacuous : (n : ℕ) (Δ : Ctxᵗ) (Γ : Ctx) → Δ ∣ Γ ⊢ ($ n) ⦂ `ℕ
Drop$-vacuous n Δ Γ = ⊢$

Drop-true-vacuous : (Δ : Ctxᵗ) (Γ : Ctx) → Δ ∣ Γ ⊢ `true ⦂ `𝔹
Drop-true-vacuous Δ Γ = ⊢true

Drop-false-vacuous : (Δ : Ctxᵗ) (Γ : Ctx) → Δ ∣ Γ ⊢ `false ⦂ `𝔹
Drop-false-vacuous Δ Γ = ⊢false

-- AND NO OTHER TERM CAN TAKE THE STEP.  The rule's left-hand side is the
-- LITERAL ITSELF — the drop rules are the only ones whose interior
-- pattern is a constructor rather than a variable — so there is nothing
-- to generalize.  Progress needs no more: a closed value at a base type
-- IS a literal (proof/Canonical.canon-base), which is why the syntactic
-- restriction costs nothing.
Drop$-only-numerals : ∀ {Δ M M′ δ} → Δ ⊢ M -→ M′ ∣ δ
  → (∀ {n Θ A} → M ≡ ($ n) ⟪ Θ , id A ⟫ → M′ ≡ $ n)
Drop$-only-numerals (TyBeta v p)            ()
Drop$-only-numerals (Beta w)                ()
Drop$-only-numerals (Peel v w rc ri rd sc)  ()
Drop$-only-numerals (TyPeelR-Λ v rc ⊢s p)   ()
Drop$-only-numerals (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm p) ()
Drop$-only-numerals (CancelR v ri r₁ d₁ r⋉ sm rc d) ()
Drop$-only-numerals (Drop$ b)               refl = refl
Drop$-only-numerals Drop-true               ()
Drop$-only-numerals Drop-false              ()
Drop$-only-numerals (IdPush v ri r₁ r⋉ sm rc d) ()
Drop$-only-numerals (ξ-·-l st)              ()
Drop$-only-numerals (ξ-·-r v st)            ()
Drop$-only-numerals (ξ-·[] st)              ()
Drop$-only-numerals (ξ-⟪⟫ ri st)            refl =
  ⊥-elim (numeral-¬step st)
  where
  numeral-¬step : ∀ {Δ n M′ δ} → Δ ⊢ ($ n) -→ M′ ∣ δ → ⊥
  numeral-¬step ()

------------------------------------------------------------------------
-- §8  THE ξ RULES — the sibling shift IS the context move
------------------------------------------------------------------------

-- Each congruence reduces a subterm IN PLACE, at the very type context
-- the corresponding TYPING rule reads it on:
--
--   ξ-⟪⟫   premise at the boundary scope's INTERIOR = `env`'s premise
--          context
--
-- (`ξ-·-l`, `ξ-·-r`, `ξ-·[]` read their premise at Δ itself, and there is
-- no ξ-Λ: strong-rep-store never reduces under a type binder.)  This is
-- not an equation: `ξ-⟪⟫` CARRIES the interior reading, which is the same
-- object `env` carries, so the two contexts are identified by
-- `interior-functional` rather than by `refl`.
ξ-⟪⟫-frame : ∀ {Γ Γᵢ Γᵢ′ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ⁱ Θ ⇒ Γᵢ′ → Γᵢ ≡ Γᵢ′
ξ-⟪⟫-frame = interior-functional

-- THE NEW OBLIGATION OF THE STORE.  A congruence leaves a SIBLING behind
-- — the other operand of an application, or the boundary scope the
-- interior stepped inside — and the step may have allocated a cell.  The
-- sibling must move by EXACTLY the move the context made, or its frame
-- lies about which cell each of its representation indices names.  Both
-- are read off the same `Alloc`, so the obligation holds definitionally:
-- at `none` both are the identity, and at `new R` the context gains
-- `bindR R` at index 0 and `map suc` on its name map while the sibling
-- gets `renᴹᴿ suc` / `renᴮᴿ suc`.
ξ-shift-none : (M : Term) (Θ : Boundary) (Δ : Ctxᵗ)
  → (↑ᴹ[ none ] M ≡ M) × (↑ᴮ[ none ] Θ ≡ Θ) × (apply none Δ ≡ Δ)
ξ-shift-none M Θ Δ = refl , refl , refl

ξ-shift-new : (R : Ty) (M : Term) (Θ : Boundary) (Δ : Ctxᵗ)
  → (↑ᴹ[ new R ] M ≡ renᴹᴿ suc M)
    × (↑ᴮ[ new R ] Θ ≡ renᴮᴿ suc Θ)
    × (apply (new R) Δ ≡ (bindR R ∷ reps Δ) ∣ map suc (names Δ))
ξ-shift-new R M Θ Δ = refl , refl , refl

-- … and the reading of the shifted scope at the shifted context is the
-- shifted reading: that is `interior-ren` at `suc`, which is the fact
-- `preserve`'s ξ-⟪⟫ case consumes.  Cited, not restated:
-- strong-rep-store.Boundary §3d.

------------------------------------------------------------------------
-- §9  DEAD SHIFT MACHINERY
------------------------------------------------------------------------

-- `shiftᵐ = renⁿ suc` (strong-rep-store.proof.TermSubst §3) and
-- `canon-shiftᵐ` (proof/Canonicity) have NO CONSUMERS: frame-exact
-- substitution weakens an image with `shiftᴵ`, which is `suc` on a
-- variable image and the IDENTITY on a value image (§5), so the
-- term-variable shift is never
-- applied to a term.  `renⁿ` itself is LIVE — `⊢renⁿ` at the identity
-- renaming is what proves `⊢weakenⁿ`, the lemma that lets a term-closed
-- image type at an arbitrary term context.
--
-- Recorded, not deleted: an audit proposes, it does not land.
shiftᵐ-is-renⁿ : (M : Term) → shiftᵐ M ≡ renⁿ suc M
shiftᵐ-is-renⁿ M = refl
