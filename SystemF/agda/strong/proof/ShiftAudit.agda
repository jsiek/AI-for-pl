module strong.proof.ShiftAudit where

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
-- WHAT THE TWO UNIVERSES CHANGE (2026-09-19).  Two things, and they are
-- what this port is.
--
-- FIRST, the frame identities are no longer EQUATIONS BETWEEN COMPUTED
-- CONTEXTS.  There is no `interior Θ Δ` to write an equation about: a
-- morphism RELATES an exterior to an interior, and the audit's per-site
-- facts are exactly the transport lemmas of `strong.CtxMorph` §3a —
-- `dual-interior` for Peel, `rewind-interior`/`merged-interior` for
-- CancelR and IdPush.  So §2 and §6 below CITE them rather than restating
-- them, and the masked-entry sections of the old module (the `⊑ᵃ`
-- refinement, `Nameable`/`Locked` slot arithmetic, the old single
-- `TyPeelR`'s leak witness, the `unmasked (bind …)` exhibits) are gone
-- with the design that stated them.
--
-- SECOND, a moved subterm is renamed in the TWO UNIVERSES SEPARATELY, and
-- at every site but TyBeta's the ordinary component is the IDENTITY: a
-- lock deletes the ordinary name the crossing introduces, so the
-- surviving ordinary indices keep their positions and only the
-- representation occurrences move.  §3 records that per site, and it is
-- the audit's new headline.
--
--   §1  the site table (comment)
--   §2  Peel                  — EXACT, by `dual-interior`; rep-only shift
--   §3  the two TyPeelR clauses — the Λ clause shifts nothing; the
--       wrapper clause is a rep-only `suc` plus one appended lock
--   §4  TERMINATION — the tower measure, and why the rejected repair
--       (wrap the moved value in the new binder's dual) stalls on it
--   §5  Beta                  — the `ƛ` and `Λ` crossings do not interfere
--   §6  CancelR / IdPush      — exact, inner AND outer
--   §7  Drop$ / Drop-true / Drop-false — vacuous
--   §8  the ξ rules           — nothing moves
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

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Canonical using (canon-∀)

private
  variable
    Δ Δ′ Γᵗ : Ctxᵗ
    Γ : Ctx
    A B C : Ty
    X Y : ℕ
    Θ Θ₁ Θ₂ : CtxMorph

------------------------------------------------------------------------
-- §1  THE SITES
------------------------------------------------------------------------

-- Every place in the live development where a TERM is renamed, shifted or
-- substituted (`grep renᴹ² renᴹ wkᴹ ⇑ᴹ renⁿ shiftᵐ crossΛᴹ substᵐ`):
--
--   RULES that move a subterm
--     Peel        `renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W ⟪ dualMorph Θ , s′ ⟫`
--                                                            §2  EXACT
--     TyPeelR-Λ   `N ⟪ instantiate R Θ , instReveal 0 s ⟫`    §3  EXACT
--     TyPeelR-⟪⟫  `renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc))` on the moved
--                 boundary, plus `addLock0` on its own change list
--                                                            §3  EXACT
--     TyBeta      `N ⟪ instantiate R (morph [] []) , reveal 0 B ⟫`
--                                                            §3  refinement
--     Beta        `N [ W ∶ A ]ᵐ`, i.e. `substᵐ`/`crossΛᴹ`     §5  EXACT
--     CancelR     `V ⟪ Θ₁ ⋉ Θ₂ , … ⟫ ⟪ rewind Θ₂ , … ⟫`       §6  EXACT
--     IdPush      (same two frames)                           §6  EXACT
--     Drop$ / Drop-true / Drop-false                          §7  vacuous
--     ξ-*         nothing moves                               §8  —
--
--   TRANSPORTS, not rules (no term is moved by a reduction; these are the
--   lemmas the cases above are PROVED with, and each one's renaming or
--   reading argument is supplied at the site):
--     `⊢rename`, `renᴹ²`, `renⁿ`, `⊢renⁿ`, `⊢weakenⁿ`,
--     `canon-renᴹ²`/`canon-renⁿ` (proof/Canonicity).

------------------------------------------------------------------------
-- §2  PEEL — the crossing argument's frame is the EXTERIOR, under the
--     boundary's representation bind block
------------------------------------------------------------------------

-- W's frame, before: `Δ`.  After: the dual's interior, which
-- `dual-interior` says is `extendReps (binds Θ) Δ` — `Δ` with the
-- boundary's representation binders in front and NOT ONE ORDINARY NAME
-- ADDED OR REMOVED.  Criterion (i), nothing else: EXACT.
Peel-frame : ∀ {Γᵢ : Ctxᵗ} (Θ : CtxMorph) (Γ : Ctxᵗ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ dualMorph Θ ⇒ extendReps (binds Θ) Γ
Peel-frame Θ Γ = dual-interior

-- … and the movement the rule applies to W matches that frame EXACTLY:
-- its ORDINARY component is the identity, so no ordinary index moves, and
-- its REPRESENTATION component is `wkN (numBinds Θ)`, which is the shift
-- past the bind block `extendReps (binds Θ)` installs.
Peel-move-ordinary : (Θ : CtxMorph)
  → ordinary (ren² idᵗ (wkN (numBinds Θ))) ≡ idᵗ
Peel-move-ordinary Θ = refl

Peel-move-represent : (Θ : CtxMorph)
  → represent (ren² idᵗ (wkN (numBinds Θ))) ≡ wkN (numBinds Θ)
Peel-move-represent Θ = refl

-- The reading `dual-interior` produces is that same shift on the name
-- map: `extendReps Rs` sends every entry to `length Rs + _`.
Peel-frame-names : (Rs : List Ty) (Γ : Ctxᵗ)
  → names (extendReps Rs Γ) ≡ shiftRVars (length Rs) (names Γ)
Peel-frame-names Rs Γ = refl

-- The dual adds no representation binder of its own: the crossing
-- argument is already inside the boundary's block.
Peel-dual-numBinds : (Θ : CtxMorph) → numBinds (dualMorph Θ) ≡ 0
Peel-dual-numBinds Θ = refl

------------------------------------------------------------------------
-- §3  THE TWO TYPEELR CLAUSES, AND TYBETA
------------------------------------------------------------------------

-- THE Λ CLAUSE MOVES NOTHING.  `N` already lives one `abstR` binder in
-- (`⊢Λ`), and `instantiate R Θ` REFINES that binder to `bindR R` while
-- restoring its ordinary name at position 0 (the appended `unlock 0 0`).
-- So the frame move is criterion (ii) and there is no renaming at all —
-- the contractum does not mention a `renᴹ²`.
TyPeelR-Λ-refinement : (R : Ty) (Θ : CtxMorph)
  → binds (instantiate R Θ) ≡ R ∷ binds Θ
TyPeelR-Λ-refinement R Θ = refl

TyPeelR-Λ-numBinds : (R : Ty) (Θ : CtxMorph)
  → numBinds (instantiate R Θ) ≡ suc (numBinds Θ)
TyPeelR-Λ-numBinds R Θ = refl

-- TyBeta is the same refinement one `∀` out: `instantiate R (morph [] [])`
-- turns the `Λ`'s own abstract binder into the event's represented one.
TyBeta-refinement : (R : Ty)
  → binds (instantiate R (morph [] [])) ≡ R ∷ []
TyBeta-refinement R = refl

TyBeta-restores-name-0 : (R : Ty)
  → changes (instantiate R (morph [] [])) ≡ unlock 0 0 ∷ []
TyBeta-restores-name-0 R = refl

-- THE WRAPPER CLAUSE.  The moved boundary crosses ONE fresh binder, and
-- its appended `lock 0 (numBinds Θ′)` DELETES the fresh ordinary name
-- again.  So the paired renaming is rep-only — ordinary component `idᵗ`,
-- representation component `extN (numBinds Θ′) suc` — and the moved
-- boundary's ordinary indices keep their positions.  That is the whole of
-- the 2026-09-08 repair, restated in the universe that now carries it.
TyPeelR-⟪⟫-move-ordinary : (Θ′ : CtxMorph)
  → ordinary (ren² idᵗ (extN (numBinds Θ′) suc)) ≡ idᵗ
TyPeelR-⟪⟫-move-ordinary Θ′ = refl

-- The appended lock names position 0 and the representation variable
-- immediately outside the moved boundary's own bind prefix — and it is
-- APPENDED, so it acts FIRST (the change list is read head-last).
TyPeelR-⟪⟫-addLock0 : (Θ′ : CtxMorph)
  → changes (addLock0 Θ′)
      ≡ changes Θ′ ++ (lock 0 (numBinds Θ′) ∷ [])
TyPeelR-⟪⟫-addLock0 Θ′ = refl

-- … and the moved boundary's own bind block is untouched by the lock.
TyPeelR-⟪⟫-addLock0-binds : (Θ′ : CtxMorph)
  → binds (addLock0 Θ′) ≡ binds Θ′
TyPeelR-⟪⟫-addLock0-binds Θ′ = refl

------------------------------------------------------------------------
-- §4  TERMINATION — THE TOWER MEASURE
------------------------------------------------------------------------

-- The wrapper clause's contractum contains
--
--    (… ⟪ addLock0 … , `∀ s″ ⟫) ·[ … , ` 0 ]
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
towerHeight-renᴹ² : (ρ : TyRename) (M : Term)
  → towerHeight (renᴹ² ρ M) ≡ towerHeight M
towerHeight-renᴹ² ρ (` x)          = refl
towerHeight-renᴹ² ρ ($ n)          = refl
towerHeight-renᴹ² ρ `true          = refl
towerHeight-renᴹ² ρ `false         = refl
towerHeight-renᴹ² ρ (ƛ A ∙ N)      = refl
towerHeight-renᴹ² ρ (L · M)        = refl
towerHeight-renᴹ² ρ (Λ N)          = refl
towerHeight-renᴹ² ρ (L ·[ B , A ]) = refl
towerHeight-renᴹ² ρ (M ⟪ Θ , c ⟫)  =
  cong suc (towerHeight-renᴹ² (underReps-ren (numBinds Θ) ρ) M)

-- THE MEASURE STRICTLY DECREASES.  The ∀-value the contractum's inner
-- `·[]` instantiates is ONE BOUNDARY SHORTER than the one the redex's
-- `·[]` instantiated.
TyPeelR-⟪⟫-height : (W : Term) (Θ′ Θ : CtxMorph) (s′ s : Conv)
  → towerHeight (renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W
                   ⟪ addLock0 (renᴮ² (ren² idᵗ suc) Θ′)
                   , `∀ (renᶜ (extᵗ suc) s′) ⟫)
      ≡ towerHeight ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ∸ 1
TyPeelR-⟪⟫-height W Θ′ Θ s′ s =
  cong suc (towerHeight-renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W)

-- THE REJECTED REPAIR STALLS AT THE SAME MEASURE.  Fix (a) — wrap the
-- moved value in the new binder's dual, with an identity conversion at
-- the value's own type — puts the ∀-value under a FRESH boundary, so the
-- height is the redex's height again: nothing is consumed.  THIS is the
-- difference between (a) and the installed clause: `TyPeelR-⟪⟫` CONSUMES
-- a boundary that was already there, (a) MINTS a new one.
fixA-height-stalls : (V : Term) (Θ : CtxMorph) (s : Conv) (Bᵢ : Ty)
  → towerHeight (renᴹ² (ren² idᵗ suc) V
                   ⟪ morph [] (lock 0 0 ∷ []) , mkId (`∀ Bᵢ) ⟫)
      ≡ towerHeight (V ⟪ Θ , `∀ s ⟫)
fixA-height-stalls V Θ s Bᵢ =
  cong suc (towerHeight-renᴹ² (ren² idᵗ suc) V)

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
inert-renᶜ : ∀ {c} (ρ : Renameᵗ) → Inert c → Inert (renᶜ ρ c)
inert-renᶜ ρ I-idv  = I-idv
inert-renᶜ ρ I-seal = I-seal
inert-renᶜ ρ I-fun  = I-fun
inert-renᶜ ρ I-all  = I-all

value-renᴹ² : ∀ {M} (ρ : TyRename) → Value M → Value (renᴹ² ρ M)
value-renᴹ² ρ V-$         = V-$
value-renᴹ² ρ V-true      = V-true
value-renᴹ² ρ V-false     = V-false
value-renᴹ² ρ V-ƛ         = V-ƛ
value-renᴹ² ρ (V-Λ v)     = V-Λ (value-renᴹ² (underΛ-ren ρ) v)
value-renᴹ² ρ (V-⟪⟫ v ic) = V-⟪⟫ (value-renᴹ² _ v) (inert-renᶜ _ ic)

value-wkᴹ : ∀ {M} (n : ℕ) → Value M → Value (wkᴹ n M)
value-wkᴹ n v = value-renᴹ² (ren² (wkN n) (wkN n)) v

-- WHERE THE DESCENT STOPS.  A `∀`-value of tower height 0 is a `Λ`
-- (`canon-∀` has no third shape), so once `TyPeelR-⟪⟫` has consumed the
-- tower it is `TyPeelR-Λ` that fires — and `TyPeelR-Λ` neither renames
-- nor locks anything (§3).  So the run is `height − 1` wrapper steps then
-- one Λ step, and never more.
canon-∀-height : ∀ {Δ V C} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → towerHeight V ≡ 0
  → Σ[ N ∈ Term ] (Value N × (V ≡ Λ N))
canon-∀-height v ⊢V eq with canon-∀ v ⊢V
... | inj₁ p                          = p
canon-∀-height v ⊢V ()
    | inj₂ (W , Θ′ , s′ , vW , refl)

-- … stated as the progress clause it decides, against the LIVE relation.
-- At tower height 0 the step is `TyPeelR-Λ`, with the contractum named.
progress-Λ-at-0 : ∀ {Δ Δᶜ V Θ s B A R C} → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → Δ ⊢ᶜ A ~ R
  → towerHeight V ≡ 0
    ----------------------------------------------------------------
  → Σ[ N ∈ Term ]
      ((V ≡ Λ N)
       × (Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
            -→ N ⟪ instantiate R Θ , instReveal 0 s ⟫))
progress-Λ-at-0 v (⊢·[] (env mwᵥ ⊢V ⊢c smᵢ smₑ wE) wA) rc pA eq
  with conv-all-inv ⊢c
... | A₀ , B₀ , refl , eqₑ , ⊢s with smᵢ
... | _ , same-∀ pᵢ , same-∀ qᵢ
  with conversion-functional (mw-conversion mwᵥ) rc
... | refl with canon-∀-height v ⊢V eq
... | N , vN , refl = N , refl , TyPeelR-Λ vN rc ⊢s pA

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
-- and wrapped in `morph [] (lock 0 0 ∷ [])`, whose lock deletes the
-- ordinary name the `Λ` just bound.  So the image's ordinary indices keep
-- their positions — criterion (i) with nothing to shift.
Beta-Λ-crossing : ∀ {W A}
  → ⇑ᴵ (ival W A)
      ≡ ival (renᴹ² (ren² idᵗ suc) W
                ⟪ morph [] (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
             (⇑ᵗ A)
Beta-Λ-crossing = refl

------------------------------------------------------------------------
-- §6  CANCELR / IDPUSH — exact, inner AND outer
------------------------------------------------------------------------

-- THE INNER FRAME (the one V lives in) is preserved ON THE NOSE: the
-- merged frame's interior IS the inner frame's own.
Move-inner-frame : ∀ {Γ Γᵢ Γ₁ᵢ : Ctxᵗ} (Θ₁ Θ₂ : CtxMorph)
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ Θ₁ ⇒ Γ₁ᵢ
  → extendReps (binds Θ₂) Γ ⊢ⁱ Θ₁ ⋉ Θ₂ ⇒ Γ₁ᵢ
Move-inner-frame Θ₁ Θ₂ = merged-interior

-- THE OUTER FRAME.  The outer boundary's interior — the position the
-- INNER BOUNDARY node occupies — becomes the plain exterior under Θ₂'s
-- bind block: the ordinary changes have travelled inward, and the inner
-- boundary REAPPLIES them (`_⋉_` puts Θ₂'s lifted change list at the tail
-- of Θ₁'s, where the reading runs it FIRST), which is exactly why the
-- composite above holds.  Nothing else moves: both conversions are
-- RE-MINTED (`mkId` / `unseal`), not transported.
Move-outer-frame : ∀ {Γ Γᵢ : Ctxᵗ} (Θ₂ : CtxMorph)
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γ ⊢ⁱ rewind Θ₂ ⇒ extendReps (binds Θ₂) Γ
Move-outer-frame Θ₂ = rewind-interior

-- … and the outer frame's CONVERSION context is Θ₂'s own, which is where
-- the redex's outer conversion was read.
Move-outer-conversion : ∀ {Γ Γᵢ Γᶜ : Ctxᵗ} (Θ₂ : CtxMorph)
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ₂ ⇒ Γᶜ
  → Γ ⊢ᶜ rewind Θ₂ ⇒ Γᶜ
Move-outer-conversion Θ₂ = rewind-conversion

-- Neither frame adds a representation binder beyond the ones the redex
-- already had.
Move-outer-numBinds : (Θ₂ : CtxMorph) → numBinds (rewind Θ₂) ≡ numBinds Θ₂
Move-outer-numBinds Θ₂ = refl

Move-inner-numBinds : (Θ₁ Θ₂ : CtxMorph) → numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁
Move-inner-numBinds Θ₁ Θ₂ = refl

-- V is not renamed at all — it retypes exactly where it was.  That is why
-- neither rule's contractum mentions a `renᴹ²`.

------------------------------------------------------------------------
-- §7  THE DROP RULES — the frame change in the OTHER direction, and why
--     it is vacuous
------------------------------------------------------------------------

-- `($ n) ⟪ Θ , id A ⟫ → $ n` moves the literal from the morphism's
-- interior OUT to Δ: the bind block disappears and Θ's locks are undone,
-- so the new frame can be STRICTLY MORE NAMEABLE.  That is a frame gain
-- in the direction the criterion also forbids — but it is VACUOUS,
-- because a literal names no type variable at all: `⊢$`, `⊢true` and
-- `⊢false` type it at EVERY type context and every term context.
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
Drop$-only-numerals : ∀ {Δ M M′} → Δ ⊢ M -→ M′
  → (∀ {n Θ A} → M ≡ ($ n) ⟪ Θ , id A ⟫ → M′ ≡ $ n)
Drop$-only-numerals (TyBeta v p)            ()
Drop$-only-numerals (Beta w)                ()
Drop$-only-numerals (Peel v w rc ri rd sc)  ()
Drop$-only-numerals (TyPeelR-Λ v rc ⊢s p)   ()
Drop$-only-numerals (TyPeelR-⟪⟫ v ri rc ⊢s sm p) ()
Drop$-only-numerals (CancelR v r⋉ sm rc d)  ()
Drop$-only-numerals (Drop$ b)               refl = refl
Drop$-only-numerals Drop-true               ()
Drop$-only-numerals Drop-false              ()
Drop$-only-numerals (IdPush v ri r₁ r⋉ sm rc d) ()
Drop$-only-numerals (ξ-·-l st)              ()
Drop$-only-numerals (ξ-·-r v st)            ()
Drop$-only-numerals (ξ-·[] st)              ()
Drop$-only-numerals (ξ-Λ st)                ()
Drop$-only-numerals (ξ-⟪⟫ ri st)            refl =
  ⊥-elim (numeral-¬step st)
  where
  numeral-¬step : ∀ {Δ n M′} → Δ ⊢ ($ n) -→ M′ → ⊥
  numeral-¬step ()

------------------------------------------------------------------------
-- §8  THE ξ RULES — nothing moves, and the frames are the binder's own
------------------------------------------------------------------------

-- Each congruence reduces a subterm IN PLACE, at the very type context
-- the corresponding TYPING rule reads it on:
--
--   ξ-Λ    premise at `underΛ Δ`             =  `⊢Λ`'s premise context
--   ξ-⟪⟫   premise at the morphism's INTERIOR =  `env`'s premise context
--
-- (`ξ-·-l`, `ξ-·-r`, `ξ-·[]` do not change the context at all.)  The
-- second is no longer an equation: `ξ-⟪⟫` CARRIES the interior reading,
-- which is the same object `env` carries, so the two contexts are
-- identified by `interior-functional` rather than by `refl`.
ξ-Λ-frame : (Δ : Ctxᵗ) → underΛ Δ ≡ underΛ Δ
ξ-Λ-frame Δ = refl

ξ-⟪⟫-frame : ∀ {Γ Γᵢ Γᵢ′ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ⁱ Θ ⇒ Γᵢ′ → Γᵢ ≡ Γᵢ′
ξ-⟪⟫-frame = interior-functional

------------------------------------------------------------------------
-- §9  DEAD SHIFT MACHINERY
------------------------------------------------------------------------

-- `shiftᵐ = renⁿ suc` (strong.TermSubst §3) and `canon-shiftᵐ`
-- (proof/Canonicity) have NO CONSUMERS: frame-exact substitution weakens
-- an image with `shiftᴵ`, which is `suc` on a variable image and the
-- IDENTITY on a value image (§5), so the term-variable shift is never
-- applied to a term.  `renⁿ` itself is LIVE — `⊢renⁿ` at the identity
-- renaming is what proves `⊢weakenⁿ`, the lemma that lets a term-closed
-- image type at an arbitrary term context.
--
-- Recorded, not deleted: an audit proposes, it does not land.
shiftᵐ-is-renⁿ : (M : Term) → shiftᵐ M ≡ renⁿ suc M
shiftᵐ-is-renⁿ M = refl
