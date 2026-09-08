module strong.proof.ShiftAudit where

-- THE SHIFT AUDIT — every place a rule MOVES A SUBTERM, checked against
-- FRAME EXACTNESS (Jeremy, 2026-09-08: "frame exactness is the main point
-- of Strong System F").
--
-- THE CRITERION.  Whenever a rule moves a subterm to a new position, the
-- subterm's TYPE CONTEXT at the new position must be EXACTLY its context
-- at the old position, up to
--
--   (i)  the index shift past the binders it CROSSED, and
--   (ii) refinement `abst → bind` of a slot it could ALREADY NAME
--        (TyBeta's reveal, TyPeelR's `instReveal`).
--
-- Any slot the subterm COULD NOT NAME before and CAN NAME after is a
-- FRAME LEAK, even when the subterm's shifted indices cannot reach it:
-- the frame must SAY THE TRUTH about what the subterm may name.
--
-- THE REPAIR IS INSTALLED (2026-09-08).  The one leak the audit found —
-- TyPeelR's moved value gained the new binder's slot UNMASKED — is closed
-- in the LIVE rules: `TyPeelR` is now the two clauses `TyPeelR-Λ` and
-- `TyPeelR-⟪⟫` (strong.Reduction).  So this module records the audit's
-- FINDINGS against the live rule set: the per-site frame identities, the
-- witness of what the leak was, the machine refutation of the repair that
-- LOOPS, and the tower measure that makes the installed one terminate.
--
--   §1  the site table (comment)
--   §2  Peel                  — EXACT, by (†)
--   §3  TyPeelR (V's frame)   — the LEAK, as it stood, and its witness
--   §4  fix (a), "wrap V in the new binder's dual" — REFUTED, it LOOPS
--   §5  TyPeelR-Λ             — the live clause: EXACT, no shift at all
--   §5b TyPeelR-⟪⟫            — the live clause: `wkᴹ 1` plus one lock
--   §5c the frame exactness of the two clauses, the tower measure, and a
--       closed two-deep run with every state typed
--   §6  TyBeta                — exact up to refinement
--   §7  Beta                  — exact (crossΛ), and the `ƛ` clause
--   §8  CancelR / IdPush      — exact, inner AND outer
--   §9  Drop$                 — vacuous (a numeral has no type variables)
--   §10 the ξ rules           — nothing moves
--   §11 dead shift machinery
--
-- The verdict table, with the fix candidates and their hazards, is
-- notes/ShiftAudit.md; the frame-identity table it feeds is Design.md §7.
-- The tightness tests for the two clauses are Examples §15b.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ
        ; _[_:=_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.TermSubst
open import strong.Reduction

open import strong.proof.Preserve
  using (⊢instReveal; wf-[]ᵗ; wf-∀⁻; ∀-inj; subst-at-0; shiftBy-[]ᵗ
        ; ren-suc-[0])
open import strong.Preservation using (preservation)
open import strong.proof.PeelDual using (interior-dual)
open import strong.proof.MoveScope using (interior-rewind; interior-⋉-rewind)
open import strong.proof.Canonical using (canon-∀)
open import strong.Examples
  using (interior-TyBeta; interior-TyPeelR; interior-Beta-Λ)

private
  variable
    Δ Δ′ : Ctxᵗ
    Γ : Ctx
    A B C : Ty
    X Y : ℕ
    Θ Θ₁ Θ₂ : CtxMorph

------------------------------------------------------------------------
-- §1  THE SITES
------------------------------------------------------------------------

-- Every place in the live development where a TERM is renamed, shifted or
-- substituted (`grep wkᴹ ⇑ᴹ renᴹ renⁿ shiftᵐ crossΛ substᵐ`):
--
--   RULES that move a subterm
--     Peel        `wkᴹ (numBinds Θ) W ⟪ dual Θ , s ⟫`        §2  EXACT
--     TyPeelR     `wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ]`
--                 the SINGLE rule, now REPLACED                §3  LEAK
--     TyPeelR-Λ   `N ⟪ morph (A ∷ binds Θ) (changes Θ) , … ⟫` §5  EXACT
--     TyPeelR-⟪⟫  `wkᴹ 1` on the moved boundary, plus
--                 `addLock0` on its own change list           §5b EXACT
--     TyBeta      `N ⟪ morph (A ∷ []) [] , reveal 0 B ⟫`      §6  refinement
--     Beta        `N [ W ∶ A ]ᵐ`, i.e. `substᵐ`/`crossΛ`      §7  EXACT
--     CancelR     `V ⟪ Θ₁ ⋉ Θ₂ , … ⟫ ⟪ rewind Θ₂ , … ⟫`       §8  EXACT
--     IdPush      (same two frames)                           §8  EXACT
--     Drop$       `($ n) ⟪ Θ , id A ⟫ → $ n`                  §9  vacuous
--     ξ-*         nothing moves                               §10 —
--
--   TRANSPORTS, not rules (no term is moved by a reduction; these are the
--   lemmas the cases above are PROVED with, and each one's `Ren`/`⊑ᵃ`
--   argument is supplied at the site):
--     `⊢rename`, `⊢retag`, `Ren-wk`, `renᴹ`, `renⁿ`, `⊢renⁿ`,
--     `⊢weakenⁿ`, `canon-renᴹ`/`canon-renⁿ` (proof/Canonicity).
--
--   DEAD after PR #199: `shiftᵐ` and `canon-shiftᵐ` (§11).

------------------------------------------------------------------------
-- §2  PEEL — the crossing argument's frame is the EXTERIOR, under a
--     MASKED bind prefix
------------------------------------------------------------------------

-- W's frame, before: `Δ`.  After: `interior (dual Θ) (interior Θ Δ)`,
-- which (†) says is `Δ` with `numBinds Θ` MASKED bind entries in front —
-- and `wkᴹ (numBinds Θ)` shifts W past exactly those.  Criterion (i),
-- nothing else: EXACT.
Peel-frame : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ᵐ Θ
  → interior (dual Θ) (interior Θ Δ)
      ≡ map maskEnt (pushBinds (binds Θ) []) ++ Δ
Peel-frame = interior-dual

-- … and the new slots are UNNAMEABLE, which is what makes (i) the whole
-- story: the crossing argument may not name a slot it could not name
-- before.  (At `binds Θ ≡ []` there is no new slot at all and the frame
-- is `Δ` on the nose.)
Peel-slot0-locked : (As : List Ty) (Δ : Ctxᵗ)
  → ¬ ((map maskEnt (pushBinds (A ∷ As) []) ++ Δ) ∋tv 0)
Peel-slot0-locked As Δ (_ , ez , ())

------------------------------------------------------------------------
-- §3  TYPEELR — THE LEAK, AS IT STOOD BEFORE THE SPLIT
------------------------------------------------------------------------

-- The single rule is GONE (strong.Reduction carries `TyPeelR-Λ` and
-- `TyPeelR-⟪⟫` instead), so this section is the RECORD of what the leak
-- was and of what closing it required.  Everything below is a statement
-- about FRAMES, and every frame here is still a frame the live clauses
-- produce, so nothing in it is stale.

-- THE MOVE.  `V`, the interior of the crossed boundary, was typed at
-- `interior Θ Δ` in the redex and at
--
--   interior (morph (A ∷ binds Θ) (changes Θ)) Δ
--     ≡ unmasked (bind (shiftBy (numBinds Θ) A)) ∷ interior Θ Δ
--
-- in the contractum (`interior-TyPeelR`, Examples §15).  So V's frame
-- gains ONE ENTRY at slot 0, and it gains it UNMASKED.  V is shifted by
-- `wkᴹ 1`, so V's own indices land at ≥ 1 and cannot reach the new slot —
-- the rule is SOUND, and Examples §15b checks that an ill-typed V stays
-- ill-typed.  But by the criterion the FRAME LIES: it offers V a slot V
-- could not name before.
--
-- THE THREE FACTS.  (a) the frame HAS the slot, nameably; (b) V DOES NOT
-- NEED it — the very `⊢rename` the live proof uses works at the MASKED
-- entry, because `Ren-wk` is `Ren suc Δ (E ∷ Δ)` for EVERY entry E;
-- (c) the INSTANTIATION NODE `·[ … , ` 0 ]` does need it, and it shares
-- V's frame.  (a)+(b) is the leak; (c) is why no repair is possible
-- WITHOUT CHANGING THE CONTRACTUM'S SHAPE (§4, §5).

-- (a) the new slot is NAMEABLE in the moved value's frame
TyPeelR-slot0-nameable : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (morph (A ∷ binds Θ) (changes Θ)) Δ ∋tv 0
TyPeelR-slot0-nameable A Θ Δ = _ , ez , nameable

-- … so a TYPE at V's position may name it
TyPeelR-slot0-typeable : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (morph (A ∷ binds Θ) (changes Θ)) Δ ⊢ᵗ ` 0
TyPeelR-slot0-typeable A Θ Δ = wf-var (TyPeelR-slot0-nameable A Θ Δ)

-- (b) V IS INDIFFERENT TO THE LOCK.  This is the live proof's own
-- `⊢wkV`, with `unmasked` replaced by `masked`: the derivation goes
-- through unchanged, so the `unmasked` in the live rule's frame is
-- STRICTLY MORE THAN V USES.
TyPeelR-V-tight : ∀ {V Bᵥ}
  → interior Θ Δ ∣ [] ⊢ V ⦂ Bᵥ
    ---------------------------------------------------------------
  → (masked (bind C) ∷ interior Θ Δ) ∣ [] ⊢ wkᴹ 1 V ⦂ ⇑ᵗ Bᵥ
TyPeelR-V-tight ⊢V = ⊢rename Ren-wk Inj-suc ⊢V

-- (c) THE NODE IS NOT.  With the slot masked the pushed-in
-- `·[ … , ` 0 ]` has no well-formed type argument, so V and the node
-- CANNOT both be served by one frame.
TyPeelR-node-needs-slot0 : ¬ ((masked (bind C) ∷ Δ) ⊢ᵗ ` 0)
TyPeelR-node-needs-slot0 (wf-var (_ , ez , ()))

-- THE LEAK, AS A REFINEMENT STEP.  The frame the moved value needs and
-- the frame the rule gives it differ by exactly ONE `le-mu` — the
-- RE-EXPOSURE clause, the one step `_⊑ᵃ_` (the refinement a TERM may
-- travel along, strong.Ctx §4b) REFUSES.  That is the sharpest statement
-- of the leak: TyPeelR moves V along a frame change that is `_⊑_` but not
-- `_⊑ᵃ_`.
TyPeelR-leak-⊑ : (C : Ty) (Δ : Ctxᵗ)
  → (masked (bind C) ∷ Δ) ⊑ (unmasked (bind C) ∷ Δ)
TyPeelR-leak-⊑ C Δ = le∷ (le-mu le-bb) (⊑-refl Δ)

TyPeelR-leak-¬⊑ᵃ : (C : Ty) (Δ : Ctxᵗ)
  → ¬ ((masked (bind C) ∷ Δ) ⊑ᵃ (unmasked (bind C) ∷ Δ))
TyPeelR-leak-¬⊑ᵃ C Δ (la∷ () _)

-- CONTRAST — the two rules that DO mask what they introduce.  Peel is
-- §2 above; frame-exact Beta's Λ crossing is `interior-Beta-Λ`, and its
-- slot 0 is REFUSED:
Beta-Λ-slot0-locked : (Δ : Ctxᵗ)
  → ¬ (interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ∋tv 0)
Beta-Λ-slot0-locked Δ (_ , ez , ())

------------------------------------------------------------------------
-- §3a  THE WITNESS — the frame authorizes strictly more than the move
--      can produce
------------------------------------------------------------------------

-- Examples §15b's redex, one binder in.  `Θᵃ` masks the single exterior
-- binder, so V's frame in the redex is `masked (bind `ℕ) ∷ []` and in the
-- contractum `unmasked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []`.
Δᵃ : Ctxᵗ
Δᵃ = unmasked (bind `ℕ) ∷ []

Θᵃ : CtxMorph
Θᵃ = morph [] (lock 0 ∷ [])

-- the redex's frame for V, and the contractum's
Ξold Ξnew Ξtight : Ctxᵗ
Ξold   = interior Θᵃ Δᵃ
Ξnew   = interior (morph (`ℕ ∷ binds Θᵃ) (changes Θᵃ)) Δᵃ
Ξtight = masked (bind `ℕ) ∷ Ξold

_ : Ξold ≡ masked (bind `ℕ) ∷ []
_ = refl

_ : Ξnew ≡ unmasked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []
_ = refl

_ : Ξnew ≡ unmasked (bind `ℕ) ∷ Ξold
_ = interior-TyPeelR `ℕ Θᵃ Δᵃ

-- THE WITNESS TERM: a value whose annotation NAMES the new slot.
nmᵃ : Term
nmᵃ = ƛ (` 0) ∙ (` 0)

-- It types at the frame the rule hands V …
⊢nmᵃ : Ξnew ∣ [] ⊢ nmᵃ ⦂ ((` 0) ⇒ (` 0))
⊢nmᵃ = ⊢ƛ (wf-var (_ , ez , nameable)) (⊢` here)

-- … and is REFUSED at the tight frame, for the one localized reason
-- (`wf-var` at a masked slot) — Jeremy's tightness test, run on the
-- FRAME rather than on the rule.
¬⊢nmᵃ : ∀ {T} → ¬ (Ξtight ∣ [] ⊢ nmᵃ ⦂ T)
¬⊢nmᵃ (⊢ƛ (wf-var (_ , ez , ())) _)

-- AND NO MOVED VALUE CAN BE IT.  `wkᴹ 1` never produces a term that
-- names slot 0, so the extra nameability the frame grants is nameability
-- NOTHING AT THAT POSITION CAN USE — the frame does not say the truth.
wkᴹ1-misses-nmᵃ : (V : Term) → wkᴹ 1 V ≢ nmᵃ
wkᴹ1-misses-nmᵃ (` x)          ()
wkᴹ1-misses-nmᵃ ($ n)          ()
wkᴹ1-misses-nmᵃ (ƛ (` X) ∙ N)  ()
wkᴹ1-misses-nmᵃ (ƛ `ℕ ∙ N)     ()
wkᴹ1-misses-nmᵃ (ƛ `𝔹 ∙ N)     ()
wkᴹ1-misses-nmᵃ (ƛ (A ⇒ B) ∙ N) ()
wkᴹ1-misses-nmᵃ (ƛ (`∀ A) ∙ N) ()
wkᴹ1-misses-nmᵃ (L · M)        ()
wkᴹ1-misses-nmᵃ (Λ N)          ()
wkᴹ1-misses-nmᵃ (L ·[ B , A ]) ()
wkᴹ1-misses-nmᵃ (M ⟪ Θ , c ⟫)  ()

------------------------------------------------------------------------
-- §4  FIX (a) — WRAP V IN THE NEW BINDER'S DUAL.  IT LOOPS.
------------------------------------------------------------------------

-- THE CANDIDATE.  Give the moved value its own boundary, whose frame is
-- the new binder's DUAL — `dual (morph (A ∷ []) []) ≡ morph [] (lock 0 ∷ [])`,
-- the same shape frame-exact Beta mints at a crossed `Λ` — and whose
-- conversion is the identity at V's own (shifted) type:
--
--   (wkᴹ 1 V ⟪ morph [] (lock 0 ∷ []) , mkId (`∀ Bᵢ↑) ⟫) ·[ Bᵢ↑ , ` 0 ]
--
-- The frame identity is then exact (`interior-Beta-Λ`'s shape at a `bind`
-- head), and the instantiation node keeps the nameable slot it needs.
--
-- THE HAZARD.  An identity conversion at a `∀` type is NECESSARILY a
-- `` `∀ `` conversion — `conv-id` wants a base type and `conv-idv` a
-- variable, so `mkId` has no other spelling — hence the inserted layer is
-- INERT `I-all`, hence the wrapped value sitting under `·[ … ]` is ITSELF
-- A TYPEELR REDEX.  Fix (a) does not converge: it inserts one layer per
-- step, forever.

-- the identity at a `∀` is a `` `∀ `` conversion, by definition
mkId-∀ : (B : Ty) → mkId (`∀ B) ≡ `∀ (mkId B)
mkId-∀ B = refl

-- … and is therefore INERT at `I-all`
mkId-∀-inert : (B : Ty) → Inert (mkId (`∀ B))
mkId-∀-inert B = I-all

-- Values survive the shift the rule performs, and so does inertness —
-- which is what makes the regress below SELF-FEEDING.
inert-renᶜ : ∀ {c} (ρ : Renameᵗ) → Inert c → Inert (renᶜ ρ c)
inert-renᶜ ρ I-idv  = I-idv
inert-renᶜ ρ I-seal = I-seal
inert-renᶜ ρ I-fun  = I-fun
inert-renᶜ ρ I-all  = I-all

value-renᴹ : ∀ {M} (ρ : Renameᵗ) → Value M → Value (renᴹ ρ M)
value-renᴹ ρ V-$          = V-$
value-renᴹ ρ V-ƛ          = V-ƛ
value-renᴹ ρ (V-Λ v)      = V-Λ (value-renᴹ (extᵗ ρ) v)
value-renᴹ ρ (V-⟪⟫ v ic)  = V-⟪⟫ (value-renᴹ _ v) (inert-renᶜ _ ic)

value-wkᴹ : ∀ {M} (n : ℕ) → Value M → Value (wkᴹ n M)
value-wkᴹ n v = value-renᴹ (wkN n) v

-- The shape fix (a) creates: a value under the new binder's dual,
-- applied to the new binder's name.
loopShape : Term → Ty → Ty → Term
loopShape V Bᵢ A = (V ⟪ morph [] (lock 0 ∷ []) , mkId (`∀ Bᵢ) ⟫) ·[ Bᵢ , A ]

-- THE PROTOTYPE RULE SET — fix (a), NOT the live rule.  Only the two
-- rules the regress needs: the repaired TyPeelR and the congruence that
-- lets it fire under the boundary it just built.
infix 2 _⊢_-→ᵃ_
data _⊢_-→ᵃ_ : Ctxᵗ → Term → Term → Set where

  TyPeelR-a : ∀ {Δ V Θ s B A Bᵢ Bₑ} → Value V
    → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ᵃ (loopShape (wkᴹ 1 V) (renameᵗ (extᵗ suc) Bᵢ) (` 0))
              ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

  ξᵃ-⟪⟫ : ∀ {Δ M M′ Θ c} → interior Θ Δ ⊢ M -→ᵃ M′
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ᵃ M′ ⟪ Θ , c ⟫

-- THE REGRESS, IN GENERAL.  A `loopShape` term steps to a `loopShape`
-- term UNDER ONE MORE BOUNDARY: the fresh dual layer fix (a) inserts is
-- a `` `∀ `` conversion over a value, so the descent never bottoms out at
-- the `Λ` — a new layer is planted on top of it at every step.
--
-- THE TWO PREMISES REGENERATE.  `Value (wkᴹ 1 V)` is `value-wkᴹ`, and
-- the conversion typing is `mkId-⊢` from the type's well-formedness
-- ALONE.  So the answer to "does TyPeelR require anything of `s` that
-- `mkId` fails?" is NO — `mkId` is exactly what the wrapper carries, and
-- `mkId-⊢` types it wherever the type is well formed, which the
-- wrapper's own `env` premise guarantees.
fixA-loop-step : ∀ {Δ V} (Bᵢ A : Ty) → Value V
  → (unmasked abst ∷ convCtx (morph [] (lock 0 ∷ [])) Δ) ⊢ᵗ Bᵢ
    -----------------------------------------------------------------
  → Δ ⊢ loopShape V Bᵢ A
      -→ᵃ (loopShape (wkᴹ 1 V) (renameᵗ (extᵗ suc) Bᵢ) (` 0))
            ⟪ morph (A ∷ []) (lock 0 ∷ []) , instReveal 0 (mkId Bᵢ) ⟫
fixA-loop-step Bᵢ A v w = TyPeelR-a v (mkId-⊢ w)

------------------------------------------------------------------------
-- §4a  THE LOOP, ON A CLOSED EXAMPLE
------------------------------------------------------------------------

-- The smallest instance: a vacuous `Λ` over a numeral, behind a trivial
-- boundary with a `∀` identity conversion, instantiated at `ℕ.
--
--   T₀ = ((ΛY. 3) ⟪ · , (∀Y. id ℕ) ⟫) [ℕ]
Vᵃ : Term
Vᵃ = Λ ($ 3)

valVᵃ : Value Vᵃ
valVᵃ = V-Λ V-$

T₀ : Term
T₀ = (Vᵃ ⟪ morph [] [] , `∀ (id `ℕ) ⟫) ·[ `ℕ , `ℕ ]

⊢T₀ : [] ∣ [] ⊢ T₀ ⦂ `ℕ
⊢T₀ = ⊢·[] (env (mw rw[] sw[]) (⊢Λ ⊢$) (conv-all (conv-id base-ℕ))
                (wf-∀ wf-ℕ))
            wf-ℕ

-- STEP 1 — fix (a) fires and inserts the first dual layer.
T₁ : Term
T₁ = (loopShape (wkᴹ 1 Vᵃ) `ℕ (` 0))
       ⟪ morph (`ℕ ∷ []) [] , instReveal 0 (id `ℕ) ⟫

stepᵃ₁ : [] ⊢ T₀ -→ᵃ T₁
stepᵃ₁ = TyPeelR-a valVᵃ (conv-id base-ℕ)

-- `wkᴹ` is the identity on this value and `instReveal 0 (id `ℕ)` is
-- `id `ℕ`, so T₁ is literally the first layer:
_ : T₁ ≡ ((Λ ($ 3)) ⟪ morph [] (lock 0 ∷ []) , `∀ (id `ℕ) ⟫) ·[ `ℕ , ` 0 ]
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
_ = refl

-- STEP 2 — and again, INSIDE the boundary step 1 built.  The interior is
-- a `loopShape` term, so `fixA-loop-step` applies verbatim.
T₂ : Term
T₂ = ((loopShape (wkᴹ 1 (wkᴹ 1 Vᵃ)) (renameᵗ (extᵗ suc) `ℕ) (` 0))
        ⟪ morph ((` 0) ∷ []) (lock 0 ∷ []) , instReveal 0 (mkId `ℕ) ⟫)
       ⟪ morph (`ℕ ∷ []) [] , instReveal 0 (id `ℕ) ⟫

stepᵃ₂ : [] ⊢ T₁ -→ᵃ T₂
stepᵃ₂ = ξᵃ-⟪⟫ (fixA-loop-step `ℕ (` 0) (value-wkᴹ 1 valVᵃ) wf-ℕ)

-- THE VERDICT.  T₂ is T₁'s redex REPRODUCED under one more boundary: the
-- `Λ` is still buried under a fresh `morph [] (lock 0 ∷ [])` layer with a
-- `` `∀ `` identity conversion, so `TyBeta` never gets to fire and the
-- term grows by one boundary per step.  `fixA-loop-step` applies to T₂'s
-- interior exactly as it applied to T₁'s, and its two premises
-- (`value-wkᴹ`, `mkId-⊢`) are available at every iteration.  Fix (a) has
-- no normal form.  ****  FIX (a) IS REFUTED.  ****
_ : T₂ ≡ (((Λ ($ 3)) ⟪ morph [] (lock 0 ∷ []) , `∀ (id `ℕ) ⟫) ·[ `ℕ , ` 0 ]
            ⟪ morph ((` 0) ∷ []) (lock 0 ∷ []) , id `ℕ ⟫)
           ⟪ morph (`ℕ ∷ []) [] , id `ℕ ⟫
_ = refl

------------------------------------------------------------------------
-- §5  TYPEELR-Λ — THE LIVE CLAUSE.  EXACT, AND THERE IS NO SHIFT.
------------------------------------------------------------------------

-- CANONICAL FORMS AT `∀` (proof/Canonical.canon-∀) say the interior of a
-- `∀`-conversion boundary is a `Λ` over a value or a WRAPPER with a `∀`
-- conversion — nothing else.  That is what lets TyPeelR SPLIT, and the
-- split is what closes §3's leak:
--
--   TyPeelR-Λ    instantiate IMMEDIATELY.  The body N already lives one
--                `abst` binder in (`⊢Λ`), so the new `bind` slot is a
--                slot N COULD ALREADY NAME: the frame move is a
--                REFINEMENT `abst → bind`, exactly TyBeta's, and THERE
--                IS NO SHIFT AT ALL.
--   TyPeelR-⟪⟫   push the type application inward, as the single rule
--                did, and mask the new binder in the MOVED BOUNDARY's
--                own change list (§5b).  The tower is finite and bottoms
--                out at the `Λ`, so the descent terminates (§5c₂).
--
-- Preservation, determinism and progress for the pair live where they
-- belong: proof/Preserve (`preserve-TyPeelR-Λ`, `preserve-TyPeelR-⟪⟫`),
-- strong.Reduction (`det`) and proof/Progress (`progress-·[]-∀conv`).
-- What this module keeps is the FRAME arithmetic behind them.

-- THE Λ CLAUSE'S FRAME MOVE IS TyBeta's.  `⊑ᵃ`, not just `⊑`: the term
-- transport accepts it, in flat contrast to §3's `TyPeelR-leak-¬⊑ᵃ`.
-- This is `preserve-TyPeelR-Λ`'s own `refine`, stated on its own.
TyPeelR-Λ-refinement : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → (unmasked abst ∷ interior Θ Δ)
      ⊑ᵃ interior (morph (A ∷ binds Θ) (changes Θ)) Δ
TyPeelR-Λ-refinement A Θ Δ = la∷ (la-uu le-ab) (⊑ᵃ-refl (interior Θ Δ))

-- … AND THE BODY IS NOT SHIFTED.  Two facts side by side: the frame it
-- lands in is its old frame with ONE entry in front, and that entry was
-- ALREADY THERE as `abst` — criterion (ii) alone, with (i) vacuous.
TyPeelR-Λ-no-shift : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (morph (A ∷ binds Θ) (changes Θ)) Δ
      ≡ unmasked (bind (shiftBy (numBinds Θ) A)) ∷ interior Θ Δ
TyPeelR-Λ-no-shift = interior-TyPeelR

-- and the slot the body could already name, in the redex
TyPeelR-Λ-slot0-old : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → (unmasked abst ∷ interior Θ Δ) ∋tv 0
TyPeelR-Λ-slot0-old Θ Δ = _ , ez , nameable

------------------------------------------------------------------------
-- §5b  TYPEELR-⟪⟫ — THE LIVE CLAUSE.  THE NEW BINDER IS MASKED IN THE
--      MOVED BOUNDARY'S OWN FRAME.
------------------------------------------------------------------------

-- `canon-∀` says the thing TyPeelR moves in the non-Λ case is A BOUNDARY.
-- A boundary carries its own change list — so the new binder can be
-- masked for it WITHOUT a second wrapper (which is what loops, §4) and
-- WITHOUT resolving anything (which is what fix (c) pays; Design.md §9
-- and Examples §13c): append `lock 0` to the moved boundary's OWN
-- changes, at the TAIL, where `applyChanges` runs it FIRST — exactly the
-- position the SCOPE MOVE `_⋉_` puts the travelling changes in.
--
-- `addLock0` and its induced-context identities are strong.CtxMorph §5;
-- the crossing itself is `⊢addLock0-cross` at `Ren-addLock0`
-- (strong.TermSubst §6), and the frame identity at the shift the rule
-- performs is `interior-addLock0-cross`.  Restated here at the rule's own
-- two contexts:

-- The appended `lock 0` is LEGAL where it acts: slot 0 of the new frame
-- is nameable (§3's `TyPeelR-slot0-nameable` — THE LEAK'S OWN SLOT IS
-- EXACTLY WHAT AUTHORIZES THE LOCK THAT CLOSES IT), so `sw-l` applies.
addLock0-sw-l : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (morph (A ∷ binds Θ) (changes Θ)) Δ ⊢ˢ (lock 0 ∷ [])
addLock0-sw-l A Θ Δ = sw-l (TyPeelR-slot0-nameable A Θ Δ) sw[]

-- THE FRAME IDENTITY.  The moved boundary's interior frame is its BIRTH
-- frame with the new binder inserted BELOW the bind prefix and MASKED —
-- the very shape (†) gives Peel's crossing argument and
-- `interior-Beta-Λ` gives Beta's.  Nothing gained, nothing lost.
interior-addLock0-shift : (Θ′ : CtxMorph) (C : Ty) (Δ : Ctxᵗ)
  → interior (addLock0 (renᴮ suc Θ′)) (unmasked (bind C) ∷ Δ)
      ≡ pushBinds (map ⇑ᵗ (binds Θ′)) (masked (bind C) ∷ scope Θ′ Δ)
interior-addLock0-shift = interior-addLock0-cross

------------------------------------------------------------------------
-- §5c  IT IS `wkᴹ 1` PLUS ONE LOCK, ON THE NOSE
------------------------------------------------------------------------

-- The contractum's inner value IS `wkᴹ 1` of the redex's inner value,
-- with `lock 0` appended to the moved boundary's own change list —
-- nothing else.  `wkᴹ 1` on a boundary renames the interior at
-- `extN (numBinds Θ′) suc`, the frame by `renᴮ suc` and the conversion at
-- `extN (numBinds Θ′) suc` (`renᴹ`'s wrapper clause), and that is exactly
-- what the rule writes.
addLock0ᵛ : Term → Term
addLock0ᵛ (` x)          = ` x
addLock0ᵛ ($ n)          = $ n
addLock0ᵛ (ƛ A ∙ N)      = ƛ A ∙ N
addLock0ᵛ (L · M)        = L · M
addLock0ᵛ (Λ N)          = Λ N
addLock0ᵛ (L ·[ B , A ]) = L ·[ B , A ]
addLock0ᵛ (M ⟪ Θ , c ⟫)  = M ⟪ addLock0 Θ , c ⟫

TyPeelR-⟪⟫-wkᴹ : (W : Term) (Θ′ : CtxMorph) (s′ : Conv)
  → addLock0ᵛ (wkᴹ 1 (W ⟪ Θ′ , `∀ s′ ⟫))
      ≡ (renᴹ (extN (numBinds Θ′) suc) W
           ⟪ addLock0 (renᴮ suc Θ′)
           , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫)
TyPeelR-⟪⟫-wkᴹ W Θ′ s′ = refl

------------------------------------------------------------------------
-- §5c₁  FRAME EXACTNESS OF THE TWO CLAUSES
------------------------------------------------------------------------

-- THE MOVED BOUNDARY'S INTERIOR IS ITS BIRTH FRAME WITH THE NEW SLOT
-- INSERTED MASKED, BELOW THE INNER BINDS.  `interior-addLock0-cross`
-- (strong.TermSubst), instantiated at the rule's own two contexts: the
-- redex reads the moved boundary at `interior Θ Δ` and the contractum at
-- `interior (morph (A ∷ binds Θ) (changes Θ)) Δ`, which IS
-- `unmasked (bind (shiftBy (numBinds Θ) A)) ∷ interior Θ Δ`
-- (`interior-TyPeelR`, `refl`).
TyPeelR-⟪⟫-frame : (A : Ty) (Θ Θ′ : CtxMorph) (Δ : Ctxᵗ)
  → interior (addLock0 (renᴮ suc Θ′))
             (interior (morph (A ∷ binds Θ) (changes Θ)) Δ)
      ≡ pushBinds (map ⇑ᵗ (binds Θ′))
          (masked (bind (shiftBy (numBinds Θ) A))
             ∷ scope Θ′ (interior Θ Δ))
TyPeelR-⟪⟫-frame A Θ Θ′ Δ =
  interior-addLock0-cross Θ′ (shiftBy (numBinds Θ) A) (interior Θ Δ)

-- … and the BIRTH frame, for comparison: the same `pushBinds` over the
-- same `scope`, with the binds UNLIFTED and no new slot.  So the move is
-- criterion (i) — the index shift past ONE crossed binder, which
-- `map ⇑ᵗ` performs on the reps and `renᴹ (extN (numBinds Θ′) suc)`
-- performs on the interior — AND NOTHING ELSE.
TyPeelR-⟪⟫-birth : (Θ′ : CtxMorph) (Ξ : Ctxᵗ)
  → interior Θ′ Ξ ≡ pushBinds (binds Θ′) (scope Θ′ Ξ)
TyPeelR-⟪⟫-birth Θ′ Ξ = refl

-- THE NEW SLOT IS UNNAMEABLE THERE — the leak, closed.  (Contrast §3's
-- `TyPeelR-slot0-nameable`, which is the leak itself; the slot is still
-- nameable at the OUTER position, which is what authorizes the lock and
-- what the instantiation node needs.)
Locked-¬Nameable : ∀ {E} → Locked E → ¬ Nameable E
Locked-¬Nameable locked ()

∋lk-¬∋tv : ∀ {Δ X} → Δ ∋lk X → ¬ (Δ ∋tv X)
∋lk-¬∋tv (E , d , lk) (E′ , d′ , nm) with ∋e-det d d′
... | refl = Locked-¬Nameable lk nm

pushBinds-∋lk0 : (As : List Ty) (E : Ent) (Δ : Ctxᵗ) → Locked E
  → pushBinds As (E ∷ Δ) ∋lk length As
pushBinds-∋lk0 []       E Δ lk = _ , ez , renᵉ-Locked lk
pushBinds-∋lk0 (A ∷ As) E Δ lk with pushBinds-∋lk0 As E Δ lk
... | _ , d , l = _ , es d , renᵉ-Locked l

TyPeelR-⟪⟫-slot-locked : (Θ′ : CtxMorph) (C : Ty) (Δ : Ctxᵗ)
  → ¬ (interior (addLock0 (renᴮ suc Θ′)) (unmasked (bind C) ∷ Δ)
         ∋tv numBinds (renᴮ suc Θ′))
TyPeelR-⟪⟫-slot-locked Θ′ C Δ =
  ∋lk-¬∋tv (subst (λ Ξ → Ξ ∋lk numBinds (renᴮ suc Θ′))
                  (sym (interior-addLock0-cross Θ′ C Δ))
                  (pushBinds-∋lk0 (map ⇑ᵗ (binds Θ′)) (masked (bind C))
                                  (scope Θ′ Δ) locked))

-- THE OUTER BOUNDARY IS THE SINGLE RULE'S, UNTOUCHED.  Sharpest form: the
-- wrapper clause's contractum is the single rule's contractum with
-- `addLock0ᵛ` applied to the moved value and NOTHING ELSE CHANGED — same
-- outer frame `morph (A ∷ binds Θ) (changes Θ)`, same minted conversion
-- `instReveal 0 s`, same pushed-in annotation `renameᵗ (extᵗ suc) Bᵢ`,
-- same type argument `` ` 0 ``.
TyPeelR-⟪⟫-outer-unchanged : (W : Term) (Θ′ Θ : CtxMorph) (s′ s : Conv)
    (A Bᵢ : Ty)
  → (addLock0ᵛ (wkᴹ 1 (W ⟪ Θ′ , `∀ s′ ⟫))
       ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
      ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫
      ≡ ((renᴹ (extN (numBinds Θ′) suc) W
            ⟪ addLock0 (renᴮ suc Θ′)
            , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫)
           ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
          ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫
TyPeelR-⟪⟫-outer-unchanged W Θ′ Θ s′ s A Bᵢ = refl

------------------------------------------------------------------------
-- §5c₂  TERMINATION — THE TOWER MEASURE, AND WHY THIS IS NOT FIX (a)
------------------------------------------------------------------------

-- The wrapper clause's contractum contains
--
--    (… ⟪ addLock0 … , `∀ s″ ⟫) ·[ … , ` 0 ]
--
-- which IS again a redex.  It is NOT fix (a)'s regress, and the measure
-- says why: the number of nested boundaries above the `Λ`.
towerHeight : Term → ℕ
towerHeight (` x)          = 0
towerHeight ($ n)          = 0
towerHeight (ƛ A ∙ N)      = 0
towerHeight (L · M)        = 0
towerHeight (Λ N)          = 0
towerHeight (L ·[ B , A ]) = 0
towerHeight (M ⟪ Θ , c ⟫)  = suc (towerHeight M)

-- The shift does not change it — which is what makes the measure usable
-- at all, since both candidate repairs shift the moved value.
towerHeight-renᴹ : (ρ : Renameᵗ) (M : Term)
  → towerHeight (renᴹ ρ M) ≡ towerHeight M
towerHeight-renᴹ ρ (` x)          = refl
towerHeight-renᴹ ρ ($ n)          = refl
towerHeight-renᴹ ρ (ƛ A ∙ N)      = refl
towerHeight-renᴹ ρ (L · M)        = refl
towerHeight-renᴹ ρ (Λ N)          = refl
towerHeight-renᴹ ρ (L ·[ B , A ]) = refl
towerHeight-renᴹ ρ (M ⟪ Θ , c ⟫)  =
  cong suc (towerHeight-renᴹ (extN (numBinds Θ) ρ) M)

-- THE MEASURE STRICTLY DECREASES.  The ∀-value the contractum's inner
-- `·[]` instantiates is ONE BOUNDARY SHORTER than the one the redex's
-- `·[]` instantiated.
TyPeelR-⟪⟫-height : (W : Term) (Θ′ Θ : CtxMorph) (s′ s : Conv)
  → towerHeight (renᴹ (extN (numBinds Θ′) suc) W
                   ⟪ addLock0 (renᴮ suc Θ′)
                   , `∀ (renᶜ (extᵗ (extN (numBinds Θ′) suc)) s′) ⟫)
      ≡ towerHeight ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ∸ 1
TyPeelR-⟪⟫-height W Θ′ Θ s′ s =
  cong suc (towerHeight-renᴹ (extN (numBinds Θ′) suc) W)

-- FIX (a) STALLS AT THE SAME MEASURE.  Its contractum's inner ∀-value is
-- `wkᴹ 1 V` under a FRESH boundary, so the height is the redex's height
-- again: nothing is consumed, and §4a's `T₀ -→ᵃ T₁ -→ᵃ T₂` is that
-- stall, twice.  THIS is the difference between (a) and the installed
-- clause: `TyPeelR-⟪⟫` CONSUMES a boundary that was already there, (a)
-- MINTS a new one.
fixA-height-stalls : (V : Term) (Θ : CtxMorph) (s : Conv) (Bᵢ : Ty)
  → towerHeight (wkᴹ 1 V ⟪ morph [] (lock 0 ∷ []) , mkId (`∀ Bᵢ) ⟫)
      ≡ towerHeight (V ⟪ Θ , `∀ s ⟫)
fixA-height-stalls V Θ s Bᵢ = cong suc (towerHeight-renᴹ (wkN 1) V)

-- WHERE THE DESCENT STOPS.  A `∀`-value of tower height 0 is a `Λ`
-- (`canon-∀` has no third shape), so once `TyPeelR-⟪⟫` has consumed the
-- tower it is `TyPeelR-Λ` that fires — and `TyPeelR-Λ` neither shifts nor
-- locks anything (§5).  So the run is `height − 1` wrapper steps then one
-- Λ step, and never more.
canon-∀-height : ∀ {Δ V C} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ C
  → towerHeight V ≡ 0
  → Σ[ N ∈ Term ] (Value N × (V ≡ Λ N))
canon-∀-height v ⊢V eq with canon-∀ v ⊢V
... | inj₁ p                          = p
canon-∀-height v ⊢V ()
    | inj₂ (W , Θ′ , s′ , vW , refl)

-- … stated as the progress clause it decides, against the LIVE relation.
-- At tower height 0 the step is `TyPeelR-Λ`, with the contractum named.
progress-Λ-at-0 : ∀ {Δ V Θ s B A C} → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
  → towerHeight V ≡ 0
    ----------------------------------------------------------------
  → Σ[ N ∈ Term ]
      ((V ≡ Λ N)
       × (Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
            -→ N ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫))
progress-Λ-at-0 v (⊢·[] (env mwᵥ ⊢V ⊢c wE) wA) eq with conv-all-inv ⊢c
... | A₀ , B₀ , refl , eqₑ , ⊢s with canon-∀-height v ⊢V eq
... | N , vN , refl = N , refl , TyPeelR-Λ vN ⊢s

------------------------------------------------------------------------
-- §5c₃  THE TWO CLAUSES ON A CLOSED TWO-DEEP TOWER
------------------------------------------------------------------------

-- A CLOSED redex whose ∀-value is a two-boundary tower over a `Λ`.  The
-- inner frame LOCKS the outer frame's binder, so the moved boundary
-- really does carry a change list for the appended lock to join.
--
--   Θᵈ  = morph (`ℕ ∷ []) []          the OUTER frame: binds X := ℕ
--   Θᵈ′ = morph [] (lock 0 ∷ [])      the INNER frame: locks X
--
-- THE RUN, MACHINE-RENDERED (scripts/render_term.sh, importing this
-- module).  Every line below is the renderer's output, not a
-- transcription.
--
--   showTmIn 0 U₀
--     = (((ΛY. 3) ⟪ ↓X , (∀Y. id ℕ) ⟫) ⟪ ↑X:=ℕ , (∀Y. id ℕ) ⟫) [ℕ]
--
--                     │  TyPeelR-⟪⟫   (tower height 2 → 1)
--                     ▼
--   showTmIn 0 U₁
--     = (((ΛZ. 3) ⟪ ↓X , ↓Y , (∀Z. id ℕ) ⟫) [Y]
--          ⟪ ↑Y:=ℕ , ↑X:=ℕ , id ℕ ⟫)
--
--                     │  ξ-⟪⟫ (TyPeelR-Λ)   (tower exhausted)
--                     ▼
--   showTmIn 0 U₂
--     = ((3 ⟪ ↑Z:=Y , ↓X , ↓Y , id ℕ ⟫) ⟪ ↑Y:=ℕ , ↑X:=ℕ , id ℕ ⟫)
--
-- READ THE MOVED BOUNDARY'S CHANGE LIST ACROSS STEP 1: `↓X` becomes
-- `↓X , ↓Y` — the SHIFTED original lock and the NEW lock, appended at the
-- tail.  Nothing else about the boundary changes, and no wrapper appears.
--
-- THE FRAMES:
--
--   showTCtxAt 9 0 (λ _ → "X") Ξᵈ₀                  =  X := ℕ
--   showTCtxAt 9 0 (λ _ → "X") Ξᵈ₁                  =  ⌷[X := ℕ]
--   showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵈ₂
--     =  Y := ℕ , X := ℕ
--   showTCtxAt 9 0 (λ { 0 → "Y" ; _ → "X" }) Ξᵈ₃
--     =  ⌷[Y := ℕ] , ⌷[X := ℕ]
--
-- `Ξᵈ₁` is W's BIRTH frame and `Ξᵈ₃` is its frame in the contractum: the
-- same frame with the new binder Y inserted MASKED.  Exact.
Θᵈ Θᵈ′ : CtxMorph
Θᵈ  = morph (`ℕ ∷ []) []
Θᵈ′ = morph [] (lock 0 ∷ [])

Wᵈ innerᵈ outerᵈ U₀ : Term
Wᵈ     = Λ ($ 3)
innerᵈ = Wᵈ ⟪ Θᵈ′ , `∀ (id `ℕ) ⟫
outerᵈ = innerᵈ ⟪ Θᵈ , `∀ (id `ℕ) ⟫
U₀     = outerᵈ ·[ `ℕ , `ℕ ]

valᵈ : Value outerᵈ
valᵈ = V-⟪⟫ (V-⟪⟫ (V-Λ V-$) I-all) I-all

-- the frames, spelled out and named so the renderer can print them
Ξᵈ₀ Ξᵈ₁ Ξᵈ₂ Ξᵈ₃ : Ctxᵗ
Ξᵈ₀ = interior Θᵈ []                                  -- the outer bind
Ξᵈ₁ = interior Θᵈ′ Ξᵈ₀                                -- W's BIRTH frame
Ξᵈ₂ = interior (morph (`ℕ ∷ `ℕ ∷ []) []) []           -- after step 1
Ξᵈ₃ = interior (morph [] (lock 1 ∷ lock 0 ∷ [])) Ξᵈ₂  -- W's NEW frame

_ : Ξᵈ₀ ≡ unmasked (bind `ℕ) ∷ []
_ = refl

_ : Ξᵈ₁ ≡ masked (bind `ℕ) ∷ []
_ = refl

⊢innerᵈ : interior Θᵈ [] ∣ [] ⊢ innerᵈ ⦂ `∀ `ℕ
⊢innerᵈ = env (mw rw[] (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[]))
               (⊢Λ ⊢$) (conv-all (conv-id base-ℕ)) (wf-∀ wf-ℕ)

⊢outerᵈ : [] ∣ [] ⊢ outerᵈ ⦂ `∀ `ℕ
⊢outerᵈ = env (mw (rw-b wf-ℕ rw[]) sw[]) ⊢innerᵈ
               (conv-all (conv-id base-ℕ)) (wf-∀ wf-ℕ)

⊢U₀ : [] ∣ [] ⊢ U₀ ⦂ `ℕ
⊢U₀ = ⊢·[] ⊢outerᵈ wf-ℕ

-- STEP 1 — `TyPeelR-⟪⟫`.  The moved boundary's own change list grows by
-- `lock 0` at the TAIL: `lock 0 ∷ []` becomes `lock 1 ∷ lock 0 ∷ []` —
-- the SHIFTED original lock (X, now one slot out) and the NEW lock (the
-- binder this step introduces).  No wrapper is minted.
U₁ : Term
U₁ = (((Λ ($ 3)) ⟪ morph [] (lock 1 ∷ lock 0 ∷ []) , `∀ (id `ℕ) ⟫)
        ·[ `ℕ , ` 0 ])
       ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , id `ℕ ⟫

stepᵈ₁ : [] ⊢ U₀ -→ U₁
stepᵈ₁ = TyPeelR-⟪⟫ (V-Λ V-$) (conv-id base-ℕ)

⊢U₁ : [] ∣ [] ⊢ U₁ ⦂ `ℕ
⊢U₁ = preservation ⊢U₀ stepᵈ₁

-- THE FRAME, AT THIS STEP.  The moved boundary's interior has BOTH slots
-- masked: X (shifted to slot 1) as it was in the redex, and the new
-- binder (slot 0) by the appended lock.  Nothing gained.
_ : Ξᵈ₂ ≡ unmasked (bind `ℕ) ∷ unmasked (bind `ℕ) ∷ []
_ = refl

_ : Ξᵈ₃ ≡ masked (bind `ℕ) ∷ masked (bind `ℕ) ∷ []
_ = refl

-- … and it is the frame identity `interior-addLock0-cross` at this
-- instance (the birth frame `masked (bind `ℕ) ∷ []`, with the new slot
-- inserted MASKED below the — empty — bind prefix).
_ : interior (addLock0 (renᴮ suc Θᵈ′))
             (interior (morph (`ℕ ∷ binds Θᵈ) (changes Θᵈ)) [])
      ≡ pushBinds (map ⇑ᵗ (binds Θᵈ′))
          (masked (bind `ℕ) ∷ scope Θᵈ′ (interior Θᵈ []))
_ = TyPeelR-⟪⟫-frame `ℕ Θᵈ Θᵈ′ []

-- STEP 2 — the tower is exhausted, so `TyPeelR-Λ` fires, INSIDE the
-- boundary step 1 built.  No shift, no lock: TyBeta's own step.
U₂ : Term
U₂ = (($ 3) ⟪ morph ((` 0) ∷ []) (lock 1 ∷ lock 0 ∷ []) , id `ℕ ⟫)
       ⟪ morph (`ℕ ∷ `ℕ ∷ []) [] , id `ℕ ⟫

stepᵈ₂ : [] ⊢ U₁ -→ U₂
stepᵈ₂ = ξ-⟪⟫ (TyPeelR-Λ V-$ (conv-id base-ℕ))

⊢U₂ : [] ∣ [] ⊢ U₂ ⦂ `ℕ
⊢U₂ = preservation ⊢U₁ stepᵈ₂

-- THE MEASURE, ON THIS RUN: 2 → 1, and at 1 the interior is a `Λ`.
_ : towerHeight outerᵈ ≡ 2
_ = refl

_ : towerHeight ((Λ ($ 3)) ⟪ morph [] (lock 1 ∷ lock 0 ∷ []) , `∀ (id `ℕ) ⟫)
      ≡ 1
_ = refl

_ : towerHeight ((Λ ($ 3)) ⟪ morph [] (lock 1 ∷ lock 0 ∷ []) , `∀ (id `ℕ) ⟫)
      ≡ towerHeight outerᵈ ∸ 1
_ = TyPeelR-⟪⟫-height Wᵈ Θᵈ′ Θᵈ (id `ℕ) (id `ℕ)

-- TIGHTNESS OF THE TWO CLAUSES is Examples §15b: an ILL-TYPED subterm —
-- ill typed for exactly one localized reason, `wf-var` at a masked slot —
-- stays ill typed in each contractum, and the wrapper clause's frame
-- REFUSES the value that the single rule's frame accepted (`⊢prb0-single`
-- against `¬⊢prb0-split`).  That is §3a's `nmᵃ` test, run at the position
-- a moved boundary's interior actually occupies.


------------------------------------------------------------------------
-- §6  TYBETA — exact up to refinement
------------------------------------------------------------------------

-- N's frame, before: `unmasked abst ∷ Δ` (that is `⊢Λ`).  After:
-- `interior (morph (A ∷ []) []) Δ ≡ unmasked (bind A) ∷ Δ`.  No shift,
-- one refinement at slot 0, and it is a slot N COULD ALREADY NAME:
-- criterion (ii) exactly.
TyBeta-frame : (A : Ty) (Δ : Ctxᵗ)
  → interior (morph (A ∷ []) []) Δ ≡ unmasked (bind A) ∷ Δ
TyBeta-frame = interior-TyBeta

TyBeta-refinement : (A : Ty) (Δ : Ctxᵗ)
  → (unmasked abst ∷ Δ) ⊑ᵃ interior (morph (A ∷ []) []) Δ
TyBeta-refinement A Δ = la∷ (la-uu le-ab) (⊑ᵃ-refl Δ)

-- The moved TYPE annotation travels the same step: `B` is read at
-- `unmasked abst ∷ Δ` in the redex (`⊢·[]`'s `∀ B`) and the minted
-- `reveal 0 B` is checked at `convCtx (morph (A ∷ []) []) Δ`, which IS
-- `unmasked (bind A) ∷ Δ`.
TyBeta-convCtx : (A : Ty) (Δ : Ctxᵗ)
  → convCtx (morph (A ∷ []) []) Δ ≡ unmasked (bind A) ∷ Δ
TyBeta-convCtx A Δ = refl

------------------------------------------------------------------------
-- §7  BETA — exact, and the `ƛ` clause
------------------------------------------------------------------------

-- THE Λ CROSSING (PR #199).  `interior-Beta-Λ`: the image's frame is its
-- BIRTH frame with the crossed slot MASKED.  §3's `Beta-Λ-slot0-locked`
-- is the tightness half.
Beta-Λ-frame : (Δ : Ctxᵗ)
  → interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ
Beta-Λ-frame = interior-Beta-Λ

-- THE `ƛ` CLAUSE.  A `ƛ` binds a TERM variable, so no type frame changes
-- and `shiftᴵ` must not shift the type side at all.  It does not: on a
-- value image it is the IDENTITY, which is correct because a value image
-- is TERM-CLOSED — and it stays term-closed after PR #199, because
-- `crossΛ W A` is a BOUNDARY and `env` types its interior at `Γ = []`.
-- So `shiftᴵ-⊢` still has no premise to discharge, at the crossed image
-- as much as at the original.
Beta-ƛ-no-shift : ∀ {W A} → shiftᴵ (ival W A) ≡ ival W A
Beta-ƛ-no-shift = refl

Beta-ƛ-crossed-no-shift : ∀ {W A} → shiftᴵ (⇑ᴵ (ival W A)) ≡ ⇑ᴵ (ival W A)
Beta-ƛ-crossed-no-shift = refl

-- … and the two crossings DO NOT INTERFERE (design law: simultaneity).
-- Crossing a `ƛ` then a `Λ` is crossing a `Λ` then a `ƛ`, on the nose,
-- for EVERY image — which is what makes the two clauses of `substᵐ`
-- independent after the crossΛ change.
⇑ᴵ-shiftᴵ-comm : (i : Img) → ⇑ᴵ (shiftᴵ i) ≡ shiftᴵ (⇑ᴵ i)
⇑ᴵ-shiftᴵ-comm (ivar x)   = refl
⇑ᴵ-shiftᴵ-comm (ival W A) = refl

-- THE `ƛ` CASE OF `⊢substᵐ`, RE-CONFIRMED: the type context is untouched
-- and the value image is carried through unchanged.  (This IS
-- `shiftᴵ-⊢`; it is restated to record that the `ival` clause needs no
-- weakening after the wrapper was introduced.)
Beta-ƛ-image : ∀ {W} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A
  → Δ ∣ (B ∷ Γ) ⊢ⁱ shiftᴵ (ival W A) ⦂ A
Beta-ƛ-image w ⊢W = shiftᴵ-⊢ (⊢ival w ⊢W)

-- The crossed image, one `Λ` in, then under a `ƛ`: still term-closed,
-- still frame-exact.
Beta-Λƛ-image : ∀ {W} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A
  → (unmasked abst ∷ Δ) ∣ (B ∷ ⤊ Γ) ⊢ⁱ shiftᴵ (⇑ᴵ (ival W A)) ⦂ ⇑ᵗ A
Beta-Λƛ-image w ⊢W = shiftᴵ-⊢ (⇑ᴵ-⊢1 (⊢ival w ⊢W))

------------------------------------------------------------------------
-- §8  CANCELR / IDPUSH — exact, inner AND outer
------------------------------------------------------------------------

-- THE INNER FRAME (the one V lives in) is preserved ON THE NOSE.
Move-inner-frame : (Θ₁ Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → interior (Θ₁ ⋉ Θ₂) (interior (rewind Θ₂) Δ) ≡ interior Θ₁ (interior Θ₂ Δ)
Move-inner-frame = interior-⋉-rewind

-- THE OUTER FRAME.  The outer boundary's interior — the position the
-- INNER BOUNDARY node occupies — becomes `interior (rewind Θ₂) Δ`, which
-- is Θ₂'s BIND BLOCK over the plain exterior: the locks have travelled
-- inward.  Nothing but the inner boundary sits there, and the inner
-- boundary REAPPLIES them (`_⋉_` puts Θ₂'s whole change list at the tail
-- of Θ₁'s, where `applyChanges` runs it FIRST), which is exactly why the
-- composite above is an equality.  Nothing else moves: both conversions
-- are RE-MINTED (`mkId` / `unseal`), not transported.
Move-outer-frame : (Θ₂ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ₂
  → interior (rewind Θ₂) Δ ≡ pushBinds (binds Θ₂) Δ
Move-outer-frame = interior-rewind

-- … and the outer frame adds no binder beyond Θ₂'s own: `rewind` carries
-- Θ₂'s binds and only rewinds its changes.
Move-outer-numBinds : (Θ₂ : CtxMorph) → numBinds (rewind Θ₂) ≡ numBinds Θ₂
Move-outer-numBinds Θ₂ = refl

Move-inner-numBinds : (Θ₁ Θ₂ : CtxMorph) → numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁
Move-inner-numBinds Θ₁ Θ₂ = refl

------------------------------------------------------------------------
-- §9  DROP$ — the frame change in the OTHER direction, and why it is
--     vacuous
------------------------------------------------------------------------

-- `($ n) ⟪ Θ , id A ⟫ → $ n` moves the numeral from `interior Θ Δ` OUT to
-- `Δ`: the bind prefix disappears and Θ's locks are lifted, so the new
-- frame is STRICTLY MORE NAMEABLE.  That is a frame gain in the direction
-- the criterion also forbids — but it is VACUOUS, because a numeral
-- names no type variable at all: `⊢$` types it at EVERY type context and
-- at every term context.
Drop$-vacuous : (n : ℕ) (Δ : Ctxᵗ) (Γ : Ctx) → Δ ∣ Γ ⊢ ($ n) ⦂ `ℕ
Drop$-vacuous n Δ Γ = ⊢$

-- AND NO OTHER TERM CAN TAKE THE STEP.  The rule's left-hand side is the
-- NUMERAL ITSELF — `Drop$` is the only rule whose interior pattern is a
-- constructor rather than a variable — so there is nothing to generalize.
-- Progress needs no more: a closed value at a base type IS a numeral
-- (proof/Canonical.canon-base), which is why the syntactic restriction
-- costs nothing.
Drop$-only-numerals : ∀ {Δ M M′} → Δ ⊢ M -→ M′
  → (∀ {n Θ A} → M ≡ ($ n) ⟪ Θ , id A ⟫ → M′ ≡ $ n)
Drop$-only-numerals (TyBeta v)  ()
Drop$-only-numerals (Beta w)    ()
Drop$-only-numerals (Peel v w)  ()
Drop$-only-numerals (TyPeelR-Λ v ⊢s)  ()
Drop$-only-numerals (TyPeelR-⟪⟫ v ⊢s) ()
Drop$-only-numerals (CancelR v d)  ()
Drop$-only-numerals (Drop$ b)      refl = refl
Drop$-only-numerals (IdPush v d)   ()
Drop$-only-numerals (ξ-·-l st)     ()
Drop$-only-numerals (ξ-·-r v st)   ()
Drop$-only-numerals (ξ-·[] st)     ()
Drop$-only-numerals (ξ-Λ st)       ()
Drop$-only-numerals (ξ-⟪⟫ st)      refl = ⊥-elim (numeral-¬step st)
  where
  numeral-¬step : ∀ {Δ n M′} → Δ ⊢ ($ n) -→ M′ → ⊥
  numeral-¬step ()

------------------------------------------------------------------------
-- §10  THE ξ RULES — nothing moves, and the frames are the binder's own
------------------------------------------------------------------------

-- Each congruence reduces a subterm IN PLACE, at the very type context
-- the corresponding TYPING rule reads it on.  Both facts are `refl`:
--
--   ξ-Λ    premise at `unmasked abst ∷ Δ`  =  `⊢Λ`'s premise context
--   ξ-⟪⟫   premise at `interior Θ Δ`       =  `env`'s premise context
--
-- (`ξ-·-l`, `ξ-·-r`, `ξ-·[]` do not change the context at all.)
ξ-Λ-frame : (Δ : Ctxᵗ) → (unmasked abst ∷ Δ) ≡ (unmasked abst ∷ Δ)
ξ-Λ-frame Δ = refl

ξ-⟪⟫-frame : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior Θ Δ ≡ pushBinds (binds Θ) (scope Θ Δ)
ξ-⟪⟫-frame Θ Δ = refl

------------------------------------------------------------------------
-- §11  DEAD SHIFT MACHINERY
------------------------------------------------------------------------

-- `shiftᵐ = renⁿ suc` (strong.TermSubst §5) and `canon-shiftᵐ`
-- (proof/Canonicity) have NO CONSUMERS after PR #199: frame-exact
-- substitution weakens an image with `shiftᴵ`, which is `there` on a
-- variable image and the IDENTITY on a value image (§7), so the
-- term-variable shift is never applied to a term.  `renⁿ` itself is
-- LIVE — `⊢renⁿ` at the identity renaming is what proves `⊢weakenⁿ`, the
-- lemma that lets a term-closed image type at an arbitrary term context.
--
-- Recorded, not deleted: an audit proposes, it does not land.
shiftᵐ-is-renⁿ : (M : Term) → shiftᵐ M ≡ renⁿ suc M
shiftᵐ-is-renⁿ M = refl
