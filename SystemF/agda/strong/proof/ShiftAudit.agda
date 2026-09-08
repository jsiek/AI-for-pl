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
--   §1  the site table (comment)
--   §2  Peel                  — EXACT, by (†)
--   §3  TyPeelR (V's frame)   — ****  LEAK  ****
--   §4  fix (a), "wrap V in the new binder's dual" — LOOPS
--   §5  fix (b), "split on the interior" — the Λ half, PROVEN EXACT
--   §5b fix (b′), the wrapper half — the frame identity, EXACT
--   §6  TyBeta                — exact up to refinement
--   §7  Beta                  — exact (crossΛ), and the `ƛ` clause
--   §8  CancelR / IdPush      — exact, inner AND outer
--   §9  Drop$                 — vacuous (a numeral has no type variables)
--   §10 the ξ rules           — nothing moves
--   §11 dead shift machinery
--
-- The verdict table with the fix candidates and their hazards is
-- notes/ShiftAudit.md; the frame-identity table it feeds is Design.md §7.

open import Data.Nat using (ℕ; zero; suc; _+_)
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
open import strong.proof.PeelDual using (interior-dual; applyChanges-++)
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
--     Peel      `wkᴹ (numBinds Θ) W ⟪ dual Θ , s ⟫`          §2  EXACT
--     TyPeelR   `wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ]`   §3  LEAK
--     TyBeta    `N ⟪ morph (A ∷ []) [] , reveal 0 B ⟫`       §6  refinement
--     Beta      `N [ W ∶ A ]ᵐ`, i.e. `substᵐ`/`crossΛ`       §7  EXACT
--     CancelR   `V ⟪ Θ₁ ⋉ Θ₂ , … ⟫ ⟪ rewind Θ₂ , … ⟫`        §8  EXACT
--     IdPush    (same two frames)                            §8  EXACT
--     Drop$     `($ n) ⟪ Θ , id A ⟫ → $ n`                   §9  vacuous
--     ξ-*       nothing moves                                §10 —
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
-- §3  TYPEELR — THE LEAK
------------------------------------------------------------------------

-- THE MOVE.  `V`, the interior of the crossed boundary, is typed at
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
-- §5  FIX (b) — SPLIT ON THE INTERIOR.  THE Λ HALF IS EXACT, AND PROVEN.
------------------------------------------------------------------------

-- CANONICAL FORMS AT `∀` (proof/Canonical.canon-∀) say the interior of a
-- `∀`-conversion boundary is a `Λ` over a value or a WRAPPER with a `∀`
-- conversion — nothing else.  So TyPeelR can SPLIT:
--
--   Λ case      instantiate IMMEDIATELY.  The body N already lives one
--               `abst` binder in (`⊢Λ`), so the new `bind` slot is a slot
--               N COULD ALREADY NAME: the frame move is a REFINEMENT
--               `abst → bind`, exactly TyBeta's, and THERE IS NO SHIFT.
--   wrapper     push the type application inward, as the live rule does.
--               The tower is finite and bottoms out at a `Λ`.
--
-- The Λ case is the one that matters — it is where the instantiation
-- actually happens — and it is EXACT.  Below: the prototype rule, its
-- frame identity, and its PRESERVATION.

-- THE FRAME MOVE IS TyBeta's.  `⊑ᵃ`, not just `⊑`: the term transport
-- accepts it (contrast §3's `TyPeelR-leak-¬⊑ᵃ`).
TyPeelR-Λ-refinement : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → (unmasked abst ∷ interior Θ Δ)
      ⊑ᵃ interior (morph (A ∷ binds Θ) (changes Θ)) Δ
TyPeelR-Λ-refinement A Θ Δ = la∷ (la-uu le-ab) (⊑ᵃ-refl (interior Θ Δ))

-- THE PROTOTYPE RULE SET (fix (b)), NOT the live rule.
infix 2 _⊢_-→ᵇ_
data _⊢_-→ᵇ_ : Ctxᵗ → Term → Term → Set where

  -- the Λ interior: instantiate at once, frame REFINED not extended
  TyPeelR-Λ : ∀ {Δ N Θ s B A Bᵢ Bₑ} → Value N
    → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ᵇ N ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

  -- the wrapper interior: the live rule, restricted.  THE LEAK SURVIVES
  -- HERE (§3 applies verbatim to `W ⟪ Θ′ , `∀ s′ ⟫`), which is why fix
  -- (b) is a PARTIAL repair — see notes/ShiftAudit.md.
  TyPeelR-⟪⟫ : ∀ {Δ W Θ′ s′ Θ s B A Bᵢ Bₑ} → Value W
    → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ᵇ (wkᴹ 1 (W ⟪ Θ′ , `∀ s′ ⟫) ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
              ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫

-- THE Λ CASE PRESERVES TYPES.  The live proof, with `int` replaced by
-- `⊢retag` along the refinement above — no `⊢rename`, no `wkᴹ`, no
-- `ren-suc-[0]`.  Every other premise is the live proof verbatim, which
-- is the point: the repair costs nothing.
preserve-TyPeelR-Λ : ∀ {Δ N Θ s B A C Bᵢ Bₑ} → Value N
  → (unmasked abst ∷ convCtx Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
  → Δ ∣ [] ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    ---------------------------------------------------------------------
  → Δ ∣ [] ⊢ N ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫ ⦂ C
preserve-TyPeelR-Λ {Δ = Δ} {N = N} {Θ = Θ} {s = s} {B = B} {A = A}
                   {Bᵢ = Bᵢ} {Bₑ = Bₑ} v ⊢s
                   (⊢·[] (env mwᵥ (⊢Λ ⊢N) ⊢c wE) wA)
  with conv-all-inv ⊢c
... | A₀ , B₀ , refl , eqE , ⊢s₀
  with conv-types-unique ⊢s ⊢s₀
... | refl , refl =
  env (mw (rw-b (⊑-wf (Δ⊑unlockedScope Θ Δ) wA) (mw-reps mwᵥ))
          (mw-changes mwᵥ))
      (⊢retag (TyPeelR-Λ-refinement A Θ Δ) ⊢N)
      conv
      (wf-[]ᵗ (wf-∀⁻ wE) wA)
  where
  A′ : Ty
  A′ = shiftBy (numBinds Θ) A

  eqB : Bₑ ≡ shiftBodyBy (numBinds Θ) B
  eqB = sym (∀-inj (trans (sym (shiftBy-shiftBodyBy (numBinds Θ) B)) eqE))

  eqT : Bₑ [ 0 := ⇑ᵗ A′ ]ᵗ ≡ shiftBy (suc (numBinds Θ)) (B [ A ]ᵗ)
  eqT = trans (cong (λ T → T [ 0 := ⇑ᵗ A′ ]ᵗ) eqB)
              (trans (subst-at-0 A′ (shiftBodyBy (numBinds Θ) B))
                     (cong ⇑ᵗ (sym (shiftBy-[]ᵗ (numBinds Θ) B A))))

  conv : convCtx (morph (A ∷ binds Θ) (changes Θ)) Δ ⊢ instReveal 0 s
           ∶ Bᵢ ⇝ shiftBy (suc (numBinds Θ)) (B [ A ]ᵗ)
  conv = subst (λ T → convCtx (morph (A ∷ binds Θ) (changes Θ)) Δ
                        ⊢ instReveal 0 s ∶ Bᵢ ⇝ T)
               eqT (⊢instReveal {A = A′} 0 ⊢s)

-- DETERMINISM.  The two patterns are DISJOINT — a `Λ` is not a
-- boundary — and each contractum is a function of the redex.  Note what
-- the Λ case buys: its contractum does not mention `Bᵢ` at all, so it is
-- determined by the redex WITHOUT `conv-src-unique`.  (The live rule
-- needs it, because the pushed-in annotation is premise-determined.)
detᵇ : ∀ {Δ M M₁ M₂} → Δ ⊢ M -→ᵇ M₁ → Δ ⊢ M -→ᵇ M₂ → M₁ ≡ M₂
detᵇ (TyPeelR-Λ v ⊢s)  (TyPeelR-Λ v′ ⊢s′)  = refl
detᵇ (TyPeelR-⟪⟫ {W = W} {Θ′ = Θ′} {s′ = s′} {Θ = Θ} {s = s} {A = A} v ⊢s)
     (TyPeelR-⟪⟫ v′ ⊢s′) =
  cong (λ T → (wkᴹ 1 (W ⟪ Θ′ , `∀ s′ ⟫) ·[ renameᵗ (extᵗ suc) T , ` 0 ])
                ⟪ morph (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫)
       (conv-src-unique ⊢s ⊢s′)

-- PROGRESS.  `canon-∀` (proof/Canonical) hands the prototype EXACTLY its
-- two patterns — a `Λ` over a value, or a wrapper with a `∀` conversion —
-- so the split is total on a typed redex, and each rule's premises come
-- off the redex's own derivation (the value from `canon-∀`, the
-- conversion typing from `conv-all-inv`, as proof/Progress already does
-- for the live rule).
progressᵇ-·[] : ∀ {Δ V Θ s B A C} → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    ----------------------------------------------------------
  → Σ[ M ∈ Term ] (Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] -→ᵇ M)
progressᵇ-·[] v (⊢·[] (env mwᵥ ⊢V ⊢c wE) wA) with conv-all-inv ⊢c
... | A₀ , B₀ , refl , eqₑ , ⊢s with canon-∀ v ⊢V
... | inj₁ (N , vN , refl)          = _ , TyPeelR-Λ vN ⊢s
... | inj₂ (W , Θ′ , s′ , vW , refl) = _ , TyPeelR-⟪⟫ vW ⊢s

-- THE Λ CASE IS FRAME-EXACT.  Two facts, side by side: the body is NOT
-- SHIFTED (it stays where `⊢Λ` put it), and the slot it gains was
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
-- §5b  FIX (b′) — CLOSING THE WRAPPER CASE TOO: THE NEW BINDER IS
--      MASKED IN THE MOVED BOUNDARY'S OWN FRAME
------------------------------------------------------------------------

-- `canon-∀` says the thing TyPeelR moves in the non-Λ case is A BOUNDARY.
-- A boundary carries its own change list — so the new binder can be
-- masked for it WITHOUT a second wrapper (which is what loops, §4) and
-- WITHOUT resolving anything (which is what fix (c) pays, §13c of
-- Examples): append `lock 0` to the moved boundary's OWN changes, at the
-- TAIL, where `applyChanges` runs it FIRST — exactly the position the
-- SCOPE MOVE `_⋉_` puts the travelling changes in.
addLock0 : CtxMorph → CtxMorph
addLock0 Θ = morph (binds Θ) (changes Θ ++ (lock 0 ∷ []))

-- the two list facts the frame identity needs
map-renᶠ-shiftScope : (S : List Change)
  → map (renᶠ suc) S ≡ shiftScope 1 S
map-renᶠ-shiftScope []             = refl
map-renᶠ-shiftScope (unlock X ∷ S) =
  cong (unlock (suc X) ∷_) (map-renᶠ-shiftScope S)
map-renᶠ-shiftScope (lock X ∷ S)   =
  cong (lock (suc X) ∷_) (map-renᶠ-shiftScope S)

-- `shiftScope 1` steps a change list PAST ONE ENTRY: the entry is
-- untouched and the list acts on the tail.  (`applyChanges-shiftScope`,
-- proof/MoveScope, is this past a whole `pushBinds` prefix; here the
-- prefix is one arbitrary entry, MASKED included.)
applyChanges-shift1 : (S : List Change) (E : Ent) (Δ : Ctxᵗ)
  → applyChanges (shiftScope 1 S) (E ∷ Δ) ≡ E ∷ applyChanges S Δ
applyChanges-shift1 []             E Δ = refl
applyChanges-shift1 (unlock X ∷ S) E Δ =
  cong (unmask (suc X)) (applyChanges-shift1 S E Δ)
applyChanges-shift1 (lock X ∷ S)   E Δ =
  cong (mask (suc X)) (applyChanges-shift1 S E Δ)

-- THE FRAME IDENTITY.  The moved boundary's interior frame is its BIRTH
-- frame with the new binder inserted BELOW the bind prefix and MASKED —
-- the very shape (†) gives Peel's crossing argument and `interior-Beta-Λ`
-- gives Beta's.  Nothing gained, nothing lost.
interior-addLock0 : (Θ′ : CtxMorph) (C : Ty) (Δ : Ctxᵗ)
  → interior (addLock0 (renᴮ suc Θ′)) (unmasked (bind C) ∷ Δ)
      ≡ pushBinds (map ⇑ᵗ (binds Θ′)) (masked (bind C) ∷ scope Θ′ Δ)
interior-addLock0 Θ′ C Δ =
  cong (pushBinds (map ⇑ᵗ (binds Θ′)))
       (trans (applyChanges-++ (map (renᶠ suc) (changes Θ′)) (lock 0 ∷ [])
                               (unmasked (bind C) ∷ Δ))
              (trans (cong (λ S → applyChanges S (masked (bind C) ∷ Δ))
                           (map-renᶠ-shiftScope (changes Θ′)))
                     (applyChanges-shift1 (changes Θ′) (masked (bind C)) Δ)))

-- … AND THE MOVED BOUNDARY CROSSES BY `⊢rename` ALONE.  `wkᴹ 1` on a
-- boundary renames its interior at `extN (numBinds Θ′) suc`
-- (strong.TermSubst, `renᴹ`'s wrapper clause), and that is exactly the
-- renaming from the birth frame into the frame above — no `⊢retag`, no
-- `le-mu`.  This is what makes (b′) exact.
Ren-addLock0 : (Θ′ : CtxMorph) (E : Ent) (Δ : Ctxᵗ)
  → Ren (extN (numBinds Θ′) suc) (interior Θ′ Δ)
        (pushBinds (map ⇑ᵗ (binds Θ′)) (E ∷ scope Θ′ Δ))
Ren-addLock0 Θ′ E Δ = ren-pushBinds (binds Θ′) suc (mkRen es)

-- The `lock 0` is LEGAL where it acts: slot 0 of the new frame is
-- nameable (§3's `TyPeelR-slot0-nameable` — the leak's own slot is
-- exactly what authorizes the lock that closes it), so `sw-l` applies.
addLock0-sw-l : (A : Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (morph (A ∷ binds Θ) (changes Θ)) Δ ⊢ˢ (lock 0 ∷ [])
addLock0-sw-l A Θ Δ = sw-l (TyPeelR-slot0-nameable A Θ Δ) sw[]

-- WHAT REMAINS for (b′) to land as a rule: `Δ ⊢ᵐ addLock0 (renᴮ suc Θ′)`
-- (the reps by `⊢ʳ-ren`, the changes by `⊢ˢ-ren` plus `addLock0-sw-l`
-- and `⊢ˢ-++`), and the moved boundary's CONVERSION re-typed at
-- `convCtx (addLock0 (renᴮ suc Θ′)) …` — where the appended lock is
-- LIFTED (`applyUnlocks` skips locks), so the conversion context is the
-- renamed one and `conv-ren` suffices.  Neither is new machinery; both
-- are the moves `⊢rename`'s own (env) case already makes.

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
Drop$-only-numerals (TyPeelR v ⊢s) ()
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
