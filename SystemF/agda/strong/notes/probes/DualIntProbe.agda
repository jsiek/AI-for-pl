module strong.notes.probes.DualIntProbe where

-- DualInt≈ (strong.DualDef) — THE TWO SUSPECTED FALSITY CORNERS, SETTLED.
--
-- The statement under probe is the ambient dual's REBUILD LAW
--
--   DualInt≈ :  Δ ∣ intOf Δ Θ ⊢ᵇ Θ  →  Δ ≼≈ intOf (intOf Δ Θ) (dualᴳ Δ Θ)
--
-- and _≼≈_ (strong.BReduction) has exactly four clauses: ≼≈[] , ≼≈abst
-- (abst on the LEFT below ANY entry on the right), ≼≈xrvld (the SAME x-rep
-- on both sides), ≼≈rvld (knowledge up to ≈Δ̄ in the target's tail).  Note
-- what is NOT there: nothing puts a rvld or an xrvld on the LEFT above an
-- `abst` on the RIGHT.  The dual's reveal block, however, emits the rep-LESS
-- reveal rvl⋆ in three situations, and every rvl⋆ rebuilds to `abst`
-- (revEnts' rvl⋆ clause).  Two of those three are Δ-entries that are NOT
-- abst, and each is a counterexample.
--
--   §1  THE XRVLD SLOT (DualDef's entᴳ-x).  Δ x-reveals slot s, Θ drops s
--       without concealing ⇒ the dual emits rvl⋆ ⇒ the rebuild has abst,
--       and the left has xrvld.  ¬DualInt-x / ¬DualInt≈-x.
--   §2  THE DOUBLE-REFUSAL SLOT (DualDef's entᴳ-B⋆).  Δ reveals slot s at a
--       rep BOTH copy guards refuse ⇒ rvl⋆ ⇒ abst, and the left has rvld.
--       ¬DualInt-B⋆ / ¬DualInt≈-B⋆.
--
-- Both refute DualInt≈ AS STATED, machine-checked (¬DualInt≈).
--
--   §3  THE REPAIR QUESTION 3(i): may _≼≈_ be WEAKENED to admit
--       left-anything vs right-abst?  ANSWER: NO.  §3.1 shows the weakened
--       ordering _≼≈⁺_ does admit both corners; §3.2 shows the three
--       transport lemmas ⊢retag≈ runs on (≼≈-∋:= , ≼≈-∋:=x , ≼≈→Absorbs)
--       all fail at the new clause; §3.3 is the decisive one — a CONCRETE
--       Peel redex, well typed at Δd, whose crossing argument W is a value
--       whose OWN boundary conceals the demoted slot, and which does NOT
--       retype at the rebuild (¬⊢W-rebuild).  The crossing's type
--       discipline does NOT exclude it: the crossing type reaches the
--       blocked slot through a REVEAL REP of Θ, which bwf↑ licenses freely.
--
-- Nothing here is imported by the development; it is evidence.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
open import strong.Unfold using (_≈Δ̄⟨_⟩_; ≈unf; ≈-refl; ≡→≈; unfSub)
open import strong.Boundary
open import strong.BReduction
open import strong.DualDef using (DualInt≈)
open import strong.DualIntProof using (DualIntHead; head-⋆-abst)

------------------------------------------------------------------------
-- §1  THE XRVLD SLOT.  Δx x-reveals slot 0 (the E★′ entry shape: "revealed;
-- rep readable one level OUT"), and Θx conceals only slot 1 — so slot 0 is
-- DROPPED WITHOUT CONCEALING.  DualDef's entᴳ-x sends it to rvl⋆ and the
-- rebuild reads that back as `abst`.
------------------------------------------------------------------------

Δx : TCtx                          -- Z:=ˣY , Y:=ℕ
Δx = xrvld (` 0) ∷ rvld `ℕ ∷ []

Θx : BCtx                          -- ↓Y:=ℕ   (drops slot 0, conceals slot 1)
Θx = cnc 1 `ℕ ∷ []

-- Δx is a well-formed context (the x-entry carries no premise) …
⊢Δx : ⊢ Δx
⊢Δx = ⊢xrvld (⊢rvld ⊢∅ wf-ℕ)

-- … and Θx is a well-formed boundary over it, so DualInt≈'s hypothesis is
-- discharged.
⊢Θx : Δx ∣ intOf Δx Θx ⊢ᵇ Θx
⊢Θx = bwf↓ (skip-xrvld here) ≈-refl wf-ℕ bwf[]

_ : intOf Δx Θx ≡ []
_ = refl

-- slot 0 is dropped, not concealed
_ : isConc 0 Θx ≡ false
_ = refl

-- … and the dual's entry there is the REP-LESS reveal
_ : entᴳ Δx Θx 0 1 ≡ rvl⋆
_ = refl

_ : dualᴳ Δx Θx ≡ rvl⋆ ∷ rvl `ℕ ∷ []
_ = refl

-- THE REBUILD: slot 0 came back ABSTRACT, and the x-rep is gone
rebuild-x : intOf (intOf Δx Θx) (dualᴳ Δx Θx) ≡ abst ∷ rvld `ℕ ∷ []
rebuild-x = refl

-- *** VERDICT (corner 1): FALSE.  LEFT xrvld vs RIGHT abst — no clause of
-- _≼≈_ admits it (≼≈xrvld demands the x-mark on BOTH sides). ***
¬DualInt-x : ¬ (Δx ≼≈ intOf (intOf Δx Θx) (dualᴳ Δx Θx))
¬DualInt-x ()

¬DualInt≈-x : ¬ DualInt≈
¬DualInt≈-x di = ¬DualInt-x (di ⊢Θx)

------------------------------------------------------------------------
-- §2  THE DOUBLE-REFUSAL SLOT.  Δd reveals slot 0 at the rep ` 0, which
-- names slot 1 — another slot Θd drops.  The RAW copy's guard
-- `dfree 0 k` refuses it (the rep is CHAINED), and the SECOND-CHANCE copy
-- at the rep unfolded in its own tail refuses it too, because the chain
-- ends at a Λ-BOUND (abst) slot and unfolding there is the identity.  So
-- DualDef's entᴳ-B⋆ fires and the knowledge is lost to rvl⋆.
--
-- This is exactly Γp (strong.BReduction) with its middle link `rvld 𝔹`
-- replaced by the Λ-binder's `abst` — i.e. Pc's site with the chain
-- terminating in an abstract variable instead of a concrete one.
------------------------------------------------------------------------

Δd : TCtx                          -- W:=X , X abstract (Λ-bound) , V:=ℕ
Δd = rvld (` 0) ∷ abst ∷ rvld `ℕ ∷ []

Θd : BCtx                          -- ↓V:=ℕ  (drops slots 0,1,2)
Θd = cnc 2 `ℕ ∷ []

⊢Δd : ⊢ Δd
⊢Δd = ⊢rvld (⊢abst (⊢rvld ⊢∅ wf-ℕ)) (wf-var here-abst)

⊢Θd : Δd ∣ intOf Δd Θd ⊢ᵇ Θd
⊢Θd = bwf↓ (skip-rvld (skip-abst here)) ≈-refl wf-ℕ bwf[]

_ : intOf Δd Θd ≡ []
_ = refl

-- BOTH guards refuse at slot 0 (k = cmax Θd ∸ 1 = 2)
_ : isConc 0 Θd ≡ false
_ = refl
_ : entAt Δd 0 ≡ rvld (` 0)
_ = refl
_ : dfree 0 2 (` 0) ≡ false                       -- the RAW copy refuses …
_ = refl
_ : unfEnt Δd 0 (` 0) ≡ ` 0                       -- … unfolding is the id …
_ = refl
_ : dfree 0 2 (unfEnt Δd 0 (` 0)) ≡ false         -- … so the retry refuses
_ = refl

_ : entᴳ Δd Θd 0 2 ≡ rvl⋆
_ = refl

_ : dualᴳ Δd Θd ≡ rvl⋆ ∷ rvl⋆ ∷ rvl `ℕ ∷ []
_ = refl

-- THE REBUILD: the knowledge "W is X" is gone; slot 0 is abstract
rebuild-d : intOf (intOf Δd Θd) (dualᴳ Δd Θd) ≡ abst ∷ abst ∷ rvld `ℕ ∷ []
rebuild-d = refl

-- *** VERDICT (corner 2): FALSE.  LEFT rvld vs RIGHT abst — again no
-- clause (≼≈rvld demands knowledge on BOTH sides). ***
¬DualInt-B⋆ : ¬ (Δd ≼≈ intOf (intOf Δd Θd) (dualᴳ Δd Θd))
¬DualInt-B⋆ ()

¬DualInt≈-B⋆ : ¬ DualInt≈
¬DualInt≈-B⋆ di = ¬DualInt-B⋆ (di ⊢Θd)

-- the headline: DualInt≈ AS STATED IS FALSE
¬DualInt≈ : ¬ DualInt≈
¬DualInt≈ = ¬DualInt≈-x

------------------------------------------------------------------------
-- §3  THE REPAIR QUESTION 3(i):  weaken _≼≈_ to admit left-anything vs
-- right-abst?
--
-- §3.1  The weakened ordering, as a LOCAL copy (the live _≼≈_ is untouched).
-- The new clause ⁺opq reads "the rebuild treats the slot as OPAQUE".
------------------------------------------------------------------------

infix 4 _≼≈⁺_
data _≼≈⁺_ : TCtx → TCtx → Set where
  ⁺[]    : [] ≼≈⁺ []
  ⁺abst  : ∀ {Δ Δ' E} → Δ ≼≈⁺ Δ' → (abst ∷ Δ) ≼≈⁺ (E ∷ Δ')
  ⁺xrvld : ∀ {Δ Δ' A} → Δ ≼≈⁺ Δ' → (xrvld A ∷ Δ) ≼≈⁺ (xrvld A ∷ Δ')
  ⁺rvld  : ∀ {Δ Δ' A B} → Δ ≼≈⁺ Δ' → A ≈Δ̄⟨ Δ' ⟩ B
         → (rvld A ∷ Δ) ≼≈⁺ (rvld B ∷ Δ')
  ⁺opq   : ∀ {Δ Δ' E} → Δ ≼≈⁺ Δ' → (E ∷ Δ) ≼≈⁺ (abst ∷ Δ')   -- NEW

-- both corners DO become derivable under the weakening — so the weakening
-- is the right shape for the rebuild law …
DualInt⁺-x : Δx ≼≈⁺ intOf (intOf Δx Θx) (dualᴳ Δx Θx)
DualInt⁺-x = ⁺opq (⁺rvld ⁺[] ≈-refl)

DualInt⁺-B⋆ : Δd ≼≈⁺ intOf (intOf Δd Θd) (dualᴳ Δd Θd)
DualInt⁺-B⋆ = ⁺opq (⁺abst (⁺rvld ⁺[] ≈-refl))

------------------------------------------------------------------------
-- §3.2  … but it destroys every transport ⊢retag≈ runs on.  ⊢retag≈'s
-- (env) case goes through bwf-retag≈, whose three conceal clauses consume
-- exactly ≼≈-∋:= (bwf↓), ≼≈→Absorbs (bwf↓'s Reversal≈ premise, via ≈-mono)
-- and ≼≈-∋:=x (bwf↓x).  At the new clause ALL THREE fail, pointwise.
------------------------------------------------------------------------

-- ≼≈-∋:= cannot extend: knowledge on the left, nothing on the right
¬∋:=-at-abst : ∀ {A} → ¬ ((abst ∷ Δd) ∋ 0 := A)
¬∋:=-at-abst ()

-- ≼≈-∋:=x cannot extend: the x-mark on the left, nothing on the right
¬∋:=x-at-abst : ∀ {A} → ¬ ((abst ∷ Δd) ∋ 0 :=x A)
¬∋:=x-at-abst ()

-- ≼≈→Absorbs cannot extend: the two contexts resolve slot 0 DIFFERENTLY —
-- `rvld (` 0)` unfolds slot 0 to its chain, `abst` leaves it alone
_ : unfSub (rvld (` 0) ∷ abst ∷ []) 0 ≡ ` 1
_ = refl
_ : unfSub (abst ∷ abst ∷ []) 0 ≡ ` 0
_ = refl

¬Absorbs-opq : ¬ (unfSub (rvld (` 0) ∷ abst ∷ []) 0
                    ≡ unfSub (abst ∷ abst ∷ []) 0)
¬Absorbs-opq ()

------------------------------------------------------------------------
-- §3.3  THE DECISIVE INSTANCE.  Is a W that USES the demoted slot's
-- knowledge actually reachable AT A PEEL CROSSING?  YES.
--
-- The crossing argument is typed at `substᵗ (ρᵇ Θ) B₁` with
-- `Scoped (baseS Θ Δ) B₁`, so B₁ may not NAME a blocked Γ-slot — but the
-- external face resolves a REVEAL to its REP, and bwf↑ licenses a reveal
-- rep to be ANY Δ-type, blocked slots included.  So the crossing type
-- reaches the demoted slot through the reveal, and W's own boundary is
-- then free to conceal that slot by ordinary knowledge (bwf↓).
--
-- Θ2 = ↑?:=W , ↓V:=ℕ  over the SAME Δd: one reveal whose rep is ` 0 — the
-- very slot §2 demotes — plus §2's conceal.
------------------------------------------------------------------------

Θ2 : BCtx
Θ2 = rvl (` 0) ∷ cnc 2 `ℕ ∷ []

-- the interior: the reveal's raw reading is BLOCKED (its rep names the
-- blocked slot 0), so the fallback chain lands on the x-entry
Ψ2 : TCtx
Ψ2 = xrvld (` 0) ∷ []

_ : intOf Δd Θ2 ≡ Ψ2
_ = refl

⊢Θ2 : Δd ∣ intOf Δd Θ2 ⊢ᵇ Θ2
⊢Θ2 = bwf↑ (wf-var here-rvld)
            (bwf↓ (skip-rvld (skip-abst here)) ≈-refl wf-ℕ bwf[])

-- the dual and the rebuild: slot 0 is demoted exactly as in §2
_ : dualᴳ Δd Θ2 ≡ rvl⋆ ∷ rvl⋆ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
_ = refl

Rd : TCtx
Rd = abst ∷ abst ∷ rvld `ℕ ∷ []

rebuild-2 : intOf (intOf Δd Θ2) (dualᴳ Δd Θ2) ≡ Rd
rebuild-2 = refl

¬DualInt-2 : ¬ (Δd ≼≈ intOf (intOf Δd Θ2) (dualᴳ Δd Θ2))
¬DualInt-2 ()

-- ---- the crossing argument W: a SEALED value whose boundary conceals the
-- demoted slot 0 by ORDINARY KNOWLEDGE (Δd ∋ 0 := ` 0) ----

Θw : BCtx
Θw = cnc 0 (` 0) ∷ []

Wtm : Term
Wtm = (ƛ (` 0) ∙ ` 0) ⟪ Θw , ` 0 ⇒ ` 0 ⟫

_ : intOf Δd Θw ≡ abst ∷ rvld `ℕ ∷ []
_ = refl

⊢Θw : Δd ∣ intOf Δd Θw ⊢ᵇ Θw
⊢Θw = bwf↓ here (≡→≈ refl) (wf-var here-abst) bwf[]

⊢W : Δd ∣ [] ⊢ Wtm ⦂ (` 0 ⇒ ` 0)
⊢W = env ⊢Θw (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
         (⊢ƛ (wf-var here-abst) (⊢` here))

Wval : Value Wtm
Wval = V-⟪⟫ (V-G G-ƛ) I-⇒

-- ---- the Peel redex it sits in.  B₁ = ` 0 ⇒ ` 0 is the REVEAL's frame
-- slot (accessible), and its external face is ` 0 ⇒ ` 0 over Δd — W's very
-- type.  So the redex is well typed and the step is a live Peel. ----

Vtm : Term
Vtm = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)

_ : baseS Θ2 Δd ≡ ok ∷ blk ∷ blk ∷ ok ∷ []
_ = refl

⊢Redex : Δd ∣ [] ⊢ (Vtm ⟪ Θ2 , (` 0 ⇒ ` 0) ⇒ `ℕ ⟫) · Wtm ⦂ `ℕ
⊢Redex =
  ⊢· (env ⊢Θ2 (sc-⇒ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)) sc-ℕ)
          (⊢ƛ (wf-⇒ (wf-var here-xrvld) (wf-var here-xrvld)) ⊢$))
     ⊢W

peel-step : Δd ⊢ (Vtm ⟪ Θ2 , (` 0 ⇒ ` 0) ⇒ `ℕ ⟫) · Wtm
              -→ (Vtm · (Wtm ⟪ dualᴳ Δd Θ2
                              , renameᵗ (swapᵇ Θ2) (` 0 ⇒ ` 0) ⟫))
                 ⟪ Θ2 , `ℕ ⟫
peel-step = Peel (V-G G-ƛ) Wval

-- *** VERDICT 3(i): the weakening is UNSOUND.  W crosses this Peel, and W
-- does NOT retype in the rebuild: BOTH conceal licences ask the rebuild
-- about slot 0, and the rebuild has `abst` there.  So a ⊢retag≈ along the
-- WEAKENED ordering would be FALSE at this very instance — the crossing's
-- type discipline does not exclude the offending W. ***
¬⊢W-rebuild : ¬ (Rd ∣ [] ⊢ Wtm ⦂ (` 0 ⇒ ` 0))
¬⊢W-rebuild (env (bwf↓  ()  _ _ _)   _ _)
¬⊢W-rebuild (env (bwf↓x ()  _ _ _ _) _ _)

-- and the weakened ordering DOES relate the two contexts, so it is exactly
-- the weakening — not some other mismatch — that would license the bad step
Δd≼⁺Rd : Δd ≼≈⁺ Rd
Δd≼⁺Rd = ⁺opq (⁺abst (⁺rvld ⁺[] ≈-refl))

------------------------------------------------------------------------
-- §4  THE TWO CORNERS AGAINST THE DELIVERED THEOREM (strong.DualIntProof).
--
-- `dual-int≈` reduces DualInt≈ to `DualIntHead`, a per-slot residue on the
-- cmax Θ DROPPED slots, and `head-⋆-abst` shows that residue degenerates
-- at an rvl⋆ slot to "Δ was abstract there".  So each corner refutes the
-- residue itself, not merely the packaged statement — which is what makes
-- the hypothesis route 3(ii) the ONLY repair left, and `dual-int-abst`
-- (every dropped slot abstract) the exact closed sub-case.
------------------------------------------------------------------------

¬DualIntHead-x : ¬ DualIntHead Δx Θx
¬DualIntHead-x h with head-⋆-abst Δx Θx h 0 (s≤s z≤n) refl
¬DualIntHead-x h | ()

¬DualIntHead-B⋆ : ¬ DualIntHead Δd Θd
¬DualIntHead-B⋆ h with head-⋆-abst Δd Θd h 0 (s≤s z≤n) refl
¬DualIntHead-B⋆ h | ()

¬DualIntHead-2 : ¬ DualIntHead Δd Θ2
¬DualIntHead-2 h with head-⋆-abst Δd Θ2 h 0 (s≤s z≤n) refl
¬DualIntHead-2 h | ()

------------------------------------------------------------------------
-- §5  THE HEADLINE, CONFIRMED: peel-step is a LIVE PRESERVATION
-- COUNTEREXAMPLE.  ⊢Redex types the redex at ℕ, peel-step steps it, and
-- the contractum has NO typing at ℕ: the only rule for the outer wrapper
-- is (env), whose interior forces ⊢· with Vtm's annotation pinning the
-- argument type, and the dual wrapper's own (env) then demands Wtm typed
-- in the REBUILD Rd at ` 0 ⇒ ` 0 — refuted (¬⊢W-rebuild).  So the
-- calculus AS IT STANDS loses subject reduction at this Peel; the three
-- DualDef parameters were not just unprovable, they were covering a
-- false theorem.
------------------------------------------------------------------------

¬⊢contractum : ¬ (Δd ∣ []
  ⊢ (Vtm · (Wtm ⟪ dualᴳ Δd Θ2 , renameᵗ (swapᵇ Θ2) (` 0 ⇒ ` 0) ⟫))
      ⟪ Θ2 , `ℕ ⟫ ⦂ `ℕ)
¬⊢contractum (env _ _ (⊢· (⊢ƛ _ _) (env _ _ ⊢Wtm))) =
  ¬⊢W-rebuild ⊢Wtm
