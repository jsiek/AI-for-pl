module strong.proof.RewindNorm where

-- NORMALISING A CHANGE LIST — WHAT IS AVAILABLE, AND WHAT IS REFUSED.
--
-- THE PROBLEM (Jeremy, 2026-09-08; measured in Examples §16).  Every
-- scope move rewrites the outer frame as `rewind Θ₂` and moves Θ₂'s
-- change list into the inner one, so over a run the SAME entries are
-- replayed and re-moved and the lists grow as
--
--     ↧X , ↥X ↧X , ↥X ↧X ↥X ↧X , …
--
-- ending in dozens of adjacent inverse pairs.  Preservation is a theorem
-- throughout — nothing is unsound — but a 36-step run reached a
-- 130-entry change list.
--
-- WHAT LANDED (strong.CtxMorph §4): the two REDUNDANCY tests.  A replay
-- is not replayed again (`Rewound`/`rewindChanges`, so `rewind` is
-- IDEMPOTENT — proof/MoveScope `rewind-idem`), and a moved copy that is
-- ALREADY THERE is dropped (`Redundant`/`mergeChanges`).  Both are EXACT:
-- the frame lemmas stay equalities.  130 → 50 on the same run.
--
-- WHAT DOES NOT LAND, AND WHY.  The obvious normalisation — CONTRACT an
-- adjacent inverse pair at one slot — is exact on the two type-context
-- functions and is REFUSED BY THE SEQUENTIAL JUDGEMENT, in BOTH
-- orientations, for two DIFFERENT reasons.  That is this module.
--
--   §1  the contractions are exact on `applyChanges` (both orientations)
--       and on `applyUnlocks` (one of them)
--   §2  … and `_⊢ˢ_` refuses both, with witnesses
--   §3  `unlocksOf` alone — the cheapest imaginable `rewind`, refuted
--       twice
--   §4  what a CANONICAL form would have to be, and the two facts it
--       still needs

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.CtxMorph

------------------------------------------------------------------------
-- §1  THE CONTRACTIONS ARE EXACT ON THE TYPE CONTEXTS
------------------------------------------------------------------------

-- `maskEnt` and `unmaskEnt` are SETTERS: each WRITES the lock layer
-- without reading it (strong.Ctx §6), so at one slot the LAST-APPLIED
-- entry wins.  There is no premise anywhere below — this is entry
-- algebra, not the discipline.
unmaskEnt-maskEnt-set : (E : Ent) → unmaskEnt (maskEnt E) ≡ unmaskEnt E
unmaskEnt-maskEnt-set (unmasked b) = refl
unmaskEnt-maskEnt-set (masked b)   = refl

maskEnt-unmaskEnt-set : (E : Ent) → maskEnt (unmaskEnt E) ≡ maskEnt E
maskEnt-unmaskEnt-set (unmasked b) = refl
maskEnt-unmaskEnt-set (masked b)   = refl

unmask-mask-set : (X : ℕ) (Δ : Ctxᵗ) → unmask X (mask X Δ) ≡ unmask X Δ
unmask-mask-set X       []      = refl
unmask-mask-set zero    (E ∷ Δ) = cong (_∷ Δ) (unmaskEnt-maskEnt-set E)
unmask-mask-set (suc X) (E ∷ Δ) = cong (E ∷_) (unmask-mask-set X Δ)

mask-unmask-set : (X : ℕ) (Δ : Ctxᵗ) → mask X (unmask X Δ) ≡ mask X Δ
mask-unmask-set X       []      = refl
mask-unmask-set zero    (E ∷ Δ) = cong (_∷ Δ) (maskEnt-unmaskEnt-set E)
mask-unmask-set (suc X) (E ∷ Δ) = cong (E ∷_) (mask-unmask-set X Δ)

-- ── THE THREE EXACT CONTRACTIONS ───────────────────────────────────────

-- `↥X ↧X` — drop the LICENSING LOCK.  Exact on BOTH functions: the
-- surviving unlock does the unmasking either way.
applyChanges-contract-ul : (X : ℕ) (S : List Change) (Δ : Ctxᵗ)
  → applyChanges (unlock X ∷ lock X ∷ S) Δ
      ≡ applyChanges (unlock X ∷ S) Δ
applyChanges-contract-ul X S Δ = unmask-mask-set X (applyChanges S Δ)

applyUnlocks-contract-ul : (X : ℕ) (S : List Change) (Δ : Ctxᵗ)
  → applyUnlocks (unlock X ∷ lock X ∷ S) Δ
      ≡ applyUnlocks (unlock X ∷ S) Δ
applyUnlocks-contract-ul X S Δ = refl

-- `↧X ↥X` — drop the UNLOCK.  Exact on `applyChanges` …
applyChanges-contract-lu : (X : ℕ) (S : List Change) (Δ : Ctxᵗ)
  → applyChanges (lock X ∷ unlock X ∷ S) Δ
      ≡ applyChanges (lock X ∷ S) Δ
applyChanges-contract-lu X S Δ = mask-unmask-set X (applyChanges S Δ)

-- … and NOT on `applyUnlocks`, which is the whole point of the
-- conversion context: the dropped unlock is an unmask the REPS are read
-- past.  ONE SLOT, ONE MASKED BINDER — and the two contexts differ.
Δ↧ : Ctxᵗ
Δ↧ = masked (bind `ℕ) ∷ []

_ : applyUnlocks (lock 0 ∷ unlock 0 ∷ []) Δ↧ ≡ unmasked (bind `ℕ) ∷ []
_ = refl

_ : applyUnlocks (lock 0 ∷ []) Δ↧ ≡ masked (bind `ℕ) ∷ []
_ = refl

¬applyUnlocks-contract-lu :
  ¬ (applyUnlocks (lock 0 ∷ unlock 0 ∷ []) Δ↧
       ≡ applyUnlocks (lock 0 ∷ []) Δ↧)
¬applyUnlocks-contract-lu ()

-- … and the rep half of `_⊢ᵐ_` sees the difference.  A frame that BINDS
-- a rep naming the slot is well formed with the pair and not without it.
Θ↧ Θ↧✗ : CtxMorph
Θ↧  = morph (` 0 ∷ []) (lock 0 ∷ unlock 0 ∷ [])
Θ↧✗ = morph (` 0 ∷ []) (lock 0 ∷ [])

⊢ᵐ-Θ↧ : Δ↧ ⊢ᵐ Θ↧
⊢ᵐ-Θ↧ = mw (rw-b (wf-var (unmasked (bind `ℕ) , ez , nameable)) rw[])
           (sw-l (unmasked (bind `ℕ) , ez , nameable)
                 (sw-u (masked (bind `ℕ) , ez , locked) sw[]))

¬⊢ᵐ-contract-lu : ¬ (Δ↧ ⊢ᵐ Θ↧✗)
¬⊢ᵐ-contract-lu (mw (rw-b (wf-var (_ , ez , ())) _) _)

------------------------------------------------------------------------
-- §2  `_⊢ˢ_` REFUSES BOTH ORIENTATIONS
------------------------------------------------------------------------

-- IN A WELL-FORMED LIST THE ENTRIES AT ONE SLOT STRICTLY ALTERNATE:
-- `sw-l` admits `lock X` only where X is NAMEABLE and `sw-u` admits
-- `unlock X` only where it is LOCKED, so `↧X ↧X` and `↥X ↥X` have no
-- derivation at all and the ONLY adjacent same-slot patterns are the two
-- inverse pairs.  Contracting either one breaks the alternation at the
-- SURVIVOR, and the survivor's own premise is what fails.

-- ── ORIENTATION `↥X ↧X`: the survivor's licence is gone ────────────────
--
-- The slot is NAMEABLE on the exterior; the lock masks it and the unlock
-- restores it.  Drop the lock and the unlock is VACUOUS — `sw-u` refuses
-- it, and refusing it is exactly what makes the dual an inverse
-- (`mask-unmask`, strong.Ctx §6b; proof/DualTightness).
Δ↥ : Ctxᵗ
Δ↥ = unmasked (bind `ℕ) ∷ []

⊢ˢ-ul : Δ↥ ⊢ˢ (unlock 0 ∷ lock 0 ∷ [])
⊢ˢ-ul = sw-u (masked (bind `ℕ) , ez , locked)
             (sw-l (unmasked (bind `ℕ) , ez , nameable) sw[])

-- the contraction changes NEITHER type context …
_ : applyChanges (unlock 0 ∷ lock 0 ∷ []) Δ↥
      ≡ applyChanges (unlock 0 ∷ []) Δ↥
_ = refl

_ : applyUnlocks (unlock 0 ∷ lock 0 ∷ []) Δ↥
      ≡ applyUnlocks (unlock 0 ∷ []) Δ↥
_ = refl

-- … and the contracted list has no derivation.
¬⊢ˢ-contract-ul : ¬ (Δ↥ ⊢ˢ (unlock 0 ∷ []))
¬⊢ˢ-contract-ul (sw-u (_ , ez , ()) _)

-- ── ORIENTATION `↧X ↥X`: the survivor lands on a masked slot ───────────
--
-- The slot is LOCKED on the exterior; the unlock exposes it and the lock
-- re-masks it.  Drop the unlock and the lock names a slot that is NOT
-- nameable — `sw-l` refuses it.  (This orientation also loses an unmask,
-- §1.)
⊢ˢ-lu : Δ↧ ⊢ˢ (lock 0 ∷ unlock 0 ∷ [])
⊢ˢ-lu = sw-l (unmasked (bind `ℕ) , ez , nameable)
             (sw-u (masked (bind `ℕ) , ez , locked) sw[])

¬⊢ˢ-contract-lu : ¬ (Δ↧ ⊢ˢ (lock 0 ∷ []))
¬⊢ˢ-contract-lu (sw-l (_ , ez , ()) _)

-- THE VERDICT.  NO adjacent-pair contraction is available: one
-- orientation is exact on both type contexts and strands its unlock, the
-- other is exact on the interior, loses an unmask on the conversion
-- context, and strands its lock.  What CAN be dropped is a WHOLE
-- redundant replay — which is what `Rewound` and `Redundant`
-- (strong.CtxMorph §4) test for.

------------------------------------------------------------------------
-- §3  `unlocksOf` ALONE — REFUTED TWICE
------------------------------------------------------------------------

-- The cheapest imaginable rewound frame keeps only the unmasks the reps
-- need: `morph (binds Θ) (unlocksOf (changes Θ))`.  It fails BOTH of
-- `rewind`'s obligations.
unlocksOf : List Change → List Change
unlocksOf []             = []
unlocksOf (lock X ∷ S)   = unlocksOf S
unlocksOf (unlock X ∷ S) = unlock X ∷ unlocksOf S

-- (1) THE FRAME IS NOT RESTORED.  `scope-rewind` (proof/MoveScope §3)
-- says the rewound frame's changes are the IDENTITY on the exterior; the
-- unlocks alone leave the slot EXPOSED, so the value's frame in the
-- contractum is strictly more nameable than the redex's.
_ : applyChanges (unlocksOf (unlock 0 ∷ [])) Δ↧ ≡ unmasked (bind `ℕ) ∷ []
_ = refl

¬scope-unlocksOf : ¬ (applyChanges (unlocksOf (unlock 0 ∷ [])) Δ↧ ≡ Δ↧)
¬scope-unlocksOf ()

-- (2) THE SURVIVING UNLOCK GOES VACUOUS, whenever its licence was a lock
-- of the same list — the §2 configuration again, now reached by
-- FILTERING rather than by contracting.
_ : unlocksOf (unlock 0 ∷ lock 0 ∷ []) ≡ unlock 0 ∷ []
_ = refl

¬⊢ˢ-unlocksOf : ¬ (Δ↥ ⊢ˢ unlocksOf (unlock 0 ∷ lock 0 ∷ []))
¬⊢ˢ-unlocksOf (sw-u (_ , ez , ()) _)

-- … and re-locking the filtered list does not save it: the replay
-- `dualScope 0 (unlocksOf S) ++ unlocksOf S` puts the unlock FIRST, on
-- the plain exterior, where the slot is nameable.
_ : dualScope 0 (unlocksOf (unlock 0 ∷ lock 0 ∷ []))
      ++ unlocksOf (unlock 0 ∷ lock 0 ∷ [])
    ≡ lock 0 ∷ unlock 0 ∷ []
_ = refl

¬⊢ˢ-replay-unlocksOf : ¬ (Δ↥ ⊢ˢ (lock 0 ∷ unlock 0 ∷ []))
¬⊢ˢ-replay-unlocksOf (sw-l _ (sw-u (_ , ez , ()) _))

------------------------------------------------------------------------
-- §4  WHAT A CANONICAL FORM WOULD HAVE TO BE
------------------------------------------------------------------------

-- §1–§3 pin the normal form down completely.  A change list is, per
-- slot, an ALTERNATING sequence (§2), and what any later reader can see
-- of it is only
--
--   its NET state at that slot         (`applyChanges`: the LEFTMOST
--                                       entry wins — head applies LAST)
--   whether it unmasked it at all      (`applyUnlocks`: a SET of slots,
--                                       strong.Ctx §6c)
--
-- so the canonical list is ONE BLOCK PER SLOT, and the block is fixed by
-- the net state, the unmask flag, and the slot's state on the EXTERIOR
-- (which `_⊢ˢ_` forces, and which is itself read off the list: the
-- RIGHTMOST entry at that slot applies FIRST):
--
--   exterior   net      unmasked   block          length
--   ---------------------------------------------------------
--   locked     unlock   yes        ↥X                  1
--   nameable   unlock   yes        ↥X ↧X               2
--   locked     lock     yes        ↧X ↥X               2
--   nameable   lock     yes        ↧X ↥X ↧X            3
--   nameable   lock     no         ↧X                  1
--   locked     lock     no         (no derivation)     —
--
-- so at most THREE entries per slot mentioned — on the Examples §16 run,
-- at most FIVE slots are ever mentioned, i.e. a bound of 15 against the
-- 50 the two redundancy tests reach and the 130 they started from.
--
-- TWO FACTS ARE STILL MISSING, and neither is in the tree:
--
--   (i)  COMMUTATION AT DISTINCT SLOTS.  `updateAt f X` and
--        `updateAt g Y` commute for `X ≢ Y`; that is what brings one
--        slot's entries adjacent so the blocks can be read off.  Only
--        the SAME-setter case is proved (`unmask-comm`, strong.Ctx §6c),
--        because that is all `applyUnlocks-absorb` needed.
--   (ii) THE ORIENTATION IS NOT SYNTACTIC IN THE SLOT ALONE.  The block
--        depends on the slot's EXTERIOR state, so the normaliser must
--        read the rightmost entry at each slot and prove that the entry's
--        own `_⊢ˢ_` premise IS the exterior's state — i.e. that
--        `applyChanges S Δ` agrees with Δ at every slot S does not
--        mention.
--
-- Until they are proved, the exact normalisation of §4 is not available
-- and the two redundancy tests are what the development carries.
