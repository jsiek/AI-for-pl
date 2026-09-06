module strong.proof.MwUObstruct where

-- WHAT LANDED, AND WHAT THE ALTERNATIVES COST — the record of the
-- 2026-09-06 tightness repair.
--
-- The repair Jeremy proposed had three parts; this module used to refute
-- them as a package.  All three LANDED, in the corrected form the
-- refutations forced:
--
--   (1) `mw-u` demands the slot be LOCKED — LANDED, and STRENGTHENED to
--       the SEQUENTIAL reading `scope Θ Δ ∋lk X` (the entry is judged on
--       the frame it acts on), with the same reading for `mw-l` and, for
--       a rep, `unlockedScope Θ Δ ⊢ᵗ A`.  The old refutations §2/§3/§4
--       were all artefacts of reading every premise on the PLAIN Δ.
--       `⊢ᵐ-⊑` survives as `⊢ᵐ-⊑ᵃ` over `_⊑ᵃ_`, the refinement WITHOUT
--       `le-mu` (strong.Ctx §4b); `⊢retag` runs on that.
--   (2) `dualScope n (unlock X ∷ Θ) = … ++ lock (n + X) ∷ []` — LANDED,
--       AND REVERSED (the old §5, which was right).
--   (3) the outer frame of CancelR/IdPush loses its scope — LANDED as
--       `rewind Θ₂ = dualScope 0 Θ₂ ++ Θ₂`, NOT as `bindsOnly Θ₂` and
--       NOT as `dropLocks Θ₂`.
--
-- WHAT REMAINS HERE ARE THE THREE REFUTATIONS THAT CHOSE `rewind`, on
-- ONE running configuration:
--
--   §1  the exterior Δ₆ masks a slot; Θ₂ UNLOCKS it; the inner frame
--       BINDS a rep that names it.  All three morphisms are well formed.
--   §2  `dropLocks Θ₂` as the outer frame: the moved copy of Θ₂'s unlock
--       is then VACUOUS, and `mw-u` refuses it.
--   §3  `bindsOnly Θ₂` as the outer frame: Θ₂'s OWN bind rep loses the
--       unlock it was read past, and `mw-b` refuses it.
--   §4  `rewind Θ₂` does both jobs — and §4 is also the answer to the
--       simultaneity question: under a mw-b read on the PLAIN exterior
--       the MERGED frame `Θ₁ ⋉ Θ₂` has no derivation, because Θ₁'s rep
--       names a slot the merged frame's own tail unlocks.
--
-- The vacuous-unlock witness that used to live in §1 is now
-- proof/DualTightness §5, where it is REFUSED.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.Reduction

------------------------------------------------------------------------
-- §0  The two REJECTED outer frames, locally
------------------------------------------------------------------------

-- Θ with its locks removed (it keeps the binds and the unlocks) …
dropLocks : CtxMorph → CtxMorph
dropLocks []             = []
dropLocks (bind A ∷ Θ)   = bind A ∷ dropLocks Θ
dropLocks (unlock X ∷ Θ) = unlock X ∷ dropLocks Θ
dropLocks (lock X ∷ Θ)   = dropLocks Θ

-- … and Θ with its whole scope deleted.
bindsOnly : CtxMorph → CtxMorph
bindsOnly []             = []
bindsOnly (bind A ∷ Θ)   = bind A ∷ bindsOnly Θ
bindsOnly (unlock X ∷ Θ) = bindsOnly Θ
bindsOnly (lock X ∷ Θ)   = bindsOnly Θ

-- All three agree on the type context they leave behind — that is why
-- the choice looks free until `_⊢ᵐ_` is asked.

------------------------------------------------------------------------
-- §1  The configuration
------------------------------------------------------------------------

-- Δ₆ masks slot 0 (a binder at ℕ).
Δ₆ : Ctxᵗ
Δ₆ = masked (bind `ℕ) ∷ []

-- Θ₂ UNLOCKS it — legal, because the slot really is locked.
Θ₂ : CtxMorph
Θ₂ = unlock 0 ∷ []

⊢ᵐΘ₂ : Δ₆ ⊢ᵐ Θ₂
⊢ᵐΘ₂ = mw-u (masked (bind `ℕ) , ez , locked nameable-b) mw[]

_ : interior Θ₂ Δ₆ ≡ bind `ℕ ∷ []
_ = refl

-- An inner frame that BINDS a rep naming that slot — legal at Θ₂'s
-- interior, where the slot is live.
Θ₁ : CtxMorph
Θ₁ = bind (` 0) ∷ []

⊢ᵐΘ₁ : interior Θ₂ Δ₆ ⊢ᵐ Θ₁
⊢ᵐΘ₁ = mw-b (wf-var (bind `ℕ , ez , nameable-b)) mw[]

-- THE MERGED FRAME the scope move builds.  Θ₂ carries no binder, so the
-- moved scope keeps its index.
Θ₆ : CtxMorph
Θ₆ = bind (` 0) ∷ unlock 0 ∷ []

_ : _≡_ {A = CtxMorph} (Θ₁ ⋉ Θ₂) Θ₆
_ = refl

-- It is well formed over Δ₆ — its rep is read past its OWN tail, i.e.
-- past the unlock, which is where the redex read it.
⊢ᵐΘ₆ : Δ₆ ⊢ᵐ Θ₆
⊢ᵐΘ₆ = mw-b (wf-var (bind `ℕ , ez , nameable-b))
            (mw-u (masked (bind `ℕ) , ez , locked nameable-b) mw[])

------------------------------------------------------------------------
-- §2  `dropLocks` REFUTED — the moved unlock goes vacuous
------------------------------------------------------------------------

-- Θ₂ has no locks, so `dropLocks Θ₂` is Θ₂ itself: the outer frame
-- unmasks the slot, and the merged frame's own copy of that unlock then
-- names a slot that is already NAMEABLE.
_ : _≡_ {A = CtxMorph} (dropLocks Θ₂) Θ₂
_ = refl

_ : interior (dropLocks Θ₂) Δ₆ ≡ bind `ℕ ∷ []
_ = refl

-- The merged frame is read there, and its `unlock 0` has no premise.
¬⊢ᵐ-dropLocks : ¬ (interior (dropLocks Θ₂) Δ₆ ⊢ᵐ (Θ₁ ⋉ Θ₂))
¬⊢ᵐ-dropLocks (mw-b _ (mw-u (_ , ez , ()) _))

------------------------------------------------------------------------
-- §3  `bindsOnly` REFUTED — the frame's own rep loses its unlock
------------------------------------------------------------------------

-- Take the MERGED frame Θ₆ as the next redex's outer frame — it is
-- reachable, being exactly what §1's move just produced.  Deleting its
-- scope strands its bind rep on the plain exterior.
_ : _≡_ {A = CtxMorph} (bindsOnly Θ₆) (bind (` 0) ∷ [])
_ = refl

¬⊢ᵗ-rep-plain : ¬ (Δ₆ ⊢ᵗ ` 0)
¬⊢ᵗ-rep-plain (wf-var (_ , ez , ()))

¬⊢ᵐ-bindsOnly : ¬ (Δ₆ ⊢ᵐ bindsOnly Θ₆)
¬⊢ᵐ-bindsOnly (mw-b w _) = ¬⊢ᵗ-rep-plain w

------------------------------------------------------------------------
-- §4  `rewind` DOES BOTH JOBS
------------------------------------------------------------------------

-- It keeps every entry and runs the inverse scope on top, so the type
-- context it leaves is the bind prefix over the PLAIN exterior …
_ : _≡_ {A = CtxMorph} (rewind Θ₂) (lock 0 ∷ unlock 0 ∷ [])
_ = refl

_ : interior (rewind Θ₂) Δ₆ ≡ Δ₆
_ = refl

_ : _≡_ {A = CtxMorph} (rewind Θ₆) (lock 0 ∷ bind (` 0) ∷ unlock 0 ∷ [])
_ = refl

_ : interior (rewind Θ₆) Δ₆ ≡ pushBinds (repsOf Θ₆) Δ₆
_ = refl

-- … and every premise is still read where the redex read it.
⊢ᵐ-rewind-Θ₂ : Δ₆ ⊢ᵐ rewind Θ₂
⊢ᵐ-rewind-Θ₂ = mw-l (bind `ℕ , ez , nameable-b) ⊢ᵐΘ₂

⊢ᵐ-rewind-Θ₆ : Δ₆ ⊢ᵐ rewind Θ₆
⊢ᵐ-rewind-Θ₆ = mw-l (bind `ℕ , ez , nameable-b) ⊢ᵐΘ₆

-- THE MERGED FRAME IS WELL FORMED OVER IT.
⊢ᵐ-merged : interior (rewind Θ₂) Δ₆ ⊢ᵐ (Θ₁ ⋉ Θ₂)
⊢ᵐ-merged = ⊢ᵐΘ₆

-- AND THIS IS WHY `mw-b` READS ITS REP ON `unlockedScope Θ Δ`.  The
-- merged frame's rep `` ` 0 `` is NOT well formed on the plain exterior
-- (`¬⊢ᵗ-rep-plain`) and IS well formed past the frame's own tail — so a
-- SIMULTANEOUS `mw-b`, reading every rep on Δ, would refuse the frame the
-- move builds.  Reading it past the tail's UNMASKS (and never past the
-- tail's locks — `unlockedScope`, not `scope`) is what makes both the
-- move and TyPeelR's `bind A ∷ Θ` well formed at once.
⊢ᵗ-rep-past-tail : unlockedScope (unlock 0 ∷ []) Δ₆ ⊢ᵗ ` 0
⊢ᵗ-rep-past-tail = wf-var (bind `ℕ , ez , nameable-b)
