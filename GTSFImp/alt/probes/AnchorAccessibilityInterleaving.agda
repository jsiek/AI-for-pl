module alt.probes.AnchorAccessibilityInterleaving where

-- File Charter:
--   * Gives a smallest typed term whose typing path interleaves regions as
--     `begin Y ; ν X ; begin X ; end Y`, leaving X live in Y's pocket.
--   * Checks that the U55 skip-to-matching-begin accessibility walk reports
--     X inaccessible at that reachable pocket.
--   * Tests a segment-preserving walk on the same interleaving, the U49
--     pocket, and the earlier raw-reopen instance.  A nonmatching begin is a
--     surviving region, so the segment walk restores its anchor after hiding
--     allocations local to the ended region.
--   * Records that the existing U40, U44, and chain-ν SCWRAP traces are
--     nested or sequential; none contains the interleaving isolated here.

open import Data.Bool using (Bool; false; true)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)
import Data.Vec.Base as Vec

open import Types
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction using (_⊢_—→_)
open import alt.probes.AnchorAccessibility
import alt.probes.ChainNuReachability as U40
import alt.probes.EscapeLambdaBodyCounterexample as U44
import alt.probes.U49PocketStrengthensCounterexample as U49
open U40 using (_⊢_—↠_)

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

empty-fresh : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
empty-fresh ()

inner-fresh : zero {n = 1} ∉ᵛ (just (suc zero) Vec.∷ Vec.[])
inner-fresh zero ()

------------------------------------------------------------------------
-- A typed interleaving: begin Y ; ν X ; begin X ; end Y
------------------------------------------------------------------------

baseEnv : TyEnv 1 0 Vec.[]
baseEnv = ∅ ,:= ℕᵗ

outerEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
outerEnv = baseEnv ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩

allocatedEnv : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
allocatedEnv = outerEnv ,:= ℕᵗ

interleavedEnv : TyEnv 2 2
    (just zero Vec.∷ just (suc zero) Vec.∷ Vec.[])
interleavedEnv =
  allocatedEnv ,begin[ zero ≔ zero ]⟨ inner-fresh ⟩

interleavedPocket : TyEnv 2 1 (just zero Vec.∷ Vec.[])
interleavedPocket = interleavedEnv ,end[ suc zero ]

outer-rep-at-base : rep? baseEnv zero ≡ just ℕᵗ
outer-rep-at-base = refl

inner-rep-at-allocation : rep? allocatedEnv zero ≡ just ℕᵗ
inner-rep-at-allocation = refl

outer-rep-in-pocket : rep? interleavedPocket (suc zero) ≡ just ℕᵗ
outer-rep-in-pocket = refl

interleavedPayload : Term 2 1
interleavedPayload = $ (κℕ 7)

outerConceal : Term 2 2
outerConceal =
  interleavedPayload ↓[ suc zero ≔ suc zero ] seal

innerReveal : Term 2 1
innerReveal = outerConceal ↑[ zero ≔ zero ] id↑

interleavedTerm : Term 1 0
interleavedTerm =
  (ν[ ℕᵗ ] innerReveal) ↑[ zero ≔ zero ] unseal

interleavedPayload-typed :
  interleavedPocket ∣ [] ⊢ interleavedPayload ⦂ ℕᵗ
interleavedPayload-typed = ⊢$ (κℕ 7)

outerConceal-typed :
  interleavedEnv ∣ [] ⊢ outerConceal ⦂ ＇ suc zero
outerConceal-typed =
  ⊢conceal refl outer-rep-in-pocket ⊢seal interleavedPayload-typed

innerReveal-typed :
  allocatedEnv ∣ [] ⊢ innerReveal ⦂ ＇ zero
innerReveal-typed =
  ⊢reveal inner-rep-at-allocation
    (⊢id↑ (＇ suc zero)) outerConceal-typed

interleavedTerm-typed :
  baseEnv ∣ [] ⊢ interleavedTerm ⦂ ℕᵗ
interleavedTerm-typed =
  ⊢reveal outer-rep-at-base ⊢unseal (⊢ν innerReveal-typed)

-- The outer end removes Y at position one and leaves the later-opened X at
-- position zero.  Thus the interleaving is present in a real typing premise,
-- not merely in a freely assembled telescope.
interleaved-X-live :
  Vec.lookup {A = Maybe (TyVar 2)}
      (just (zero {n = 1}) Vec.∷ Vec.[]) (zero {n = 0})
    ≡ just (zero {n = 1})
interleaved-X-live = refl

interleaved-X-inaccessible : ¬ (zero ∈acc interleavedPocket)
interleaved-X-inaccessible ()

interleaved-Y-accessible : suc zero ∈acc interleavedPocket
interleaved-Y-accessible = refl

------------------------------------------------------------------------
-- Segment-preserving accessibility candidate
------------------------------------------------------------------------

-- A begin crossed while seeking some other matching begin survives that end.
-- Marking its anchor after the recursive walk preserves precisely that live
-- region while the ν case still hides allocations local to the ended segment.
markAccessible : ∀ {Θ} → TyVar Θ → Vec.Vec Bool Θ → Vec.Vec Bool Θ
markAccessible zero (value Vec.∷ values) = true Vec.∷ values
markAccessible (suc α) (value Vec.∷ values) =
  value Vec.∷ markAccessible α values

mutual
  segmentAccessible : ∀ {Θ Δ σ} → TyEnv Θ Δ σ → Vec.Vec Bool Θ
  segmentAccessible ∅ = Vec.[]
  segmentAccessible (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) = segmentAccessible Ψ
  segmentAccessible (Ψ ,typ) = segmentAccessible Ψ
  segmentAccessible (Ψ ,:= A) = true Vec.∷ segmentAccessible Ψ
  segmentAccessible (Ψ ,end[ Y ]) = segmentBelow Ψ Y

  segmentBelow : ∀ {Θ Δ σ}
    → TyEnv Θ Δ σ → TyVar Δ → Vec.Vec Bool Θ
  segmentBelow ∅ ()
  segmentBelow (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) X with Y ≟ X
  segmentBelow (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) .Y | yes refl =
    segmentAccessible Ψ
  segmentBelow (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) X | no Y≢X =
    markAccessible α (segmentBelow Ψ (punchOut Y X Y≢X))
  segmentBelow {Θ = Θ} (Ψ ,typ) zero = allInaccessible Θ
  segmentBelow (Ψ ,typ) (suc X) = segmentBelow Ψ X
  segmentBelow (Ψ ,:= A) X = false Vec.∷ segmentBelow Ψ X
  segmentBelow (Ψ ,end[ Y ]) X = segmentBelow Ψ (punchIn Y X)

infix 4 _∈seg_

_∈seg_ : ∀ {Θ Δ σ} → TyVar Θ → TyEnv Θ Δ σ → Set
α ∈seg Ψ = Vec.lookup (segmentAccessible Ψ) α ≡ true

interleaved-X-segment-accessible : zero ∈seg interleavedPocket
interleaved-X-segment-accessible = refl

interleaved-Y-segment-accessible : suc zero ∈seg interleavedPocket
interleaved-Y-segment-accessible = refl

u49-young-segment-inaccessible : ¬ (zero ∈seg U49.pocketEnv)
u49-young-segment-inaccessible ()

u49-old-segment-accessible : suc zero ∈seg U49.pocketEnv
u49-old-segment-accessible = refl

-- The earlier U55 raw reopen remains inaccessible: only a nonmatching begin
-- crossed by an end is restored.  This candidate fixes reachable interleaving
-- without silently validating arbitrary raw begins.
u55-raw-reopen-still-segment-inaccessible :
  ¬ (zero ∈seg u55-reopened-pocket)
u55-raw-reopen-still-segment-inaccessible ()

------------------------------------------------------------------------
-- Existing reachable traces: no interleaving
------------------------------------------------------------------------

-- U40's application and ★ traces contain `ν X ; begin X ; end X`; the
-- wrapper conceal closes the same sole begin.  U44 similarly contains
-- `begin X ; end X`.  The escape/re-entry spine is sequential
-- `begin X ; end X ; begin X ; end X`.  None has two simultaneously live
-- regions with an outer end crossing the later begin.
u40-app-trace-rechecked :
  U40.emptyEnv ⊢ U40.closedAppSource —↠ U40.closedAppAfterSCWrap
u40-app-trace-rechecked = U40.closed-app-scwrap-trace

u40-star-trace-rechecked :
  U40.emptyEnv ⊢ U40.closedStarSource —↠ U40.closedStarAfterSCWrap
u40-star-trace-rechecked = U40.closed-star-scwrap-trace

u44-escape-step-rechecked :
  U44.lambdaEnv ⊢ U44.sourceBody —→ U44.targetBody
u44-escape-step-rechecked = U44.sourceBody-step
