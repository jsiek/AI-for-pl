module strong.notes.ReUnlockWall where

-- File Charter:
--   * The machine-checked record of ONE defect in the reduction rules and
--     of its repair: `rewind Θ` and `Θ₁ ⋉ Θ₂` had no conversion context
--     whenever Θ locks, so `CancelR`'s and `IdPush`'s contracta were
--     untypeable.
--   * It holds the obstruction (`no-old-rewind-conv`, stated against a
--     local copy of the conversion judgement as it stood) and the two
--     checks that the repaired judgement does give those frames a
--     conversion context.
--   * Nothing here runs a program.  The reasoning is in
--     notes/DECISIONS.md (2026-09-17); the rule that changed is
--     `conv-unlock-live` in strong.CtxMorph §3.
--
-- HOW THIS WAS FOUND.  By finishing the tower example
-- (strong.Examples §5a).  The eleventh step of that
-- run is `CancelR`, whose contractum wraps the cancelled value in
-- `rewind Θ₂` and in `Θ₁ ⋉ Θ₂`, where Θ₁ is the argument's
-- `dualMorph Θ₂` from the `Peel` that sent it across.  Every state up to
-- and including the redex is well typed, so this is a defect in the rules
-- and not in the example.
--
-- WHAT IS NOT CHECKED HERE.  That the frame below is the one that run's
-- eleventh step cancels against.  That link is a comment: the states the
-- run passes through are no longer written down, and the only evidence
-- for it is that the run completes at all.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹)
open import strong.Ctx
open import strong.CtxMorph
open import strong.TypeCheck using (conv!)

------------------------------------------------------------------------
-- 1. The locking frame, and the contexts it runs in
------------------------------------------------------------------------

-- Θ₂ LOCKS: it is `TyPeelR-Λ`'s `instantiate` over a frame that had
-- already crossed two `Λ`s.
Θlock : CtxMorph
Θlock = instantiate (` 0) (morph [] (lock 0 2 ∷ lock 0 0 ∷ []))

Θlock-explicit :
  Θlock ≡ morph (` 0 ∷ []) (lock 1 3 ∷ lock 1 1 ∷ unlock 0 0 ∷ [])
Θlock-explicit = refl

repsW : RepCtx
repsW = bindR (` 0) ∷ bindR (` 0) ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []

-- the exterior the step runs in, and the two contexts Θlock induces
Δ-out Δ-arg Δ-conv : Ctxᵗ
Δ-out = (bindR (` 0) ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 2 ∷ [])
Δ-arg = repsW ∣ (1 ∷ 3 ∷ [])
Δ-conv = repsW ∣ (0 ∷ 1 ∷ 3 ∷ [])

-- The conversion run starts from the exterior extended by the frame's own
-- binds.  Checked, rather than asserted, because `no-old-rewind-conv`
-- below is a statement about exactly this context and would be a true
-- statement about an irrelevant one if this were wrong.
chk-reps : reps (extendReps (binds (rewind Θlock)) Δ-out) ≡ repsW
chk-reps = refl

chk-names : names (extendReps (binds (rewind Θlock)) Δ-out) ≡ 1 ∷ 3 ∷ []
chk-names = refl

------------------------------------------------------------------------
-- 2. The wall
------------------------------------------------------------------------

-- THE CONVERSION JUDGEMENT AS IT STOOD, before the re-unlock clause.  A
-- `rewind` appends the dual of every change, so `rewind Θlock`
-- re-`unlock`s two representation variables whose `lock`s the conversion
-- context SKIPPED — and under these three clauses that is a freshness
-- violation.
infix 4 _∣_⊢χᶜ°_⇒_
data _∣_⊢χᶜ°_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  conv°[] : ∀ {Δ} → Ξ ∣ Δ ⊢χᶜ° [] ⇒ Δ
  conv°-lock : ∀ {Δ₁ Δ₂ χ X α} → Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ° χ ⇒ Δ₂
    → Ξ ∣ Δ₁ ⊢χᶜ° lock X α ∷ χ ⇒ Δ₂
  conv°-unlock : ∀ {Δ₁ Δ₂ Δ₃ χ X α} → Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ° χ ⇒ Δ₂
    → Δ₂ ∌ʳ α
    → α ⊢+ Δ₂ at X ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χᶜ° unlock X α ∷ χ ⇒ Δ₃

-- `rewind Θlock` has NO conversion context, so `env` cannot type
-- `CancelR`'s contractum and the run stops dead.
no-old-rewind-conv : ∀ {Δᶜ}
  → repsW ∣ (1 ∷ 3 ∷ []) ⊢χᶜ° changes (rewind Θlock) ⇒ Δᶜ → ⊥
no-old-rewind-conv
  (conv°-lock _
    (conv°-unlock _
      (conv°-unlock _
        (conv°-lock _
          (conv°-lock _ (conv°-unlock _ conv°[] _ ins-here)))
        (fresh∷ _ (fresh∷ _ (fresh∷ ne _))) _)
      _ _)) = ne refl

------------------------------------------------------------------------
-- 3. The repair
------------------------------------------------------------------------

-- With the re-unlock clause the run goes through, and the conversion
-- context is the one Θlock's own conversion produced — which is exactly
-- what `CancelR`'s minted `mkId A` is checked against.
rewind-conv-repaired : Δ-out ⊢ᶜ rewind Θlock ⇒ Δ-conv
rewind-conv-repaired = proj₂ (conv! Δ-out (rewind Θlock))

-- The same wall stands in front of `CancelR`'s OTHER frame, `Θ₁ ⋉ Θ₂`,
-- whenever the crossing argument acquired Θ₂'s dual at a `Peel`.
cancel-inner-conv-repaired :
  Δ-arg ⊢ᶜ dualMorph Θlock ⋉ Θlock ⇒ Δ-conv
cancel-inner-conv-repaired =
  proj₂ (conv! Δ-arg (dualMorph Θlock ⋉ Θlock))
