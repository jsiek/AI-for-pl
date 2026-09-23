module strong-rep-store.notes.ReUnlockWall where

-- THE MODULE NAME IS A DATE-STAMPED PROPER NOUN.  `Change`'s two
-- constructors were renamed `lock`/`unlock` → `unbind`/`bind` on
-- 2026-09-23 (notes/DECISIONS.md), so the "re-unlock" clause this
-- file is about is now `conv-bind-live`.

-- File Charter:
--   * The machine-checked record of ONE defect in the reduction rules and
--     of its repair: `rewind Θ` and `Θ₁ ++ Θ₂` had no conversion context
--     whenever Θ unbinds, so `CancelR`'s and `IdPush`'s contracta were
--     untypeable.
--   * It holds the obstruction (`no-old-rewind-conv`, stated against a
--     local copy of the conversion judgement as it stood) and the two
--     checks that the repaired judgement does give those frames a
--     conversion context.
--   * Nothing here runs a program.  The reasoning is in
--     notes/DECISIONS.md (2026-09-17); the rule that changed is
--     `conv-bind-live` in strong-rep-store.Boundary §3.
--
-- HOW THIS WAS FOUND.  By finishing the tower example
-- (strong-rep-store.Examples §5a).  The eleventh step of that
-- run is `CancelR`, whose contractum wraps the cancelled value in
-- `rewind Θ₂` and in `Θ₁ ++ Θ₂`, where Θ₁ is the argument's
-- `dual Θ₂` from the `Peel` that sent it across.  Every state up to
-- and including the redex is well typed, so this is a defect in the rules
-- and not in the example.
--
-- WHAT IS NOT CHECKED HERE.  That the frame below is the one that run's
-- eleventh step cancels against.  That link is a comment: the states the
-- run passes through are no longer written down, and the only evidence
-- for it is that the run completes at all.

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹)
open import strong-rep-store.Ctx
open import strong-rep-store.Boundary
open import strong-rep-store.TypeCheck using (conv!)

------------------------------------------------------------------------
-- 1. The unbinding frame, and the contexts it runs in
------------------------------------------------------------------------

-- Θ₂ UNBINDS: it is `TyPeelR-Λ`'s `inst` over a frame that had
-- already crossed two `Λ`s.
Θunbind : Boundary
Θunbind = inst ((unbind 0 2 ∷ unbind 0 0 ∷ []))

Θunbind-explicit :
  Θunbind ≡ (unbind 1 3 ∷ unbind 1 1 ∷ bind 0 0 ∷ [])
Θunbind-explicit = refl

repsW : RepCtx
repsW = bindR (` 0) ∷ bindR (` 0) ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []

-- The exterior the step runs in.  WITH THE STORE (experiment 2,
-- 2026-09-22) the cell `` ` 0 `` that `inst` mints is ALLOCATED
-- on the ambient context rather than carried on the frame, so the
-- exterior already holds it and the crossing argument's context is the
-- same one: the bind block that used to separate `Δ-out` from `Δ-arg`
-- is gone.
Δ-out Δ-arg Δ-conv : Ctxᵗ
Δ-out  = repsW ∣ (1 ∷ 3 ∷ [])
Δ-arg  = Δ-out
Δ-conv = repsW ∣ (0 ∷ 1 ∷ 3 ∷ [])

-- The conversion run starts AT THE EXTERIOR — there is no bind block to
-- extend it by.  Checked, rather than asserted, because
-- `no-old-rewind-conv` below is a statement about exactly this context
-- and would be a true statement about an irrelevant one if this were
-- wrong.  (It used to be stated about
-- `extendReps (binds (rewind Θunbind)) Δ-out`, which is what `Δ-out` now
-- IS.)
chk-reps : reps Δ-out ≡ repsW
chk-reps = refl

chk-names : names Δ-out ≡ 1 ∷ 3 ∷ []
chk-names = refl

------------------------------------------------------------------------
-- 2. The wall
------------------------------------------------------------------------

-- THE CONVERSION JUDGEMENT AS IT STOOD, before the re-bind clause.  A
-- `rewind` appends the dual of every change, so `rewind Θunbind`
-- re-`bind`s two representation variables whose `unbind`s the conversion
-- context SKIPPED — and under these three clauses that is a freshness
-- violation.
infix 4 _∣_⊢χᶜ°_⇒_
data _∣_⊢χᶜ°_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  conv°[] : ∀ {Δ} → Ξ ∣ Δ ⊢χᶜ° [] ⇒ Δ
  conv°-unbind : ∀ {Δ₁ Δ₂ χ X α} → Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ° χ ⇒ Δ₂
    → Ξ ∣ Δ₁ ⊢χᶜ° unbind X α ∷ χ ⇒ Δ₂
  conv°-bind : ∀ {Δ₁ Δ₂ Δ₃ χ X α} → Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ° χ ⇒ Δ₂
    → Δ₂ ∌ʳ α
    → α ⊢+ Δ₂ at X ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χᶜ° bind X α ∷ χ ⇒ Δ₃

-- `rewind Θunbind` has NO conversion context, so `env` cannot type
-- `CancelR`'s contractum and the run stops dead.
no-old-rewind-conv : ∀ {Δᶜ}
  → repsW ∣ (1 ∷ 3 ∷ []) ⊢χᶜ° (rewind Θunbind) ⇒ Δᶜ → ⊥
no-old-rewind-conv
  (conv°-unbind _
    (conv°-bind _
      (conv°-bind _
        (conv°-unbind _
          (conv°-unbind _ (conv°-bind _ conv°[] _ ins-here)))
        (fresh∷ _ (fresh∷ _ (fresh∷ ne _))) _)
      _ _)) = ne refl

------------------------------------------------------------------------
-- 3. The repair
------------------------------------------------------------------------

-- With the re-bind clause the run goes through, and the conversion
-- context is the one Θunbind's own conversion produced — which is exactly
-- what `CancelR`'s minted `mkId A` is checked against.
rewind-conv-repaired : Δ-out ⊢ᶜ rewind Θunbind ⇒ Δ-conv
rewind-conv-repaired = proj₂ (conv! Δ-out (rewind Θunbind))

-- The same wall stands in front of `CancelR`'s OTHER frame, `Θ₁ ++ Θ₂`,
-- whenever the crossing argument acquired Θ₂'s dual at a `Peel`.
cancel-inner-conv-repaired :
  Δ-arg ⊢ᶜ dual Θunbind ++ Θunbind ⇒ Δ-conv
cancel-inner-conv-repaired =
  proj₂ (conv! Δ-arg (dual Θunbind ++ Θunbind))
