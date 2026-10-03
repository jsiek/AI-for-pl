open import TypeSafety using (Preservation; PreservationWf)

module proof.DGG.RunTyping
  (preservation : Preservation)
  (preservationWf : PreservationWf)
  where

-- File Charter:
--   * TYPING AND CONTEXT WELL-FORMEDNESS ALONG A RUN, from the one-step
--     statements `Preservation` and `PreservationWf` (TypeSafety.agda).
--     An ordinary helper module, parameterized by those two statements
--     (proof/DGG/PLAN.md §1), used by the DGG's Proof modules to supply
--     the `WfCtx` premises of Sim, SimBack and the catch-ups.
--   * `wf*`/`⊢*` end at `runCtx r`; `wfˢ`/`⊢ˢ` at `applyˢ (allocs r) Δ`,
--     the form the statements' worlds use (`runCtx≡applyˢ`).

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (subst)

open import Types using (Ty)
open import Ctx using (Ctxᵗ; WfCtx)
open import Terms using (Term; _∣_⊢_⦂_)
open import Reduction using (_⊢_-→*_; done; _then_; runCtx)
open import proof.DGG.Evolve using (applyˢ; allocs; runCtx≡applyˢ)

private
  variable
    Δ : Ctxᵗ
    M N : Term
    A : Ty

wf* : WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A → (r : Δ ⊢ M -→* N) → WfCtx (runCtx r)
wf* wf ⊢M done        = wf
wf* wf ⊢M (st then r) =
  wf* (preservationWf wf ⊢M st) (preservation wf ⊢M st) r

⊢* : WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A → (r : Δ ⊢ M -→* N)
  → runCtx r ∣ [] ⊢ N ⦂ A
⊢* wf ⊢M done        = ⊢M
⊢* wf ⊢M (st then r) =
  ⊢* (preservationWf wf ⊢M st) (preservation wf ⊢M st) r

wfˢ : WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A → (r : Δ ⊢ M -→* N)
  → WfCtx (applyˢ (allocs r) Δ)
wfˢ wf ⊢M r = subst WfCtx (runCtx≡applyˢ r) (wf* wf ⊢M r)

⊢ˢ : ∀ {Δ M N A} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A → (r : Δ ⊢ M -→* N)
  → applyˢ (allocs r) Δ ∣ [] ⊢ N ⦂ A
⊢ˢ {N = N} {A = A} wf ⊢M r =
  subst (λ Γ → Γ ∣ [] ⊢ N ⦂ A) (runCtx≡applyˢ r) (⊢* wf ⊢M r)
