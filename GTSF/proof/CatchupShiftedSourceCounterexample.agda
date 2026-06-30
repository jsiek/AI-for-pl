module proof.CatchupShiftedSourceCounterexample where

-- File Charter:
--   * Checked counterexample to the current statement of
--     `shifted-source-catchup-Λ-inversion`.
--   * The postulate does not assume the shifted source value is `No•`.
--     Applying it to a lambda value whose body contains a runtime type
--     application produces an impossible `No•` value after unshifted catchup.
--   * This module deliberately imports the postulate from `proof.Catchup` and
--     derives `⊥`; it should stay out of `All.agda`.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import TermNarrowing
open import proof.Catchup using (shifted-source-catchup-Λ-inversion)

id★ᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id ★ ∶ᶜ ★ ⊒ ★
id★ᶜ = cast-id wf★ refl , id★

id★↦id★ᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id ★ ↦ id ★ ∶ᶜ (★ ⇒ ★) ⊒ (★ ⇒ ★)
id★↦id★ᶜ =
  cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
  cross (id★ ↦ id★)

badN : Term
badN = ƛ ((` zero) •)

badV′ : Term
badV′ = ƛ blame

badNo•⊥ : No• badN → ⊥
badNo•⊥ (no•-ƛ ())

badStep⊥ :
  ∀ {χ W} →
  badN —→[ χ ] W →
  ⊥
badStep⊥ (pure-step ())

badCatchupNo•⊥ :
  ∀ {χs W} →
  badN —↠[ χs ] W →
  No• W →
  ⊥
badCatchupNo•⊥ ↠-refl noW = badNo•⊥ noW
badCatchupNo•⊥ (↠-step red _) _ = badStep⊥ red

badBody :
  suc zero ∣ (zero ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ badN ⊒ badV′ ∶ id ★ ↦ id ★
badBody =
  ƛ⊒ƛ id★↦id★ᶜ (⊒blame id★ᶜ)

shifted-source-catchup-Λ-inversion-counterexample : ⊥
shifted-source-catchup-Λ-inversion-counterexample
    with shifted-source-catchup-Λ-inversion
      {Δ = zero}
      {σ = []}
      {χs = []}
      {W = badN}
      {Δ′ = suc zero}
      {Π = []}
      {Π′ = []}
      {π = []}
      {N = badN}
      {V′ = badV′}
      {p = id ★ ↦ id ★}
      (ƛ ((` zero) •))
      ↠-refl
      refl
      refl
      refl
      ⊒ˢ-nil
      badBody
... | _ , W′ , _ , _ , _ , _ , _ , noW′ , N↠W′ , _ =
  badCatchupNo•⊥ N↠W′ noW′
