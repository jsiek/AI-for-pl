module GradualExamples where

-- File Charter:
--   * Closed GTSF source examples checked by `GradualTypeCheck` and run
--     through source checking, compilation, and target evaluation.
--   * Adapted from the PolyUpDown fresh examples by dropping explicit
--     up/down coercion syntax.
--   * Each directly executable source program has both typing evidence and a
--     fuel-bounded `Run` regression for its expected target value.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)

open import Types
open import Ctx using (ctxWf-[])
open import Coercions using () renaming (_! to _!ᶜ)
import Eval as Eval
open import GradualTerms
open import GradualTypeCheck
  using (IsJust; is-just; toWitness; type-check; type-check-expect)
open import NuTerms using (Term) renaming ($ to $ᵀ; _⟨_⟩ to _⟨ᵀ_⟩)
open import Primitives
import Run as Run

------------------------------------------------------------------------
-- Shared terms and helpers
------------------------------------------------------------------------

nat : ℕ → GTerm
nat n = $ (κℕ n)

natᵀ : ℕ → Term
natᵀ n = $ᵀ (κℕ n)

taggedNatᵀ : ℕ → Term
taggedNatᵀ n = natᵀ n ⟨ᵀ (‵ `ℕ) !ᶜ ⟩

c : GTerm
c = nat 7

n42 : GTerm
n42 = nat 42

n69 : GTerm
n69 = nat 69

idDyn : GTerm
idDyn = ƛ ★ ⇒ ` 0

natId : GTerm
natId = ƛ (‵ `ℕ) ⇒ ` 0

polyId : GTerm
polyId = Λ (ƛ (＇ 0) ⇒ ` 0)

polyApp : GTerm
polyApp =
  Λ
    (Λ
      (ƛ ((＇ 1) ⇒ (＇ 0)) ⇒
        ƛ (＇ 1) ⇒
          (` 1 ·[ 1 ] ` 0)))

polyK : GTerm
polyK = Λ (ƛ (＇ 0) ⇒ ƛ (＇ 0) ⇒ ` 1)

polyBetaId : GTerm
polyBetaId =
  Λ
    (ƛ (＇ 0) ⇒
      ((ƛ (＇ 0) ⇒ ` 0) ·[ 2 ] ` 0))

expect-⊢ :
  (M : GTerm) →
  (A : Ty) →
  IsJust (type-check-expect 0 [] ctxWf-[] M A) →
  0 ∣ [] ⊢ M ⦂ A
expect-⊢ M A ok = toWitness ok

run-term : ∀ {M} → Maybe (Run.RunResult M) → Maybe Term
run-term nothing = nothing
run-term (just r) = just (Eval.finalTerm (Run.evaluation r))

run-gas : ℕ
run-gas = 100

------------------------------------------------------------------------
-- Basic source examples
------------------------------------------------------------------------

idDyn-⊢ : 0 ∣ [] ⊢ idDyn ⦂ (★ ⇒ ★)
idDyn-⊢ = expect-⊢ idDyn (★ ⇒ ★) is-just

natId-⊢ : 0 ∣ [] ⊢ natId ⦂ ((‵ `ℕ) ⇒ (‵ `ℕ))
natId-⊢ = expect-⊢ natId ((‵ `ℕ) ⇒ (‵ `ℕ)) is-just

polyId-⊢ : 0 ∣ [] ⊢ polyId ⦂ `∀ ((＇ 0) ⇒ (＇ 0))
polyId-⊢ = expect-⊢ polyId (`∀ ((＇ 0) ⇒ (＇ 0))) is-just

example-dyn-id : GTerm
example-dyn-id = idDyn ·[ 10 ] c

example-dyn-id-⊢ : 0 ∣ [] ⊢ example-dyn-id ⦂ ★
example-dyn-id-⊢ = expect-⊢ example-dyn-id ★ is-just

example-nat-id : GTerm
example-nat-id = natId ·[ 11 ] c

example-nat-id-⊢ : 0 ∣ [] ⊢ example-nat-id ⦂ (‵ `ℕ)
example-nat-id-⊢ = expect-⊢ example-nat-id (‵ `ℕ) is-just

example-poly-id : GTerm
example-poly-id = (polyId `[ ‵ `ℕ ]) ·[ 12 ] c

example-poly-id-⊢ : 0 ∣ [] ⊢ example-poly-id ⦂ (‵ `ℕ)
example-poly-id-⊢ = expect-⊢ example-poly-id (‵ `ℕ) is-just

------------------------------------------------------------------------
-- Ahmed et al. style polymorphic examples
------------------------------------------------------------------------

sec2-app-dyn : GTerm
sec2-app-dyn =
  (((polyApp `[ ★ ]) `[ ★ ]) ·[ 20 ] idDyn) ·[ 21 ] c

sec2-app-dyn-⊢ : 0 ∣ [] ⊢ sec2-app-dyn ⦂ ★
sec2-app-dyn-⊢ = expect-⊢ sec2-app-dyn ★ is-just

sec2-app-base : GTerm
sec2-app-base =
  (((polyApp `[ ‵ `ℕ ]) `[ ‵ `ℕ ]) ·[ 22 ] natId) ·[ 23 ] c

sec2-app-base-⊢ : 0 ∣ [] ⊢ sec2-app-base ⦂ (‵ `ℕ)
sec2-app-base-⊢ = expect-⊢ sec2-app-base (‵ `ℕ) is-just

sec5-β : GTerm
sec5-β = (polyBetaId `[ ‵ `ℕ ]) ·[ 24 ] c

sec5-β-⊢ : 0 ∣ [] ⊢ sec5-β ⦂ (‵ `ℕ)
sec5-β-⊢ = expect-⊢ sec5-β (‵ `ℕ) is-just

sec6-K-dyn : GTerm
sec6-K-dyn =
  ((polyK `[ ★ ]) ·[ 25 ] n42) ·[ 26 ] n69

sec6-K-dyn-⊢ : 0 ∣ [] ⊢ sec6-K-dyn ⦂ ★
sec6-K-dyn-⊢ = expect-⊢ sec6-K-dyn ★ is-just

sec6-K-base : GTerm
sec6-K-base =
  ((polyK `[ ‵ `ℕ ]) ·[ 27 ] n42) ·[ 28 ] n69

sec6-K-base-⊢ : 0 ∣ [] ⊢ sec6-K-base ⦂ (‵ `ℕ)
sec6-K-base-⊢ = expect-⊢ sec6-K-base (‵ `ℕ) is-just

------------------------------------------------------------------------
-- Successful execution tests
------------------------------------------------------------------------

example-dyn-id-run :
  run-term (Run.run run-gas example-dyn-id) ≡ just (taggedNatᵀ 7)
example-dyn-id-run = refl

example-nat-id-run :
  run-term (Run.run run-gas example-nat-id) ≡ just (natᵀ 7)
example-nat-id-run = refl

example-poly-id-run :
  run-term (Run.run run-gas example-poly-id) ≡ just (natᵀ 7)
example-poly-id-run = refl

sec2-app-dyn-run :
  run-term (Run.run run-gas sec2-app-dyn) ≡ just (taggedNatᵀ 7)
sec2-app-dyn-run = refl

sec2-app-base-run :
  run-term (Run.run run-gas sec2-app-base) ≡ just (natᵀ 7)
sec2-app-base-run = refl

sec5-β-run :
  run-term (Run.run run-gas sec5-β) ≡ just (natᵀ 7)
sec5-β-run = refl

sec6-K-dyn-run :
  run-term (Run.run run-gas sec6-K-dyn) ≡ just (taggedNatᵀ 42)
sec6-K-dyn-run = refl

sec6-K-base-run :
  run-term (Run.run run-gas sec6-K-base) ≡ just (natᵀ 42)
sec6-K-base-run = refl

------------------------------------------------------------------------
-- Rejection tests
------------------------------------------------------------------------

bad-app : GTerm
bad-app = c ·[ 90 ] c

bad-app-test : type-check 0 [] ctxWf-[] bad-app ≡ nothing
bad-app-test = refl

bad-type-app : GTerm
bad-type-app = c `[ ‵ `ℕ ]

bad-type-app-test : type-check 0 [] ctxWf-[] bad-type-app ≡ nothing
bad-type-app-test = refl

bad-constant-Λ : GTerm
bad-constant-Λ = Λ c

bad-constant-Λ-test : type-check 0 [] ctxWf-[] bad-constant-Λ ≡ nothing
bad-constant-Λ-test = refl
