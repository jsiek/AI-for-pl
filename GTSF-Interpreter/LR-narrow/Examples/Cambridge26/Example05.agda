module LR-narrow.Examples.Cambridge26.Example05 where

-- File Charter:
--   * Checks Cambridge26 Example 5, where only the precise program blames.
--   * GTSF has no closed constant of a second base type, so the mismatching
--     ground value is the tagged dynamic identity (ground `★ ⇒ ★`).
--   * Proves the resulting closed narrowing belongs to `LR-narrow` directly
--     from the two interpreter computations.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Interpreter using (blamed; interpret; returned)
open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import LR-narrow.Context.KripkeRefl using (interpretation-⊒ⁱ-refl)
open import LR-narrow.World using
  (Interpretation; left-types; left-world; right-types; right-world)
open import NuTerms using (`_; ƛ_; _·_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import TypeCheck using (is-just)
open import Types using (★)

example : ClosedExample
example =
  checked-example ★ ★
    dynamic-result
    dynamic-result-c
    dynamic-result-narrowing
  (as-dynamic-nat-function (ƛ (` 0)) · wrong-ground-argument)
  (id★ · wrong-ground-argument)
  is-just is-just

private
  -- Both computations time out with zero, one, or two units of fuel.  With
  -- three or more, the imprecise left computation returns and the precise
  -- right computation blames.  The clauses below make that fuel
  -- analysis exhaustive.
  three : ℕ
  three = suc (suc (suc zero))

  precise-blames : ∀ {w}
    → (I : Interpretation {[]} {zero} {zero} w)
    → interpret (right-world w) [] (right-types I)
        (precise-term example) three
      ≡ blamed (right-world w)
  precise-blames I = refl

  precise-return-impossible : ∀ {w n U V}
    → (I : Interpretation {[]} {zero} {zero} w)
    → interpret (right-world w) [] (right-types I)
        (precise-term example) n
      ≡ returned U V
    → ⊥
  precise-return-impossible {n = zero} I ()
  precise-return-impossible {n = suc zero} I ()
  precise-return-impossible {n = suc (suc zero)} I ()
  precise-return-impossible {n = suc (suc (suc n))} I ()

  imprecise-return-world : ∀ {w n U V}
    → (I : Interpretation {[]} {zero} {zero} w)
    → interpret (left-world w) [] (left-types I)
        (imprecise-term example) n
      ≡ returned U V
    → left-world w ≡ U
  imprecise-return-world {n = zero} I ()
  imprecise-return-world {n = suc zero} I ()
  imprecise-return-world {n = suc (suc zero)} I ()
  imprecise-return-world {n = suc (suc (suc n))} I refl = refl

  imprecise-blame-impossible : ∀ {w n U}
    → (I : Interpretation {[]} {zero} {zero} w)
    → interpret (left-world w) [] (left-types I)
        (imprecise-term example) n
      ≡ blamed U
    → ⊥
  imprecise-blame-impossible {n = zero} I ()
  imprecise-blame-impossible {n = suc zero} I ()
  imprecise-blame-impossible {n = suc (suc zero)} I ()
  imprecise-blame-impossible {n = suc (suc (suc n))} I ()

-- `forward-return` takes its blame alternative, so this proof never has to
-- construct the active positive-index `id★` payload relation. The current
-- interpretation is already a suitable common future.
example-membership : Membership example
example-membership {w} I k = record
  { forward-return = λ { {n = n} _ left-returns →
      inj₂
        (three , right-world w , w , I ,
         interpretation-⊒ⁱ-refl I ,
         imprecise-return-world {n = n} I left-returns , refl ,
         precise-blames I) }
  ; backward-return = λ { {n = n} _ right-returns →
      ⊥-elim (precise-return-impossible {n = n} I right-returns) }
  ; forward-blame = λ { {n = n} _ left-blames →
      ⊥-elim (imprecise-blame-impossible {n = n} I left-blames) }
  }
