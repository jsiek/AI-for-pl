module GenTraceScratch where

-- Root scratch for the GEN-path trace question.
-- It records checked facts about where fresh-name tags are minted:
--   * `genᵐ` gives the fresh variable the `★∼X` direction;
--   * flipping that GEN environment gives the matching `X∼★` injection;
--   * Example 12 reaches a value of the shape `(U ↓ seal Y S) ⟨Y!⟩`;
--   * the catalog GEN-path entries still pass the evaluator-backed screen.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Consistency using
  (Var∼; X∼★; ★∼X; Env∼; idᶜ; genᵐ; flipᵐ; _⊢_∼_; id; _!)
open import Conversion using (seal)
import CastTerms as CT
open import CastTerms using (Term; Value; $; _⟨_⟩; _↓_; _《_》; inj)
open import Reduction using (bind; keep; applyEnv)
open import Primitives using (κℕ)

import proof.DGG.Examples as Ex
import proof.DGG.ReachabilityCatalog as Cat
import proof.DGG.ReachabilityScreen as RS


------------------------------------------------------------------------
-- GEN environment direction
------------------------------------------------------------------------

gen-fresh-zero-is-projection :
  genᵐ (idᶜ {Δ = 0}) Fin.zero ≡ ★∼X
gen-fresh-zero-is-projection = refl

example12-post-gen-tag-env : Env∼ 3
example12-post-gen-tag-env =
  flipᵐ
    (genᵐ
      (applyEnv (bind (＇ Fin.zero))
        (applyEnv (bind ★) (idᶜ {Δ = 0}))))

example12-post-gen-tag-env-zero :
  example12-post-gen-tag-env Fin.zero ≡ X∼★
example12-post-gen-tag-env-zero = refl


------------------------------------------------------------------------
-- Name-tagged sealed value in the Example 12 right trace
------------------------------------------------------------------------

example12-sealed-at-generated-name : Term 3
example12-sealed-at-generated-name =
  $ (κℕ 7) ↓ seal Fin.zero (‵ `ℕ)

example12-generated-name-tag :
  example12-post-gen-tag-env ⊢ ＇ Fin.zero ∼ ★
example12-generated-name-tag = id (＇ Fin.zero) !

example12-name-tagged-sealed : Term 3
example12-name-tagged-sealed =
  example12-sealed-at-generated-name ⟨ example12-generated-name-tag ⟩

example12-name-tagged-sealed-value :
  Value example12-name-tagged-sealed
example12-name-tagged-sealed-value = ($ (κℕ 7) ↓ CT.seal) 《 inj 》

example12-right-step₂-change :
  Ex.OneStep.change Ex.right-step₂ ≡ bind (‵ `ℕ)
example12-right-step₂-change = refl

example12-right-step₄-change :
  Ex.OneStep.change Ex.right-step₄ ≡ keep
example12-right-step₄-change = refl

example12-right-step₄-next :
  Ex.OneStep.next Ex.right-step₄ ≡ Ex.right₅
example12-right-step₄-next = refl


------------------------------------------------------------------------
-- Catalog GEN-path screen gates
------------------------------------------------------------------------

left-only-gen-path-screen-clean :
  RS.crossing-suspect (Cat.compiled Cat.left-only-gen-path) ≡ RS.clean
left-only-gen-path-screen-clean = Cat.left-only-gen-path-screens-clean

gen-inst-return-poly-screen-clean :
  RS.crossing-suspect (Cat.compiled Cat.gen-inst-return-poly) ≡ RS.clean
gen-inst-return-poly-screen-clean = Cat.gen-inst-return-poly-screens-clean

gen-inst-self-nat-screen-clean :
  RS.crossing-suspect (Cat.compiled Cat.gen-inst-self-nat) ≡ RS.clean
gen-inst-self-nat-screen-clean = Cat.gen-inst-self-nat-screens-clean

example12-right-tags-nonempty :
  RS.SideSummary.tags (RS.runSummary 30 Ex.example12-right) ≢ []
example12-right-tags-nonempty ()

left-only-gen-path-left-tags-nonempty :
  RS.SideSummary.tags
    (RS.runSummary 80
      (RS.Entry.more-precise (Cat.compiled Cat.left-only-gen-path))) ≢ []
left-only-gen-path-left-tags-nonempty ()

left-only-gen-path-right-tags-empty :
  RS.SideSummary.tags
    (RS.runSummary 80
      (RS.Entry.more-imprecise (Cat.compiled Cat.left-only-gen-path))) ≡ []
left-only-gen-path-right-tags-empty = refl

gen-inst-return-poly-tags-empty :
  RS.SideSummary.tags
    (RS.runSummary 70
      (RS.Entry.more-precise (Cat.compiled Cat.gen-inst-return-poly))) ≡ []
gen-inst-return-poly-tags-empty = refl

gen-inst-self-nat-tags-empty :
  RS.SideSummary.tags
    (RS.runSummary 70
      (RS.Entry.more-precise (Cat.compiled Cat.gen-inst-self-nat))) ≡ []
gen-inst-self-nat-tags-empty = refl
