module Examples where

-- File Charter:
--   * Representative typed programs for STLCSub.
--   * Exercises width/permutation record subtyping, subsumption, projection,
--     beta-reduction, and the executable evaluator.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat renaming
  (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (toWitness; True)

open import Eval using (eval)
open import STLCSub
open import TypeCheckDec using (type-check-expect)

expect-⊢ : (Γ : Ctx) -> (M : Term) -> (A : Ty) ->
           True (type-check-expect Γ M A) -> Γ ⊢ M ⦂ A
expect-⊢ Γ M A ok = toWitness {a? = type-check-expect Γ M A} ok

gas : ℕ
gas = 20

name : Label
name = zeroℕ

age : Label
age = sucℕ zeroℕ

personTy : Ty
personTy = `⟨ (name ⦂ᶠ nat) ∷ (age ⦂ᶠ nat) ∷ [] ⟩

ageTy : Ty
ageTy = `⟨ (age ⦂ᶠ nat) ∷ [] ⟩

person<:age : personTy <: ageTy
person<:age = S-record (fs∷ (ty-there (λ ()) ty-here) S-refl fs[])

age<:top : ageTy <: top
age<:top = S-top

idAge<:personTop : (ageTy ⇒ ageTy) <: (personTy ⇒ top)
idAge<:personTop = S-arrow person<:age age<:top

person : Term
person =
  `record ((name ≔ `zero) ∷ (age ≔ `suc `zero) ∷ [])

person-⊢ : [] ⊢ person ⦂ personTy
person-⊢ = expect-⊢ [] person personTy tt

person-as-age-⊢ : [] ⊢ person ⦂ ageTy
person-as-age-⊢ = expect-⊢ [] person ageTy tt

person-as-top-⊢ : [] ⊢ person ⦂ top
person-as-top-⊢ = expect-⊢ [] person top tt

projectAge : Term
projectAge = person ‼ age

projectAge-⊢ : [] ⊢ projectAge ⦂ nat
projectAge-⊢ = expect-⊢ [] projectAge nat tt

projectAge-↠ : projectAge —↠ `suc `zero
projectAge-↠ =
  projectAge
    —→⟨ β-proj (tm-there (λ ()) tm-here) ⟩
  `suc `zero
    ∎

projectAge-eval : eval gas projectAge ≡ `suc `zero
projectAge-eval = refl

idAge : Term
idAge = ƛ ageTy ⇒ ` 0

idAge-⊢ : [] ⊢ idAge ⦂ (ageTy ⇒ ageTy)
idAge-⊢ = expect-⊢ [] idAge (ageTy ⇒ ageTy) tt

idAge-as-personTop-⊢ : [] ⊢ idAge ⦂ (personTy ⇒ top)
idAge-as-personTop-⊢ = expect-⊢ [] idAge (personTy ⇒ top) tt

idAgePerson : Term
idAgePerson = idAge · person

idAgePerson-⊢ : [] ⊢ idAgePerson ⦂ ageTy
idAgePerson-⊢ = expect-⊢ [] idAgePerson ageTy tt

idAgePerson-↠ : idAgePerson —↠ person
idAgePerson-↠ =
  idAgePerson
    —→⟨ β-ƛ (`record _) ⟩
  person
    ∎

idAgePerson-eval : eval gas idAgePerson ≡ person
idAgePerson-eval = refl

caseNat : Term
caseNat = case_[zero⇒_|suc⇒_] (`suc `zero) `zero (`suc (` 0))

caseNat-⊢ : [] ⊢ caseNat ⦂ nat
caseNat-⊢ = expect-⊢ [] caseNat nat tt

caseNat-↠ : caseNat —↠ `suc `zero
caseNat-↠ =
  caseNat
    —→⟨ β-suc `zero ⟩
  `suc `zero
    ∎

caseNat-eval : eval gas caseNat ≡ `suc `zero
caseNat-eval = refl
