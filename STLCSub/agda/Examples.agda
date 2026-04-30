module Examples where

-- File Charter:
--   * Representative typed programs for STLCSub.
--   * Exercises width/permutation record subtyping, subsumption, projection,
--     beta-reduction, and the executable evaluator.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)

open import Eval using (eval)
open import STLCSub

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
person-⊢ = ⊢record (⊢∷ ⊢zero (⊢∷ (⊢suc ⊢zero) ⊢[]))

person-as-age-⊢ : [] ⊢ person ⦂ ageTy
person-as-age-⊢ = ⊢sub person-⊢ person<:age

person-as-top-⊢ : [] ⊢ person ⦂ top
person-as-top-⊢ = ⊢sub person-as-age-⊢ S-top

projectAge : Term
projectAge = person ‼ age

projectAge-⊢ : [] ⊢ projectAge ⦂ nat
projectAge-⊢ = ⊢proj person-as-age-⊢ ty-here

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
idAge-⊢ = ⊢ƛ (⊢` Z)

idAge-as-personTop-⊢ : [] ⊢ idAge ⦂ (personTy ⇒ top)
idAge-as-personTop-⊢ = ⊢sub idAge-⊢ idAge<:personTop

idAgePerson : Term
idAgePerson = idAge · person

idAgePerson-⊢ : [] ⊢ idAgePerson ⦂ ageTy
idAgePerson-⊢ = ⊢· idAge-⊢ person-as-age-⊢

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
caseNat-⊢ = ⊢case (⊢suc ⊢zero) ⊢zero (⊢suc (⊢` Z))

caseNat-↠ : caseNat —↠ `suc `zero
caseNat-↠ =
  caseNat
    —→⟨ β-suc `zero ⟩
  `suc `zero
    ∎

caseNat-eval : eval gas caseNat ≡ `suc `zero
caseNat-eval = refl
