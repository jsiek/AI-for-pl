module proof.LR.TimingProbe where

-- File Charter:
--   * Probe for the cast lemma's case 6 (notes/logrel-dgg.md, Section 7,
--     obstacle O1): related source programs in which the right
--     instantiates a polymorphic value once, at a cast, while the left
--     instantiates it twice, later.
--   * The programs are related by source term precision (`left⊑right`),
--     checked by `GradualTypeCheck`, elaborated by `compileᴱ` and run by
--     `Eval`; the facts are the number of store variables each run
--     allocates, and that neither run blames.

import Data.Fin as Fin
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import GradualTerms
open import GradualTypeCheck
open import Imprecision
open import Consistency using (_∼_)
open import GradualTermImprecision
open import Primitives
open import Eval using (eval; EvalOutcome; outcomeCtx; returned; blamed)
open import LR.Elaborate using (compileᴱ)
open import CastTerms using (Term)

ℕᵗ 𝔹ᵗ : Ty 0
ℕᵗ = ‵ `ℕ
𝔹ᵗ = ‵ `𝔹

X : Ty 1
X = ＇ Fin.zero

-- a polymorphic value built from `λy:★. y` by a `gen` cast (passing it
-- where `∀X.X→X` is expected); each instantiation creates a variable
-- that the body cast tags arguments with (`X!`) and projects results at
-- (`?X`)
idT : GTerm 0
idT = (ƛ (`∀ (X ⇒ X)) ⇒ ` 0) ·[ 5 ] (ƛ ★ ⇒ ` 0)

-- left: f keeps its type ∀X.X→X and is instantiated twice
left : GTerm 0
left =
  (ƛ (`∀ (X ⇒ X)) ⇒
     ((ƛ ℕᵗ ⇒ ((` 1 `[ 𝔹ᵗ ]) ·[ 1 ] $ (κ𝔹 true)))
        ·[ 2 ] ((` 0 `[ ℕᵗ ]) ·[ 3 ] $ (κℕ 3))))
  ·[ 4 ] idT

-- right: f has type ★→★, so the argument is instantiated at the cast
right : GTerm 0
right =
  (ƛ (★ ⇒ ★) ⇒
     ((ƛ ★ ⇒ (` 1 ·[ 1 ] $ (κ𝔹 true)))
        ·[ 2 ] (` 0 ·[ 3 ] $ (κℕ 3))))
  ·[ 4 ] idT

-- the arguments alone: the same functions, returning f
leftArg rightArg : GTerm 0
leftArg = (ƛ (`∀ (X ⇒ X)) ⇒ ` 0) ·[ 4 ] idT
rightArg = (ƛ (★ ⇒ ★) ⇒ ` 0) ·[ 4 ] idT

left-⊢ : 0 ∣ [] ⊢ left ⦂ 𝔹ᵗ
left-⊢ = fromJust (type-check-expect 0 [] left 𝔹ᵗ) is-just

right-⊢ : 0 ∣ [] ⊢ right ⦂ ★
right-⊢ = fromJust (type-check-expect 0 [] right ★) is-just

leftArg-⊢ : 0 ∣ [] ⊢ leftArg ⦂ `∀ (X ⇒ X)
leftArg-⊢ = fromJust (type-check-expect 0 [] leftArg (`∀ (X ⇒ X))) is-just

rightArg-⊢ : 0 ∣ [] ⊢ rightArg ⦂ (★ ⇒ ★)
rightArg-⊢ = fromJust (type-check-expect 0 [] rightArg (★ ⇒ ★)) is-just

-- the number of store variables a run allocates
allocs : ∀ {M : Term 0} → Maybe (EvalOutcome M) → Maybe ℕ
allocs (just r) = just (outcomeCtx r)
allocs nothing = nothing

-- the run returns a value, not blame
returns : ∀ {M : Term 0} → Maybe (EvalOutcome M) → Bool
returns (just (returned r)) = true
returns (just (blamed χs ss)) = false
returns nothing = false

gas : ℕ
gas = 200

-- the left's argument is a value: nothing is allocated
leftArg-allocs : allocs (eval gas (compileᴱ leftArg-⊢)) ≡ just 0
leftArg-allocs = refl

-- the right's argument allocates α′ (the cast's `inst`) and β′ (the
-- instantiation of `idT` at α′), before f is used
rightArg-allocs : allocs (eval gas (compileᴱ rightArg-⊢)) ≡ just 2
rightArg-allocs = refl

-- the whole left program allocates σ₁ and σ₂, one per instantiation
left-allocs : allocs (eval gas (compileᴱ left-⊢)) ≡ just 2
left-allocs = refl

-- the whole right program allocates nothing more: both uses of f run
-- the one instantiation, so σ₁ and σ₂ both meet β′
right-allocs : allocs (eval gas (compileᴱ right-⊢)) ≡ just 2
right-allocs = refl

-- neither program blames
left-returns : returns (eval gas (compileᴱ left-⊢)) ≡ true
left-returns = refl

right-returns : returns (eval gas (compileᴱ right-⊢)) ≡ true
right-returns = refl

------------------------------------------------------------------------
-- The two programs are related by source term precision
------------------------------------------------------------------------

private
  cons : ∀ (A B : Ty 0) → IsJust (consistent? A B) → A ∼ B
  cons A B ok = fromJust (consistent? A B) ok

  ∀XX : Ty 0
  ∀XX = `∀ (X ⇒ X)

  -- the parameter: `∀X.X→X ⊑ ★→★`, with X left-only
  pF : idᵐ ⊢ ∀XX ⊑ (★ ⇒ ★)
  pF = ∀⊑ nonvar-fun (∈-fun-left var-∈) (⇒⊑⇒ (X⊑★ refl) (X⊑★ refl))

  pId : idᵐ ⊢ ∀XX ⊑ ∀XX
  pId = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

  γF : CtxImp idᵐ
  γF = ctx-imp ∀XX (★ ⇒ ★) pF ∷ []

  γN : CtxImp idᵐ
  γN = ctx-imp ℕᵗ ★ ι⊑★ ∷ γF

  idT⊑idT : idᵐ ∣ [] ⊢ᴳ idT ⊑ idT ⦂ ∀XX ⊑ ∀XX ∶ pId
  idT⊑idT =
    ·⊑·ᴳ {pA = pId} {pB = pId} (ƛ⊑ƛᴳ (x⊑xᴳ Zⁱ))
      (ƛ⊑ƛᴳ {pA = ★⊑★} {pB = ★⊑★} (x⊑xᴳ Zⁱ))
      (cons ∀XX (★ ⇒ ★) is-just) (cons ∀XX (★ ⇒ ★) is-just)

  -- `f [ℕ] 3 ⊑ f 3` and `f [𝔹] true ⊑ f true`
  useN : idᵐ ∣ γF ⊢ᴳ (` 0 `[ ℕᵗ ]) ·[ 3 ] $ (κℕ 3) ⊑ ` 0 ·[ 3 ] $ (κℕ 3)
    ⦂ ℕᵗ ⊑ ★ ∶ ι⊑★
  useN =
    ·⊑·ᴳ ([]⊑ᴳ (x⊑xᴳ Zⁱ) ι⊑★ (⇒⊑⇒ ι⊑★ ι⊑★)) (κ⊑κᴳ (κℕ 3))
      (cons ℕᵗ ℕᵗ is-just) (cons ★ ℕᵗ is-just)

  useB : idᵐ ∣ γN ⊢ᴳ (` 1 `[ 𝔹ᵗ ]) ·[ 1 ] $ (κ𝔹 true)
      ⊑ ` 1 ·[ 1 ] $ (κ𝔹 true) ⦂ 𝔹ᵗ ⊑ ★ ∶ ι⊑★
  useB =
    ·⊑·ᴳ ([]⊑ᴳ (x⊑xᴳ (Sⁱ Zⁱ)) ι⊑★ (⇒⊑⇒ ι⊑★ ι⊑★)) (κ⊑κᴳ (κ𝔹 true))
      (cons 𝔹ᵗ 𝔹ᵗ is-just) (cons ★ 𝔹ᵗ is-just)

left⊑right : idᵐ ∣ [] ⊢ᴳ left ⊑ right ⦂ 𝔹ᵗ ⊑ ★ ∶ ι⊑★
left⊑right =
  ·⊑·ᴳ {pA = pF}
    (ƛ⊑ƛᴳ
      (·⊑·ᴳ {pA = ι⊑★} (ƛ⊑ƛᴳ useB) useN
        (cons ℕᵗ ℕᵗ is-just) (cons ★ ★ is-just)))
    idT⊑idT (cons ∀XX ∀XX is-just) (cons (★ ⇒ ★) ∀XX is-just)
