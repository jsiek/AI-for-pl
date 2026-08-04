module proof.Compilation.CompileDynamicApplicationTest where

-- File Charter:
--   * Regression test for fixed-domain dynamic application compilation.
--   * Checks the function cast to `★ ⇒ ★` and the argument cast to `★`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_; proj₁)

open import Types
open import Ctx using (ctxWf-[]; ctxWf-∷)
open import Compile using
  ( cast
  ; compile
  ; consistency-cast-plan
  ; dynamic-application-function-consistent
  )
import Imprecision as Imp
open import Primitives using (κℕ)
open import GradualTerms
  using ()
  renaming
    ( `_ to `ᴳ_
    ; _·[_]_ to _·ᴳ[_]_
    ; $ to $ᴳ
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢$ to ⊢ᴳ$
    )
open import NuTerms
  using ()
  renaming
    ( `_ to `ᵀ_
    ; _·_ to _·ᵀ_
    ; $ to $ᵀ
    )

test-label : Label
test-label = 72

nat~star : zero Imp.⊢ ‵ `ℕ ~ ★
nat~star = (‵ `ℕ) , Imp.idι , (Imp.tag `ℕ)

dynamic-app-⊢ :
  zero ∣ ★ ∷ [] ⊢ᴳ
    `ᴳ zero ·ᴳ[ test-label ] $ᴳ (κℕ zero) ⦂ ★
dynamic-app-⊢ =
  ⊢ᴳ·★ (⊢ᴳ` Z) (⊢ᴳ$ (κℕ zero)) nat~star

compile-dynamic-application-fixed-domain :
  proj₁ (compile (ctxWf-∷ wf★ ctxWf-[]) dynamic-app-⊢)
    ≡ cast
        (consistency-cast-plan {Δ = zero}
          test-label dynamic-application-function-consistent)
        (`ᵀ zero)
      ·ᵀ cast
        (consistency-cast-plan {Δ = zero} test-label nat~star)
        ($ᵀ (κℕ zero))
compile-dynamic-application-fixed-domain = refl
