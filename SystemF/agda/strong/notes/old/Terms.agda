module strong.notes.old.Terms where

-- Strong System F — runtime terms in de Bruijn form.  Source terms are the
-- fragment without the reveal/conceal wrappers; those two are runtime-only.
--
-- The wrappers carry the types the reduction rules manipulate:
--   reveal   M ↑[ A , B ]      — A is X's representation, B the annotation.
--                                X is bound fresh at type-index 0 of M.
--   conceal  M ↓[ X , A , B ]  — X is the concealed type-variable index,
--                                A its representation, B the annotation.

open import Data.Nat using (ℕ)
open import strong.Types

infix  9 `_
infix  9 $_
infix  5 ƛ_∙_
infix  5 Λ_
infixl 7 _·_
infixl 8 _·[_,_]
infixl 8 _↑[_,_]
infixl 8 _↓[_,_,_]

data Term : Set where
  `_        : ℕ → Term                       -- term variable (de Bruijn index)
  $_        : ℕ → Term                       -- numeral literal n
  ƛ_∙_      : Ty → Term → Term               -- λx:A. N          (annotation ∙ body)
  _·_       : Term → Term → Term             -- L · M
  Λ_        : Term → Term                    -- ΛX. N
  _·[_,_]   : Term → Ty → Ty → Term          -- L @B[A]           (B the ∀-body, A the argument)
  _↑[_,_]   : Term → Ty → Ty → Term          -- M ↑[X:=A]@B        (reveal)
  _↓[_,_,_] : Term → ℕ → Ty → Ty → Term      -- M ↓[X:=A]@B        (conceal)
