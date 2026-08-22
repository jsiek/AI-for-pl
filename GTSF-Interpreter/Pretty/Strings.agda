module Pretty.Strings where

-- File Charter:
--   * Provides the small string and generated-name layer shared by the GTSF
--     syntax pretty printers.
--   * Contains no language syntax or semantic dependency.

open import Agda.Builtin.String using
  (String; primShowNat; primStringAppend)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)

infixr 5 _++ˢ_
_++ˢ_ : String → String → String
_++ˢ_ = primStringAppend

parenthesize : String → String
parenthesize text = "(" ++ˢ text ++ˢ ")"

lookupName : String → List String → ℕ → String
lookupName fallback [] index = fallback ++ˢ primShowNat index
lookupName fallback (name ∷ names) zero = name
lookupName fallback (name ∷ names) (suc index) =
  lookupName fallback names index

preferredNameAt : String → String → String → String → ℕ → String
preferredNameAt first second third numbered zero = first
preferredNameAt first second third numbered (suc zero) = second
preferredNameAt first second third numbered (suc (suc zero)) = third
preferredNameAt first second third numbered (suc (suc (suc index))) =
  numbered ++ˢ primShowNat (suc index)

freshTermName : List String → String
freshTermName names = preferredNameAt "x" "y" "z" "x" (length names)
