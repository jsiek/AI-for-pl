module Examples where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _≟_; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Nullary using (yes; no)

open import Types
open import Store
open import Coercions
open import PolyCast
open import Reduction
open import Eval

