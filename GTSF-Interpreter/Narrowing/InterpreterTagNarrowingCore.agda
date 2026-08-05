module Narrowing.InterpreterTagNarrowingCore where

-- File Charter:
--   * Defines world-indexed narrowing of runtime ground tags.
--   * Keeps the relation separate from construction and equality proofs.
--   * Contains no interpreter execution or reduction semantics.

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterWorldNarrowing
open import Types

module TagRelatedWorlds =
  WorldNarrowing InterpreterTypeNarrowing

open TagRelatedWorlds

data TagNarrowing
    {W W′ : World}
    (R : WorldRelation W W′) :
    Tag → Tag → Set₁ where
  variable-tag⊑ :
    ∀ {name name′} →
    TypeNameNarrowing R name name′ →
    TagNarrowing R
      (variable-tag name)
      (variable-tag name′)

  base-tag⊑ :
    ∀ ι →
    TagNarrowing R (base-tag ι) (base-tag ι)

  function-tag⊑ :
    TagNarrowing R function-tag function-tag
