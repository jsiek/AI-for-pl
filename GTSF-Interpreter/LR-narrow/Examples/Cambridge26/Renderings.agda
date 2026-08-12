module LR-narrow.Examples.Cambridge26.Renderings where

-- File Charter:
--   * Applies the general pretty printer to the checked Cambridge26 records.
--   * Exposes Cambridge-oriented judgments: imprecise endpoint first,
--     precise endpoint second, and the canonical narrowing coercion.
--   * Recovers lambda annotations from the checked endpoint typings.

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_; _++_)

import LR-narrow.Examples.Cambridge26.Example01 as E01
import LR-narrow.Examples.Cambridge26.Example02 as E02
import LR-narrow.Examples.Cambridge26.Example03 as E03
import LR-narrow.Examples.Cambridge26.Example04 as E04
import LR-narrow.Examples.Cambridge26.Example05 as E05
import LR-narrow.Examples.Cambridge26.Example06 as E06
import LR-narrow.Examples.Cambridge26.Example07 as E07
import LR-narrow.Examples.Cambridge26.Example08 as E08
import LR-narrow.Examples.Cambridge26.Example09 as E09
import LR-narrow.Examples.Cambridge26.Example10 as E10
import LR-narrow.Examples.Cambridge26.Example11 as E11
import LR-narrow.Examples.Cambridge26.Example12 as E12
import LR-narrow.Examples.Cambridge26.Example13 as E13
import LR-narrow.Examples.Cambridge26.Example14 as E14
import LR-narrow.Examples.Cambridge26.Example15 as E15
import LR-narrow.Examples.Cambridge26.Example16 as E16
import LR-narrow.Examples.Cambridge26.Example17 as E17
import LR-narrow.Examples.Cambridge26.Example18 as E18
import LR-narrow.Examples.Cambridge26.Example18b as E18b
import LR-narrow.Examples.Cambridge26.Example19 as E19
import LR-narrow.Examples.Cambridge26.Example20 as E20
import LR-narrow.Examples.Cambridge26.Example21 as E21
import LR-narrow.Examples.Cambridge26.Example22 as E22
import LR-narrow.Examples.Cambridge26.LabeledPrograms as LP
import LR-narrow.Examples.Cambridge26.LabeledRelations as LR

open import LR-narrow.Examples.Cambridge26.Specification
open import Pretty.Coercions using (renderCoercion)
open import Pretty.Narrowings using (renderNarrowingDerivation)
open import Pretty.Strings using (_++ˢ_)
open import Pretty.TypedTerms using (renderTypedTerm)
open import Pretty.Types using (renderType)

renderClosedExample : ClosedExample → List String
renderClosedExample example =
  ("⊢ " ++ˢ renderTypedTerm (imprecise-typing example) ++ˢ
    " : " ++ˢ renderType (imprecise-type example)) ∷
  ("⊢ " ++ˢ renderTypedTerm (precise-typing example) ++ˢ
    " : " ++ˢ renderType (precise-type example)) ∷
  renderNarrowingDerivation (narrowing example) ++
  "-------------------------------- [LR-OBLIGATION]" ∷
  ("⊢ " ++ˢ renderTypedTerm (imprecise-typing example) ++ˢ
    " ⊒ " ++ˢ renderTypedTerm (precise-typing example) ++ˢ
    " : " ++ˢ renderCoercion (narrowing-coercion example)) ∷ []

example01 : List String
example01 = renderClosedExample E01.example
example02 : List String
example02 = renderClosedExample E02.example
example03 : List String
example03 = renderClosedExample E03.example
example04 : List String
example04 = renderClosedExample E04.example
example05 : List String
example05 = renderClosedExample E05.example
example06 : List String
example06 = renderClosedExample E06.example
example07 : List String
example07 = renderClosedExample E07.example
example08 : List String
example08 = renderClosedExample E08.example
example09 : List String
example09 = renderClosedExample E09.example
example10 : List String
example10 = renderClosedExample E10.example
example11 : List String
example11 = renderClosedExample E11.example
example12 : List String
example12 = renderClosedExample E12.example
example13 : List String
example13 = renderClosedExample E13.example
example14 : List String
example14 = renderClosedExample E14.example
example15 : List String
example15 = renderClosedExample E15.example
example16 : List String
example16 = renderClosedExample E16.example
example17 : List String
example17 = renderClosedExample E17.example
example18 : List String
example18 = renderClosedExample E18.example
example18b : List String
example18b = renderClosedExample E18b.example
example19 : List String
example19 = renderClosedExample E19.example
example20 : List String
example20 = renderClosedExample E20.example
example21 : List String
example21 = renderClosedExample E21.example

all-numbered : List (List String)
all-numbered =
  example01 ∷ example02 ∷ example03 ∷ example04 ∷ example05 ∷
  example06 ∷ example07 ∷ example08 ∷ example09 ∷ example10 ∷
  example11 ∷ example12 ∷ example13 ∷ example14 ∷ example15 ∷
  example16 ∷ example17 ∷ example18 ∷ example18b ∷ example19 ∷
  example20 ∷ example21 ∷ []

example22 : List String
example22 =
  renderNarrowingDerivation (TypeExample.narrowing E22.dynamic-first) ++
  renderNarrowingDerivation (TypeExample.narrowing E22.dynamic-second)

labeled-programs : List String
labeled-programs =
  renderTypedTerm (CheckedProgram.typing LP.program-a) ∷
  renderTypedTerm (CheckedProgram.typing LP.program-b) ∷
  renderTypedTerm (CheckedProgram.typing LP.program-c) ∷
  renderTypedTerm (CheckedProgram.typing LP.program-d) ∷ []

labeled-relations : List String
labeled-relations =
  renderClosedExample LR.example-e ++
  renderClosedExample LR.example-f ++
  renderClosedExample LR.example-g-corrected
