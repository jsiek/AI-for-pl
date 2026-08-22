module LR-narrow.Examples.Cambridge26.K.Renderings where

-- File Charter:
--   * Applies the general pretty printer to every checked K example.
--   * Stores each Cambridge-oriented endpoint pair followed by its canonical
--     narrowing coercion.

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)

import LR-narrow.Examples.Cambridge26.K.Example01 as E01
import LR-narrow.Examples.Cambridge26.K.Example02 as E02
import LR-narrow.Examples.Cambridge26.K.Example03 as E03
import LR-narrow.Examples.Cambridge26.K.Example04 as E04
import LR-narrow.Examples.Cambridge26.K.Example05 as E05
import LR-narrow.Examples.Cambridge26.K.Example06 as E06
import LR-narrow.Examples.Cambridge26.K.Example07 as E07
import LR-narrow.Examples.Cambridge26.K.Example08 as E08
import LR-narrow.Examples.Cambridge26.K.Example09 as E09
import LR-narrow.Examples.Cambridge26.K.Example10 as E10
import LR-narrow.Examples.Cambridge26.K.Example11 as E11
import LR-narrow.Examples.Cambridge26.K.Example12 as E12
import LR-narrow.Examples.Cambridge26.K.Example13 as E13
import LR-narrow.Examples.Cambridge26.K.Example14 as E14
import LR-narrow.Examples.Cambridge26.K.Example15 as E15
import LR-narrow.Examples.Cambridge26.K.Example16 as E16
import LR-narrow.Examples.Cambridge26.K.Example17 as E17
import LR-narrow.Examples.Cambridge26.K.Example18 as E18
import LR-narrow.Examples.Cambridge26.K.Example19 as E19
import LR-narrow.Examples.Cambridge26.K.Example20 as E20

open import LR-narrow.Examples.Cambridge26.Renderings using
  (renderClosedExample)

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
example19 : List String
example19 = renderClosedExample E19.example
example20 : List String
example20 = renderClosedExample E20.example

all-examples : List (List String)
all-examples =
  example01 ∷ example02 ∷ example03 ∷ example04 ∷ example05 ∷
  example06 ∷ example07 ∷ example08 ∷ example09 ∷ example10 ∷
  example11 ∷ example12 ∷ example13 ∷ example14 ∷ example15 ∷
  example16 ∷ example17 ∷ example18 ∷ example19 ∷ example20 ∷ []
