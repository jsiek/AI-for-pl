module CoercionGradualGuarantee where

open import Types
open import Contexts
open import Coercions

{-

  lemma simᶜ:
    if c ⊑ᶜ d
    and d —→ᶜᶜ d′
    then c —↠ᶜᶜ c′ and c′ ⊑ᶜ d′

-}

