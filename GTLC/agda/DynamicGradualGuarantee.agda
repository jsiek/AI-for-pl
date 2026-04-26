module DynamicGradualGuarantee where

-- File Charter:
--   * Public wrapper for the dynamic gradual guarantee theorem.
--   * Proof details are implemented in `proof/DynamicGradualGuarantee.agda`.

open import proof.DynamicGradualGuarantee public
  using (_⇓_; Diverges; Blames; DivergeOrBlameᶜ; DivergeOrBlame;
         dynamic-gradual-guarantee)
