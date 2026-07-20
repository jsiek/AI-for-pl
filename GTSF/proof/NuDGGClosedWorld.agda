module proof.NuDGGClosedWorld where

-- File Charter:
--   * Supplies the empty Nu store well-formedness witness shared by the closed
--     DGG spine and the three terminal specializations.
--   * Keeps cheap terminal-statement checks independent of the compiler/DGG
--     spine module.

open import Data.List using ([])

open import NuStore using (StoreWf)


empty-store-wf :
  ∀ {Δ} →
  StoreWf Δ []
empty-store-wf =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; unique = λ ()
    }
