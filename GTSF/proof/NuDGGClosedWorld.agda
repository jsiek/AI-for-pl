module proof.NuDGGClosedWorld where

-- File Charter:
--   * Supplies the empty Nu store well-formedness witness shared by the closed
--     DGG spine and the three terminal specializations.
--   * Supplies the vacuous world-coherence witness for closed simulations.
--   * Keeps cheap terminal-statement checks independent of the compiler/DGG
--     spine module.

open import Data.List using ([])

open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImpEntry)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent; world-coherent)


empty-store-wf :
  ∀ {Δ} →
  StoreWf Δ []
empty-store-wf =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; unique = λ ()
    }


empty-world-coherent :
  ∀ {Δᴸ Δᴿ} →
  WorldCoherent ([] {A = StoreImpEntry [] Δᴸ Δᴿ})
empty-world-coherent = world-coherent (λ ())
