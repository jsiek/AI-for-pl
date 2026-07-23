module
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedWideningCatchupCounterexample
  where

-- File Charter:
--   * Records why the former paired-widening counterexample is excluded by
--     the strengthened relation.
--   * Refutes compatibility for the active-source-unseal versus
--     inert-target-variable-tag pair at the exact problematic endpoints.
--   * Contains no terminal catch-up theorem or proof implementation.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)

import Coercions as C
open import Coercions using (Inert; _!)
open import Imprecision using (_ˣ⊑ˣ_)
open import PairedWideningCompatibility using
  ( PairedWideningCompatible
  ; compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import Types using (★; ＇_)


private
  target-inert : Inert ((＇ zero) !)
  target-inert = (＇ zero) !


active-unseal-inert-tag-incompatible :
  PairedWideningCompatible
    ((zero ˣ⊑ˣ zero) ∷ [])
    (suc zero) (suc zero)
    (C.unseal zero ★) ((＇ zero) !)
    ★ (＇ zero) →
  ⊥
active-unseal-inert-tag-incompatible
    (compatible-source-inert ())
active-unseal-inert-tag-incompatible
    (compatible-target-inert-bridge bridge)
    with bridge target-inert
active-unseal-inert-tag-incompatible
    (compatible-target-inert-bridge bridge) | ()
