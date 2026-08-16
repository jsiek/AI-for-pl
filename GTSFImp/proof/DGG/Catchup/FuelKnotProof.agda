module proof.DGG.Catchup.FuelKnotProof where

-- File Charter:
--   * Restores the M6 well-founded fuel knot over the LG-3 columnless
--     surfaces.
--   * Keeps the incomplete workers explicit as factories: extra-cast,
--     value-catch-up, and the M5 instantiation factory.
--   * Once the blocked wrapper-aware inversion supplies the first two
--     factories, this module's public builder discharges the mutual fuel
--     plumbing without changing the knot surface.

open import Data.Nat using (ℕ; _<_)
open import Induction.WellFounded using (Acc; acc)
import Data.Nat.Induction as NatInduction

open import proof.DGG.Catchup.ValueCatchupRightDef using
  (ExtraCastRightAt; InstCatchupRightAt; ValueCatchupRightAt;
   FuelKnot; FuelStepSurface)


ExtraCastFactory : Set₁
ExtraCastFactory =
  ∀ fuel
  → FuelStepSurface fuel
  → InstCatchupRightAt fuel
  → ExtraCastRightAt fuel


ValueCatchupFactory : Set₁
ValueCatchupFactory =
  ∀ fuel
  → ExtraCastRightAt fuel
  → FuelStepSurface fuel
  → ValueCatchupRightAt fuel


InstCatchupFactory : Set₁
InstCatchupFactory =
  ∀ fuel
  → FuelStepSurface fuel
  → InstCatchupRightAt fuel


build-fuel-knot-acc :
  ExtraCastFactory
  → ValueCatchupFactory
  → InstCatchupFactory
  → (fuel : ℕ)
  → Acc _<_ fuel
  → FuelKnot fuel
build-fuel-knot-acc extra-factory value-factory inst-factory
    fuel (acc smaller) =
  record
    { extra-cast-at = current-extra
    ; inst-catchup-at = current-inst
    ; value-catchup-at = current-value
    }
  where
  fuel-step : FuelStepSurface fuel
  fuel-step = record
    { smaller-extra = λ {m} m<fuel →
        FuelKnot.extra-cast-at
          (build-fuel-knot-acc extra-factory value-factory inst-factory
            m (smaller m<fuel))
    ; smaller-inst = λ {m} m<fuel →
        FuelKnot.inst-catchup-at
          (build-fuel-knot-acc extra-factory value-factory inst-factory
            m (smaller m<fuel))
    ; smaller-value = λ {m} m<fuel →
        FuelKnot.value-catchup-at
          (build-fuel-knot-acc extra-factory value-factory inst-factory
            m (smaller m<fuel))
    }

  current-inst : InstCatchupRightAt fuel
  current-inst = inst-factory fuel fuel-step

  current-extra : ExtraCastRightAt fuel
  current-extra = extra-factory fuel fuel-step current-inst

  current-value : ValueCatchupRightAt fuel
  current-value = value-factory fuel current-extra fuel-step


build-fuel-knot :
  ExtraCastFactory
  → ValueCatchupFactory
  → InstCatchupFactory
  → (fuel : ℕ)
  → FuelKnot fuel
build-fuel-knot extra-factory value-factory inst-factory fuel =
  build-fuel-knot-acc extra-factory value-factory inst-factory fuel
    (NatInduction.<-wellFounded fuel)
