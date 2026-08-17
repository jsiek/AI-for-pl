module proof.DGG.Catchup.FuelKnotProof where

-- File Charter:
--   * Ties the M6 extra-cast and provenance-carrying value-catch-up workers
--     by well-founded recursion on fuel.
--   * Leaves the unfinished M5 dependency explicit as a factory from each
--     recursive smaller-fuel surface to the current instantiation worker.
--   * Exposes the unindexed provenance-carrying value catch-up theorem at
--     one more than the input column's structural size.

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (n<1+n)
open import Induction.WellFounded using (Acc; acc)
import Data.Nat.Induction as NatInduction

open import proof.DGG.Catchup.ValueCatchupRightDef using
  (columnSize; ExtraCastRightAt; InstCatchupRightAt;
   ValueCatchupRightProv²;
   FuelKnot; FuelStepSurface)
open import proof.DGG.Catchup.ExtraCastRightAtProof using
  (extra-cast-right-at)
open import proof.DGG.Catchup.ValueCatchupRightProof using
  (value-catchup-right-prov-at)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)


build-fuel-knot-acc :
    RightInjInversion²
  → (inst-factory : ∀ fuel
      → FuelStepSurface fuel
      → InstCatchupRightAt fuel)
  → (fuel : ℕ)
  → Acc _<_ fuel
  → FuelKnot fuel
build-fuel-knot-acc right-inj-inversion² inst-factory fuel
    (acc smaller) =
  record
    { extra-cast-at = current-extra
    ; inst-catchup-at = current-inst
    ; value-catchup-at =
        value-catchup-right-prov-at current-extra fuel-step
    }
  where
  fuel-step : FuelStepSurface fuel
  fuel-step = record
    { smaller-extra = λ {m} m<fuel →
        FuelKnot.extra-cast-at
          (build-fuel-knot-acc right-inj-inversion² inst-factory m
            (smaller m<fuel))
    ; smaller-inst = λ {m} m<fuel →
        FuelKnot.inst-catchup-at
          (build-fuel-knot-acc right-inj-inversion² inst-factory m
            (smaller m<fuel))
    ; smaller-value = λ {m} m<fuel →
        FuelKnot.value-catchup-at
          (build-fuel-knot-acc right-inj-inversion² inst-factory m
            (smaller m<fuel))
    }

  current-inst : InstCatchupRightAt fuel
  current-inst = inst-factory fuel fuel-step

  current-extra : ExtraCastRightAt fuel
  current-extra =
    extra-cast-right-at right-inj-inversion² fuel-step current-inst


build-fuel-knot :
    RightInjInversion²
  → (inst-factory : ∀ fuel
      → FuelStepSurface fuel
      → InstCatchupRightAt fuel)
  → (fuel : ℕ)
  → FuelKnot fuel
build-fuel-knot right-inj-inversion² inst-factory fuel =
  build-fuel-knot-acc right-inj-inversion² inst-factory fuel
    (NatInduction.<-wellFounded fuel)


value-catchup-right-prov² :
    RightInjInversion²
  → (inst-factory : ∀ fuel
      → FuelStepSurface fuel
      → InstCatchupRightAt fuel)
  → ValueCatchupRightProv²
value-catchup-right-prov² right-inj-inversion² inst-factory rel vM
    vM′ κ q provenance =
  FuelKnot.value-catchup-at
    (build-fuel-knot right-inj-inversion² inst-factory
      (suc (columnSize κ)))
    rel vM vM′ κ (n<1+n (columnSize κ)) q provenance
