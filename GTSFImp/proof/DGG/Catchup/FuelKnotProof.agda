module proof.DGG.Catchup.FuelKnotProof where

-- File Charter:
--   * Restores the M6 well-founded fuel knot over the LG-3 columnless
--     surfaces.
--   * Keeps the incomplete workers explicit as factories: extra-cast,
--     value-catch-up, and the M5 instantiation factory.
--   * Also provides the LG-3 structural factory adapter: internal factories
--     can carry `StructuralWorldExtendᴿ`, while the exported knot still
--     exposes only the public erased surfaces.

open import Data.Nat using (ℕ; _<_)
open import Induction.WellFounded using (Acc; acc)
import Data.Nat.Induction as NatInduction

open import proof.DGG.Catchup.ValueCatchupRightDef using
  (ExtraCastRightAt; InstCatchupRightAt; ValueCatchupRightAt;
   FuelKnot; FuelStepSurface)
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (StructuralExtraCastRightAt; StructuralInstCatchupRightAt;
   StructuralValueCatchupRightAt;
   erase-structural-extra-cast-right-at;
   erase-structural-inst-catchup-right-at;
   erase-structural-value-catchup-right-at)


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

record StructuralFuelStepSurface (fuel : ℕ) : Set₁ where
  field
    smaller-structural-extra :
      ∀ {m} → m < fuel → StructuralExtraCastRightAt m
    smaller-inst :
      ∀ {m} → m < fuel → StructuralInstCatchupRightAt m
    smaller-structural-value :
      ∀ {m} → m < fuel → StructuralValueCatchupRightAt m


erase-structural-fuel-step : ∀ {fuel}
  → StructuralFuelStepSurface fuel
  → FuelStepSurface fuel
erase-structural-fuel-step structural-step = record
  { smaller-extra = λ m<fuel →
      erase-structural-extra-cast-right-at
        (StructuralFuelStepSurface.smaller-structural-extra
          structural-step m<fuel)
  ; smaller-inst = λ m<fuel →
      erase-structural-inst-catchup-right-at
        (StructuralFuelStepSurface.smaller-inst structural-step m<fuel)
  ; smaller-value = λ m<fuel →
      erase-structural-value-catchup-right-at
        (StructuralFuelStepSurface.smaller-structural-value
          structural-step m<fuel)
  }


record StructuralFuelKnot (fuel : ℕ) : Set₁ where
  field
    structural-extra-cast-at : StructuralExtraCastRightAt fuel
    structural-inst-catchup-at : StructuralInstCatchupRightAt fuel
    structural-value-catchup-at : StructuralValueCatchupRightAt fuel


erase-structural-fuel-knot : ∀ {fuel}
  → StructuralFuelKnot fuel
  → FuelKnot fuel
erase-structural-fuel-knot structural-knot = record
  { extra-cast-at =
      erase-structural-extra-cast-right-at
        (StructuralFuelKnot.structural-extra-cast-at structural-knot)
  ; inst-catchup-at =
      erase-structural-inst-catchup-right-at
        (StructuralFuelKnot.structural-inst-catchup-at structural-knot)
  ; value-catchup-at =
      erase-structural-value-catchup-right-at
        (StructuralFuelKnot.structural-value-catchup-at structural-knot)
  }


StructuralExtraCastFactory : Set₁
StructuralExtraCastFactory =
  ∀ fuel
  → StructuralFuelStepSurface fuel
  → StructuralInstCatchupRightAt fuel
  → StructuralExtraCastRightAt fuel


StructuralValueCatchupFactory : Set₁
StructuralValueCatchupFactory =
  ∀ fuel
  → StructuralExtraCastRightAt fuel
  → StructuralFuelStepSurface fuel
  → StructuralValueCatchupRightAt fuel


StructuralInstCatchupFactory : Set₁
StructuralInstCatchupFactory =
  ∀ fuel
  → StructuralFuelStepSurface fuel
  → StructuralInstCatchupRightAt fuel


build-structural-fuel-knot-acc :
  StructuralExtraCastFactory
  → StructuralValueCatchupFactory
  → StructuralInstCatchupFactory
  → (fuel : ℕ)
  → Acc _<_ fuel
  → StructuralFuelKnot fuel
build-structural-fuel-knot-acc extra-factory value-factory inst-factory
    fuel (acc smaller) =
  record
    { structural-extra-cast-at = current-structural-extra
    ; structural-inst-catchup-at = current-structural-inst
    ; structural-value-catchup-at = current-structural-value
    }
  where
  structural-fuel-step : StructuralFuelStepSurface fuel
  structural-fuel-step = record
    { smaller-structural-extra = λ {m} m<fuel →
        StructuralFuelKnot.structural-extra-cast-at
          (build-structural-fuel-knot-acc extra-factory value-factory
            inst-factory m (smaller m<fuel))
    ; smaller-inst = λ {m} m<fuel →
        StructuralFuelKnot.structural-inst-catchup-at
          (build-structural-fuel-knot-acc extra-factory value-factory
            inst-factory m (smaller m<fuel))
    ; smaller-structural-value = λ {m} m<fuel →
        StructuralFuelKnot.structural-value-catchup-at
          (build-structural-fuel-knot-acc extra-factory value-factory
            inst-factory m (smaller m<fuel))
    }

  current-structural-inst : StructuralInstCatchupRightAt fuel
  current-structural-inst = inst-factory fuel structural-fuel-step

  current-structural-extra : StructuralExtraCastRightAt fuel
  current-structural-extra =
    extra-factory fuel structural-fuel-step current-structural-inst

  current-structural-value : StructuralValueCatchupRightAt fuel
  current-structural-value =
    value-factory fuel current-structural-extra structural-fuel-step


build-structural-fuel-knot :
  StructuralExtraCastFactory
  → StructuralValueCatchupFactory
  → StructuralInstCatchupFactory
  → (fuel : ℕ)
  → FuelKnot fuel
build-structural-fuel-knot extra-factory value-factory inst-factory fuel =
  erase-structural-fuel-knot
    (build-structural-fuel-knot-acc extra-factory value-factory inst-factory
      fuel (NatInduction.<-wellFounded fuel))
