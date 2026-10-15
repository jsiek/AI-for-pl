module T6D8a4CompileReachabilityProbe where

-- File Charter:
--   * Audits the D8a3 refuting caller configuration against the LG-2
--     compile-image and reduction-occupancy surfaces.
--   * States the exact world geometry and checks that both the old and fresh
--     target centers are occupied before and after the wrapper rebase.
--   * Shows that occupancy admits the combined argument/body configuration;
--     it does not claim either a source-program witness or unreachability.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (★; ＇_)
open import Consistency using (toRenameᵗ)
open import Imprecision using (X⊑X; X⊑★; ★⊑★)
open import CastTerms using (Value; _·_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.GroundingMint as Mint
import proof.DGG.GroundingPreserve as Preserve
import proof.DGG.Occupancy as Occupancy
open import proof.DGG.Parked.ParkedWorldDef using (ParkedWorld)
import T6D8a2ClosedValueRebaseTransportProbe as P
import T6D8a2CallerSupplyProbe as Caller
import T6D8a3OccurrenceFeasibilityProbe as Occurrence


------------------------------------------------------------------------
-- Exact world and store geometry
------------------------------------------------------------------------

root-source-store : CTI2.sourceStoreʷ P.W ≡ P.source-store
root-source-store = refl

root-target-store : CTI2.targetStoreʷ P.W ≡ P.target-store
root-target-store = refl

premise-source-store : CTI2.sourceStoreʷ P.Wᵖ ≡ P.source-store
premise-source-store = refl

premise-target-store : CTI2.targetStoreʷ P.Wᵖ ≡ P.target-store
premise-target-store = refl

root-source-pivot-center :
  toRenameᵗ (CTI2.ηᴸʷ P.W) P.X ≡ Fin.suc Fin.zero
root-source-pivot-center = refl

root-fresh-target-center :
  toRenameᵗ (CTI2.ηᴿʷ P.W) P.Y-fresh ≡ Fin.zero
root-fresh-target-center = refl

root-old-target-center :
  toRenameᵗ (CTI2.ηᴿʷ P.W) P.Y-old ≡ Fin.suc Fin.zero
root-old-target-center = refl

premise-source-pivot-center :
  toRenameᵗ (CTI2.ηᴸʷ P.Wᵖ) P.X ≡ Fin.zero
premise-source-pivot-center = refl

premise-fresh-target-center :
  toRenameᵗ (CTI2.ηᴿʷ P.Wᵖ) P.Y-fresh ≡ Fin.zero
premise-fresh-target-center = refl

premise-old-target-center :
  toRenameᵗ (CTI2.ηᴿʷ P.Wᵖ) P.Y-old ≡ Fin.suc Fin.zero
premise-old-target-center = refl

root-fresh-mark : CTI2.impEnvʷ P.W Fin.zero ≡ X⊑★
root-fresh-mark = refl

root-old-mark : CTI2.impEnvʷ P.W (Fin.suc Fin.zero) ≡ X⊑X
root-old-mark = refl

premise-fresh-mark : CTI2.impEnvʷ P.Wᵖ Fin.zero ≡ X⊑★
premise-fresh-mark = refl

premise-old-mark : CTI2.impEnvʷ P.Wᵖ (Fin.suc Fin.zero) ≡ X⊑X
premise-old-mark = refl


------------------------------------------------------------------------
-- Exact value/relation shape at the beta caller
------------------------------------------------------------------------

source-argument-is-value : Value Caller.source-argument
source-argument-is-value = Caller.source-argument-value

target-argument-is-value : Value Caller.target-argument
target-argument-is-value = Caller.target-argument-value

argument-is-entangled-at-old-pivot :
  P.W CTI2.∣ [] ⊢²
    Caller.source-argument ⊑ Caller.target-argument ∶ ★⊑★
argument-is-entangled-at-old-pivot = Caller.argument-at-W

body-occurs-under-fresh-pivot-rebase :
  P.W CTI2.∣ Caller.root-source-ctx ⊢²
    Occurrence.source-body ⊑ Occurrence.target-body ∶
      Occurrence.p-root-body
body-occurs-under-fresh-pivot-rebase = Occurrence.body-at-root

caller-configuration :
  P.W CTI2.∣ [] ⊢²
    Occurrence.source-function · Caller.source-argument ⊑
    Occurrence.target-function · Caller.target-argument ∶
      Occurrence.p-root-body
caller-configuration = Occurrence.application-at-root


------------------------------------------------------------------------
-- LG-2 occupancy audit
------------------------------------------------------------------------

root-fresh-center-occupied : CTI2.Occupied P.W Fin.zero
root-fresh-center-occupied =
  Occupancy.rightOnly-new-target-occupiedᴼ {W = P.W-paired} P.ℕ₁

root-old-center-occupied : CTI2.Occupied P.W (Fin.suc Fin.zero)
root-old-center-occupied =
  Occupancy.rightOnly-old-occupiedᴼ {W = P.W-paired} P.ℕ₁
    (Occupancy.bothBind-new-target-occupiedᴼ {W = P.W₀}
      X⊑X P.ℕ₀ P.ℕ₀)

premise-fresh-center-occupied : CTI2.Occupied P.Wᵖ Fin.zero
premise-fresh-center-occupied =
  Occupancy.rebase-occupied-forwardᴼ P.forward-rebase
    root-fresh-center-occupied

premise-old-center-occupied : CTI2.Occupied P.Wᵖ (Fin.suc Fin.zero)
premise-old-center-occupied =
  Occupancy.rebase-occupied-forwardᴼ P.forward-rebase
    root-old-center-occupied

root-every-center-occupied : (Z : Fin.Fin 2) → CTI2.Occupied P.W Z
root-every-center-occupied Fin.zero = root-fresh-center-occupied
root-every-center-occupied (Fin.suc Fin.zero) = root-old-center-occupied
root-every-center-occupied (Fin.suc (Fin.suc ()))

premise-every-center-occupied : (Z : Fin.Fin 2) → CTI2.Occupied P.Wᵖ Z
premise-every-center-occupied Fin.zero = premise-fresh-center-occupied
premise-every-center-occupied (Fin.suc Fin.zero) =
  premise-old-center-occupied
premise-every-center-occupied (Fin.suc (Fin.suc ()))

root-source-pivot-occupied :
  CTI2.Occupied P.W (toRenameᵗ (CTI2.ηᴸʷ P.W) P.X)
root-source-pivot-occupied = P.Y-old , refl

premise-source-pivot-occupied :
  CTI2.Occupied P.Wᵖ (toRenameᵗ (CTI2.ηᴸʷ P.Wᵖ) P.X)
premise-source-pivot-occupied = P.Y-fresh , refl

root-see-through-empty : CTI2.NoTargetOccupantAtSource P.W P.X → ⊥
root-see-through-empty =
  Preserve.occupied-see-through-empty {W = P.W} P.X
    root-source-pivot-occupied

premise-see-through-empty :
  CTI2.NoTargetOccupantAtSource P.Wᵖ P.X → ⊥
premise-see-through-empty =
  Preserve.occupied-see-through-empty {W = P.Wᵖ} P.X
    premise-source-pivot-occupied

occupancy-admits-refuting-configuration :
  (CTI2.Occupied P.W (toRenameᵗ (CTI2.ηᴸʷ P.W) P.X) ×
    (P.W CTI2.∣ [] ⊢² Caller.source-argument ⊑
      Caller.target-argument ∶ ★⊑★)) ×
  (CTI2.Occupied P.Wᵖ (toRenameᵗ (CTI2.ηᴸʷ P.Wᵖ) P.X) ×
    (P.W CTI2.∣ Caller.root-source-ctx ⊢²
      Occurrence.source-body ⊑ Occurrence.target-body ∶
        Occurrence.p-root-body))
occupancy-admits-refuting-configuration =
  (root-source-pivot-occupied , argument-is-entangled-at-old-pivot) ,
  (premise-source-pivot-occupied , body-occurs-under-fresh-pivot-rebase)


------------------------------------------------------------------------
-- Compile-image phase boundary
------------------------------------------------------------------------

root-is-parked : ParkedWorld P.W
root-is-parked = Caller.parked-W

root-is-not-a-compile-recursion-world : Mint.CompileImageWorld P.W → ⊥
root-is-not-a-compile-recursion-world ()

premise-is-not-a-compile-recursion-world :
  Mint.CompileImageWorld P.Wᵖ → ⊥
premise-is-not-a-compile-recursion-world ()

lg2-reduction-knot-is-available : Preserve.RelatedReductionGroundingKnot
lg2-reduction-knot-is-available = Preserve.grounding-preservation-knot
