module SourceStarPackageCounterScratch where

-- File Charter:
--   * Records a checked counterexample to the round-14
--     `source-star-cast-package` shape with an arbitrary output target name.
--   * Uses `TerminusRebuildProbe.InstanceB` to instantiate all theorem
--     premises, then proves the requested `TaggedTransferOutput` impossible.
--   * Depends only on the live partner relation and the existing terminus
--     rebuild probe; it is not imported by the main development.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types
open import Consistency using (id; _!)
open import CastTerms using (_⟨_⟩; _↓_)
import CastTerms as CTerms
open import Conversion using (seal)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.SealTransferCore as STC
import proof.DGG.TerminusRebuildProbe as TRP
import proof.DGG.Inversion.SpineValueDef as SVD

open CTI2 using (_∣_⊢²_⊑_∶_)

open TRP.InstanceB

Y≢Y₂ : Y ≢ Y₂
Y≢Y₂ ()

target-tag : CTerms.Term 2
target-tag =
  ((U₀ ↓ seal Y₂ ★) ↓ seal Y (＇ Y₂))
    ⟨ id {μ = target-env} (＇ Y) ! ⟩

source-tag : CTerms.Term 1
source-tag =
  (V₀ ↓ seal X ★) ⟨ id {μ = source-env} (＇ X) ! ⟩

source-output-tag : CTerms.Term 1
source-output-tag =
  (source-tag ↓ seal X ★) ⟨ id {μ = source-env} (＇ X) ! ⟩

source-spine : SVD.SpineValue source
source-spine =
  SVD.sv-seal
    (SVD.sv-cast
      (SVD.sv-seal
        (SVD.sv-cast (SVD.sv-ƛ (CTerms.` 0)) CTerms.inj))
      CTerms.inj)

source-inert : CTerms.Inert (id {μ = source-env} (＇ X) !)
source-inert = CTerms.inj

target-tag-value : CTerms.Value target-tag
target-tag-value =
  ((TRP.dyn-id-value CTerms.↓ CTerms.seal) CTerms.↓ CTerms.seal)
    CTerms.《 CTerms.inj 》

no-base-partner :
  CTI2.Rep★PartnerOK W X V₀ (just Y₂) target-tag
  → ⊥
no-base-partner (CTI2.rep★-untagged ())
no-base-partner (CTI2.rep★-nonvar-tag ())

no-inner-partner :
  CTI2.Rep★PartnerOK W X source-tag (just Y₂) target-tag
  → ⊥
no-inner-partner (CTI2.rep★-untagged ())
no-inner-partner (CTI2.rep★-nonvar-tag ())
no-inner-partner (CTI2.rep★-matched-inner-tags X≢X aligned) =
  X≢X refl
no-inner-partner (CTI2.rep★-round-trip ok) =
  no-base-partner ok

no-output-partner :
  CTI2.Rep★PartnerOK W X source-output-tag (just Y₂) target-tag
  → ⊥
no-output-partner (CTI2.rep★-untagged ())
no-output-partner (CTI2.rep★-nonvar-tag ())
no-output-partner (CTI2.rep★-matched-inner-tags X≢X aligned) =
  X≢X refl
no-output-partner (CTI2.rep★-round-trip ok) =
  no-inner-partner ok

counter-premise :
  W ∣ [] ⊢² source ⊑ target-tag ∶ X⊑★-W
counter-premise = tagged-input

no-output-package :
  STC.TaggedTransferOutput W [] source-output-tag target-tag X Y₂
  → ⊥
no-output-package pkg
    with STC.TaggedTransferOutput.partner pkg
no-output-package pkg
    | CTI2.matched-seal-star-partner ok =
  no-output-partner ok
