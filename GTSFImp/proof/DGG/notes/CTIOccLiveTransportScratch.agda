module CTIOccLiveTransportScratch where

-- File Charter:
--   * Notes-only S-OCC pre-flight V2/V3 scratch.
--   * Defines the live occupancy predicate over CTI2 worlds and checks
--     representative transport facts for initial worlds, source-only lifts,
--     right-only target allocation, and rebasing.
--   * Records checked statement shapes for the strengthened partner premise
--     and for the β-inst/β-gen allocation worlds.  No live CTI2 or proof file
--     is edited.

open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import TyStore using (TyStore)
open import Consistency using (_↪ᵗ_; id↪ᵗ; toRenameᵗ)
open import Imprecision using (ImpEnv; VarImp; X⊑★)
open import CastTerms using (Term)
open import Conversion using (Conv↓; seal)

import proof.DGG.CastTermImprecision2 as CTI2
open import proof.TypeInTermSubst using (toRename-id-eq)

open CTI2 using
  (World; world; ηᴿʷ; ηᴸʷ; sourceStoreʷ; targetStoreʷ;
   liftWorldLeft; rightOnlyWorld; RebaseAt; TagRebaseAtᴸ;
   Rep★PartnerOK; SealPartnerOK; SourceConcealPartnerOK)

------------------------------------------------------------------------
-- Live occupancy predicate
------------------------------------------------------------------------

Occupied : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Fin.Fin Δ
  → Set
Occupied {Δᴿ = Δᴿ} W Z =
  Σ[ Y ∈ Fin.Fin Δᴿ ] toRenameᵗ (ηᴿʷ W) Y ≡ Z

NoTargetOccupant : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Fin.Fin Δ
  → Set
NoTargetOccupant W Z = Occupied W Z → ⊥

NoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Fin.Fin Δᴸ
  → Set
NoTargetOccupantAtSource W X =
  NoTargetOccupant W (toRenameᵗ (ηᴸʷ W) X)

------------------------------------------------------------------------
-- Strengthened live clause shape
------------------------------------------------------------------------

record StarRepTargetPremiseᴼ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : Fin.Fin Δᴸ)
    (P : Term Δᴸ) (Xᴿ? : Maybe (Fin.Fin Δᴿ)) (M′ : Term Δᴿ)
    : Set where
  constructor star-rep-target-premiseᴼ
  field
    no-target : NoTargetOccupantAtSource W X
    rep★ : Rep★PartnerOK W X P Xᴿ? M′

record StrengthenedSealPartnerShapeᴼ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : Fin.Fin Δᴸ)
    (P : Term Δᴸ) (Xᴿ? : Maybe (Fin.Fin Δᴿ)) (M′ : Term Δᴿ)
    : Set where
  constructor strengthened-seal-partner-shapeᴼ
  field
    strengthened-star-rep-target :
      StarRepTargetPremiseᴼ W X P Xᴿ? M′
      → SealPartnerOK W X P ★ Xᴿ? M′

record StrengthenedSourceConcealShapeᴼ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : Fin.Fin Δᴸ)
    (P : Term Δᴸ) (Xᴿ? : Maybe (Fin.Fin Δᴿ)) (M′ : Term Δᴿ)
    : Set where
  constructor strengthened-source-conceal-shapeᴼ
  field
    strengthened-source-seal :
      StarRepTargetPremiseᴼ W X P Xᴿ? M′
      → SourceConcealPartnerOK W P (seal X ★) Xᴿ? M′

------------------------------------------------------------------------
-- Representative occupancy transport checks
------------------------------------------------------------------------

initialWorldᴼ : ∀ {Δ}
  → ImpEnv Δ
  → TyStore Δ
  → World Δ Δ Δ
initialWorldᴼ μ Σ = world id↪ᵗ id↪ᵗ μ Σ Σ

initial-every-center-occupiedᴼ : ∀ {Δ}
    {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (Z : Fin.Fin Δ)
  → Occupied (initialWorldᴼ μ Σ) Z
initial-every-center-occupiedᴼ Z = Z , toRename-id-eq Z

initial-no-see-through-emptyᴼ : ∀ {Δ}
    {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (Z : Fin.Fin Δ)
  → NoTargetOccupant (initialWorldᴼ μ Σ) Z
  → ⊥
initial-no-see-through-emptyᴼ {μ = μ} {Σ = Σ} Z no-target =
  no-target (initial-every-center-occupiedᴼ {μ = μ} {Σ = Σ} Z)

liftWorldLeft-fresh-no-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    (v : VarImp)
  → NoTargetOccupant (liftWorldLeft v W) Fin.zero
liftWorldLeft-fresh-no-targetᴼ v (Y , ())

rightOnly-new-target-occupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    (B : Ty Δᴿ)
  → Occupied (rightOnlyWorld W B) Fin.zero
rightOnly-new-target-occupiedᴼ B = Fin.zero , refl

rebase-occupied-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ Z}
  → RebaseAt W W′ Xᴸ Xᴿ
  → Occupied W Z
  → Occupied W′ Z
rebase-occupied-forwardᴼ rb (Y , eq) =
  Y , trans (CTI2.RebaseAt.ηᴿ-frozen rb Y) eq

rebase-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ Z}
  → RebaseAt W W′ Xᴸ Xᴿ
  → NoTargetOccupant W Z
  → NoTargetOccupant W′ Z
rebase-no-target-forwardᴼ rb no-target (Y , eq′) =
  no-target (Y , trans (sym (CTI2.RebaseAt.ηᴿ-frozen rb Y)) eq′)

tag-rebase-no-target-forwardᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ? Z}
  → TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
  → NoTargetOccupant W Z
  → NoTargetOccupant W′ Z
tag-rebase-no-target-forwardᴼ CTI2.tag-rebase-idᴸ no-target =
  no-target
tag-rebase-no-target-forwardᴼ (CTI2.tag-rebase-varᴸ rb) no-target =
  rebase-no-target-forwardᴼ rb no-target
tag-rebase-no-target-forwardᴼ
    (CTI2.tag-rebase-onlyᴸ _ _ _) no-target =
  no-target

------------------------------------------------------------------------
-- V3 allocation/atomicity representatives
------------------------------------------------------------------------

β-inst-allocation-occupies-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → Occupied (rightOnlyWorld W ★) Fin.zero
β-inst-allocation-occupies-targetᴼ {W = W} =
  rightOnly-new-target-occupiedᴼ {W = W} ★

β-gen-allocation-occupies-targetᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    (C : Ty Δᴿ)
  → Occupied (rightOnlyWorld W C) Fin.zero
β-gen-allocation-occupies-targetᴼ {W = W} C =
  rightOnly-new-target-occupiedᴼ {W = W} C

source-only-runtime-cell-remains-unoccupiedᴼ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → NoTargetOccupantAtSource (liftWorldLeft X⊑★ W) Fin.zero
source-only-runtime-cell-remains-unoccupiedᴼ {W = W} =
  liftWorldLeft-fresh-no-targetᴼ {W = W} X⊑★
