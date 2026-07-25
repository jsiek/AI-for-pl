module
  proof.Source.Administration.NuImprecisionSourceAdministrationState
  where

-- File Charter:
--   * Defines the constructor-form control state for private source
--     administration after structural value catch-up has finished.
--   * Distinguishes ordinary pending casts, runtime bullet elimination, and
--     source allocation while sharing the side-neutral administration rank.
--   * Leaves precise typing and QTI evidence to the future hereditary source
--     administration spine rather than hiding it in the numeric state.
--   * Gives ordinary source `ν` and source-only `νcast` the same operational
--     allocation state.
--   * Gives narrowing and widening the same pending-cast state.
--   * Does not add a paired-widening state: that boundary enters the pending
--     cast worker once and then adds the inert target frame nonrecursively.
--   * Contains no semantic recursion, postulate, hole, permissive option, or
--     termination bypass.

open import Coercions using (Coercion)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import NuTerms using (Term; Value)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureDef
  using (nuAdministrationRank; pendingAdministrationRank)


data SourceAdministrationState : Set where
  casts : List Coercion → SourceAdministrationState
  bullet : List Coercion → SourceAdministrationState
  ν : Coercion → List Coercion → SourceAdministrationState


sourceAdministrationRank :
  ∀ {V : Term} →
  Value V →
  SourceAdministrationState →
  ℕ
sourceAdministrationRank vV (casts cs) =
  pendingAdministrationRank vV cs
sourceAdministrationRank vV (bullet cs) =
  pendingAdministrationRank vV cs
sourceAdministrationRank vV (ν c cs) =
  nuAdministrationRank vV c cs
