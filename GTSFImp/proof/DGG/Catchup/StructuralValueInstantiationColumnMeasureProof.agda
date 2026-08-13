module
  proof.DGG.Catchup.StructuralValueInstantiationColumnMeasureProof where

-- File Charter:
--   * Proves structural-instantiation rank facts for typed cast columns.
--   * Shows that store transport preserves column weight and length.
--   * Establishes strict descent across a target `Λ` allocation.

open import Data.Nat using (suc)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
import CastTerms as CT
open import Reduction using (StoreChange; bind; _∷_; [])
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (CastColumn; []ᶜ; _▻ᶜ_; mapColumn; mapColumn₁)
open import proof.DGG.Catchup.ColumnSupportProof using
  (castSize-applyConsistency)
open import
  proof.DGG.Catchup.StructuralValueInstantiationMeasureDef

open +-*-Solver using (solve; _:+_; _:*_; con)
  renaming (_:=_ to _:=ᵉ_)


column-administration-weight-map₁ : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (κ : CastColumn A B)
  → columnAdministrationWeight (mapColumn₁ χ κ) ≡
      columnAdministrationWeight κ
column-administration-weight-map₁ χ []ᶜ = refl
column-administration-weight-map₁ χ (c ▻ᶜ κ)
    rewrite castSize-applyConsistency χ c
          | column-administration-weight-map₁ χ κ = refl


column-length-map₁ : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (κ : CastColumn A B)
  → columnLength (mapColumn₁ χ κ) ≡ columnLength κ
column-length-map₁ χ []ᶜ = refl
column-length-map₁ χ (c ▻ᶜ κ)
    rewrite column-length-map₁ χ κ = refl


lambda-instantiation-rank-decreases : ∀ {Δ A B}
    {V : CT.Term (suc Δ)} (vV : CT.Value V)
    (R : Ty Δ) (κ : CastColumn A B)
  → pendingAdministrationRank (CT.Λ vV) κ ≡
      suc (suc (pendingAdministrationRank vV
        (mapColumn (bind R ∷ []) κ)))
lambda-instantiation-rank-decreases vV R κ
    rewrite column-administration-weight-map₁ (bind R) κ
          | column-length-map₁ (bind R) κ =
  solve 3
    (λ w p l →
      (con 2 :* ((con 1 :+ w) :+ p)) :+ l :=ᵉ
      con 2 :+ ((con 2 :* (w :+ p)) :+ l))
    refl
    (valueAdministrationWeight vV)
    (columnAdministrationWeight κ)
    (columnLength κ)
