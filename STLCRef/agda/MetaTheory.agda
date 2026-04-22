module MetaTheory where

-- File Charter:
--   * Public metatheory statements/wrappers for STLCRef.
--   * Exposes progress, preservation, and type-safety for references.

open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Agda.Builtin.List using ([])

open import STLCRef
open import proof.TypeSafety using (StoreWellTyped; StoreExt; store-wt-empty)
import proof.TypeSafety as TypeSafetyProof

progress :
  {M : Term} {A : Ty} {Σ : StoreTy} {μ : Store} ->
  [] ∣ Σ ⊢ M ⦂ A ->
  StoreWellTyped Σ μ ->
  (∃[ c' ] ((M , μ) —→ c')) ⊎ Value M
progress = TypeSafetyProof.progress

preservation :
  {M M' : Term} {A : Ty} {Σ : StoreTy} {μ μ' : Store} ->
  [] ∣ Σ ⊢ M ⦂ A ->
  StoreWellTyped Σ μ ->
  (M , μ) —→ (M' , μ') ->
  ∃[ Σ' ]
    StoreExt Σ Σ' ×
    ([] ∣ Σ' ⊢ M' ⦂ A) ×
    StoreWellTyped Σ' μ'
preservation = TypeSafetyProof.preservation

type-safety :
  {M N : Term} {A : Ty} {μ : Store} ->
  [] ∣ [] ⊢ M ⦂ A ->
  (M , []) —↠ (N , μ) ->
  (∃[ c' ] ((N , μ) —→ c')) ⊎ Value N
type-safety = TypeSafetyProof.typeSafety

initial-store-wt : StoreWellTyped [] []
initial-store-wt = store-wt-empty
