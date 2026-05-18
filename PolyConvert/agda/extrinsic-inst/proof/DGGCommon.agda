module proof.DGGCommon where

-- File Charter:
--   * Shared observations and relation abbreviations for the PolyConvert DGG
--     proof skeleton.
--   * Keeps proof modules independent from `GradualGuarantee` to avoid import
--     cycles.
--   * No simulation proof obligations live here.

open import Data.List using ([]; length)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Store
open import Terms
open import TermImprecision
open import Reduction

record SimWorld : Set where
  constructor mkWorld
  field
    Ψˡ Ψʳ : SealCtx
    Σˡ Σʳ : Store
    wfΣˡ : StoreWf 0 Ψˡ Σˡ
    wfΣʳ : StoreWf 0 Ψʳ Σʳ
    len-sync : length Σˡ ≡ length Σʳ

open SimWorld public

WorldRel : SimWorld → Term → Term → Ty → Ty → Set
WorldRel W M M′ A B =
  ⟪ 0 , Ψˡ W , Σˡ W , Ψʳ W , Σʳ W , [] ⟫
    ⊢ M ⊑ M′ ⦂ A ⊑ B
