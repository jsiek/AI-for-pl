module LR-narrow.Atoms where

-- File Charter:
--   * Defines semantic atoms over distinct precise and imprecise contexts.
--   * Requires downward closure, endpoint typing, and alignment at a center
--     variable.
--   * Reindexes an existing atom through a paired fresh store binding.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

open import Types
open import TyStore
open import CastTerms
open import Consistency using (toRenameᵗ; wk↪ᵗ)
open import proof.TypeInTermSubst
  using (renameᵗᵐ-preserves-Value; typing-shiftᵗ-bind)
open import LR-narrow.WorldCore

StepIndexedRelation : TyCtx → TyCtx → Set₁
StepIndexedRelation Δᴾ Δᴵ = ℕ → Term Δᴵ → Term Δᴾ → Set

DownwardClosed : ∀ {Δᴾ Δᴵ} → StepIndexedRelation Δᴾ Δᴵ → Set
DownwardClosed R = ∀ {k Vᴵ Vᴾ}
  → R (suc k) Vᴵ Vᴾ
  → R k Vᴵ Vᴾ

record SemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) : Set₁ where
  constructor semantic-atom
  field
    preciseVariable : TyVar Δᴾ
    impreciseVariable : TyVar Δᴵ
    preciseAligned :
      toRenameᵗ (preciseEmbedding W) preciseVariable ≡ Z
    impreciseAligned :
      toRenameᵗ (impreciseEmbedding W) impreciseVariable ≡ Z
    relation : StepIndexedRelation Δᴾ Δᴵ
    relation-downward : DownwardClosed relation
    relation-valid : ∀ {k Vᴵ Vᴾ}
      → relation k Vᴵ Vᴾ
      → (Value Vᴵ ×
          ⟨ Δᴵ , impreciseStore W , [] ⟩
            ⊢ Vᴵ ⦂ ＇ impreciseVariable)
        × (Value Vᴾ ×
          ⟨ Δᴾ , preciseStore W , [] ⟩ ⊢ Vᴾ ⦂ ＇ preciseVariable)

open SemanticAtom public

record AtomHolds {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z} (a : SemanticAtom W Z) (k : ℕ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor atom-holds
  field
    relation-holds : relation a k Vᴵ Vᴾ

open AtomHolds public

data LiftedRelation {Δᴾ Δᴵ} (R : StepIndexedRelation Δᴾ Δᴵ) :
    StepIndexedRelation (suc Δᴾ) (suc Δᴵ) where
  lift-related : ∀ {k Vᴵ Vᴾ}
    → R k Vᴵ Vᴾ
    → LiftedRelation R k (⇑ᵗᵐ Vᴵ) (⇑ᵗᵐ Vᴾ)

lifted-downward : ∀ {Δᴾ Δᴵ} {R : StepIndexedRelation Δᴾ Δᴵ}
  → DownwardClosed R
  → DownwardClosed (LiftedRelation R)
lifted-downward down (lift-related related) =
  lift-related (down related)

weaken-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → SemanticAtom W Z
  → SemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z)
weaken-semantic-atom Aᴾ Aᴵ a =
  semantic-atom (Fin.suc (preciseVariable a))
    (Fin.suc (impreciseVariable a))
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (LiftedRelation (relation a))
    (lifted-downward (relation-downward a)) valid
  where
  valid : ∀ {k Vᴵ Vᴾ}
    → LiftedRelation (relation a) k Vᴵ Vᴾ
    → (Value Vᴵ ×
        ⟨ _ , store-bind _ Aᴵ , [] ⟩ ⊢ Vᴵ ⦂ ＇ _)
      × (Value Vᴾ ×
        ⟨ _ , store-bind _ Aᴾ , [] ⟩ ⊢ Vᴾ ⦂ ＇ _)
  valid (lift-related related) =
    let (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) = relation-valid a related
    in (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴵ ,
        typing-shiftᵗ-bind Vᴵ⊢) ,
       (renameᵗᵐ-preserves-Value wk↪ᵗ vVᴾ ,
        typing-shiftᵗ-bind Vᴾ⊢)

fresh-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
    (R : StepIndexedRelation (suc Δᴾ) (suc Δᴵ))
  → DownwardClosed R
  → (∀ {k Vᴵ Vᴾ}
      → R k Vᴵ Vᴾ
      → (Value Vᴵ ×
          ⟨ suc Δᴵ , store-bind (impreciseStore W) Aᴵ , [] ⟩
            ⊢ Vᴵ ⦂ ＇ Fin.zero)
        × (Value Vᴾ ×
          ⟨ suc Δᴾ , store-bind (preciseStore W) Aᴾ , [] ⟩
            ⊢ Vᴾ ⦂ ＇ Fin.zero))
  → SemanticAtom (pairedBindCore W Aᴾ Aᴵ) Fin.zero
fresh-semantic-atom Aᴾ Aᴵ R down valid =
  semantic-atom Fin.zero Fin.zero refl refl R down valid
