module proof.DGGCommon where

-- File Charter:
--   * Shared observations and relation abbreviations for the PolyConvert DGG
--     proof skeleton.
--   * Keeps proof modules independent from `MetaTheory` to avoid import cycles.
--   * No simulation proof obligations live here.

open import Data.List using ([]; length)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

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

TermRel :
  SealCtx → Store → SealCtx → Store → Term → Term → Ty → Ty → Set
TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B =
  ⟪ 0 , Ψˡ , Σˡ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B

WorldRel : SimWorld → Term → Term → Ty → Ty → Set
WorldRel W =
  TermRel (Ψˡ W) (Σˡ W) (Ψʳ W) (Σʳ W)

Blame : Term → Set
Blame M = ∃[ ℓ ] (M ≡ blame ℓ)

Blames : Store → Term → Set
Blames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

Converges : Store → Term → Set
Converges Σ M =
  ∃[ Σ′ ] ∃[ W ] ((Σ ∣ M —↠ Σ′ ∣ W) × (Value W ⊎ Blame W))

Diverges : Store → Term → Set
Diverges Σ M = ¬ Converges Σ M

DivergeOrBlame : Store → Term → Set
DivergeOrBlame Σ M =
  ∀ Σ′ N →
  Σ ∣ M —↠ Σ′ ∣ N →
  Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σ′ ∣ N —→ Σ″ ∣ N″))
