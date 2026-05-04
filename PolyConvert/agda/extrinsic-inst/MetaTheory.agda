module MetaTheory where

-- File Charter:
--   * Public metatheory statements for the current PolyConvert slice.
--   * Exposes theorem statements at the top level while keeping proof details
--     under `proof/`.
--   * Currently exports progress for closed terms over the store-threaded
--     reduction relation.

open import Data.List using ([])
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Types
open import Store
open import Terms
open import TermImprecision
open import Reduction

import proof.Progress as ProgressProof
import proof.Preservation as PreservationProof
import proof.DynamicGradualGuarantee as DGGProof

progress :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A →
  ProgressProof.Progress {Σ = Σ} M
progress = ProgressProof.progress

preservation :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty} →
  StoreWf Δ Ψ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Σ ∣ M —→ Σ′ ∣ M′ →
  ∃[ Ψ′ ]
    (StoreWf Δ Ψ′ Σ′ ×
     (Δ ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M′ ⦂ A))
preservation wfΣ M⊢ red with PreservationProof.preservation-step wfΣ M⊢ red
preservation wfΣ M⊢ red | Ψ′ , eqΨ , M′⊢ =
  Ψ′ ,
  PreservationProof.exact-storeWf
    {shape = PreservationProof.step-ctx-shape red}
    eqΨ
    (PreservationProof.step-storeWf wfΣ M⊢ red) ,
  M′⊢

------------------------------------------------------------------------
-- Dynamic gradual guarantee
------------------------------------------------------------------------

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

dynamic-gradual-guarantee :
  ∀ {Ψ Σ M M′ A B} →
  StoreWf 0 Ψ Σ →
  ⟪ 0 , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
  (∀ {Σˡ′ V} →
     Value V →
     Σ ∣ M —↠ Σˡ′ ∣ V →
     ∃[ Ψˡ′ ]
       (StoreWf 0 Ψˡ′ Σˡ′ ×
        ∃[ Σʳ′ ] ∃[ V′ ]
          (Value V′ ×
           (Σ ∣ M′ —↠ Σʳ′ ∣ V′) ×
           (⟪ 0 , Ψˡ′ , Σˡ′ , [] ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ B))))
  ×
  (Diverges Σ M → Diverges Σ M′)
  ×
  (∀ {Σʳ′ V′} →
     Value V′ →
     Σ ∣ M′ —↠ Σʳ′ ∣ V′ →
     (∃[ Ψˡ′ ] ∃[ Σˡ′ ]
       (StoreWf 0 Ψˡ′ Σˡ′ ×
        ∃[ V ]
          (Value V ×
           (Σ ∣ M —↠ Σˡ′ ∣ V) ×
           (⟪ 0 , Ψˡ′ , Σˡ′ , [] ⟫ ⊢ V ⊑ V′ ⦂ A ⊑ B))))
     ⊎ Blames Σ M)
  ×
  (Diverges Σ M′ → DivergeOrBlame Σ M)
dynamic-gradual-guarantee = DGGProof.dynamic-gradual-guarantee
