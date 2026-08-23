module proof.LR-narrow.UniversalInstantiation where

-- File Charter:
--   * Eliminates the positive-index head of UniversalsRelated.
--   * Observes type application in the current, pre-allocation world.
--   * Exposes that successful returns factor through the chosen extension.
--   * Returns the endpoint body witnesses stored in ValueImprecision.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation

related-universal-instantiation : ∀
    {Δᴾ Δᴵ Δᶜ} {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ p) (suc k) Vᴵ Vᴾ
  → Σ[ Bᴾ ∈ Ty (suc Δᴾ) ]
    Σ[ Bᴵ ∈ Ty (suc Δᴵ) ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) (`∀ Bᴵ) ≡ `∀ Aᴵ)
      × ((s : Bᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Bᴵ [ Rᴵ ]ᵗ)
        → let bound = pairedBindWorld W Rᴾ Rᴵ r
              step = future-paired (future-refl {W = W}) r
          in ComputationsRelated W (PostBindValueRelation step s)
               (suc k) (Vᴵ ⦂∀ Bᴵ [ Rᴵ ])
                 (Vᴾ ⦂∀ Bᴾ [ Rᴾ ]))
related-universal-instantiation {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {W = W}
    {r = r}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , head , tail) =
  Bᴾ , Bᴵ , eqᴾ , eqᴵ ,
  (λ s → head W (future-refl {W = W}) Rᴾ Rᴵ r s)

right-related-universal-instantiation : ∀
    {Δᴾ Δᴵ Δᶜ} {Aᴾ : Ty (suc Δᶜ)} {Aᴵ : Ty Δᶜ}
    {Rᴾ : Ty Δᴾ} {W : World Δᴾ Δᴵ Δᶜ}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ ⇑ᵗ Aᴵ}
    {nonvar : NonVar Aᴾ} {occurs : Fin.zero ∈ᵗ Aᴾ}
    {r★ : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ ⊑ ★}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑ nonvar occurs p) (suc k) Vᴵ Vᴾ
  → Σ[ Bᴾ ∈ Ty (suc Δᴾ) ]
    Σ[ Bᴵ ∈ Ty Δᴵ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) Bᴵ ≡ Aᴵ)
      × ((s : Bᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Bᴵ)
        → let bound = preciseBindWorld W Rᴾ r★
              step = future-precise (future-refl {W = W}) r★
          in ComputationsRelated W (PostBindValueRelation step s)
               (suc k) Vᴵ (Vᴾ ⦂∀ Bᴾ [ Rᴾ ]))
right-related-universal-instantiation {Rᴾ = Rᴾ} {W = W} {r★ = r★}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , head , tail) =
  Bᴾ , Bᴵ , eqᴾ , eqᴵ ,
  (λ s → head W (future-refl {W = W}) Rᴾ r★ s)
