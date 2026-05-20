module GradualGuarantee where

-- File Charter:
--   * Public gradual guarantee statements for PolyConvert.
--   * Exposes top-level theorem wrappers around proof assemblies.

open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)

open import Types
open import Store
open import Imprecision using (Imp; extend-X⊑X; _∣_⊢_⦂_⊑_)
open import Terms
open import GradualTerms
  using (GPrec; GPCtx; GTerm; leftGCtx; rightGCtx; _∣_⊢ᴳ_⊑_; _∣_⊢_⦂_)
open import TermImprecision
open import Reduction

import proof.DynamicGradualGuarantee as DGGProof
import proof.StaticGradualGuarantee as SGGProof

static-gradual-guarantee :
  ∀ {M M′ : GTerm} {A} →
  0 ∣ [] ⊢ᴳ M ⊑ M′ →
  0 ∣ [] ⊢ M ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ] (0 ∣ [] ⊢ M′ ⦂ B)  ×  (0 ∣ [] ⊢ p ⦂ A ⊑ B)
static-gradual-guarantee =
  SGGProof.static-gradual-guarantee {Δ = 0} {Γ = []}

dynamic-gradual-guarantee :
  ∀ {Ψ Σ M M′ A B} →
  StoreWf 0 Ψ Σ →
  ⟪ 0 , Ψ , Σ , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
  (∀ {Σˡ′ V} →
     Value V →
     Σ ∣ M —↠ Σˡ′ ∣ V →
     ∃[ Ψˡ′ ]
       (StoreWf 0 Ψˡ′ Σˡ′ ×
        ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
          (StoreWf 0 Ψʳ′ Σʳ′ ×
           ∃[ V′ ]
             (Value V′ ×
              (Σ ∣ M′ —↠ Σʳ′ ∣ V′) ×
              (⟪ 0 , Ψˡ′ , Σˡ′ , Ψʳ′ , Σʳ′ , [] ⟫
                ⊢ V ⊑ V′ ⦂ A ⊑ B)))))
  ×
  (Diverges Σ M → Diverges Σ M′)
  ×
  (∀ {Σʳ′ V′} →
     Value V′ →
     Σ ∣ M′ —↠ Σʳ′ ∣ V′ →
     (∃[ Ψʳ′ ]
       (StoreWf 0 Ψʳ′ Σʳ′ ×
        ∃[ Ψˡ′ ] ∃[ Σˡ′ ]
          (StoreWf 0 Ψˡ′ Σˡ′ ×
           ∃[ V ]
             (Value V ×
              (Σ ∣ M —↠ Σˡ′ ∣ V) ×
              (⟪ 0 , Ψˡ′ , Σˡ′ , Ψʳ′ , Σʳ′ , [] ⟫
                ⊢ V ⊑ V′ ⦂ A ⊑ B)))))
     ⊎ Blames Σ M)
  ×
  (Diverges Σ M′ → DivergeOrBlame Σ M)
dynamic-gradual-guarantee = DGGProof.dynamic-gradual-guarantee
