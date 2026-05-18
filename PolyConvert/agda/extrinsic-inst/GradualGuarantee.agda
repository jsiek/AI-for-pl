module GradualGuarantee where

-- File Charter:
--   * Public gradual guarantee statements for PolyConvert.
--   * Exposes top-level theorem wrappers around proof assemblies.

open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)

open import Types
open import Store
open import Imprecision using (Imp; plains; _∣_⊢_⦂_⊑_)
open import Terms
open import GradualTerms
  using (GPrec; GPCtx; GTerm; leftGCtx; rightGCtx; _⊢ᴳ_⊑_; _∣_⊢_⦂_)
open import TermImprecision
open import Reduction

import proof.DynamicGradualGuarantee as DGGProof
import proof.StaticGradualGuarantee as SGGProof

static-gradual-guarantee :
  ∀ {Δ} {Γ : GPCtx Δ} {M M′ : GTerm} {A} →
  Δ ⊢ᴳ M ⊑ M′ →
  Δ ∣ leftGCtx Γ ⊢ M ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (Δ ∣ rightGCtx Γ ⊢ M′ ⦂ B) × (0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B)
static-gradual-guarantee = SGGProof.static-gradual-guarantee

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
