module SimRight where

-- File Charter:
--   * Single-step right-to-left simulation helper for `DGGSim.agda`.
--   * Provides `sim-right`, the one-step analogue of `sim-right*`.
--   * Follows the case-expansion style of GTLC's `sim-back`, with every
--     right reduction constructor split out explicitly.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import UpDown using (WfTy-weakenˢ)
open import Store using (StoreWf)
open import ImprecisionIndexed
open import Terms using (Term; Value; blame; _⦂∀_[_]; _up_; _down_; wk⊑; wk⊒)
open import TermImprecisionIndexed
open import ReductionFresh
open import SimRightLemmas
open import PreservationFresh using (wkΨ-cast-tag-⊑-≤; wkΨ-cast-tag-⊒-≤)

Blame : Term → Set
Blame M = ∃[ ℓ ] (M ≡ blame ℓ)

Blames : Store → Term → Set
Blames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

sim-right :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σʳ ∣ M′ —→ Σʳ′ ∣ N′ →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
    Σ[ Σˡ′ ∈ Store ]
    Σ[ N ∈ Term ]
      ((Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
  ⊎ Blames Σˡ M

-- Raw non-store-allocating steps.

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (β vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (β-up-∀ vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (β-up-↦ vV vW)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (β-down-↦ vV vW)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (id-up vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (id-down vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (seal-unseal vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (tag-untag-ok vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (tag-untag-bad vV G≢H)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step δ-⊕) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (blame-·₂ vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·α) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-up) =
  inj₂ (sim-right-w12-right-blame-up-blames M⊑M′)

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-down) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-⊕₁) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (blame-⊕₂ vV)) = {!!}

-- Store-allocating and congruence steps.

sim-right M⊑M′ wfΣˡ wfΣʳ β-Λ = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (β-down-∀ vV) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (β-down-ν vV) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (β-up-ν vV) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·α redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
    with M⊑M′
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑⦂∀-ν A B pν rel wfA hT inst
    with sim-right rel wfΣˡ wfΣʳ (ξ-up redM)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑⦂∀-ν A B pν rel wfA hT inst
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′) =
  inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , (N ⦂∀ A [ _ ]) ,
    sim-right-w12-tyapp-↠ M↠N ,
    ⊑⦂∀-ν A B pν N⊑N′
      (WfTy-weakenˢ wfA Ψˡ≤Ψˡ″)
      (WfTy-weakenˢ hT Ψˡ≤Ψˡ″)
      inst)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑⦂∀-ν A B pν rel wfA hT inst
  | inj₂ (Σˡ′ , ℓ , M↠blame) =
  inj₂ (Σˡ′ , ℓ , sim-right-w12-tyapp-blame-↠ M↠blame)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑up Φ lenΦ rel hu hu′
    with sim-right rel wfΣˡ wfΣʳ redM
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑up Φ lenΦ rel hu hu′
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with sim-right-w12-multi-store-growth M↠N
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑up Φ lenΦ rel hu hu′
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
    with sim-right-w12-wkΨ-cast-tag-⊑-≤₂ Ψˡ≤Ψˡ″ lenΦ
           (wk⊑ Σˡ≤Σˡ′ hu) (wk⊑ Σˡ≤Σˡ′ hu′)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑up Φ lenΦ rel hu hu′
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
  | Φ′ , lenΦ′ , hu″ , hu′″ =
  inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , (N up _) , up-↠ M↠N ,
    ⊑up Φ′ lenΦ′ N⊑N′ hu″ hu′″)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑up Φ lenΦ rel hu hu′
  | inj₂ (Σˡ′ , ℓ , M↠blame) =
  inj₂ (Σˡ′ , ℓ , sim-right-w12-up-blame-↠ M↠blame)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upL Φ lenΦ rel hu
    with sim-right rel wfΣˡ wfΣʳ (ξ-up redM)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upL Φ lenΦ rel hu
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with sim-right-w12-multi-store-growth M↠N
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upL Φ lenΦ rel hu
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡ″ lenΦ (wk⊑ Σˡ≤Σˡ′ hu)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upL Φ lenΦ rel hu
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
  | Φ′ , lenΦ′ , hu″ =
  inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , (N up _) , up-↠ M↠N ,
    ⊑upL Φ′ lenΦ′ N⊑N′ hu″)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upL Φ lenΦ rel hu
  | inj₂ (Σˡ′ , ℓ , M↠blame) =
  inj₂ (Σˡ′ , ℓ , sim-right-w12-up-blame-↠ M↠blame)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upR Φ lenΦ rel hu′
    with sim-right rel wfΣˡ wfΣʳ redM
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upR Φ lenΦ rel hu′
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with sim-right-w12-multi-store-growth M↠N
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upR Φ lenΦ rel hu′
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡ″ lenΦ (wk⊑ Σˡ≤Σˡ′ hu′)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upR Φ lenΦ rel hu′
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
  | Φ′ , lenΦ′ , hu′″ =
  inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N ,
    ⊑upR Φ′ lenΦ′ N⊑N′ hu′″)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑upR Φ lenΦ rel hu′
  | inj₂ blames =
  inj₂ blames
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑downL Φ lenΦ rel hd
    with sim-right rel wfΣˡ wfΣʳ (ξ-up redM)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑downL Φ lenΦ rel hd
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with sim-right-w12-multi-store-growth M↠N
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑downL Φ lenΦ rel hd
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
    with wkΨ-cast-tag-⊒-≤ Ψˡ≤Ψˡ″ lenΦ (wk⊒ Σˡ≤Σˡ′ hd)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑downL Φ lenΦ rel hd
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Σˡ≤Σˡ′
  | Φ′ , lenΦ′ , hd″ =
  inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , (N down _) , down-↠ M↠N ,
    ⊑downL Φ′ lenΦ′ N⊑N′ hd″)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑downL Φ lenΦ rel hd
  | inj₂ (Σˡ′ , ℓ , M↠blame) =
  inj₂ (Σˡ′ , ℓ , sim-right-w12-down-blame-↠ M↠blame)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up {p = u′} redM)
  | ⊑blameR {ℓ = ℓ} hM =
  inj₂ (_ , ℓ , (blame ℓ ∎))

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-down redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₁ redL) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₂ vV redM) = {!!}
