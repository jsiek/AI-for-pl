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
open import Terms using (Term; Value; blame; _·_; _⦂∀_[_]; _up_; _down_; wk⊑; wk⊒)
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

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·α) =
  sim-right-w09-r13 M⊑M′

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-up) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-down) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-⊕₁) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (blame-⊕₂ vV)) = {!!}

-- Store-allocating and congruence steps.

sim-right M⊑M′ wfΣˡ wfΣʳ β-Λ = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (β-down-∀ vV) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (β-down-ν vV) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (β-up-ν vV) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
    with M⊑M′
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑⦂∀-ν A B pν rel wfA hT inst
    with sim-right rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑⦂∀-ν A B pν rel wfA hT inst
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′) =
  inj₁
    ( Ψˡ″
    , Ψˡ≤Ψˡ″
    , Σˡ′
    , N ⦂∀ A [ _ ]
    , sim-right-w09-typeapp-↠ M↠N
    , ⊑⦂∀-ν A B pν N⊑N′
        (WfTy-weakenˢ wfA Ψˡ≤Ψˡ″)
        (WfTy-weakenˢ hT Ψˡ≤Ψˡ″)
        inst
    )
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑⦂∀-ν A B pν rel wfA hT inst
  | inj₂ M-blames =
  inj₂ (sim-right-w09-typeapp-blames M-blames)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑upL Φ lenΦ rel hu
    with sim-right rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑upL Φ lenΦ rel hu
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡ″ lenΦ
           (wk⊑ (sim-right-w09-multi-store-growth M↠N) hu)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑upL Φ lenΦ rel hu
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Φ′ , lenΦ′ , hu′ =
  inj₁
    ( Ψˡ″
    , Ψˡ≤Ψˡ″
    , Σˡ′
    , N up _
    , up-↠ M↠N
    , ⊑upL Φ′ lenΦ′ N⊑N′ hu′
    )
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑upL Φ lenΦ rel hu
  | inj₂ M-blames =
  inj₂ (sim-right-w09-up-blames M-blames)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑downL Φ lenΦ rel hd
    with sim-right rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑downL Φ lenΦ rel hd
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with wkΨ-cast-tag-⊒-≤ Ψˡ≤Ψˡ″ lenΦ
           (wk⊒ (sim-right-w09-multi-store-growth M↠N) hd)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑downL Φ lenΦ rel hd
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Φ′ , lenΦ′ , hd′ =
  inj₁
    ( Ψˡ″
    , Ψˡ≤Ψˡ″
    , Σˡ′
    , N down _
    , down-↠ M↠N
    , ⊑downL Φ′ lenΦ′ N⊑N′ hd′
    )
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑downL Φ lenΦ rel hd
  | inj₂ M-blames =
  inj₂ (sim-right-w09-down-blames M-blames)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑· L⊑L′ Arg⊑Arg′
    with sim-right L⊑L′ wfΣˡ wfΣʳ redL
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑· L⊑L′ Arg⊑Arg′
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , L↠N , N⊑N′) =
  inj₁
    ( Ψˡ″
    , Ψˡ≤Ψˡ″
    , Σˡ′
    , N · _
    , appL-↠ L↠N
    , ⊑· N⊑N′
        (wkΨΣ-⊑ Ψˡ≤Ψˡ″
          (sim-right-w09-multi-store-growth L↠N)
          Arg⊑Arg′)
    )
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑· L⊑L′ Arg⊑Arg′
  | inj₂ L-blames =
  inj₂ (sim-right-w09-appL-blames L-blames)
sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL)
  | ⊑blameR {ℓ = ℓ} hM =
  inj₂ (_ , ℓ , (blame ℓ ∎))

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·α redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-down redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₁ redL) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₂ vV redM) = {!!}
