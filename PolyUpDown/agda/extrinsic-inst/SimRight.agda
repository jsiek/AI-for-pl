module SimRight where

-- File Charter:
--   * Single-step right-to-left simulation helper for `DGGSim.agda`.
--   * Provides `sim-right`, the one-step analogue of `sim-right*`.
--   * Follows the case-expansion style of GTLC's `sim-back`, with every
--     right reduction constructor split out explicitly.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Store using (StoreWf)
open import ImprecisionIndexed
open import Terms using (Term; Value; blame)
open import TermImprecisionIndexed
open import ReductionFresh
open import SimRightLemmas

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

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁) with M⊑M′
sim-right {Σˡ = Σˡ} M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑· L⊑blame relM
    with sim-right-w11-right-blame-left-blames L⊑blame
sim-right {Σˡ = Σˡ} M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑· L⊑blame relM | Σˡ′ , ℓ′ , L↠blame =
    Data.Sum.inj₂ (Σˡ′ , ℓ′ , sim-right-w11-appL-blame-↠ L↠blame)
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑⦂∀-ν A B p rel wfA hT inst
    with sim-right rel wfΣˡ wfΣʳ (id-step blame-·₁)
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑⦂∀-ν A B p rel wfA hT inst
  | Data.Sum.inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑blame)
    with sim-right-w11-right-blame-left-blames N⊑blame
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑⦂∀-ν A B p rel wfA hT inst
  | Data.Sum.inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑blame)
  | Σᵇ , ℓᵇ , N↠blame =
    Data.Sum.inj₂
      (Σᵇ , ℓᵇ ,
       multi-trans
         (sim-right-w11-tyapp-↠ M↠N)
         (sim-right-w11-tyapp-blame-↠ N↠blame))
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑⦂∀-ν A B p rel wfA hT inst
  | Data.Sum.inj₂ (Σᵇ , ℓᵇ , M↠blame) =
    Data.Sum.inj₂ (Σᵇ , ℓᵇ , sim-right-w11-tyapp-blame-↠ M↠blame)
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑upL Φ lenΦ rel hu
    with sim-right rel wfΣˡ wfΣʳ (id-step blame-·₁)
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑upL Φ lenΦ rel hu
  | Data.Sum.inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑blame)
    with sim-right-w11-right-blame-left-blames N⊑blame
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑upL Φ lenΦ rel hu
  | Data.Sum.inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑blame)
  | Σᵇ , ℓᵇ , N↠blame =
    Data.Sum.inj₂
      (Σᵇ , ℓᵇ ,
       multi-trans (up-↠ M↠N) (sim-right-w11-up-blame-↠ N↠blame))
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑upL Φ lenΦ rel hu
  | Data.Sum.inj₂ (Σᵇ , ℓᵇ , M↠blame) =
    Data.Sum.inj₂ (Σᵇ , ℓᵇ , sim-right-w11-up-blame-↠ M↠blame)
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑downL Φ lenΦ rel hd
    with sim-right rel wfΣˡ wfΣʳ (id-step blame-·₁)
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑downL Φ lenΦ rel hd
  | Data.Sum.inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑blame)
    with sim-right-w11-right-blame-left-blames N⊑blame
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑downL Φ lenΦ rel hd
  | Data.Sum.inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑blame)
  | Σᵇ , ℓᵇ , N↠blame =
    Data.Sum.inj₂
      (Σᵇ , ℓᵇ ,
       multi-trans (down-↠ M↠N) (sim-right-w11-down-blame-↠ N↠blame))
sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑downL Φ lenΦ rel hd
  | Data.Sum.inj₂ (Σᵇ , ℓᵇ , M↠blame) =
    Data.Sum.inj₂ (Σᵇ , ℓᵇ , sim-right-w11-down-blame-↠ M↠blame)
sim-right {Σˡ = Σˡ} M⊑M′ wfΣˡ wfΣʳ (id-step blame-·₁)
  | ⊑blameR {ℓ = ℓ} hM′ =
    Data.Sum.inj₂ (Σˡ , ℓ , ((blame ℓ) ∎))

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step (blame-·₂ vV)) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-·α) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (id-step blame-up) = {!!}

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

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-down redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₁ redL) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₂ vV redM) = {!!}
