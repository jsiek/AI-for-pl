module SimRight where

-- File Charter:
--   * Single-step right-to-left simulation helper for `DGGSim.agda`.
--   * Provides `sim-right`, the one-step analogue of `sim-right*`.
--   * Follows the case-expansion style of GTLC's `sim-back`, with every
--     right reduction constructor split out explicitly.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-trans)
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
open import PreservationFresh using (wkΨ-cast-tag-⊑-≤; wkΨ-cast-tag-⊒-≤)
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
  -- BLOCKED[W03][R23]: Hole R23 at /Users/jsiek/AI-for-pl/PolyUpDown/agda/extrinsic-inst/SimRight.agda:91 still contains `{!!}` after the reported success.

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·₁ redL) = {!!}

sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
    with M⊑M′
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑⦂∀-ν A B p rel wfA hT inst
    with sim-right rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑⦂∀-ν A B p rel wfA hT inst
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′) =
  inj₁
    (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N ⦂∀ A [ _ ] ,
     sim-right-w09-typeapp-↠ M↠N ,
     ⊑⦂∀-ν A B p N⊑N′
       (WfTy-weakenˢ wfA Ψˡ≤Ψˡ″)
       (WfTy-weakenˢ hT Ψˡ≤Ψˡ″)
       inst)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑⦂∀-ν A B p rel wfA hT inst
  | inj₂ M↠blame =
  inj₂ (sim-right-w09-typeapp-blames M↠blame)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑upL Φ lenΦ rel hu
    with sim-right rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑upL Φ lenΦ rel hu
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡ″ lenΦ
           (wk⊑ (sim-right-w03-multi-store-growth M↠N) hu)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑upL Φ lenΦ rel hu
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Φ′ , lenΦ′ , hu′ =
  inj₁
    (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N up _ ,
     up-↠ M↠N ,
     ⊑upL Φ′ lenΦ′ N⊑N′ hu′)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑upL Φ lenΦ rel hu
  | inj₂ M↠blame =
  inj₂ (sim-right-w09-up-blames M↠blame)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑downL Φ lenΦ rel hd
    with sim-right rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑downL Φ lenΦ rel hd
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
    with wkΨ-cast-tag-⊒-≤ Ψˡ≤Ψˡ″ lenΦ
           (wk⊒ (sim-right-w03-multi-store-growth M↠N) hd)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑downL Φ lenΦ rel hd
  | inj₁ (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′)
  | Φ′ , lenΦ′ , hd′ =
  inj₁
    (Ψˡ″ , Ψˡ≤Ψˡ″ , Σˡ′ , N down _ ,
     down-↠ M↠N ,
     ⊑downL Φ′ lenΦ′ N⊑N′ hd′)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑downL Φ lenΦ rel hd
  | inj₂ M↠blame =
  inj₂ (sim-right-w09-down-blames M↠blame)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑· L⊑V Arg⊑Arg′
    with sim-right-w03-left-value-catchup-or-blame vV wfΣˡ L⊑V
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑· L⊑V Arg⊑Arg′
  | inj₁ (Ψˡᵥ , Ψˡ≤Ψˡᵥ , Σˡᵥ , wfΣˡᵥ , W , vW , L↠W , W⊑V)
    with sim-right
           (wkΨΣ-⊑ Ψˡ≤Ψˡᵥ
             (sim-right-w03-multi-store-growth L↠W)
             Arg⊑Arg′)
           wfΣˡᵥ wfΣʳ redM
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑· L⊑V Arg⊑Arg′
  | inj₁ (Ψˡᵥ , Ψˡ≤Ψˡᵥ , Σˡᵥ , wfΣˡᵥ , W , vW , L↠W , W⊑V)
  | inj₁ (Ψˡ″ , Ψˡᵥ≤Ψˡ″ , Σˡ′ , N , M↠N , N⊑N′) =
  inj₁
    (Ψˡ″ , ≤-trans Ψˡ≤Ψˡᵥ Ψˡᵥ≤Ψˡ″ , Σˡ′ , W · N ,
     multi-trans (appL-↠ {M = _} L↠W) (appR-↠ vW M↠N) ,
     ⊑·
       (wkΨΣ-⊑ Ψˡᵥ≤Ψˡ″ (sim-right-w03-multi-store-growth M↠N) W⊑V)
       N⊑N′)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑· L⊑V Arg⊑Arg′
  | inj₁ (Ψˡᵥ , Ψˡ≤Ψˡᵥ , Σˡᵥ , wfΣˡᵥ , W , vW , L↠W , W⊑V)
  | inj₂ M↠blame =
  inj₂
    (sim-right-w03-prefix-blames
      (appL-↠ {M = _} L↠W)
      (sim-right-w03-appR-blames vW M↠blame))
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑· L⊑V Arg⊑Arg′
  | inj₂ L↠blame =
  inj₂ (sim-right-w03-appL-blames L↠blame)
sim-right {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ (ξ-·₂ vV redM)
  | ⊑blameR {ℓ = ℓ} hM =
  inj₂ (_ , ℓ , (blame ℓ ∎))

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-·α redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-up redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-down redM) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₁ redL) = {!!}

sim-right M⊑M′ wfΣˡ wfΣʳ (ξ-⊕₂ vV redM) = {!!}
