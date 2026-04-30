module DGGSim where

-- File Charter:
--   * States the dynamic gradual guarantee for closed extrinsic-inst
--   * `PolyUpDown` terms using a simulation-shaped proof outline.
--   * Avoids the logical-relation fundamental theorem used by
--     `DynamicGradualGuarantee.agda`.
--   * Uses the corrected imprecision orientation: `M ⊑ M′` means `M` is
--     less imprecise/more precise and `M′` is more imprecise/less precise.
--   * Works top-down: the public theorem is proved from named simulation
--     obligations, which are postulated below as the remaining proof plan.

open import Data.List using ([]; _++_; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; trans)
open import Relation.Nullary using (¬_)

open import Types
open import UpDown using (Up; Down; wt-↦)
open import Store using (StoreWf)
open import ImprecisionIndexed
open import Terms
  using
    ( Term
    ; blame
    ; ƛ_⇒_
    ; _·_
    ; _⦂∀_[_]
    ; _up_
    ; _down_
    ; substᵗᵐ
    ; `_
    ; _∣_∣_∣_⊢_⦂_
    )
open import TermProperties using (substˣ-term; _[_])
open import TermImprecisionIndexed
open import ReductionFresh
open import SimLeftLemmas

open import PreservationFresh
  using
    ( step-preserves-store-wf
    ; wkΨ-cast-tag-⊑-≤
    )

------------------------------------------------------------------------
-- Closed instances and observable outcomes
------------------------------------------------------------------------

closedTySub : Substᵗ
closedTySub X = ‵ `ℕ

close : Term → Term
close M = substᵗᵐ closedTySub (substˣ-term (λ x → ` x) M)

closeˡ : Term → Term
closeˡ = close

closeʳ : Term → Term
closeʳ = close

steps :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  ℕ
steps (_ ∎) = zero
steps (_ —→⟨ _ ⟩ M↠N) = suc (steps M↠N)

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

prefix-blames :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Blames Σ′ N →
  Blames Σ M
prefix-blames M↠N (Σᵇ , ℓ , N↠blame) =
  Σᵇ , ℓ , multi-trans M↠N N↠blame

------------------------------------------------------------------------
-- Simulation proof obligations
------------------------------------------------------------------------

postulate
  initial-simulation :
    ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    (wfΣ : StoreWf 0 Ψ Σ) →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ closeˡ M ⊑ closeʳ M′ ⦂ p

sim-left :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —→ Σˡ′ ∣ N →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
sim-left M⊑M′ wfΣˡ wfΣʳ red with red

-- Congruence: application operator.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑· L⊑L′ Arg⊑Arg′
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·₁ redL
  | ⊑· L⊑L′ Arg⊑Arg′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , (M′ᵣ · _) , appL-↠ M′↠M′ᵣ ,
  ⊑· Nᵣ⊑M′ᵣ {!!}

-- Congruence: application operand.
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·₂ vV redM)
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ Arg⊑Arg′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} vV L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ Arg⊑Arg′
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
    with sim-left Arg⊑Arg′ wfΣˡ wfΣʳᵥ redM
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | ξ-·₂ vV redM
  | ⊑· L⊑L′ Arg⊑Arg′
  | Σʳᵥ , wfΣʳᵥ , V′ , vV′ , L′↠V′ , V⊑V′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , (V′ · M′ᵣ) ,
  multi-trans (appL-↠ {M = _} L′↠V′) (appR-↠ vV′ M′↠M′ᵣ) ,
  ⊑· (wkΨΣ-⊑ Ψˡ≤Ψˡᵣ (store-growth redM) V⊑V′) Nᵣ⊑M′ᵣ

-- Congruence: type application.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·α redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-·α redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀ rel wfA wfB hT
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀ rel wfA wfB hT
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-·α redM
  | ⊑⦂∀-ν A B p rel wfA hT inst =
  {!!}

-- Congruence: up casts.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-up redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-up redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑up Φ lenΦ rel hu hu′
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑up Φ lenΦ rel hu hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upL Φ lenΦ rel hu
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upL Φ lenΦ rel hu
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ hu
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-up redM
  | ⊑upL Φ lenΦ rel hu
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ ,
  ⊑upL Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ (Terms.wk⊑ (store-growth redM) huᵣ)

-- Congruence: down casts.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-down redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-down redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑down Φ lenΦ rel hd hd′
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑down Φ lenΦ rel hd hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downL Φ lenΦ rel hd
    with sim-left rel wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-down redM
  | ⊑downL Φ lenΦ rel hd
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Congruence: primitive operator left operand.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₁ redL)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑⊕ L⊑L′ Arg⊑Arg′
    with sim-left L⊑L′ wfΣˡ wfΣʳ redL
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₁ redL
  | ⊑⊕ L⊑L′ Arg⊑Arg′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- Congruence: primitive operator right operand.
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
    with M⊑M′
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₂ vV redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (ξ-⊕₂ vV redM)
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑⊕ L⊑L′ Arg⊑Arg′
    with sim-left Arg⊑Arg′ wfΣˡ wfΣʳ redM
sim-left M⊑M′ wfΣˡ wfΣʳ red | ξ-⊕₂ vV redM
  | ⊑⊕ L⊑L′ Arg⊑Arg′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- β reduction
-- β reduction, ⊑upR
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
    with wkΨ-cast-tag-⊑-≤ Ψˡ≤Ψˡᵣ lenΦ hu′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ
  | Φᵣ , lenΦᵣ , huᵣ =
  Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ up _ , up-↠ M′↠M′ᵣ ,
  ⊑upR Φᵣ lenΦᵣ Nᵣ⊑M′ᵣ huᵣ

-- β reduction, ⊑downR
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}

-- β reduction, ⊑·
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} (ƛ A ⇒ N) L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , ƛN⊑V′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳᶠ} vW W⊑W′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , ƛN⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta {Σʳ = Σʳᵃ} ƛN⊑V′ vV′ W⊑W′ᵥ vW vW′ᵥ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β {B = A} {N = N} {V = W} vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , ƛN⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N[W]⊑N′ =
  Ψˡ , ≤-refl , Σʳᵝ , N′ ,
  multi-trans
    (appL-↠ {M = _} L′↠V′)
    (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′) ,
  N[W]⊑N′

-- β-up-∀
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-∀ vV) =
  {!!}

-- β-up-↦
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-up-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-up-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} (vV up _↦_) L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vup⊑V′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳᶠ} vW W⊑W′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vup⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-up {Σʳ = Σʳᵃ} Vup⊑V′ vV vV′
           W⊑W′ᵥ vW vW′ᵥ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-up-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vup⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Ψˡ , ≤-refl , Σʳᵝ , N′ ,
  multi-trans
    (appL-↠ {M = _} L′↠V′)
    (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′) ,
  N⊑N′
  
-- β-down-↦
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
    with M⊑M′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-down-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑upR Φ lenΦ rel hu′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
    with sim-left rel wfΣˡ wfΣʳ (id-step (β-down-↦ vV vW))
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑downR Φ lenΦ rel hd′
  | Ψˡᵣ , Ψˡ≤Ψˡᵣ , Σʳᵣ , M′ᵣ , M′↠M′ᵣ , Nᵣ⊑M′ᵣ =
  {!!}
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳ} (vV down _↦_) L⊑L′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vdown⊑V′
    with left-value-right-catchup {Ψˡ = Ψˡ} {Ψʳ = Ψʳ}
           {Σˡ = Σˡ} {Σʳ = Σʳᶠ} vW W⊑W′
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vdown⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
    with sim-left-beta-down {Σʳ = Σʳᵃ} Vdown⊑V′ vV vV′
           W⊑W′ᵥ vW vW′ᵥ
sim-left {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  M⊑M′ wfΣˡ wfΣʳ red | id-step (β-down-↦ {V = V} {W = W} vV vW)
  | ⊑· L⊑L′ W⊑W′
  | Σʳᶠ , wfΣʳᶠ , V′ , vV′ , L′↠V′ , Vdown⊑V′
  | Σʳᵃ , wfΣʳᵃ , W′ᵥ , vW′ᵥ , W′↠W′ᵥ , W⊑W′ᵥ
  | Σʳᵝ , N′ , V′W′↠N′ , N⊑N′ =
  Ψˡ , ≤-refl , Σʳᵝ , N′ ,
  multi-trans
    (appL-↠ {M = _} L′↠V′)
    (multi-trans (appR-↠ vV′ W′↠W′ᵥ) V′W′↠N′) ,
  N⊑N′
  
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (id-up vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (id-down vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (seal-unseal vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (tag-untag-ok vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (tag-untag-bad vV G≢H) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step δ-⊕ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-·₁ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (blame-·₂ vV) =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-·α =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-up =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-down =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step blame-⊕₁ =
  {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | id-step (blame-⊕₂ vV) =
  {!!}

-- PolyUpDown-specific store-allocation/poly-instantiation cases.
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-Λ = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-down-∀ vV = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-down-ν vV = {!!}
sim-left M⊑M′ wfΣˡ wfΣʳ red | β-up-ν vV = {!!}

--------------------------------------------------------------------------------

sim-left* :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Σˡ ∣ M —↠ Σˡ′ ∣ N →
  Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
    Σ[ Σʳ′ ∈ Store ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
    Σ[ N′ ∈ Term ]
      ((Σʳ ∣ M′ —↠ Σʳ′ ∣ N′) ×
       (⟪ 0 , Ψˡ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p))
sim-left* {Σʳ = Σʳ} {M′ = M′} M⊑M′ wfΣˡ wfΣʳ (M ∎) =
  wfΣˡ , Σʳ , wfΣʳ , M′ , (M′ ∎) , M⊑M′
sim-left* M⊑M′ wfΣˡ wfΣʳ (M —→⟨ M→M₁ ⟩ M₁↠N)
    with step-preserves-store-wf wfΣˡ (⊑-left-typed M⊑M′) M→M₁
       | sim-left M⊑M′ wfΣˡ wfΣʳ M→M₁
sim-left* M⊑M′ wfΣˡ wfΣʳ (M —→⟨ M→M₁ ⟩ M₁↠N)
  | Ψwf , wfΣ₁ | Ψ₁ , Ψˡ≤Ψ₁ , Σʳ₁ , M′₁ , M′↠M′₁ , M₁⊑M′₁ =
  {!!}

--------------------------------------------------------------------------------

postulate
  sim-right* :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Σʳ ∣ M′ —↠ Σʳ′ ∣ N′ →
    (Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ Σʳ′ ]
      Σ[ Σˡ′ ∈ Store ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
      Σ[ N ∈ Term ]
        ((Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
         (⟪ 0 , Ψˡ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ N′ ⦂ p)))
    ⊎ Blames Σˡ M

  left-value-catchup-or-blame :
    ∀ {Ψˡ Σˡ N V′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    Value V′ →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ N ⊑ V′ ⦂ p →
    (Σ[ Σˡ′ ∈ Store ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ Σˡ′ ]
      Σ[ V ∈ Term ]
        (Value V ×
         (Σˡ ∣ N —↠ Σˡ′ ∣ V) ×
         (⟪ 0 , Ψˡ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
    ⊎ Blames Σˡ N

  right-converges-implies-left-converges :
    ∀ {Ψˡ Σˡ Σʳ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Converges Σʳ M′ →
    Converges Σˡ M

  right-diverges-implies-left-blame-or-step :
    ∀ {Ψˡ Σˡ Σʳ Σˡ′ M M′ N A B} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
    Diverges Σʳ M′ →
    Σˡ ∣ M —↠ Σˡ′ ∣ N →
    Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σˡ′ ∣ N —→ Σ″ ∣ N″))

------------------------------------------------------------------------
-- Dynamic gradual guarantee, via simulation
------------------------------------------------------------------------

dynamic-gradual-guarantee-part1 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     Σ[ Σʳ′ ∈ Store ]
       Σ[ V′ ∈ Term ]
         (Value V′ ×
          (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
dynamic-gradual-guarantee-part1
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p}
  wfΣ rel {Σˡ′ = Σˡ′} vV M↠V
    with sim-left* {Ψˡ = Ψ} {Ψʳ = Ψ} {Σˡ = Σ} {Σʳ = Σ}
      {A = A} {B = B} {p = p} (initial-simulation wfΣ rel)
      wfΣ wfΣ M↠V
... | wfΣˡ′ , Σʳ₁ , wfΣʳ₁ , N′ , M′↠N′ , simVN′
    with left-value-right-catchup {Ψˡ = Ψ} {Ψʳ = Ψ} {Σˡ = Σˡ′}
      {Σʳ = Σʳ₁} {A = A} {B = B} {p = p} vV simVN′
... | Σʳ′ , wfΣʳ′ , V′ , vV′ , N′↠V′ , V⊑V′ =
  Σʳ′ , V′ ,
  vV′ , multi-trans M′↠N′ N′↠V′ , V⊑V′

dynamic-gradual-guarantee-part2 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  Diverges Σ (closeˡ M) →
  Diverges Σ (closeʳ M′)
dynamic-gradual-guarantee-part2
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p} wfΣ rel divˡ convʳ =
  divˡ
    (right-converges-implies-left-converges {Ψˡ = Ψ}
      {Σˡ = Σ} {Σʳ = Σ} {A = A} {B = B} {p = p}
      (initial-simulation wfΣ rel)
      convʳ)

dynamic-gradual-guarantee-part3 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  (∀ {Σʳ′ V′} →
     Value V′ →
     (M′↠V′ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) →
     (Σ[ Σˡ′ ∈ Store ]
       Σ[ V ∈ Term ]
         (Value V ×
          (Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) ×
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
     ⊎ Blames Σ (closeˡ M))
dynamic-gradual-guarantee-part3
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p}
  wfΣ rel {Σʳ′ = Σʳ′} vV′ M′↠V′
    with sim-right* {Ψˡ = Ψ} {Ψʳ = Ψ} {Σˡ = Σ} {Σʳ = Σ}
      {A = A} {B = B} {p = p} (initial-simulation wfΣ rel) M′↠V′
... | inj₂ M↠blame = inj₂ M↠blame
... | inj₁ (wfΣʳ′ , Σˡ₁ , wfΣˡ₁ , N , M↠N , simNV′)
    with left-value-catchup-or-blame {Ψˡ = Ψ} {Σˡ = Σˡ₁}
      {A = A} {B = B} {p = p} vV′ simNV′
... | inj₁ (Σˡ′ , wfΣˡ′ , V , vV , N↠V , V⊑V′) =
  inj₁
    (Σˡ′ , V ,
     vV , multi-trans M↠N N↠V , V⊑V′)
... | inj₂ N↠blame =
  inj₂ (prefix-blames M↠N N↠blame)

dynamic-gradual-guarantee-part4 :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  Diverges Σ (closeʳ M′) →
  DivergeOrBlame Σ (closeˡ M)
dynamic-gradual-guarantee-part4
  {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p} wfΣ rel divʳ Σˡ′ N M↠N =
  right-diverges-implies-left-blame-or-step {Ψˡ = Ψ}
    {Σˡ = Σ} {Σʳ = Σ} {A = A} {B = B} {p = p}
    (initial-simulation wfΣ rel)
    divʳ
    M↠N

dynamic-gradual-guarantee :
  ∀ {Ψ Σ M M′ A B} {p : [] ⊢ A ⊑ᵢ B} →
  (wfΣ : StoreWf 0 Ψ Σ) →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ M′ ⦂ p →
  -- Part 1: a less-imprecise value run is matched by a more-imprecise one.
  (∀ {Σˡ′ V} →
     Value V →
     (M↠V : Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) →
     Σ[ Σʳ′ ∈ Store ]
       Σ[ V′ ∈ Term ]
         (Value V′ ×
          (Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) ×
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
  ×
  -- Part 2: divergence of the less-imprecise term is preserved.
  (Diverges Σ (closeˡ M) → Diverges Σ (closeʳ M′))
  ×
  -- Part 3: a more-imprecise value run is caught up by the left,
  -- or left blames.
  (∀ {Σʳ′ V′} →
     Value V′ →
     (M′↠V′ : Σ ∣ closeʳ M′ —↠ Σʳ′ ∣ V′) →
     (Σ[ Σˡ′ ∈ Store ]
       Σ[ V ∈ Term ]
         (Value V ×
          (Σ ∣ closeˡ M —↠ Σˡ′ ∣ V) ×
          (⟪ 0 , Ψ , Σˡ′ , [] , [] ⟫ ⊢ V ⊑ V′ ⦂ p)))
     ⊎ Blames Σ (closeˡ M))
  ×
  -- Part 4: if the right diverges, every left reduct can still step or blames.
  (Diverges Σ (closeʳ M′) → DivergeOrBlame Σ (closeˡ M))
dynamic-gradual-guarantee wfΣ rel =
  dynamic-gradual-guarantee-part1 wfΣ rel ,
  (dynamic-gradual-guarantee-part2 wfΣ rel ,
   (dynamic-gradual-guarantee-part3 wfΣ rel ,
    dynamic-gradual-guarantee-part4 wfΣ rel))
