module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import UpDown using (Down; Label)
open import ImprecisionIndexed
open import Terms using (Term; _⦂∀_[_]; _up_; _down_; blame)
open import TermImprecisionIndexed
open import ReductionFresh
open import SimLeftLemmas using (sim-left-w03-⊑ᵢ-proof-irrel)

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-right` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-right-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `SimRight.agda` hole lines it supports.

-- Worker W01 helper slot

-- Worker W02 helper slot

-- Worker W03 helper slot

-- Worker W04 helper slot

-- Worker W05 helper slot

-- Worker W06 helper slot

-- Supports SimRight.agda R06 (line 55): eliminate an identity-down cast on
-- the right, commuting through left-only casts and reporting left blame.
sim-right-w06-tapp-↠ :
  ∀ {Σ Σ′ M N B T} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (N ⦂∀ B [ T ])
sim-right-w06-tapp-↠ {B = B} {T = T} (M ∎) = (M ⦂∀ B [ T ]) ∎
sim-right-w06-tapp-↠ {B = B} {T = T} (M —→⟨ M→M₁ ⟩ M₁↠N) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M₁ ⟩ sim-right-w06-tapp-↠ M₁↠N

sim-right-w06-id-down-core :
  ∀ {Ψ Σˡ V M C A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ M ⊑ (V down Down.id C) ⦂ p →
  (Σ[ N ∈ Term ]
    ((Σˡ ∣ M —↠ Σˡ ∣ N) ×
     (⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ N ⊑ V ⦂ p)))
  ⊎ (Σ[ ℓ ∈ Label ] (Σˡ ∣ M —↠ Σˡ ∣ blame ℓ))
sim-right-w06-id-down-core (⊑upL Φ lenΦ rel hu)
    with sim-right-w06-id-down-core rel
sim-right-w06-id-down-core (⊑upL Φ lenΦ rel hu)
  | inj₁ (N , M↠N , N⊑V) =
  inj₁ (N up _ , up-↠ M↠N , ⊑upL Φ lenΦ N⊑V hu)
sim-right-w06-id-down-core (⊑upL Φ lenΦ rel hu)
  | inj₂ (ℓ , M↠blame) =
  inj₂ (ℓ ,
    multi-trans (up-↠ M↠blame)
      ((blame ℓ up _) —→⟨ id-step blame-up ⟩ blame ℓ ∎))
sim-right-w06-id-down-core
    (⊑⦂∀-ν A B {T = T} pν rel wfA hT inst)
    with sim-right-w06-id-down-core rel
sim-right-w06-id-down-core
    (⊑⦂∀-ν A B {T = T} pν rel wfA hT inst)
  | inj₁ (N , M↠N , N⊑V) =
  inj₁ (N ⦂∀ A [ T ] , sim-right-w06-tapp-↠ M↠N ,
        ⊑⦂∀-ν A B pν N⊑V wfA hT inst)
sim-right-w06-id-down-core
    (⊑⦂∀-ν A B {T = T} pν rel wfA hT inst)
  | inj₂ (ℓ , M↠blame) =
  inj₂ (ℓ ,
    multi-trans (sim-right-w06-tapp-↠ M↠blame)
      ((blame ℓ ⦂∀ A [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎))
sim-right-w06-id-down-core {p = p}
    (⊑down {pB = pB} Φ lenΦ rel hd (UpDown.wt-id wfC)) =
  inj₁ (_ , (_ ∎) ,
    subst (λ q → _ ⊢ _ ⊑ _ ⦂ q)
      (sim-left-w03-⊑ᵢ-proof-irrel pB p)
      (⊑downL {pB = pB} Φ lenΦ rel hd))
sim-right-w06-id-down-core {p = p}
    (⊑downR {pA = pA} Φ lenΦ rel (UpDown.wt-id wfC)) =
  inj₁ (_ , (_ ∎) ,
    subst (λ q → _ ⊢ _ ⊑ _ ⦂ q)
      (sim-left-w03-⊑ᵢ-proof-irrel pA p) rel)
sim-right-w06-id-down-core (⊑downL Φ lenΦ rel hd)
    with sim-right-w06-id-down-core rel
sim-right-w06-id-down-core (⊑downL Φ lenΦ rel hd)
  | inj₁ (N , M↠N , N⊑V) =
  inj₁ (N down _ , down-↠ M↠N , ⊑downL Φ lenΦ N⊑V hd)
sim-right-w06-id-down-core (⊑downL Φ lenΦ rel hd)
  | inj₂ (ℓ , M↠blame) =
  inj₂ (ℓ ,
    multi-trans (down-↠ M↠blame)
      ((blame ℓ down _) —→⟨ id-step blame-down ⟩ blame ℓ ∎))
sim-right-w06-id-down-core (⊑blameR hM) =
  inj₂ (_ , (blame _ ∎))

-- Supports SimRight.agda R06 (line 55): package the core same-store result in
-- the public `sim-right` existential shape.
sim-right-w06-id-down :
  ∀ {Ψˡ Σˡ V M C A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψˡ , Σˡ , [] , [] ⟫ ⊢ M ⊑ (V down Down.id C) ⦂ p →
  (Σ[ Ψˡ″ ∈ SealCtx ]
    Σ[ Ψˡ≤Ψˡ″ ∈ Ψˡ ≤ Ψˡ″ ]
    Σ[ Σˡ′ ∈ Store ]
    Σ[ N ∈ Term ]
      ((Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
       (⟪ 0 , Ψˡ″ , Σˡ′ , [] , [] ⟫ ⊢ N ⊑ V ⦂ p)))
  ⊎ (Σ[ Σˡ′ ∈ Store ] Σ[ ℓ ∈ Label ] (Σˡ ∣ M —↠ Σˡ′ ∣ blame ℓ))
sim-right-w06-id-down {Ψˡ = Ψˡ} {Σˡ = Σˡ} rel
    with sim-right-w06-id-down-core rel
sim-right-w06-id-down {Ψˡ = Ψˡ} {Σˡ = Σˡ} rel
  | inj₁ (N , M↠N , N⊑V) =
  inj₁ (Ψˡ , ≤-refl , Σˡ , N , M↠N , N⊑V)
sim-right-w06-id-down {Σˡ = Σˡ} rel | inj₂ (ℓ , M↠blame) =
  inj₂ (Σˡ , ℓ , M↠blame)

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot
