module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

open import Data.List using ([])
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import UpDown using (Up; Down; Label; wt-id)
open import Store using (Store)
open import ImprecisionIndexed
open import Terms using (Term; blame; _up_; _down_; _⦂∀_[_])
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

-- Supports SimRight.agda R05 (line 53): lift a blame path through an
-- enclosing up cast while eliminating right identity-up casts.
sim-right-w05-up-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {ℓ : Label} {p : Up} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M up p) —↠ Σ′ ∣ blame ℓ
sim-right-w05-up-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ up p) —→⟨ id-step blame-up ⟩ blame ℓ ∎
sim-right-w05-up-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ sim-right-w05-up-blame-↠ M′↠blame

-- Supports SimRight.agda R05 (line 53): lift a blame path through an
-- enclosing down cast while eliminating right identity-up casts.
sim-right-w05-down-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {ℓ : Label} {p : Down} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M down p) —↠ Σ′ ∣ blame ℓ
sim-right-w05-down-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ down p) —→⟨ id-step blame-down ⟩ blame ℓ ∎
sim-right-w05-down-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M down p) —→⟨ ξ-down M→M′ ⟩ sim-right-w05-down-blame-↠ M′↠blame

-- Supports SimRight.agda R05 (line 53): lift reduction through type
-- application for the `⊑⦂∀-ν` asymmetric case.
sim-right-w05-tyapp-↠ :
  ∀ {Σ Σ′ : Store} {M N : Term} {B T : Ty} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (N ⦂∀ B [ T ])
sim-right-w05-tyapp-↠ (M ∎) = (M ⦂∀ _ [ _ ]) ∎
sim-right-w05-tyapp-↠ (M —→⟨ M→M′ ⟩ M′↠N) =
  (M ⦂∀ _ [ _ ]) —→⟨ ξ-·α M→M′ ⟩ sim-right-w05-tyapp-↠ M′↠N

-- Supports SimRight.agda R05 (line 53): lift blame through type application
-- for the `⊑⦂∀-ν` asymmetric case.
sim-right-w05-tyapp-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {ℓ : Label} {B T : Ty} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
sim-right-w05-tyapp-blame-↠ {ℓ = ℓ} {B = B} {T = T} (_ ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎
sim-right-w05-tyapp-blame-↠ {B = B} {T = T} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
  sim-right-w05-tyapp-blame-↠ M′↠blame

-- Supports SimRight.agda R05 (line 53): eliminate a right identity-up cast,
-- commuting through left-only wrappers.
sim-right-w05-id-up :
  ∀ {Ψ Σˡ V M C A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ M ⊑ (V up UpDown.id C) ⦂ p →
  (Σ[ N ∈ Term ]
    ((Σˡ ∣ M —↠ Σˡ ∣ N) ×
     (⟪ 0 , Ψ , Σˡ , [] , [] ⟫ ⊢ N ⊑ V ⦂ p)))
  ⊎ (Σ[ Σᵇ ∈ Store ] Σ[ ℓ ∈ Label ] (Σˡ ∣ M —↠ Σᵇ ∣ blame ℓ))
sim-right-w05-id-up (⊑up Φ lenΦ rel hu (wt-id wfA)) =
  inj₁ (_ , (_ ∎) , ⊑upL Φ lenΦ rel hu)
sim-right-w05-id-up {p = p} (⊑upR {pA = pA} Φ lenΦ rel (wt-id wfA)) =
  inj₁
    (_ , (_ ∎) ,
     subst (λ q → _ ⊢ _ ⊑ _ ⦂ q)
       (sim-left-w03-⊑ᵢ-proof-irrel pA p) rel)
sim-right-w05-id-up (⊑upL Φ lenΦ rel hu)
    with sim-right-w05-id-up rel
sim-right-w05-id-up (⊑upL Φ lenΦ rel hu)
  | inj₁ (N , M↠N , N⊑V) =
  inj₁ (_ , up-↠ M↠N , ⊑upL Φ lenΦ N⊑V hu)
sim-right-w05-id-up (⊑upL Φ lenΦ rel hu)
  | inj₂ (Σᵇ , ℓ , M↠blame) =
  inj₂ (Σᵇ , ℓ , sim-right-w05-up-blame-↠ M↠blame)
sim-right-w05-id-up (⊑downL Φ lenΦ rel hd)
    with sim-right-w05-id-up rel
sim-right-w05-id-up (⊑downL Φ lenΦ rel hd)
  | inj₁ (N , M↠N , N⊑V) =
  inj₁ (_ , down-↠ M↠N , ⊑downL Φ lenΦ N⊑V hd)
sim-right-w05-id-up (⊑downL Φ lenΦ rel hd)
  | inj₂ (Σᵇ , ℓ , M↠blame) =
  inj₂ (Σᵇ , ℓ , sim-right-w05-down-blame-↠ M↠blame)
sim-right-w05-id-up (⊑⦂∀-ν A B pν rel wfA hT inst)
    with sim-right-w05-id-up rel
sim-right-w05-id-up (⊑⦂∀-ν A B pν rel wfA hT inst)
  | inj₁ (N , M↠N , N⊑V) =
  inj₁
    (_ , sim-right-w05-tyapp-↠ M↠N ,
     ⊑⦂∀-ν A B pν N⊑V wfA hT inst)
sim-right-w05-id-up (⊑⦂∀-ν A B pν rel wfA hT inst)
  | inj₂ (Σᵇ , ℓ , M↠blame) =
  inj₂ (Σᵇ , ℓ , sim-right-w05-tyapp-blame-↠ M↠blame)
sim-right-w05-id-up (⊑blameR {ℓ = ℓ} hM) =
  inj₂ (_ , ℓ , (blame ℓ ∎))

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot
