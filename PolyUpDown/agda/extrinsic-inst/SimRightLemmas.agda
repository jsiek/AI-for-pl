module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

open import Data.List using ([])
open import Data.Product using (_,_; Σ-syntax)

open import Types
open import UpDown using (Label; Up; Down)
open import Store using (Store)
open import ImprecisionIndexed
open import Terms using (Term; blame; _·_; _⦂∀_[_]; _up_; _down_)
open import TermImprecisionIndexed
open import ReductionFresh

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

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Supports R11 (`blame-·₁`): transport a blame trace through left contexts.
sim-right-w11-up-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {ℓ : Label} {p : Up} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M up p) —↠ Σ′ ∣ blame ℓ
sim-right-w11-up-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ up p) —→⟨ id-step blame-up ⟩ ((blame ℓ) ∎)
sim-right-w11-up-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ sim-right-w11-up-blame-↠ M′↠blame

-- Supports R11 (`blame-·₁`): transport a blame trace through left contexts.
sim-right-w11-down-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {ℓ : Label} {p : Down} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M down p) —↠ Σ′ ∣ blame ℓ
sim-right-w11-down-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ down p) —→⟨ id-step blame-down ⟩ ((blame ℓ) ∎)
sim-right-w11-down-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M down p) —→⟨ ξ-down M→M′ ⟩
    sim-right-w11-down-blame-↠ M′↠blame

-- Supports R11 (`blame-·₁`): transport a trace through type application.
sim-right-w11-tyapp-↠ :
  ∀ {Σ Σ′ : Store} {M N : Term} {B T : Ty} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (N ⦂∀ B [ T ])
sim-right-w11-tyapp-↠ {B = B} {T = T} (M ∎) = (M ⦂∀ B [ T ]) ∎
sim-right-w11-tyapp-↠ {B = B} {T = T} (M —→⟨ M→M′ ⟩ M′↠N) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
    sim-right-w11-tyapp-↠ M′↠N

-- Supports R11 (`blame-·₁`): transport a blame trace through type app.
sim-right-w11-tyapp-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {ℓ : Label} {B T : Ty} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
sim-right-w11-tyapp-blame-↠ {ℓ = ℓ} {B = B} {T = T} (_ ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ ((blame ℓ) ∎)
sim-right-w11-tyapp-blame-↠ {B = B} {T = T}
    (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
    sim-right-w11-tyapp-blame-↠ M′↠blame

-- Supports R11 (`blame-·₁`): transport a function-position blame trace.
sim-right-w11-appL-blame-↠ :
  ∀ {Σ Σ′ : Store} {L M : Term} {ℓ : Label} →
  Σ ∣ L —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (L · M) —↠ Σ′ ∣ blame ℓ
sim-right-w11-appL-blame-↠ {M = M} {ℓ = ℓ} (_ ∎) =
  (blame ℓ · M) —→⟨ id-step blame-·₁ ⟩ ((blame ℓ) ∎)
sim-right-w11-appL-blame-↠ {M = M} (L —→⟨ L→L′ ⟩ L′↠blame) =
  (L · M) —→⟨ ξ-·₁ L→L′ ⟩
    sim-right-w11-appL-blame-↠ L′↠blame

-- Supports R11 (`blame-·₁`): right blame implies left blames.
sim-right-w11-right-blame-left-blames :
  ∀ {Ψ Σ M ℓ A B} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
  Σ[ Σ′ ∈ Store ]
    Σ[ ℓ′ ∈ Label ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ′)
sim-right-w11-right-blame-left-blames (⊑⦂∀-ν A B p rel wfA hT inst)
    with sim-right-w11-right-blame-left-blames rel
sim-right-w11-right-blame-left-blames (⊑⦂∀-ν A B p rel wfA hT inst)
  | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w11-tyapp-blame-↠ M↠blame
sim-right-w11-right-blame-left-blames (⊑upL Φ lenΦ rel hu)
    with sim-right-w11-right-blame-left-blames rel
sim-right-w11-right-blame-left-blames (⊑upL Φ lenΦ rel hu)
  | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w11-up-blame-↠ M↠blame
sim-right-w11-right-blame-left-blames (⊑downL Φ lenΦ rel hd)
    with sim-right-w11-right-blame-left-blames rel
sim-right-w11-right-blame-left-blames (⊑downL Φ lenΦ rel hd)
  | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w11-down-blame-↠ M↠blame
sim-right-w11-right-blame-left-blames (⊑blameR {ℓ = ℓ′} hM) =
  _ , ℓ′ , ((blame ℓ′) ∎)

-- Worker W12 helper slot
