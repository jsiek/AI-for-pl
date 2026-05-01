module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

open import Data.List using ([])
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import UpDown using (Down; Label; Up)
open import Store using (StoreWf; _⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans)
open import ImprecisionIndexed
open import Terms using (Term; Value; blame; _·_; _⦂∀_[_]; _up_; _down_; ⊢blame)
open import TermImprecisionIndexed
open import ReductionFresh

SimRightBlames : Store → Term → Set
SimRightBlames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

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

-- Supports R23: store growth for the left multi-step witnesses introduced
-- while catching the function position up to a value.
sim-right-w03-multi-store-growth :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ⊆ˢ Σ′
sim-right-w03-multi-store-growth (M ∎) = ⊆ˢ-refl
sim-right-w03-multi-store-growth (M —→⟨ M→M′ ⟩ M′↠N) =
  ⊆ˢ-trans (store-growth M→M′)
            (sim-right-w03-multi-store-growth M′↠N)

-- Supports R23: prepend an already-known left trace to a later blame trace.
sim-right-w03-prefix-blames :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  SimRightBlames Σ′ N →
  SimRightBlames Σ M
sim-right-w03-prefix-blames M↠N (Σᵇ , ℓ , N↠blame) =
  Σᵇ , ℓ , multi-trans M↠N N↠blame

-- Supports R23: lift a blame trace through application left congruence.
sim-right-w03-appL-blames :
  ∀ {Σ : Store} {L M : Term} →
  SimRightBlames Σ L →
  SimRightBlames Σ (L · M)
sim-right-w03-appL-blames {M = M} (Σ′ , ℓ , L↠blame) =
  Σ′ , ℓ ,
  multi-trans (appL-↠ {M = M} L↠blame)
    ((blame ℓ · M) —→⟨ id-step blame-·₁ ⟩ blame ℓ ∎)

-- Supports R23: lift a blame trace through application right congruence.
sim-right-w03-appR-blames :
  ∀ {Σ : Store} {V M : Term} →
  Value V →
  SimRightBlames Σ M →
  SimRightBlames Σ (V · M)
sim-right-w03-appR-blames {V = V} vV (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (appR-↠ vV M↠blame)
    ((V · blame ℓ) —→⟨ id-step (blame-·₂ vV) ⟩ blame ℓ ∎)

postulate
  -- Supports R23: when the right function is already a value, the left
  -- function can catch up to a related value or reach blame.
  sim-right-w03-left-value-catchup-or-blame :
    ∀ {Ψ Σ M V A B} →
    Value V →
    StoreWf 0 Ψ Σ →
    ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ V ⦂ A ⊑ B →
    (Σ[ Ψ′ ∈ SealCtx ]
      Σ[ Ψ≤Ψ′ ∈ Ψ ≤ Ψ′ ]
      Σ[ Σ′ ∈ Store ]
      Σ[ wfΣ′ ∈ StoreWf 0 Ψ′ Σ′ ]
      Σ[ W ∈ Term ]
        (Value W ×
         (Σ ∣ M —↠ Σ′ ∣ W) ×
         (⟪ 0 , Ψ′ , Σ′ , [] , [] , plain-[] , refl ⟫ ⊢ W ⊑ V ⦂ A ⊑ B)))
    ⊎ SimRightBlames Σ M

-- Worker W04 helper slot

-- Worker W05 helper slot

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Supports R13: lift inner blame traces through type application.
sim-right-w09-typeapp-↠ :
  ∀ {Σ Σ′ : Store} {M N : Term} {B T : Ty} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (N ⦂∀ B [ T ])
sim-right-w09-typeapp-↠ {B = B} {T = T} (M ∎) = (M ⦂∀ B [ T ]) ∎
sim-right-w09-typeapp-↠ {B = B} {T = T} (M —→⟨ red ⟩ M↠N) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α red ⟩ sim-right-w09-typeapp-↠ M↠N

-- Supports R13: lift a blame trace through type application.
sim-right-w09-typeapp-blames :
  ∀ {Σ : Store} {M : Term} {B T : Ty} →
  SimRightBlames Σ M →
  SimRightBlames Σ (M ⦂∀ B [ T ])
sim-right-w09-typeapp-blames {B = B} {T = T} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (sim-right-w09-typeapp-↠ M↠blame)
    ((blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎)

-- Supports R13: lift a blame trace through an up cast.
sim-right-w09-up-blames :
  ∀ {Σ : Store} {M : Term} {u : Up} →
  SimRightBlames Σ M →
  SimRightBlames Σ (M up u)
sim-right-w09-up-blames {u = u} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (up-↠ M↠blame)
    ((blame ℓ up u) —→⟨ id-step blame-up ⟩ blame ℓ ∎)

-- Supports R13: lift a blame trace through a down cast.
sim-right-w09-down-blames :
  ∀ {Σ : Store} {M : Term} {d : Down} →
  SimRightBlames Σ M →
  SimRightBlames Σ (M down d)
sim-right-w09-down-blames {d = d} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (down-↠ M↠blame)
    ((blame ℓ down d) —→⟨ id-step blame-down ⟩ blame ℓ ∎)

-- Supports R13: if the right term is blame, the left term can reach blame.
sim-right-w09-right-blame-rel-blames :
  ∀ {Ψ : SealCtx} {Σ : Store} {M : Term} {A B : Ty} {ℓ : Label} →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ blame ℓ ⦂ A ⊑ B →
  SimRightBlames Σ M
sim-right-w09-right-blame-rel-blames (⊑⦂∀-ν A B p rel wfA hT inst) =
  sim-right-w09-typeapp-blames (sim-right-w09-right-blame-rel-blames rel)
sim-right-w09-right-blame-rel-blames (⊑upL Φ lenΦ rel hu) =
  sim-right-w09-up-blames (sim-right-w09-right-blame-rel-blames rel)
sim-right-w09-right-blame-rel-blames (⊑downL Φ lenΦ rel hd) =
  sim-right-w09-down-blames (sim-right-w09-right-blame-rel-blames rel)
sim-right-w09-right-blame-rel-blames (⊑blameR {ℓ = ℓ′} hM) =
  _ , ℓ′ , (blame ℓ′ ∎)

-- Supports R13: right-side `blame-·α` leaves the left with a blame trace.
sim-right-w09-right-blame-typeapp-blames :
  ∀ {Ψ : SealCtx} {Σ : Store} {M : Term} {A B C T : Ty} {ℓ : Label} →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ (blame ℓ ⦂∀ C [ T ]) ⦂ A ⊑ B →
  SimRightBlames Σ M
sim-right-w09-right-blame-typeapp-blames (⊑⦂∀ rel wfA wfB hT) =
  sim-right-w09-typeapp-blames (sim-right-w09-right-blame-rel-blames rel)
sim-right-w09-right-blame-typeapp-blames (⊑⦂∀-ν A B p rel wfA hT inst) =
  sim-right-w09-typeapp-blames
    (sim-right-w09-right-blame-typeapp-blames rel)
sim-right-w09-right-blame-typeapp-blames (⊑upL Φ lenΦ rel hu) =
  sim-right-w09-up-blames (sim-right-w09-right-blame-typeapp-blames rel)
sim-right-w09-right-blame-typeapp-blames (⊑downL Φ lenΦ rel hd) =
  sim-right-w09-down-blames (sim-right-w09-right-blame-typeapp-blames rel)
sim-right-w09-right-blame-typeapp-blames (⊑blameR {ℓ = ℓ′} hM) =
  _ , ℓ′ , (blame ℓ′ ∎)

-- Supports R13: package the right-side `blame-·α` case result.
sim-right-w09-r13 :
  ∀ {Ψ : SealCtx} {Σ : Store} {M : Term} {A B C T : Ty} {ℓ : Label} →
  ⟪ 0 , Ψ , Σ , [] , [] , plain-[] , refl ⟫ ⊢ M ⊑ (blame ℓ ⦂∀ C [ T ]) ⦂ A ⊑ B →
  (Σ[ Ψ″ ∈ SealCtx ]
    Σ[ Ψ≤Ψ″ ∈ Ψ ≤ Ψ″ ]
    Σ[ Σ′ ∈ Store ]
    Σ[ N ∈ Term ]
      ((Σ ∣ M —↠ Σ′ ∣ N) ×
       (⟪ 0 , Ψ″ , Σ′ , [] , [] , plain-[] , refl ⟫ ⊢ N ⊑ blame ℓ ⦂ A ⊑ B)))
  ⊎ SimRightBlames Σ M
sim-right-w09-r13 rel =
  inj₂ (sim-right-w09-right-blame-typeapp-blames rel)

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot
