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

open import Types
open import UpDown using (Down; Label; Up)
open import Store using (_⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans)
open import ImprecisionIndexed
open import Terms using (Term; blame; _·_; _⦂∀_[_]; _up_; _down_; ⊢blame)
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

SimRightBlames : Store → Term → Set
SimRightBlames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

-- Supports R22: store growth extracted from a multi-step reduction.
sim-right-w09-multi-store-growth :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ⊆ˢ Σ′
sim-right-w09-multi-store-growth (M ∎) = ⊆ˢ-refl
sim-right-w09-multi-store-growth (M —→⟨ M→M′ ⟩ M′↠N) =
  ⊆ˢ-trans (store-growth M→M′) (sim-right-w09-multi-store-growth M′↠N)

-- Supports R22: lift a blame trace through the function side of application.
sim-right-w09-appL-blames :
  ∀ {Σ : Store} {L M : Term} →
  SimRightBlames Σ L →
  SimRightBlames Σ (L · M)
sim-right-w09-appL-blames {M = M} (Σ′ , ℓ , L↠blame) =
  Σ′ , ℓ ,
  multi-trans (appL-↠ {M = M} L↠blame)
    ((blame ℓ · M) —→⟨ id-step blame-·₁ ⟩ blame ℓ ∎)

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
  ∀ {Ψ : SealCtx} {Σ : Store} {M : Term} {A B : Ty}
    {p : [] ⊢ A ⊑ᵢ B} {ℓ : Label} →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
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
  ∀ {Ψ : SealCtx} {Σ : Store} {M : Term} {A B C T : Ty}
    {p : [] ⊢ A ⊑ᵢ B} {ℓ : Label} →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ (blame ℓ ⦂∀ C [ T ]) ⦂ p →
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
  ∀ {Ψ : SealCtx} {Σ : Store} {M : Term} {A B C T : Ty}
    {p : [] ⊢ A ⊑ᵢ B} {ℓ : Label} →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ (blame ℓ ⦂∀ C [ T ]) ⦂ p →
  (Σ[ Ψ″ ∈ SealCtx ]
    Σ[ Ψ≤Ψ″ ∈ Ψ ≤ Ψ″ ]
    Σ[ Σ′ ∈ Store ]
    Σ[ N ∈ Term ]
      ((Σ ∣ M —↠ Σ′ ∣ N) ×
       (⟪ 0 , Ψ″ , Σ′ , [] , [] ⟫ ⊢ N ⊑ blame ℓ ⦂ p)))
  ⊎ SimRightBlames Σ M
sim-right-w09-r13 rel =
  inj₂ (sim-right-w09-right-blame-typeapp-blames rel)

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot
