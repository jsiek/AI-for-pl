module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-right` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-right-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `SimRight.agda` hole lines it supports.

open import Data.List using (List; length; _++_; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-comm; m+[n∸m]≡n)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; trans)

open import Types
open import Store using (_⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans)
open import UpDown using (Up; Down; Label; CastPerm; cast-tag; _∣_∣_∣_⊢_⦂_⊑_)
open import Terms using (Term; _up_; _down_; _⦂∀_[_]; blame)
open import ImprecisionIndexed
open import TermImprecisionIndexed
open import ReductionFresh
open import PreservationFresh using (length-append-tag; wkΨ-cast-tag-⊑)

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

-- Worker W12 helper slot

-- R25: weaken two up-cast typings through the same generated tag context.
sim-right-w12-wkΨ-cast-tag-⊑-+₂ :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}
    {A B A′ B′ : Ty}{u u′ : Up} →
  (k : ℕ) →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u ⦂ A ⊑ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ k + Ψ) ×
     (Δ ∣ (k + Ψ) ∣ Σ ∣ Φ′ ⊢ u ⦂ A ⊑ B) ×
     (Δ ∣ (k + Ψ) ∣ Σ ∣ Φ′ ⊢ u′ ⦂ A′ ⊑ B′))
sim-right-w12-wkΨ-cast-tag-⊑-+₂ zero lenΦ hu hu′ =
  _ , lenΦ , hu , hu′
sim-right-w12-wkΨ-cast-tag-⊑-+₂ (suc k) lenΦ hu hu′
    with sim-right-w12-wkΨ-cast-tag-⊑-+₂ k lenΦ hu hu′
sim-right-w12-wkΨ-cast-tag-⊑-+₂ (suc k) lenΦ hu hu′
  | Φ′ , lenΦ′ , hu″ , hu′″ =
  (Φ′ ++ cast-tag ∷ []) ,
  trans (length-append-tag Φ′) (cong suc lenΦ′) ,
  wkΨ-cast-tag-⊑ hu″ ,
  wkΨ-cast-tag-⊑ hu′″

-- R25.
sim-right-w12-wkΨ-cast-tag-⊑-≤₂ :
  ∀ {Δ Ψ Ψ′}{Σ : Store}{Φ : List CastPerm}
    {A B A′ B′ : Ty}{u u′ : Up} →
  Ψ ≤ Ψ′ →
  length Φ ≡ Ψ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u ⦂ A ⊑ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
  Σ[ Φ′ ∈ List CastPerm ]
    ((length Φ′ ≡ Ψ′) ×
     (Δ ∣ Ψ′ ∣ Σ ∣ Φ′ ⊢ u ⦂ A ⊑ B) ×
     (Δ ∣ Ψ′ ∣ Σ ∣ Φ′ ⊢ u′ ⦂ A′ ⊑ B′))
sim-right-w12-wkΨ-cast-tag-⊑-≤₂ {Δ} {Ψ} {Ψ′} {Σ} {A = A}
    {B = B} {A′ = A′} {B′ = B′} {u = u} {u′ = u′}
    Ψ≤Ψ′ lenΦ hu hu′
    with sim-right-w12-wkΨ-cast-tag-⊑-+₂ (Ψ′ ∸ Ψ) lenΦ hu hu′
sim-right-w12-wkΨ-cast-tag-⊑-≤₂ {Δ} {Ψ} {Ψ′} {Σ} {A = A}
    {B = B} {A′ = A′} {B′ = B′} {u = u} {u′ = u′}
    Ψ≤Ψ′ lenΦ hu hu′
  | Φ′ , lenΦ′ , hu″ , hu′″ =
  let eq = trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′) in
  Φ′ , trans lenΦ′ eq ,
  subst (λ q → Δ ∣ q ∣ Σ ∣ Φ′ ⊢ u ⦂ A ⊑ B) eq hu″ ,
  subst (λ q → Δ ∣ q ∣ Σ ∣ Φ′ ⊢ u′ ⦂ A′ ⊑ B′) eq hu′″

-- R25: extract store growth from a left multi-step produced by the recursive
-- simulation call.
sim-right-w12-multi-store-growth :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ⊆ˢ Σ′
sim-right-w12-multi-store-growth (M ∎) = ⊆ˢ-refl
sim-right-w12-multi-store-growth (M —→⟨ M→M′ ⟩ M′↠N) =
  ⊆ˢ-trans (store-growth M→M′) (sim-right-w12-multi-store-growth M′↠N)

-- R25: lift a successful left trace through type application when a
-- left-only `⊑⦂∀-ν` wrapper surrounds the right `ξ-up` step.
sim-right-w12-tyapp-↠ :
  ∀ {Σ Σ′ : Store} {M N : Term} {B T : Ty} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ (N ⦂∀ B [ T ])
sim-right-w12-tyapp-↠ {B = B} {T = T} (M ∎) =
  (M ⦂∀ B [ T ]) ∎
sim-right-w12-tyapp-↠ {B = B} {T = T}
    (M —→⟨ M→M′ ⟩ M′↠N) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
  sim-right-w12-tyapp-↠ M′↠N

-- R14: propagate a left-side blame trace through wrappers introduced only on
-- the left of a term-imprecision derivation.
sim-right-w12-up-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {u : Up} {ℓ : Label} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M up u) —↠ Σ′ ∣ blame ℓ
sim-right-w12-up-blame-↠ {u = u} {ℓ = ℓ} (M ∎) =
  (blame ℓ up u) —→⟨ id-step blame-up ⟩ blame ℓ ∎
sim-right-w12-up-blame-↠ {u = u} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up u) —→⟨ ξ-up M→M′ ⟩
  sim-right-w12-up-blame-↠ M′↠blame

-- R14.
sim-right-w12-down-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {d : Down} {ℓ : Label} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M down d) —↠ Σ′ ∣ blame ℓ
sim-right-w12-down-blame-↠ {d = d} {ℓ = ℓ} (M ∎) =
  (blame ℓ down d) —→⟨ id-step blame-down ⟩ blame ℓ ∎
sim-right-w12-down-blame-↠ {d = d} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M down d) —→⟨ ξ-down M→M′ ⟩
  sim-right-w12-down-blame-↠ M′↠blame

-- R14.
sim-right-w12-tyapp-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {B T : Ty} {ℓ : Label} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
sim-right-w12-tyapp-blame-↠ {B = B} {T = T} {ℓ = ℓ} (M ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎
sim-right-w12-tyapp-blame-↠ {B = B} {T = T}
    (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
  sim-right-w12-tyapp-blame-↠ M′↠blame

-- R14: if the more-imprecise side is already blame, the precise side either is
-- blame or reaches blame after stripping left-only wrappers.
sim-right-w12-right-blame-blames :
  ∀ {E M A B ℓ} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ blame ℓ ⦂ p →
  Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ]
    (TPEnv.store E ∣ M —↠ Σ′ ∣ blame ℓ′)
sim-right-w12-right-blame-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-tyapp-blame-↠ M↠blame
sim-right-w12-right-blame-blames (⊑upL Φ lenΦ rel hu)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-blames (⊑upL Φ lenΦ rel hu)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-up-blame-↠ M↠blame
sim-right-w12-right-blame-blames (⊑downL Φ lenΦ rel hd)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-blames (⊑downL Φ lenΦ rel hd)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-down-blame-↠ M↠blame
sim-right-w12-right-blame-blames (⊑blameR {ℓ = ℓ′} hM) =
  _ , ℓ′ , (blame ℓ′ ∎)

-- R14: inversion for a right-side `blame up _` redex.
sim-right-w12-right-blame-up-blames :
  ∀ {E M A B ℓ u′} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ ((blame ℓ) up u′) ⦂ p →
  Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ]
    (TPEnv.store E ∣ M —↠ Σ′ ∣ blame ℓ′)
sim-right-w12-right-blame-up-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
    with sim-right-w12-right-blame-up-blames rel
sim-right-w12-right-blame-up-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-tyapp-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑up Φ lenΦ rel hu hu′)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-up-blames (⊑up Φ lenΦ rel hu hu′)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-up-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑upL Φ lenΦ rel hu)
    with sim-right-w12-right-blame-up-blames rel
sim-right-w12-right-blame-up-blames (⊑upL Φ lenΦ rel hu)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-up-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑upR Φ lenΦ rel hu′) =
  sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-up-blames (⊑downL Φ lenΦ rel hd)
    with sim-right-w12-right-blame-up-blames rel
sim-right-w12-right-blame-up-blames (⊑downL Φ lenΦ rel hd)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-down-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑blameR {ℓ = ℓ′} hM) =
  _ , ℓ′ , (blame ℓ′ ∎)
