module DenotationMeta where

-- File Charter:
--   * The main properties of the denotation (Denotation.agda) of PolyCν,
--     stated for closed programs run from the empty store, as thin
--     wrappers around the proofs:
--       - consistency (proof/DenotConsistency.agda);
--       - soundness for reduction, for well-typed programs
--         (proof/DenotSoundness.agda): a run to a value gives an element
--         of the denotation with its observation; a run to ℧ gives err;
--       - adequacy, for Scoped programs, without typing
--         (proof/DenotAdequacy.agda): an element of the denotation comes
--         from a run to a value with its observation, ending in a store
--         of the element's counter; err comes from a run to ℧;
--       - elaborated programs are Scoped (proof/ScopedProps.agda).
--   * The invariant Scoped is defined in DenotInvariants.agda.

open import Data.List using ([]; length)
open import Data.Product using (∃-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Terms
open import Reduction
open import Typing using (_∣_∣_⊢_⦂_)
open import StoreWf using (wfˢ[])
open import GraphModel
open import Denotation
open import GradualityDefinitions using (observe)
open import GradualTerms using (_∣_⊢ᴳ_⦂_)
open import Compile using (elab)
open import CompileInvariants using (wfc[])
open import DenotInvariants using (Scoped)
import proof.DenotConsistency as C
import proof.DenotSoundness as S
import proof.DenotAdequacy as A
import proof.ScopedProps as SP

------------------------------------------------------------------------
-- Consistency
------------------------------------------------------------------------

denotation-consistent : ∀ M θ ρ n
  → (∀ x → Consistent (ρ x))
  → Consistentᴿ (⟦ M ⟧ θ ρ n)
denotation-consistent M θ ρ n cρ = C.⟦⟧-consistent M θ {ρ} {n} cρ

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------

sound-val : ∀ {M V Σ′ A}
  → [] ∣ [] ∣ [] ⊢ M ⦂ A
  → [] ▷ M —↠ Σ′ ▷ V
  → (vV : Value V)
  → ∃[ v ] (ret v (length Σ′) ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ 0 × obs v ≡ observe vV)
sound-val ⊢M M↠V vV = S.sound-val wfˢ[] ⊢M M↠V vV

sound-℧ : ∀ {M Σ′ A}
  → [] ∣ [] ∣ [] ⊢ M ⦂ A
  → [] ▷ M —↠ Σ′ ▷ ℧
  → err ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ 0
sound-℧ ⊢M M↠℧ = S.sound-℧ wfˢ[] ⊢M M↠℧

------------------------------------------------------------------------
-- Adequacy
------------------------------------------------------------------------

adequacy-val : ∀ {M v m}
  → Scoped 0 M
  → ret v m ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ 0
  → ∃[ Σ′ ] ∃[ V ] ∃[ vV ]
      (([] ▷ M —↠ Σ′ ▷ V) × length Σ′ ≡ m × obs v ≡ observe {V} vV)
adequacy-val sc v∈ = A.adequacy-val {Σ = []} sc v∈

adequacy-err : ∀ {M}
  → Scoped 0 M
  → err ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ 0
  → ∃[ Σ′ ] ([] ▷ M —↠ Σ′ ▷ ℧)
adequacy-err sc e∈ = A.adequacy-err {Σ = []} sc e∈

------------------------------------------------------------------------
-- Elaborated programs are Scoped
------------------------------------------------------------------------

elab-scoped : ∀ {M A} (d : [] ∣ [] ⊢ᴳ M ⦂ A) → Scoped 0 (elab d)
elab-scoped d = SP.elab-Scoped wf[] wfc[] d
