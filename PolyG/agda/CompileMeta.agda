module CompileMeta where

-- File Charter:
--   * Public metatheory of elaboration (Compile.agda) from PolyGν to
--     PolyCν: elaboration preserves typing, the precision derivation of
--     a surface precision judgment relates the two sides' types, and
--     elaboration preserves term precision (thesis Lemma 218).
--   * Each theorem is stated in full under the context invariants of
--     CompileInvariants.agda, and again for closed terms.
--   * Thin wrappers around proof/CompileTyping.agda and
--     proof/CompilePrecision.agda.

open import Data.List using ([])

open import Types
open import Typing using (_∣_∣_⊢_⦂_)
open import GradualTerms
open import Compile using (elab)
open import TermPrecision using (_∣_⊢_⊑_⦂_; psize)
open import GradualTermPrecision using (_∣_⊢_⊑ᴳ_⦂_)
open import CompileInvariants
open import proof.CompileTyping using (elab-⊢)
open import proof.CompilePrecision using (⊑ᴳ-types; elab-⊑)

------------------------------------------------------------------------
-- Elaboration preserves typing
------------------------------------------------------------------------

elab-preserves-typing : ∀ {Σ Δ Γ M A}
  → WfTyEnv Δ
  → WfCtx (tsize Δ) Γ
  → (d : Δ ∣ Γ ⊢ᴳ M ⦂ A)
  → Σ ∣ Δ ∣ Γ ⊢ elab d ⦂ A
elab-preserves-typing = elab-⊢

elab-preserves-typing-closed : ∀ {Σ M A}
  → (d : [] ∣ [] ⊢ᴳ M ⦂ A)
  → Σ ∣ [] ∣ [] ⊢ elab d ⦂ A
elab-preserves-typing-closed d = elab-⊢ wf[] wfc[] d

------------------------------------------------------------------------
-- Surface precision relates the types of the two sides
------------------------------------------------------------------------

⊑ᴳ-relates-types : ∀ {Δ⊑ Γ⊑ Δ Δ′ Γ Γ′ M M′ A A′ p}
  {d : Δ ∣ Γ ⊢ᴳ M ⦂ A} {d′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′}
  → Δ⊑ ⦂ Δ ⊑ᵉ Δ′
  → psize Δ⊑ ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′
  → Δ⊑ ∣ Γ⊑ ⊢ d ⊑ᴳ d′ ⦂ p
  → psize Δ⊑ ⊢ p ⦂ A ⊑ A′
⊑ᴳ-relates-types = ⊑ᴳ-types

⊑ᴳ-relates-types-closed : ∀ {M M′ A A′ p}
  {d : [] ∣ [] ⊢ᴳ M ⦂ A} {d′ : [] ∣ [] ⊢ᴳ M′ ⦂ A′}
  → [] ∣ [] ⊢ d ⊑ᴳ d′ ⦂ p
  → 0 ⊢ p ⦂ A ⊑ A′
⊑ᴳ-relates-types-closed d⊑d′ = ⊑ᴳ-types ⊑ᵉ[] ⊑ᶜ[] d⊑d′

------------------------------------------------------------------------
-- Elaboration preserves precision (thesis Lemma 218)
------------------------------------------------------------------------

elab-preserves-precision : ∀ {Δ⊑ Γ⊑ Δ Δ′ Γ Γ′ M M′ A A′ p}
  {d : Δ ∣ Γ ⊢ᴳ M ⦂ A} {d′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′}
  → Δ⊑ ⦂ Δ ⊑ᵉ Δ′
  → psize Δ⊑ ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′
  → Δ⊑ ∣ Γ⊑ ⊢ d ⊑ᴳ d′ ⦂ p
  → Δ⊑ ∣ Γ⊑ ⊢ elab d ⊑ elab d′ ⦂ p
elab-preserves-precision = elab-⊑

elab-preserves-precision-closed : ∀ {M M′ A A′ p}
  {d : [] ∣ [] ⊢ᴳ M ⦂ A} {d′ : [] ∣ [] ⊢ᴳ M′ ⦂ A′}
  → [] ∣ [] ⊢ d ⊑ᴳ d′ ⦂ p
  → [] ∣ [] ⊢ elab d ⊑ elab d′ ⦂ p
elab-preserves-precision-closed d⊑d′ = elab-⊑ ⊑ᵉ[] ⊑ᶜ[] d⊑d′
