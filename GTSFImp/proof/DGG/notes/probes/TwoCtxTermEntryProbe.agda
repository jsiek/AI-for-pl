{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxTermEntryProbe where

-- File Charter:
--   * Checks a term-entry relation indexed by the two-Ctx world itself.
--   * Gives constructor-form term binding plus lookup introduction,
--     weakening, and inversion sufficient for a real variable CTI rule.
--   * Records why the existing typed alias fixture cannot use that rule:
--     both of its endpoint term contexts are empty.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc; zero)

open import Types using (Ty; ★)
open import TyStore using (store-empty)
open import TermCtx using (Z; S)
import Imprecision as I
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Γᵉ; Term; `_; _∋ᵗ_⦂_)
open import proof.DGG.TwoCtxWorld
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe


data TermEntryImprecisionᶜ₀ {Cᴸ Cᴿ : Ctx}
    (W : Cᴸ ⊑ᶜ Cᴿ) (x : ℕ) :
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)} →
    A ⊑ᵀ⟨ W ⟩ B → Set where
  term-entryᶜ₀ : ∀ {A B} {p : A ⊑ᵀ⟨ W ⟩ B}
    → Cᴸ ∋ᵗ x ⦂ A
    → Cᴿ ∋ᵗ x ⦂ B
    → TermEntryImprecisionᶜ₀ W x p


bindTermᶜ₀ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → A ⊑ᵀ⟨ W ⟩ B
  → ⟨ Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , A ∷ Γᵉ Cᴸ ⟩ ⊑ᶜ
      ⟨ Δᵉ Cᴿ , CastTerms.Σᵉ Cᴿ , B ∷ Γᵉ Cᴿ ⟩
bindTermᶜ₀ W p = bind-termᶜ W p


term-entry-hereᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    (p : A ⊑ᵀ⟨ W ⟩ B)
  → TermEntryImprecisionᶜ₀ (bindTermᶜ₀ W p) zero p
term-entry-hereᶜ₀ p = term-entryᶜ₀ Z Z


term-entry-thereᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {x A B} {p : A ⊑ᵀ⟨ W ⟩ B}
    {A₀ : Ty (Δᵉ Cᴸ)} {B₀ : Ty (Δᵉ Cᴿ)}
    (p₀ : A₀ ⊑ᵀ⟨ W ⟩ B₀)
  → TermEntryImprecisionᶜ₀ W x p
  → TermEntryImprecisionᶜ₀ (bindTermᶜ₀ W p₀) (suc x) p
term-entry-thereᶜ₀ p₀ (term-entryᶜ₀ xᴸ xᴿ) =
  term-entryᶜ₀ (S xᴸ) (S xᴿ)


term-entry-tailᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {x A B} {p : A ⊑ᵀ⟨ W ⟩ B}
    {A₀ : Ty (Δᵉ Cᴸ)} {B₀ : Ty (Δᵉ Cᴿ)}
    {p₀ : A₀ ⊑ᵀ⟨ W ⟩ B₀}
  → TermEntryImprecisionᶜ₀ (bindTermᶜ₀ W p₀) (suc x) p
  → TermEntryImprecisionᶜ₀ W x p
term-entry-tailᶜ₀ (term-entryᶜ₀ (S xᴸ) (S xᴿ)) =
  term-entryᶜ₀ xᴸ xᴿ


data VariableCTIᶜ₀ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Term (Δᵉ Cᴸ) → Term (Δᵉ Cᴿ) →
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)} →
    A ⊑ᵀ⟨ W ⟩ B → Set where
  var⊑varᶜ₀ : ∀ {x A B} {p : A ⊑ᵀ⟨ W ⟩ B}
    → TermEntryImprecisionᶜ₀ W x p
    → VariableCTIᶜ₀ W (` x) (` x) p


star-context : Ctx
star-context = ⟨ zero , store-empty , ★ ∷ [] ⟩

star-world : star-context ⊑ᶜ star-context
star-world = bindTermᶜ₀ emptyᶜ I.★⊑★

star-variableᶜ₀ : VariableCTIᶜ₀ star-world (` zero) (` zero) I.★⊑★
star-variableᶜ₀ = var⊑varᶜ₀ (term-entry-hereᶜ₀ I.★⊑★)


strict-source-has-no-term-entry : ∀ {x A}
  → source-X-context ∋ᵗ x ⦂ A
  → ⊥
strict-source-has-no-term-entry ()


strict-target-has-no-term-entry : ∀ {x A}
  → target-alpha-beta-context ∋ᵗ x ⦂ A
  → ⊥
strict-target-has-no-term-entry ()
