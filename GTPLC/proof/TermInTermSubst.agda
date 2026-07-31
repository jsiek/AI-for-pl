module proof.TermInTermSubst where

-- File Charter:
--   * Term-variable renaming and substitution properties for GTPLC terms.
--   * Derives the single-variable typing substitution theorem used by
--     beta-reduction preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import Types
open import TyStore
open import Ctx
open import Coercions
open import Primitives
open import Terms
open import proof.TypeInTermSubst

------------------------------------------------------------------------
-- Renaming term variables
------------------------------------------------------------------------

rename-preserves-Value : ∀ ρ {V}
  → Value V
  → Value (rename ρ V)
rename-preserves-Value ρ (ƛ N) = ƛ _
rename-preserves-Value ρ (Λ vV) = Λ (rename-preserves-Value ρ vV)
rename-preserves-Value ρ ($ κ) = $ κ
rename-preserves-Value ρ (vV ⟨ i ⟩) =
  rename-preserves-Value ρ vV ⟨ i ⟩

RenameWf : Ctx → Ctx → Rename → Set₁
RenameWf Γ Γ′ ρ =
  ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

RenameWf-ext : ∀ {Γ Γ′ A ρ}
  → RenameWf Γ Γ′ ρ
  → RenameWf (A ∷ Γ) (A ∷ Γ′) (ext ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

RenameWf-⤊ : ∀ {Γ Γ′ ρ}
  → RenameWf Γ Γ′ ρ
  → RenameWf (⤊ᵗ Γ) (⤊ᵗ Γ′) ρ
RenameWf-⤊ hρ h
    with lookup-map-inv h
RenameWf-⤊ hρ h | A , A∈Γ , refl =
  lookup-map (hρ A∈Γ)

typing-rename : ∀ {Δ Σ Γ Γ′ M A ρ}
  → RenameWf Γ Γ′ ρ
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , Γ′ ⟩ ⊢ rename ρ M ⦂ A
typing-rename hρ (⊢` h) = ⊢` (hρ h)
typing-rename hρ (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-rename (RenameWf-ext hρ) hM)
typing-rename hρ (⊢· hL hM) =
  ⊢· (typing-rename hρ hL) (typing-rename hρ hM)
typing-rename hρ (⊢Λ vM hM) =
  ⊢Λ (rename-preserves-Value _ vM)
    (typing-rename (RenameWf-⤊ hρ) hM)
typing-rename hρ (⊢ν hA hL c⊢) =
  ⊢ν hA (typing-rename hρ hL) c⊢
typing-rename hρ (⊢$ κ) = ⊢$ κ
typing-rename hρ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-rename hρ hL) op (typing-rename hρ hM)
typing-rename hρ (⊢⟨⟩ c⊢ hM) =
  ⊢⟨⟩ c⊢ (typing-rename hρ hM)
typing-rename hρ (⊢blame hA) = ⊢blame hA

typing-rename-shift : ∀ {Δ Σ Γ M A B}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , B ∷ Γ ⟩ ⊢ rename suc M ⦂ A
typing-rename-shift hM =
  typing-rename (λ h → S h) hM

------------------------------------------------------------------------
-- Substituting term variables
------------------------------------------------------------------------

subst-preserves-Value : ∀ σ {V}
  → Value V
  → Value (Terms.subst σ V)
subst-preserves-Value σ (ƛ N) = ƛ _
subst-preserves-Value σ (Λ vV) =
  Λ (subst-preserves-Value (↑ σ) vV)
subst-preserves-Value σ ($ κ) = $ κ
subst-preserves-Value σ (vV ⟨ i ⟩) =
  subst-preserves-Value σ vV ⟨ i ⟩

SubstWf : TyCtx → TyStore → Ctx → Ctx → Subst → Set₁
SubstWf Δ Σ Γ Γ′ σ =
  ∀ {x A} → Γ ∋ x ⦂ A → ⟨ Δ , Σ , Γ′ ⟩ ⊢ σ x ⦂ A

SubstWf-exts : ∀ {Δ Σ Γ Γ′ A σ}
  → SubstWf Δ Σ Γ Γ′ σ
  → SubstWf Δ Σ (A ∷ Γ) (A ∷ Γ′) (exts σ)
SubstWf-exts hσ Z = ⊢` Z
SubstWf-exts hσ (S h) = typing-rename-shift (hσ h)

SubstWf-↑ : ∀ {Δ Σ Γ Γ′ σ}
  → SubstWf Δ Σ Γ Γ′ σ
  → SubstWf (suc Δ) (⟰ᵗ Σ) (⤊ᵗ Γ) (⤊ᵗ Γ′) (↑ σ)
SubstWf-↑ hσ h
    with lookup-map-inv h
SubstWf-↑ hσ h | A , A∈Γ , refl =
  typing-shiftᵗ (hσ A∈Γ)

typing-subst : ∀ {Δ Σ Γ Γ′ M A σ}
  → SubstWf Δ Σ Γ Γ′ σ
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , Γ′ ⟩ ⊢ Terms.subst σ M ⦂ A
typing-subst hσ (⊢` h) = hσ h
typing-subst hσ (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-subst (SubstWf-exts hσ) hM)
typing-subst hσ (⊢· hL hM) =
  ⊢· (typing-subst hσ hL) (typing-subst hσ hM)
typing-subst hσ (⊢Λ vM hM) =
  ⊢Λ (subst-preserves-Value _ vM)
    (typing-subst (SubstWf-↑ hσ) hM)
typing-subst hσ (⊢ν hA hL c⊢) =
  ⊢ν hA (typing-subst hσ hL) c⊢
typing-subst hσ (⊢$ κ) = ⊢$ κ
typing-subst hσ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-subst hσ hL) op (typing-subst hσ hM)
typing-subst hσ (⊢⟨⟩ c⊢ hM) =
  ⊢⟨⟩ c⊢ (typing-subst hσ hM)
typing-subst hσ (⊢blame hA) = ⊢blame hA

singleSubstWf : ∀ {Δ Σ Γ A V}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ A
  → SubstWf Δ Σ (A ∷ Γ) Γ (singleSub V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢` h

typing-single-subst : ∀ {Δ Σ Γ N V A B}
  → ⟨ Δ , Σ , A ∷ Γ ⟩ ⊢ N ⦂ B
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ A
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N [ V ] ⦂ B
typing-single-subst hN hV =
  typing-subst (singleSubstWf hV) hN
