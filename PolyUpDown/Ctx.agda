module Ctx where

-- File Charter:
--   * Context-focused lemmas: lookup transport and context-map commutation facts.
--   * Theorems whose main subject is `Ctx`, `map` over contexts, or `∋` lookup.
--   * No generic `Ty` substitution algebra and no coercion/store metatheory.
-- Note to self:
--   * If a new lemma is primarily about context structure or context lookup, put it
--     here; otherwise move it to the more specific owning module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (map; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import Types
open import TypeProperties using (liftSubstˢ; substᵗ-suc-renameᵗ-suc; substᵗ-⇑ˢ)

------------------------------------------------------------------------
-- Context lookup transport under renaming/substitution
------------------------------------------------------------------------

renameLookup :
  ∀{Δ}{Ψ}{Ψ′}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  Γ ∋ x ⦂ A →
  map (renameˢ ρ) Γ ∋ x ⦂ renameˢ ρ A
renameLookup ρ Z = Z
renameLookup ρ (S h) = S (renameLookup ρ h)

substLookup :
  ∀{Δ}{Δ′}{Ψ}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ Ψ} →
  (σ : Substᵗ Δ Δ′ Ψ) →
  Γ ∋ x ⦂ A →
  map (substᵗ σ) Γ ∋ x ⦂ substᵗ σ A
substLookup σ Z = Z
substLookup σ (S h) = S (substLookup σ h)

------------------------------------------------------------------------
-- Context-level map commutation lemmas
------------------------------------------------------------------------

map-substᵗ-⤊ᵗ :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (Γ : Ctx Δ Ψ) →
  map (substᵗ (extsᵗ σ)) (map (renameᵗ Sᵗ) Γ) ≡
  map (renameᵗ Sᵗ) (map (substᵗ σ) Γ)
map-substᵗ-⤊ᵗ σ [] = refl
map-substᵗ-⤊ᵗ σ (A ∷ Γ) =
  cong₂ _∷_
    (substᵗ-suc-renameᵗ-suc σ A)
    (map-substᵗ-⤊ᵗ σ Γ)

map-substᵗ-⤊ˢ :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (Γ : Ctx Δ Ψ) →
  map (substᵗ (liftSubstˢ σ)) (⤊ˢ Γ) ≡
  ⤊ˢ (map (substᵗ σ) Γ)
map-substᵗ-⤊ˢ σ [] = refl
map-substᵗ-⤊ˢ σ (A ∷ Γ) =
  cong₂ _∷_
    (substᵗ-⇑ˢ σ A)
    (map-substᵗ-⤊ˢ σ Γ)
