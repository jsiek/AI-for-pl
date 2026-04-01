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
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong₂; sym)

open import Types
open import TypeProperties
  using
    ( liftSubstˢ
    ; substᵗ-suc-renameᵗ-suc
    ; substᵗ-⇑ˢ
    ; renameᵗ-suc-comm
    ; renameᵗ-⇑ˢ
    ; renameˢ-renameᵗ
    ; renameˢ-ext-⇑ˢ
    )

------------------------------------------------------------------------
-- Context lookup transport under renaming/substitution
------------------------------------------------------------------------

⤊ᵗ : ∀{Δ}{Ψ} → Ctx Δ Ψ → Ctx (suc Δ) Ψ
⤊ᵗ Γ = map (renameᵗ Sᵗ) Γ

renameLookup :
  ∀{Δ}{Ψ}{Ψ′}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  Γ ∋ x ⦂ A →
  map (renameˢ ρ) Γ ∋ x ⦂ renameˢ ρ A
renameLookup ρ Z = Z
renameLookup ρ (S h) = S (renameLookup ρ h)

renameLookupᵗ :
  ∀{Δ}{Δ′}{Ψ}{Γ : Ctx Δ Ψ}{x : Var}{A : Ty Δ Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
renameLookupᵗ ρ Z = Z
renameLookupᵗ ρ (S h) = S (renameLookupᵗ ρ h)

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

map-renameᵗ-⤊ᵗ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (Γ : Ctx Δ Ψ) →
  map (renameᵗ (extᵗ ρ)) (map (renameᵗ Sᵗ) Γ) ≡
  map (renameᵗ Sᵗ) (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ᵗ ρ [] = refl
map-renameᵗ-⤊ᵗ ρ (A ∷ Γ) =
  cong₂ _∷_
    (sym (renameᵗ-suc-comm ρ A))
    (map-renameᵗ-⤊ᵗ ρ Γ)

map-renameᵗ-⤊ˢ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (Γ : Ctx Δ Ψ) →
  map (renameᵗ ρ) (⤊ˢ Γ) ≡
  ⤊ˢ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ˢ ρ [] = refl
map-renameᵗ-⤊ˢ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameᵗ-⇑ˢ ρ A)
    (map-renameᵗ-⤊ˢ ρ Γ)

map-renameˢ-⤊ᵗ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (Γ : Ctx Δ Ψ) →
  map (renameˢ ρ) (⤊ᵗ Γ) ≡
  ⤊ᵗ (map (renameˢ ρ) Γ)
map-renameˢ-⤊ᵗ ρ [] = refl
map-renameˢ-⤊ᵗ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-renameᵗ Sᵗ ρ A)
    (map-renameˢ-⤊ᵗ ρ Γ)

map-renameˢ-⤊ˢ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (Γ : Ctx Δ Ψ) →
  map (renameˢ (extˢ ρ)) (⤊ˢ Γ) ≡
  ⤊ˢ (map (renameˢ ρ) Γ)
map-renameˢ-⤊ˢ ρ [] = refl
map-renameˢ-⤊ˢ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-ext-⇑ˢ ρ A)
    (map-renameˢ-⤊ˢ ρ Γ)
