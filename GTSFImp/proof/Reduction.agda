module proof.Reduction where

-- File Charter:
--   * Proof lemmas for the store-changing reduction relation.
--   * Supplies cast congruence over multi-step reduction and inert
--     preservation under store-change transport.
--   * Depends on Reduction for the base relations and proof.Consistency for
--     generated-cast safety.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)

open import Types
open import Consistency hiding (keep)
import Consistency as C
open import CastTerms using (Term; _⟨_⟩; Inert; inj; fun; all; genᵥ)
open import Reduction
open import proof.Consistency using (gen-safe)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using
  (rename-star-injective; rename-occurs)

cast-↠ : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → M —↠[ χs ] N
  → M ⟨ c ⟩ —↠[ χs ] N ⟨ χs ▶ᶜ c ⟩
cast-↠ {M = M} c (_ ∎[]) = (M ⟨ c ⟩) ∎[]
cast-↠ {M = M} {N = P} {χs = χ ∷ χs} c
    (_ —→[ χ ]⟨ M→N ⟩ N↠P) =
  (M ⟨ c ⟩)
    —→[ χ ]⟨ ξ-⟨⟩ M→N refl ⟩
  _
    —↠[ χs ]⟨ cast-↠ (χ ▷ᶜ c) N↠P ⟩
  (P ⟨ χs ▶ᶜ (χ ▷ᶜ c) ⟩) ∎[]

applyStoreChange-Inert : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (χ : StoreChange Δ Δ′)
  → Inert c
  → Inert (χ ▷ᶜ c)
applyStoreChange-Inert keep inert = inert
applyStoreChange-Inert (bind A)
    (inj ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = C.⇒∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = C.⇒∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A)
    (inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = C.ι∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = C.ι∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A)
    (inj {G = ＇ X} ⦃ Gᵍ = ＇ .X ⦄
      ⦃ G∼★ = C.X∼★ᵍ eq ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ＇ Fin.suc X ⦄ ⦃ G∼★ = C.X∼★ᵍ eq ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A)
    (inj ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = C.∀∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = C.∀∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (bind A) fun = fun
applyStoreChange-Inert (bind A) all = all
applyStoreChange-Inert (bind A)
    (genᵥ {A = A₀} {B = B} {c = c}
      ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈B ⦄ A≢★ safe) =
  subst≡
    (λ z → Inert (gen_ ⦃ Bnv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
      ⦃ z∈B = z ⦄ _ _))
    (PI.∈ᵗ-unique (rename-occurs (extᵗ Fin.suc) z∈B) _)
    (genᵥ ⦃ Bnv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
      ⦃ z∈B = rename-occurs (extᵗ Fin.suc) z∈B ⦄
      A′≢★
      (gen-safe _ A′≢★ (renameNonVar (extᵗ Fin.suc) Bnv)
        (rename-occurs (extᵗ Fin.suc) z∈B)))
  where
  A′≢★ = λ eq → A≢★ (rename-star-injective Fin.suc eq)

applyConsistencies-Inert : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (χs : StoreChanges Δ Δ′)
  → Inert c
  → Inert (χs ▶ᶜ c)
applyConsistencies-Inert [] inert = inert
applyConsistencies-Inert (χ ∷ χs) inert =
  applyConsistencies-Inert χs (applyStoreChange-Inert χ inert)
