module proof.Reduction where

-- File Charter:
--   * Proof lemmas for the store-changing reduction relation.
--   * Supplies arrow preservation under store-change transport,
--     application congruence over multi-step reduction, and inert
--     preservation under store-change transport.
--   * Depends on Reduction for the base relations and proof.Consistency for
--     generated-cast safety.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (subst to subst≡)

open import Types
open import Consistency hiding (keep)
import Consistency as C
open import CastTerms using
  (Term; Value; _·_; _⟨_⟩; Inert; inj; fun; all; genᵥ)
open import Reduction
open import proof.Consistency using (gen-safe)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using
  (rename-star-injective; rename-occurs; renameᵗᵐ-preserves-Value)

applyTy-⇒ : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′) (A B : Ty Δ)
  → applyTy χ (A ⇒ B) ≡ applyTy χ A ⇒ applyTy χ B
applyTy-⇒ keep A B = refl
applyTy-⇒ (bind C) A B = refl

applyTys-⇒ : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (A B : Ty Δ)
  → applyTys χs (A ⇒ B) ≡ applyTys χs A ⇒ applyTys χs B
applyTys-⇒ [] A B = refl
applyTys-⇒ (keep ∷ χs) A B = applyTys-⇒ χs A B
applyTys-⇒ ((bind C) ∷ χs) A B =
  applyTys-⇒ χs (⇑ᵗ A) (⇑ᵗ B)

appL-↠ : ∀ {Δ Δ′} {L M : Term Δ} {L′ : Term Δ′}
    {χs : StoreChanges Δ Δ′}
  → L —↠[ χs ] L′
  → L · M —↠[ χs ] L′ · applyTerms χs M
appL-↠ {L = L} {M = M} (_ ∎[]) = (L · M) ∎[]
appL-↠ {L = L} {M = M} {L′ = P} {χs = χ ∷ χs}
    (_ —→[ χ ]⟨ L→N ⟩ N↠P) =
  L · M
    —→[ χ ]⟨ ξ-·₁ L→N refl ⟩
  _
    —↠[ χs ]⟨ appL-↠ N↠P ⟩
  P · applyTerms χs (χ ▷ᵀ M) ∎[]

appR-↠ : ∀ {Δ Δ′} {V M : Term Δ} {M′ : Term Δ′}
    {χs : StoreChanges Δ Δ′}
  → Value V
  → M —↠[ χs ] M′
  → V · M —↠[ χs ] applyTerms χs V · M′
appR-↠ {V = V} {M = M} vV (_ ∎[]) = (V · M) ∎[]
appR-↠ {V = V} {M = M} {M′ = P} {χs = keep ∷ χs} vV
    (_ —→[ keep ]⟨ M→N ⟩ N↠P) =
  V · M
    —→[ keep ]⟨ ξ-·₂ vV M→N refl ⟩
  _
    —↠[ χs ]⟨ appR-↠ vV N↠P ⟩
  applyTerms χs V · P ∎[]
appR-↠ {V = V} {M = M} {M′ = P} {χs = bind A ∷ χs} vV
    (_ —→[ bind A ]⟨ M→N ⟩ N↠P) =
  V · M
    —→[ bind A ]⟨ ξ-·₂ vV M→N refl ⟩
  _
    —↠[ χs ]⟨
      appR-↠ (renameᵗᵐ-preserves-Value wk↪ᵗ vV) N↠P ⟩
  applyTerms χs (bind A ▷ᵀ V) · P ∎[]

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
    (inj {G = ＇ X} ⦃ Gᵍ = ＇ .X ⦄
      ⦃ G∼★ = C.X∼★ᶜ eq ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ＇ Fin.suc X ⦄ ⦃ G∼★ = C.X∼★ᶜ eq ⦄
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
