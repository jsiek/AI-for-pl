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

------------------------------------------------------------------------
-- Context lookup transport under renaming/substitution
------------------------------------------------------------------------

⤊ᵗ : Ctx → Ctx
⤊ᵗ Γ = map (renameᵗ suc) Γ

renameLookup :
  {Γ : Ctx}{x : Var}{A : Ty} →
  (ρ : Renameˢ) →
  Γ ∋ x ⦂ A →
  map (renameˢ ρ) Γ ∋ x ⦂ renameˢ ρ A
renameLookup ρ Z = Z
renameLookup ρ (S h) = S (renameLookup ρ h)

renameLookupᵗ :
  {Γ : Ctx}{x : Var}{A : Ty} →
  (ρ : Renameᵗ) →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
renameLookupᵗ ρ Z = Z
renameLookupᵗ ρ (S h) = S (renameLookupᵗ ρ h)

substLookup :
  {Γ : Ctx}{x : Var}{A : Ty} →
  (σ : Substᵗ) →
  Γ ∋ x ⦂ A →
  map (substᵗ σ) Γ ∋ x ⦂ substᵗ σ A
substLookup σ Z = Z
substLookup σ (S h) = S (substLookup σ h)

------------------------------------------------------------------------
-- Context-level map commutation lemmas
------------------------------------------------------------------------

map-substᵗ-⤊ᵗ :
  (σ : Substᵗ) (Γ : Ctx) →
  map (substᵗ (extsᵗ σ)) (map (renameᵗ suc) Γ) ≡
  map (renameᵗ suc) (map (substᵗ σ) Γ)
map-substᵗ-⤊ᵗ σ [] = refl
map-substᵗ-⤊ᵗ σ (A ∷ Γ) =
  cong₂ _∷_
    (substᵗ-suc-renameᵗ-suc σ A)
    (map-substᵗ-⤊ᵗ σ Γ)

map-substᵗ-⤊ˢ :
  (σ : Substᵗ) (Γ : Ctx) →
  map (substᵗ (liftSubstˢ σ)) (⤊ˢ Γ) ≡
  ⤊ˢ (map (substᵗ σ) Γ)
map-substᵗ-⤊ˢ σ [] = refl
map-substᵗ-⤊ˢ σ (A ∷ Γ) =
  cong₂ _∷_
    (substᵗ-⇑ˢ σ A)
    (map-substᵗ-⤊ˢ σ Γ)

map-renameᵗ-⤊ᵗ :
  (ρ : Renameᵗ) (Γ : Ctx) →
  map (renameᵗ (extᵗ ρ)) (map (renameᵗ suc) Γ) ≡
  map (renameᵗ suc) (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ᵗ ρ [] = refl
map-renameᵗ-⤊ᵗ ρ (A ∷ Γ) =
  cong₂ _∷_
    (sym (renameᵗ-suc-comm ρ A))
    (map-renameᵗ-⤊ᵗ ρ Γ)

map-renameᵗ-⤊ˢ :
  (ρ : Renameᵗ) (Γ : Ctx) →
  map (renameᵗ ρ) (⤊ˢ Γ) ≡
  ⤊ˢ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ˢ ρ [] = refl
map-renameᵗ-⤊ˢ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameᵗ-⇑ˢ ρ A)
    (map-renameᵗ-⤊ˢ ρ Γ)

map-renameˢ-⤊ᵗ :
  (ρ : Renameˢ) (Γ : Ctx) →
  map (renameˢ ρ) (⤊ᵗ Γ) ≡
  ⤊ᵗ (map (renameˢ ρ) Γ)
map-renameˢ-⤊ᵗ ρ [] = refl
map-renameˢ-⤊ᵗ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-renameᵗ suc ρ A)
    (map-renameˢ-⤊ᵗ ρ Γ)

map-renameˢ-⤊ˢ :
  (ρ : Renameˢ) (Γ : Ctx) →
  map (renameˢ (extˢ ρ)) (⤊ˢ Γ) ≡
  ⤊ˢ (map (renameˢ ρ) Γ)
map-renameˢ-⤊ˢ ρ [] = refl
map-renameˢ-⤊ˢ ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-ext-⇑ˢ ρ A)
    (map-renameˢ-⤊ˢ ρ Γ)

------------------------------------------------------------------------
-- Context well-formedness
------------------------------------------------------------------------

CtxWf : TyCtx → SealCtx → Ctx → Set
CtxWf Δ Ψ Γ = ∀ {x A} → Γ ∋ x ⦂ A → WfTy Δ Ψ A

ctxWf-[] : {Δ : TyCtx} {Ψ : SealCtx} → CtxWf Δ Ψ []
ctxWf-[] ()

ctxWf-∷ :
  {Δ : TyCtx} {Ψ : SealCtx} {Γ : Ctx} {A : Ty} →
  WfTy Δ Ψ A →
  CtxWf Δ Ψ Γ →
  CtxWf Δ Ψ (A ∷ Γ)
ctxWf-∷ hA hΓ Z = hA
ctxWf-∷ hA hΓ (S h) = hΓ h
