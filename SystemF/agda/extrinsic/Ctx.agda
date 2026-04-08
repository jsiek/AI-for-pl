module extrinsic.Ctx where

-- File Charter:
--   * Context-level helper lemmas for extrinsic System F.
--   * Provides lookup transport through mapped contexts.
--   * Provides inversion and well-formedness helpers for contexts.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Data.List using ([]; _∷_; map)
open import Data.Nat.Base using (suc)

open import extrinsic.Types

------------------------------------------------------------------------
-- Context lookup under list maps
------------------------------------------------------------------------

lookup-map-renameᵗ :
  {Γ : Ctx} {x : Var} {A : Ty} {ρ : Renameᵗ} →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
lookup-map-renameᵗ Z = Z
lookup-map-renameᵗ (S h) = S (lookup-map-renameᵗ h)

lookup-map-substᵗ :
  {Γ : Ctx} {x : Var} {A : Ty} {σ : Substᵗ} →
  Γ ∋ x ⦂ A →
  map (substᵗ σ) Γ ∋ x ⦂ substᵗ σ A
lookup-map-substᵗ Z = Z
lookup-map-substᵗ (S h) = S (lookup-map-substᵗ h)

lookup-map-inv :
  {Γ : Ctx} {x : Var} {B : Ty} {f : Ty → Ty} →
  map f Γ ∋ x ⦂ B →
  Σ Ty (λ A → (Γ ∋ x ⦂ A) × (B ≡ f A))
lookup-map-inv {Γ = A ∷ Γ} {x = 0} Z = A , (Z , refl)
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h)
  with lookup-map-inv h
... | A' , (hA' , eq) = A' , (S hA' , eq)

------------------------------------------------------------------------
-- Context well-formedness
------------------------------------------------------------------------

CtxWf : TyCtx → Ctx → Set
CtxWf Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → WfTy Δ A

ctxWf-[] : {Δ : TyCtx} → CtxWf Δ []
ctxWf-[] ()

ctxWf-∷ : {Δ : TyCtx} {Γ : Ctx} {A : Ty} →
  WfTy Δ A →
  CtxWf Δ Γ →
  CtxWf Δ (A ∷ Γ)
ctxWf-∷ hA hΓ Z = hA
ctxWf-∷ hA hΓ (S h) = hΓ h
