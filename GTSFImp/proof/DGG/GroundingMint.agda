{-# OPTIONS --safe #-}

module proof.DGG.GroundingMint where

-- File Charter:
--   * Records target occupancy throughout canonical compilation worlds.
--   * Uses the source-rebase count as the direct history invariant; there is
--     no wrapper that restates the permitted world constructors.
--   * Connects precise source marks to target occupants through the canonical
--     direct world invariants.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong)

open import Types
open import Imprecision using (ImpEnv; X⊑X)
open import CastTerms using (Ctx; Δᵉ)
open import proof.DGG.World
open import proof.DGG.WorldInvariants
import GradualTermImprecision as GTI
import proof.DGG.CompilePreservesImprecision as Compile


------------------------------------------------------------------------
-- Initial compile-world occupancy
------------------------------------------------------------------------

initialWorld-occupied : ∀ {Δ} {μ : ImpEnv Δ}
  → (X : TyVar Δ)
  → Σ[ Y ∈ TyVar Δ ]
      toRenameⁱ (ηᴿᶜ (initialWorldᶜ μ)) Y
        ≡ toRenameⁱ (ηᴸᶜ (initialWorldᶜ μ)) X
initialWorld-occupied {μ = μ} X =
  X , cong (λ eta → toRenameⁱ eta X)
    (sym (initialWorld-embeddingsᶜ μ))


initialWorld-no-see-through-empty : ∀ {Δ} {μ : ImpEnv Δ}
  → (X : TyVar Δ)
  → (∀ Y → toRenameⁱ (ηᴿᶜ (initialWorldᶜ μ)) Y
      ≢ toRenameⁱ (ηᴸᶜ (initialWorldᶜ μ)) X)
  → ⊥
initialWorld-no-see-through-empty {μ = μ} X no-target
    with initialWorld-occupied {μ = μ} X
initialWorld-no-see-through-empty X no-target | Y , aligned =
  no-target Y aligned


------------------------------------------------------------------------
-- Compile-recursion occupancy
------------------------------------------------------------------------

target-endpoint-occupied : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
  → (Y : TyVar (Δᵉ Γᴿ))
  → Σ[ Y′ ∈ TyVar (Δᵉ Γᴿ) ]
      toRenameⁱ (ηᴿᶜ γ) Y′ ≡ toRenameⁱ (ηᴿᶜ γ) Y
target-endpoint-occupied Y = Y , refl


no-rebase-precise-source-occupied : ∀ {Γᴸ Γᴿ}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
  → sourceRebaseCountᶜ γ ≡ 0
  → (X : TyVar (Δᵉ Γᴸ))
  → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) X) ≡ X⊑X
  → Σ[ Y ∈ TyVar (Δᵉ Γᴿ) ]
      toRenameⁱ (ηᴿᶜ γ) Y ≡ toRenameⁱ (ηᴸᶜ γ) X
no-rebase-precise-source-occupied {γ = γ} no-rebase X precise =
  preciseMarksAlignedᶜ (directInvariantsᶜ γ no-rebase) X precise


initialContext-precise-source-occupied : ∀ {Δ} {μ : ImpEnv Δ}
    (δ : GTI.CtxImp μ)
  → (X : TyVar Δ)
  → marksᶜ (Compile.initialContextWorld δ)
      (toRenameⁱ (ηᴸᶜ (Compile.initialContextWorld δ)) X) ≡ X⊑X
  → Σ[ Y ∈ TyVar Δ ]
      toRenameⁱ (ηᴿᶜ (Compile.initialContextWorld δ)) Y
        ≡ toRenameⁱ (ηᴸᶜ (Compile.initialContextWorld δ)) X
initialContext-precise-source-occupied δ =
  no-rebase-precise-source-occupied
    {γ = Compile.initialContextWorld δ}
    (Compile.initialContext-no-source-rebase δ)


source-only-fresh-no-target : ∀ {Γᴸ Γᴿ}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
  → ∀ Y → toRenameⁱ (ηᴿᶜ (liftLeftᶜ γ)) Y
      ≢ toRenameⁱ (ηᴸᶜ (liftLeftᶜ γ)) Fin.zero
source-only-fresh-no-target Y ()


no-rebase-precise-see-through-empty : ∀ {Γᴸ Γᴿ}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
  → (no-rebase : sourceRebaseCountᶜ γ ≡ 0)
  → (X : TyVar (Δᵉ Γᴸ))
  → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) X) ≡ X⊑X
  → (∀ Y → toRenameⁱ (ηᴿᶜ γ) Y
      ≢ toRenameⁱ (ηᴸᶜ γ) X)
  → ⊥
no-rebase-precise-see-through-empty {γ = γ}
    no-rebase X precise no-target
    with no-rebase-precise-source-occupied
      {γ = γ} no-rebase X precise
no-rebase-precise-see-through-empty
    no-rebase X precise no-target
    | Y , aligned =
  no-target Y aligned
