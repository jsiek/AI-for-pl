{-# OPTIONS --safe #-}

module
  proof.DGG.notes.PairedUniversalCastApplicationBoundaryProbe where

-- File Charter:
--   * States the exact semantic boundary exposed by the nonstructural
--     universal branch of paired beta-universal cast distribution.
--   * Keeps the source at the mandatory post-step checkpoint while the
--     target continues through its type application under the distributed
--     result cast.
--   * Returns the whole target trace, world evolution, and final CTI
--     evidence directly, without a result wrapper or residual classifier.
--   * Remains a notes-only probe until the target-continuation induction and
--     its overlap with the other beta-universal branches are understood.

open import Data.List using ([])
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using
  ( Ty; TyCtx; NonVar; _∈ᵗ_; `∀; _[_]ᵗ; ⇑ᵗ; renameᵗ; extᵗ )
open import TyStore using (TyStore)
open import Consistency using (Env∼; extᵐ; _⊢_∼_; _[_]ᶜ; ∀ᶜ_)
open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⦂∀_[_]; _⟨_⟩)
open import Reduction using
  (StoreChanges; applyTys; applyConsistencies; keep; _—↠[_]_)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)

import Imprecision as I
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World
open import proof.DGG.WorldEvolutionSequence using (MultiWorldEvolution)


PairedUniversalCastApplicationBoundaryᵀ : Set
PairedUniversalCastApplicationBoundaryᵀ =
  ∀ {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {D C : Ty (Nat.suc Δᴸ)} {D′ C′ : Ty (Nat.suc Δᴿ)}
    {A : Ty Δᴸ} {A′ : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    {c : extᵐ ν ⊢ D ∼ C} {c′ : extᵐ ν′ ⊢ D′ ∼ C′}
    {non-var : NonVar
      (renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) D)}
    {occurs : Fin.zero ∈ᵗ
      renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) D}
    {body : I.instᵐ (marksᶜ γ) I.⊢
      renameᵗ (extᵗ (toRenameⁱ (ηᴸᶜ γ))) D ⊑
      ⇑ᵗ (`∀ (renameᵗ (extᵗ (toRenameⁱ (ηᴿᶜ γ))) D′))}
  → openFramesᶜ γ ≡ []
  → γ CTI.⊢² M ⊑ M′ ∶ I.∀⊑ non-var occurs body
  → (q : A ⊑ᵀ⟨ γ ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵀ⟨ γ ⟩ C′ [ A′ ]ᵗ)
  → Value M
  → Value M′
  → Σ[ Δᴿ′ ∈ TyCtx ]
    Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
    Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
    Σ[ γ′ ∈
      ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
    Σ[ s ∈ C [ A ]ᵗ ⊑ᵀ⟨ γ′ ⟩
        applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
      (M′ ⦂∀ D′ [ A′ ] —↠[ χsᴿ ] N′)
      × MultiWorldEvolution
          {W = γ} {W′ = γ′}
          (keep ∷ˢ []ˢ) (keep ∷ˢ χsᴿ)
      × (γ′ CTI.⊢²
          (M ⦂∀ D [ A ]) ⟨ c [ A ]ᶜ ⟩ ⊑
          N′ ⟨ applyConsistencies χsᴿ (c′ [ A′ ]ᶜ) ⟩ ∶ s)
