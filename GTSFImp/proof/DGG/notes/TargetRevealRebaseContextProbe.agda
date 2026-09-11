{-# OPTIONS --safe #-}

module proof.DGG.notes.TargetRevealRebaseContextProbe where

-- File Charter:
--   * Pins the live CTI-indexed evaluation-context zipper at application-left
--     reconstruction and the trusted non-top allocation/discharge geometry.
--   * Checks that the root world evolves ordinarily while the complete final
--     CTI reconstructs the surviving nested source-rebase frame.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import TermCtx using (TermCtx)
open import Types using (Ty; TyCtx)
open import TyStore using (TyStore)
open import Conversion using (Conv↑)
open import Imprecision using (⇒⊑⇒)
open import CastTerms using (Term; ⟨_,_,_⟩; _·_; _↑_)
open import Reduction using
  (StoreChange; applyTerm; bind)
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)

import Imprecision as I
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.Examples.TargetIdentityReveal as TIR
open import proof.DGG.SimTargetRevealRebaseContextDef
open import proof.DGG.SourceRebase using (source-rebase-now)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-bind-left-aligned)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution; evolutions-refl; evolutions-step-left )


app-left-rebuilds-whole-source : ∀
    {Δᴸ Δᴿ Δᴸ′ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
    (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    (χᴸ : StoreChange Δᴸ Δᴸ′) (P : Term Δᴸ′)
  → RebuildSource
      (focus-there (focus-·₁ function-rel argument-rel) focus-here)
      χᴸ P (P · applyTerm χᴸ M)
app-left-rebuilds-whole-source function-rel argument-rel χᴸ P =
  rebuild-there (rebuild-here refl) (rebuild-edge refl)

app-left-reveal-wraps-whole : ∀
    {Δᴸ Δᴿ : TyCtx}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {L M : Term Δᴸ} {L′ M′ : Term Δᴿ}
    {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    (function-rel : γ CTI.⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB)
    (argument-rel : γ CTI.⊢² M ⊑ M′ ∶ pA)
    {C D : Ty Δᴿ} (c : Conv↑ Δᴿ C D)
  → targetTerm (pack (CTI.·⊑·² function-rel argument-rel)) ↑ c
      ≡ (L′ · M′) ↑ c
app-left-reveal-wraps-whole function-rel argument-rel c = refl


tir-root-aligned-evolution :
  MultiWorldEvolution
    {W = TIR.checkpoint₁-world} {W′ = TIR.checkpoint₃-world}
    (bind TIR.ℕᵗ ∷ˢ []ˢ) []ˢ
tir-root-aligned-evolution =
  evolutions-step-left refl
    (evolution-bind-left-aligned refl
      TIR.checkpoint₃-alpha-ok
      TIR.checkpoint₃-alpha-boundary
      TIR.checkpoint₃-alpha-representation)
    evolutions-refl

tir-final-paired-outer-inner-rebase :
  TIR.checkpoint₃-reveals-imprecision ≡
    CTI.reveal⊑reveal²
      TIR.checkpoint₃-source-reveal⊢
      TIR.checkpoint₁-alpha-reveal⊢
      refl refl I.ι⊑★
      (CTI.⊑reveal-rebase²
        TIR.checkpoint₁-beta-reveal⊢
        (source-rebase-now TIR.checkpoint₃-beta-ok
          TIR.checkpoint₃-beta-representation)
        TIR.checkpoint₃-function-imprecision
        (I.⇒⊑⇒ I.X⊑X I.★⊑★))
      TIR.ℕ⇒★⊑★⇒★
tir-final-paired-outer-inner-rebase = refl
