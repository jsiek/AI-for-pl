{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxTargetStripReconstructionProbe where

-- File Charter:
--   * Checks the structural replacement for TargetStripProof's sole
--     lower-left world producer.
--   * Peels a lifted-source rebase plan, rather than reconstructing a world
--     from separately supplied embeddings, stores, and invariants.
--   * Shows that the lifted result rebuilds exactly, while the lowered world
--     retains constructor-form source-rebase provenance and direct invariants.

open import Data.Nat using (suc)
open import Data.List using (_∷_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ⇑ᵗ)
open import TyStore using (TyStore; store-lift)
import TermCtx as TC
open TC using (TermCtx)
open import CastTerms using (Ctx; ⟨_,_,_⟩)
open import proof.DGG.World
open import proof.DGG.WorldInvariants
open import proof.DGG.SourceRebasePlan


private
  fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl


-- The live producer has a rebase of `liftWorldLeft W` at `suc X`.  With
-- constructor provenance, only two plan heads can have those indices:
-- an already-aligned identity or the commutation through `lift-left-rawᶜ`.

lowerLiftSourceRebasePlanᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ}
  → SourceRebasePlan
      (lift-left-rawᶜ W Γᴸ⁺≡) (Fin.suc Xᴸ) Xᴿ
  → SourceRebasePlan W Xᴸ Xᴿ
lowerLiftSourceRebasePlanᶜ₀ (source-rebase-id aligned) =
  source-rebase-id (fin-suc-injective aligned)
lowerLiftSourceRebasePlanᶜ₀
    (source-rebase-lift-left plan Γᴸ⁺≡) = plan


lowerLiftSourceWorldᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ}
  → SourceRebasePlan
      (lift-left-rawᶜ W Γᴸ⁺≡) (Fin.suc Xᴸ) Xᴿ
  → ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩
lowerLiftSourceWorldᶜ₀ plan =
  rebaseSource (lowerLiftSourceRebasePlanᶜ₀ plan)


lowerLiftSource-rebuildᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ}
      (plan : SourceRebasePlan
        (lift-left-rawᶜ W Γᴸ⁺≡) (Fin.suc Xᴸ) Xᴿ)
  → lift-left-rawᶜ (lowerLiftSourceWorldᶜ₀ plan) Γᴸ⁺≡
      ≡ rebaseSource plan
lowerLiftSource-rebuildᶜ₀ (source-rebase-id aligned) = refl
lowerLiftSource-rebuildᶜ₀
    (source-rebase-lift-left plan Γᴸ⁺≡) = refl


lowerLiftSource-rebaseᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ}
      (plan : SourceRebasePlan
        (lift-left-rawᶜ W Γᴸ⁺≡) (Fin.suc Xᴸ) Xᴿ)
  → RebaseSourceᶜ W (lowerLiftSourceWorldᶜ₀ plan) Xᴸ Xᴿ
lowerLiftSource-rebaseᶜ₀ plan =
  sourceRebasePlan-sound (lowerLiftSourceRebasePlanᶜ₀ plan)


lowerLiftSource-invariantsᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      {Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ}
      (plan : SourceRebasePlan
        (lift-left-rawᶜ W Γᴸ⁺≡) (Fin.suc Xᴸ) Xᴿ)
  → DirectWorldInvariantsᶜ (lowerLiftSourceWorldᶜ₀ plan)
lowerLiftSource-invariantsᶜ₀ plan =
  directInvariantsᶜ (lowerLiftSourceWorldᶜ₀ plan)


-- The plan premise above is essential producer provenance.  Endpoint and
-- embedding facts alone cannot invert arbitrary raw histories: type lifting
-- and term binding admit both constructor orders below.  They have the same
-- endpoints, center, embeddings, and marks, but distinct history heads.

lift-after-termᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → A ⊑ᵀ⟨ W ⟩ B
  → ⟨ suc Δᴸ , store-lift Σᴸ , ⇑ᵗ A ∷ TC.⇑ᶜ Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , B ∷ Γᴿ ⟩
lift-after-termᶜ₀ {W = W} represented =
  lift-left-rawᶜ (bind-termᶜ W represented) refl


term-after-liftᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
  → ⇑ᵗ A ⊑ᵀ⟨ lift-left-rawᶜ W refl ⟩ B
  → ⟨ suc Δᴸ , store-lift Σᴸ , ⇑ᵗ A ∷ TC.⇑ᶜ Γᴸ ⟩ ⊑ᶜ
      ⟨ Δᴿ , Σᴿ , B ∷ Γᴿ ⟩
term-after-liftᶜ₀ {W = W} represented′ =
  bind-termᶜ (lift-left-rawᶜ W refl) represented′


interleaved-center-sameᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {represented : A ⊑ᵀ⟨ W ⟩ B}
      {represented′ : ⇑ᵗ A ⊑ᵀ⟨ lift-left-rawᶜ W refl ⟩ B}
  → centerᶜ (lift-after-termᶜ₀ {W = W} represented)
      ≡ centerᶜ (term-after-liftᶜ₀ {W = W} represented′)
interleaved-center-sameᶜ₀ = refl


interleaved-ηᴸ-sameᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {represented : A ⊑ᵀ⟨ W ⟩ B}
      {represented′ : ⇑ᵗ A ⊑ᵀ⟨ lift-left-rawᶜ W refl ⟩ B}
  → ηᴸᶜ (lift-after-termᶜ₀ {W = W} represented)
      ≡ ηᴸᶜ (term-after-liftᶜ₀ {W = W} represented′)
interleaved-ηᴸ-sameᶜ₀ = refl


interleaved-ηᴿ-sameᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {represented : A ⊑ᵀ⟨ W ⟩ B}
      {represented′ : ⇑ᵗ A ⊑ᵀ⟨ lift-left-rawᶜ W refl ⟩ B}
  → ηᴿᶜ (lift-after-termᶜ₀ {W = W} represented)
      ≡ ηᴿᶜ (term-after-liftᶜ₀ {W = W} represented′)
interleaved-ηᴿ-sameᶜ₀ = refl


interleaved-marks-sameᶜ₀ :
    ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {represented : A ⊑ᵀ⟨ W ⟩ B}
      {represented′ : ⇑ᵗ A ⊑ᵀ⟨ lift-left-rawᶜ W refl ⟩ B}
  → marksᶜ (lift-after-termᶜ₀ {W = W} represented)
      ≡ marksᶜ (term-after-liftᶜ₀ {W = W} represented′)
interleaved-marks-sameᶜ₀ = refl
