{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxWorldInvariantsProbe where

-- File Charter:
--   * Checks the four direct nominal invariants for the two-Ctx world
--     skeleton, with endpoint stores obtained from the relation indices.
--   * Gives the direct-store rebase graph and its same-world case without
--     following representation aliases.
--   * Does not claim a general source-rebase function; that requires a
--     structural plan for commuting endpoint allocations in the raw history.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using
  (Ty; TyCtx; TyVar; ＇_; ‵_; ★; _⇒_; `∀; ⇑ᵗ; renameᵗ; renameᵗ-cong;
   renameᵗ-comp; renameᵗ-shift)
open import TyStore using (lookupStore; store-lift; store-bind)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ)
open import Consistency using (_↪ᵗ_; keep; skip; toRenameᵗ)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; instᵐ; _⊢_⊑_)
open import proof.ImprecisionConsistency using (rename-⊑)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe


private
  fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

  variable≢star : ∀ {Δ : TyCtx} {X : TyVar Δ}
    → _≡_ {A = Ty Δ} (＇_ {Δ = Δ} X) (★ {Δ = Δ})
    → ⊥
  variable≢star ()

  imprecision-cong : ∀ {Δ} {μ : ImpEnv Δ} {A A′ B B′ : Ty Δ}
    → A ≡ A′
    → B ≡ B′
    → μ ⊢ A ⊑ B
    → μ ⊢ A′ ⊑ B′
  imprecision-cong refl refl A⊑B = A⊑B

  renameᵗ-keep-shift : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
  renameᵗ-keep-shift η A =
    trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
      (renameᵗ-shift (toRenameᵗ η) A)

  renameᵗ-skip : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (skip η)) A
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
  renameᵗ-skip η A =
    trans (renameᵗ-cong A (λ X → refl))
      (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc A))

  lift-old-representation : ∀ {Δ} {μ : ImpEnv Δ} {v}
      {A B : Ty Δ}
    → μ ⊢ A ⊑ B
    → extendᵐ v μ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
  lift-old-representation A⊑B =
    rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) A⊑B

  unshift-star : ∀ {Δ} {A : Ty Δ}
    → ⇑ᵗ A ≡ ★
    → A ≡ ★
  unshift-star {A = ＇ X} ()
  unshift-star {A = ‵ ι} ()
  unshift-star {A = ★} refl = refl
  unshift-star {A = A ⇒ B} ()
  unshift-star {A = `∀ A} ()


record DirectWorldInvariantsᶜ₀ {Cᴸ Cᴿ : Ctx}
    (W : Cᴸ ⊑ᶜ₀ Cᴿ) : Set where
  constructor direct-world-invariantsᶜ₀
  field
    preciseMarksAlignedᶜ₀ :
      ∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
      → marksᶜ₀ W (toRenameᵗ (ηᴸᶜ₀ W) Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar (Δᵉ Cᴿ) ]
          toRenameᵗ (ηᴿᶜ₀ W) Xᴿ ≡ toRenameᵗ (ηᴸᶜ₀ W) Xᴸ

    representationsImpreciseᶜ₀ :
      ∀ {Xᴸ : TyVar (Δᵉ Cᴸ)} {Xᴿ : TyVar (Δᵉ Cᴿ)}
      → toRenameᵗ (ηᴸᶜ₀ W) Xᴸ ≡ toRenameᵗ (ηᴿᶜ₀ W) Xᴿ
      → marksᶜ₀ W ⊢
          renameᵗ (toRenameᵗ (ηᴸᶜ₀ W)) (lookupStore (Σᵉ Cᴸ) Xᴸ)
          ⊑ renameᵗ (toRenameᵗ (ηᴿᶜ₀ W)) (lookupStore (Σᵉ Cᴿ) Xᴿ)

    unmatchedTargetsDynamicᶜ₀ :
      ∀ (Xᴿ : TyVar (Δᵉ Cᴿ))
      → (∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
          → toRenameᵗ (ηᴸᶜ₀ W) Xᴸ ≢ toRenameᵗ (ηᴿᶜ₀ W) Xᴿ)
      → lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar (Δᵉ Cᴿ) ]
            (lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ＇ Yᴿ)
          × (∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
              → toRenameᵗ (ηᴸᶜ₀ W) Xᴸ
                ≢ toRenameᵗ (ηᴿᶜ₀ W) Yᴿ)

    dynamicStarSourcesUnoccupiedᶜ₀ :
      ∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
      → marksᶜ₀ W (toRenameᵗ (ηᴸᶜ₀ W) Xᴸ) ≡ X⊑★
      → lookupStore (Σᵉ Cᴸ) Xᴸ ≡ ★
      → ∀ (Xᴿ : TyVar (Δᵉ Cᴿ))
      → toRenameᵗ (ηᴿᶜ₀ W) Xᴿ ≢ toRenameᵗ (ηᴸᶜ₀ W) Xᴸ

open DirectWorldInvariantsᶜ₀ public


skipCenter-invariantsᶜ₀ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ₀ Cᴿ)
  → DirectWorldInvariantsᶜ₀ W
  → DirectWorldInvariantsᶜ₀ (skip-centerᶜ₀ W)
skipCenter-invariantsᶜ₀ {Cᴸ = Cᴸ} {Cᴿ = Cᴿ} W inv =
  direct-world-invariantsᶜ₀ precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ₀ W)
        (toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
          ≡ toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAlignedᶜ₀ inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
        ≡ toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
    → extendᵐ X⊑★ (marksᶜ₀ W) ⊢
        renameᵗ (toRenameᵗ (skip (ηᴸᶜ₀ W)))
          (lookupStore (Σᵉ Cᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿᶜ₀ W)))
          (lookupStore (Σᵉ Cᴿ) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skip (ηᴸᶜ₀ W) (lookupStore (Σᵉ Cᴸ) Xᴸ)))
      (sym (renameᵗ-skip (ηᴿᶜ₀ W) (lookupStore (Σᵉ Cᴿ) Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ₀ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ)
    → lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
            ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ₀ inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , shifted-head-no-source)
    where
    shifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Yᴿ
    shifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ₀ W)
        (toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑★
    → lookupStore (Σᵉ Cᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
        ≢ toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
  unoccupied Xᴸ mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ₀ inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)


directInvariantsᶜ₀ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ₀ Cᴿ)
  → DirectWorldInvariantsᶜ₀ W
directInvariantsᶜ₀ emptyᶜ₀ =
  direct-world-invariantsᶜ₀ (λ ()) (λ { {()} }) (λ ()) (λ ())
directInvariantsᶜ₀ (skip-centerᶜ₀ W) =
  skipCenter-invariantsᶜ₀ W (directInvariantsᶜ₀ W)
directInvariantsᶜ₀
    (lift-both-rawᶜ₀ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W v eqᴸ eqᴿ) =
  direct-world-invariantsᶜ₀ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ₀ W

  precise : ∀ Xᴸ
    → extendᵐ v (marksᶜ₀ W) (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ)
        ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ₀ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
    → extendᵐ v (marksᶜ₀ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ₀ W)))
          (lookupStore (store-lift Σᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ₀ W)))
          (lookupStore (store-lift Σᴿ) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned = Imprecision.X⊑X
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ₀ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ₀ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ₀ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ)
    → lookupStore (store-lift Σᴿ) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-lift Σᴿ) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ₀ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ v (marksᶜ₀ W) (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ)
        ≡ X⊑★
    → lookupStore (store-lift Σᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ₀ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ₀
    (lift-left-rawᶜ₀ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W eqᴸ) =
  direct-world-invariantsᶜ₀ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ₀ W

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ₀ W) (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ₀ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≡ toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
    → instᵐ (marksᶜ₀ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ₀ W)))
          (lookupStore (store-lift Σᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿᶜ₀ W)))
          (lookupStore Σᴿ Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ₀ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-skip (ηᴿᶜ₀ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ₀ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ)
    → lookupStore Σᴿ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ] (lookupStore Σᴿ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
            ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ₀ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ₀ W) (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-lift Σᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ₀ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ₀ (bind-termᶜ₀ W represented) =
  direct-world-invariantsᶜ₀
    (preciseMarksAlignedᶜ₀ inv)
    (representationsImpreciseᶜ₀ inv)
    (unmatchedTargetsDynamicᶜ₀ inv)
    (dynamicStarSourcesUnoccupiedᶜ₀ inv)
  where
  inv = directInvariantsᶜ₀ W

directInvariantsᶜ₀
    (bind-both-star-rawᶜ₀ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      {A = A} {B = B} W represented A≢★ eqᴸ eqᴿ) =
  direct-world-invariantsᶜ₀ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ₀ W

  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ₀ W)
        (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ₀ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
    → extendᵐ X⊑★ (marksᶜ₀ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ₀ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ₀ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ₀ W) A))
      (sym (renameᵗ-keep-shift (ηᴿᶜ₀ W) B))
      (lift-old-representation represented)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ₀ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ₀ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ₀ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ₀ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ₀ W)
        (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = ⊥-elim (A≢★ entry)
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ₀ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ₀
    (bind-both-rawᶜ₀ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {A = A} {B = B}
      W represented eqᴸ eqᴿ) =
  direct-world-invariantsᶜ₀ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ₀ W

  precise : ∀ Xᴸ
    → extendᵐ X⊑X (marksᶜ₀ W)
        (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ₀ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
    → extendᵐ X⊑X (marksᶜ₀ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ₀ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ₀ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ₀ W) A))
      (sym (renameᵗ-keep-shift (ηᴿᶜ₀ W) B))
      (lift-old-representation represented)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ₀ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ₀ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ₀ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ₀ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑X (marksᶜ₀ W)
        (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  unoccupied Fin.zero () entry Xᴿ aligned
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ₀ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ₀
    (bind-right-rawᶜ₀ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W B fresh eqᴿ) =
  direct-world-invariantsᶜ₀ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ₀ W

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ₀ W) (toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
          ≡ toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAlignedᶜ₀ inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
    → instᵐ (marksᶜ₀ W) ⊢
        renameᵗ (toRenameᵗ (skip (ηᴸᶜ₀ W)))
          (lookupStore Σᴸ Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ₀ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Xᴸ} {Fin.zero} ()
  reps {Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skip (ηᴸᶜ₀ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ₀ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ₀ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) Yᴿ)
  unmatched Fin.zero no-source = fresh
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ₀ inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ₀ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ₀ W) (toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑★
    → lookupStore Σᴸ Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ₀ W)) Xᴿ
        ≢ toRenameᵗ (skip (ηᴸᶜ₀ W)) Xᴸ
  unoccupied Xᴸ mark entry Fin.zero ()
  unoccupied Xᴸ mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ₀ inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)

directInvariantsᶜ₀
    (bind-left-rawᶜ₀ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W A eqᴸ) =
  direct-world-invariantsᶜ₀ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ₀ W

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ₀ W) (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ₀ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≡ toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
    → instᵐ (marksᶜ₀ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ₀ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿᶜ₀ W)))
          (lookupStore Σᴿ Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ₀ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-skip (ηᴿᶜ₀ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ₀ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ)
    → lookupStore Σᴿ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ] (lookupStore Σᴿ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
            ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ₀ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ₀ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ₀ W) (toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (skip (ηᴿᶜ₀ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ₀ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ ()
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ₀ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)


-- Endpoint indices make both stores and both term contexts definitionally
-- fixed across this graph.  Its last premise compares the direct store
-- entries; there is deliberately no representation-chain closure.

data RebaseSourceᶜ₀ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ₀ Cᴿ) :
    Cᴸ ⊑ᶜ₀ Cᴿ → TyVar (Δᵉ Cᴸ) → TyVar (Δᵉ Cᴿ) → Set where
  rebase-sourceᶜ₀ : ∀ {W′ : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
    → (center-same : centerᶜ₀ W′ ≡ centerᶜ₀ W)
    → (∀ {Yᴸ} → Yᴸ ≢ Xᴸ
        → toRenameᵗ (ηᴸᶜ₀ W′) Yᴸ
          ≡ subst Fin.Fin (sym center-same) (toRenameᵗ (ηᴸᶜ₀ W) Yᴸ))
    → (∀ Yᴿ → toRenameᵗ (ηᴿᶜ₀ W′) Yᴿ
        ≡ subst Fin.Fin (sym center-same) (toRenameᵗ (ηᴿᶜ₀ W) Yᴿ))
    → toRenameᵗ (ηᴸᶜ₀ W′) Xᴸ ≡ toRenameᵗ (ηᴿᶜ₀ W′) Xᴿ
    → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ₀⟨ W′ ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
    → RebaseSourceᶜ₀ W W′ Xᴸ Xᴿ


sameWorldRebaseSourceᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    {Xᴸ : TyVar (Δᵉ Cᴸ)} {Xᴿ : TyVar (Δᵉ Cᴿ)}
  → toRenameᵗ (ηᴸᶜ₀ W) Xᴸ ≡ toRenameᵗ (ηᴿᶜ₀ W) Xᴿ
  → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ₀⟨ W ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
  → RebaseSourceᶜ₀ W W Xᴸ Xᴿ
sameWorldRebaseSourceᶜ₀ aligned represented =
  rebase-sourceᶜ₀ refl (λ _ → refl) (λ _ → refl) aligned represented
