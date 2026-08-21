{-# OPTIONS --safe #-}

module proof.DGG.TwoCtxWorldInvariants where

-- File Charter:
--   * Derives the four direct nominal invariants for every constructor of the
--     two-Ctx world, with endpoint stores obtained from the relation indices.
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
open import proof.DGG.TwoCtxWorld


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


record DirectWorldInvariantsᶜ {Cᴸ Cᴿ : Ctx}
    (W : Cᴸ ⊑ᶜ Cᴿ) : Set where
  constructor direct-world-invariantsᶜ
  field
    preciseMarksAlignedᶜ :
      ∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
      → marksᶜ W (toRenameᵗ (ηᴸᶜ W) Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar (Δᵉ Cᴿ) ]
          toRenameᵗ (ηᴿᶜ W) Xᴿ ≡ toRenameᵗ (ηᴸᶜ W) Xᴸ

    representationsImpreciseᶜ :
      ∀ {Xᴸ : TyVar (Δᵉ Cᴸ)} {Xᴿ : TyVar (Δᵉ Cᴿ)}
      → toRenameᵗ (ηᴸᶜ W) Xᴸ ≡ toRenameᵗ (ηᴿᶜ W) Xᴿ
      → marksᶜ W ⊢
          renameᵗ (toRenameᵗ (ηᴸᶜ W)) (lookupStore (Σᵉ Cᴸ) Xᴸ)
          ⊑ renameᵗ (toRenameᵗ (ηᴿᶜ W)) (lookupStore (Σᵉ Cᴿ) Xᴿ)

    unmatchedTargetsDynamicᶜ :
      ∀ (Xᴿ : TyVar (Δᵉ Cᴿ))
      → (∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
          → toRenameᵗ (ηᴸᶜ W) Xᴸ ≢ toRenameᵗ (ηᴿᶜ W) Xᴿ)
      → lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar (Δᵉ Cᴿ) ]
            (lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ＇ Yᴿ)
          × (∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
              → toRenameᵗ (ηᴸᶜ W) Xᴸ
                ≢ toRenameᵗ (ηᴿᶜ W) Yᴿ)

    dynamicStarSourcesUnoccupiedᶜ :
      ∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
      → marksᶜ W (toRenameᵗ (ηᴸᶜ W) Xᴸ) ≡ X⊑★
      → lookupStore (Σᵉ Cᴸ) Xᴸ ≡ ★
      → ∀ (Xᴿ : TyVar (Δᵉ Cᴿ))
      → toRenameᵗ (ηᴿᶜ W) Xᴿ ≢ toRenameᵗ (ηᴸᶜ W) Xᴸ

open DirectWorldInvariantsᶜ public


skipCenter-invariantsᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
  → DirectWorldInvariantsᶜ W
  → DirectWorldInvariantsᶜ (skip-centerᶜ W)
skipCenter-invariantsᶜ {Cᴸ = Cᴸ} {Cᴿ = Cᴿ} W inv =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
          ≡ toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
        ≡ toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
    → extendᵐ X⊑★ (marksᶜ W) ⊢
        renameᵗ (toRenameᵗ (skip (ηᴸᶜ W)))
          (lookupStore (Σᵉ Cᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿᶜ W)))
          (lookupStore (Σᵉ Cᴿ) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skip (ηᴸᶜ W) (lookupStore (Σᵉ Cᴸ) Xᴸ)))
      (sym (renameᵗ-skip (ηᴿᶜ W) (lookupStore (Σᵉ Cᴿ) Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ)
    → lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (skip (ηᴿᶜ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , shifted-head-no-source)
    where
    shifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ W)) Yᴿ
    shifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (Σᵉ Cᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
        ≢ toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
  unoccupied Xᴸ mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)


directInvariantsᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
  → DirectWorldInvariantsᶜ W
directInvariantsᶜ emptyᶜ =
  direct-world-invariantsᶜ (λ ()) (λ { {()} }) (λ ()) (λ ())
directInvariantsᶜ (skip-centerᶜ W) =
  skipCenter-invariantsᶜ W (directInvariantsᶜ W)
directInvariantsᶜ
    (lift-both-rawᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W v eqᴸ eqᴿ) =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W

  precise : ∀ Xᴸ
    → extendᵐ v (marksᶜ W) (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ)
        ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
    → extendᵐ v (marksᶜ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ W)))
          (lookupStore (store-lift Σᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ W)))
          (lookupStore (store-lift Σᴿ) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned = Imprecision.X⊑X
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-lift Σᴿ) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-lift Σᴿ) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ v (marksᶜ W) (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ)
        ≡ X⊑★
    → lookupStore (store-lift Σᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ
    (lift-left-rawᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W eqᴸ) =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≡ toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
    → instᵐ (marksᶜ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ W)))
          (lookupStore (store-lift Σᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿᶜ W)))
          (lookupStore Σᴿ Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-skip (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ)
    → lookupStore Σᴿ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ] (lookupStore Σᴿ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (skip (ηᴿᶜ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-lift Σᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ (bind-termᶜ W represented) =
  direct-world-invariantsᶜ
    (preciseMarksAlignedᶜ inv)
    (representationsImpreciseᶜ inv)
    (unmatchedTargetsDynamicᶜ inv)
    (dynamicStarSourcesUnoccupiedᶜ inv)
  where
  inv = directInvariantsᶜ W

directInvariantsᶜ
    (bind-both-star-rawᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      {A = A} {B = B} W represented A≢★ eqᴸ eqᴿ) =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W

  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
    → extendᵐ X⊑★ (marksᶜ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ W) A))
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) B))
      (lift-old-representation represented)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = ⊥-elim (A≢★ entry)
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ
    (bind-both-rawᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} {A = A} {B = B}
      W represented eqᴸ eqᴿ) =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W

  precise : ∀ Xᴸ
    → extendᵐ X⊑X (marksᶜ W)
        (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
    → extendᵐ X⊑X (marksᶜ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ W) A))
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) B))
      (lift-old-representation represented)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑X (marksᶜ W)
        (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero () entry Xᴿ aligned
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ
    (bind-right-rawᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W B fresh eqᴿ) =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
          ≡ toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
        ≡ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
    → instᵐ (marksᶜ W) ⊢
        renameᵗ (toRenameᵗ (skip (ηᴸᶜ W)))
          (lookupStore Σᴸ Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿᶜ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Xᴸ} {Fin.zero} ()
  reps {Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skip (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿᶜ W)) Yᴿ)
  unmatched Fin.zero no-source = fresh
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore Σᴸ Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (keep (ηᴿᶜ W)) Xᴿ
        ≢ toRenameᵗ (skip (ηᴸᶜ W)) Xᴸ
  unoccupied Xᴸ mark entry Fin.zero ()
  unoccupied Xᴸ mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)

directInvariantsᶜ
    (bind-left-rawᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ} W A eqᴸ) =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≡ toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
    → instᵐ (marksᶜ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸᶜ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿᶜ W)))
          (lookupStore Σᴿ Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-skip (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ)
    → lookupStore Σᴿ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ] (lookupStore Σᴿ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
            ≢ toRenameᵗ (skip (ηᴿᶜ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿᶜ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (skip (ηᴿᶜ W)) Xᴿ
        ≢ toRenameᵗ (keep (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ ()
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)


-- Endpoint indices make both stores and both term contexts definitionally
-- fixed across this graph.  Its last premise compares the direct store
-- entries; there is deliberately no representation-chain closure.

data RebaseSourceᶜ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Cᴸ ⊑ᶜ Cᴿ → TyVar (Δᵉ Cᴸ) → TyVar (Δᵉ Cᴿ) → Set where
  rebase-sourceᶜ : ∀ {W′ : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    → (center-same : centerᶜ W′ ≡ centerᶜ W)
    → (∀ {Yᴸ} → Yᴸ ≢ Xᴸ
        → toRenameᵗ (ηᴸᶜ W′) Yᴸ
          ≡ subst Fin.Fin (sym center-same) (toRenameᵗ (ηᴸᶜ W) Yᴸ))
    → (∀ Yᴿ → toRenameᵗ (ηᴿᶜ W′) Yᴿ
        ≡ subst Fin.Fin (sym center-same) (toRenameᵗ (ηᴿᶜ W) Yᴿ))
    → toRenameᵗ (ηᴸᶜ W′) Xᴸ ≡ toRenameᵗ (ηᴿᶜ W′) Xᴿ
    → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W′ ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
    → RebaseSourceᶜ W W′ Xᴸ Xᴿ


sameWorldRebaseSourceᶜ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Xᴸ : TyVar (Δᵉ Cᴸ)} {Xᴿ : TyVar (Δᵉ Cᴿ)}
  → toRenameᵗ (ηᴸᶜ W) Xᴸ ≡ toRenameᵗ (ηᴿᶜ W) Xᴿ
  → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
  → RebaseSourceᶜ W W Xᴸ Xᴿ
sameWorldRebaseSourceᶜ aligned represented =
  rebase-sourceᶜ refl (λ _ → refl) (λ _ → refl) aligned represented
