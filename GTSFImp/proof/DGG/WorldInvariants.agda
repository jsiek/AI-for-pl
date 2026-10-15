{-# OPTIONS --safe #-}

module proof.DGG.WorldInvariants where

-- File Charter:
--   * Derives the four direct allocation invariants for histories containing
--     no source-rebase change, with endpoint stores obtained from the world
--     indices.
--   * Requires `sourceRebaseCountᶜ W ≡ 0` explicitly because current
--     alignment after a rebase is not allocation pairing.
--   * Gives the direct-store rebase graph and its same-world case without
--     following representation aliases.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using
  (Ty; TyCtx; TyVar; ＇_; ‵_; ★; _⇒_; `∀; ⇑ᵗ; renameᵗ)
open import TyStore using (lookupStore; store-lift; store-bind)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; instᵐ; _⊢_⊑_)
open import proof.ImprecisionConsistency using (rename-⊑)
open import proof.DGG.World


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
      → marksᶜ W (toRenameⁱ (ηᴸᶜ W) Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar (Δᵉ Cᴿ) ]
          toRenameⁱ (ηᴿᶜ W) Xᴿ ≡ toRenameⁱ (ηᴸᶜ W) Xᴸ

    representationsImpreciseᶜ :
      ∀ {Xᴸ : TyVar (Δᵉ Cᴸ)} {Xᴿ : TyVar (Δᵉ Cᴿ)}
      → toRenameⁱ (ηᴸᶜ W) Xᴸ ≡ toRenameⁱ (ηᴿᶜ W) Xᴿ
      → marksᶜ W ⊢
          renameᵗ (toRenameⁱ (ηᴸᶜ W)) (lookupStore (Σᵉ Cᴸ) Xᴸ)
          ⊑ renameᵗ (toRenameⁱ (ηᴿᶜ W)) (lookupStore (Σᵉ Cᴿ) Xᴿ)

    unmatchedTargetsDynamicᶜ :
      ∀ (Xᴿ : TyVar (Δᵉ Cᴿ))
      → (∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
          → toRenameⁱ (ηᴸᶜ W) Xᴸ ≢ toRenameⁱ (ηᴿᶜ W) Xᴿ)
      → lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar (Δᵉ Cᴿ) ]
            (lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ＇ Yᴿ)
          × (∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
              → toRenameⁱ (ηᴸᶜ W) Xᴸ
                ≢ toRenameⁱ (ηᴿᶜ W) Yᴿ)

    dynamicStarSourcesUnoccupiedᶜ :
      ∀ (Xᴸ : TyVar (Δᵉ Cᴸ))
      → marksᶜ W (toRenameⁱ (ηᴸᶜ W) Xᴸ) ≡ X⊑★
      → lookupStore (Σᵉ Cᴸ) Xᴸ ≡ ★
      → ∀ (Xᴿ : TyVar (Δᵉ Cᴿ))
      → toRenameⁱ (ηᴿᶜ W) Xᴿ ≢ toRenameⁱ (ηᴸᶜ W) Xᴸ

open DirectWorldInvariantsᶜ public


skipCenter-invariantsᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
  → DirectWorldInvariantsᶜ W
  → DirectWorldInvariantsᶜ (skip-centerᶜ W)
skipCenter-invariantsᶜ {Cᴸ = Cᴸ} {Cᴿ = Cᴿ} W inv =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
          ≡ toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
        ≡ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
    → extendᵐ X⊑★ (marksᶜ W) ⊢
        renameᵗ (toRenameⁱ (skipⁱ (ηᴸᶜ W)))
          (lookupStore (Σᵉ Cᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameⁱ (skipⁱ (ηᴿᶜ W)))
          (lookupStore (Σᵉ Cᴿ) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skipⁱ (ηᴸᶜ W) (lookupStore (Σᵉ Cᴸ) Xᴸ)))
      (sym (renameᵗ-skipⁱ (ηᴿᶜ W) (lookupStore (Σᵉ Cᴿ) Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ)
    → lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (Σᵉ Cᴿ) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
            ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , shifted-head-no-source)
    where
    shifted-head-no-source : ∀ Xᴸ
      → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Yᴿ
    shifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (Σᵉ Cᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
        ≢ toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
  unoccupied Xᴸ mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)


directInvariantsᶜ : ∀ {Cᴸ Cᴿ} (W : Cᴸ ⊑ᶜ Cᴿ)
  → sourceRebaseCountᶜ W ≡ 0
  → DirectWorldInvariantsᶜ W
directInvariantsᶜ emptyᶜ refl =
  direct-world-invariantsᶜ (λ ()) (λ { {()} }) (λ ()) (λ ())
directInvariantsᶜ (W ▻ᶜ center-changeᶜ) no-rebase =
  skipCenter-invariantsᶜ W (directInvariantsᶜ W no-rebase)
directInvariantsᶜ
    (W ▻ᶜ lift-both-changeᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      v eqᴸ eqᴿ) no-rebase =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W no-rebase

  precise : ∀ Xᴸ
    → extendᵐ v (marksᶜ W) (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ)
        ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
          ≡ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≡ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
    → extendᵐ v (marksᶜ W) ⊢
        renameᵗ (toRenameⁱ (keepⁱ (ηᴸᶜ W)))
          (lookupStore (store-lift Σᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameⁱ (keepⁱ (ηᴿᶜ W)))
          (lookupStore (store-lift Σᴿ) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned = Imprecision.X⊑X
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-lift Σᴿ) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-lift Σᴿ) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
            ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Yᴿ)
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
      → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ v (marksᶜ W) (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ)
        ≡ X⊑★
    → lookupStore (store-lift Σᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
        ≢ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ
    (W ▻ᶜ lift-left-changeᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      eqᴸ) no-rebase =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W no-rebase

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
          ≡ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≡ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
    → instᵐ (marksᶜ W) ⊢
        renameᵗ (toRenameⁱ (keepⁱ (ηᴸᶜ W)))
          (lookupStore (store-lift Σᴸ) Xᴸ)
        ⊑ renameᵗ (toRenameⁱ (skipⁱ (ηᴿᶜ W)))
          (lookupStore Σᴿ Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-skipⁱ (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ)
    → lookupStore Σᴿ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ] (lookupStore Σᴿ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
            ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-lift Σᴸ) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
        ≢ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ (W ▻ᶜ bind-term-changeᶜ represented) no-rebase =
  direct-world-invariantsᶜ
    (preciseMarksAlignedᶜ inv)
    (representationsImpreciseᶜ inv)
    (unmatchedTargetsDynamicᶜ inv)
    (dynamicStarSourcesUnoccupiedᶜ inv)
  where
  inv = directInvariantsᶜ W no-rebase

directInvariantsᶜ
    (W ▻ᶜ bind-both-star-changeᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      {A = A} {B = B} represented A≢★ eqᴸ eqᴿ) no-rebase =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W no-rebase

  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
          ≡ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≡ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
    → extendᵐ X⊑★ (marksᶜ W) ⊢
        renameᵗ (toRenameⁱ (keepⁱ (ηᴸᶜ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameⁱ (keepⁱ (ηᴿᶜ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) A))
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) B))
      (lift-old-representation represented)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
            ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Yᴿ)
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
      → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (marksᶜ W)
        (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
        ≢ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = ⊥-elim (A≢★ entry)
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ
    (W ▻ᶜ bind-both-changeᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      {A = A} {B = B} represented eqᴸ eqᴿ) no-rebase =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W no-rebase

  precise : ∀ Xᴸ
    → extendᵐ X⊑X (marksᶜ W)
        (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
          ≡ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≡ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
    → extendᵐ X⊑X (marksᶜ W) ⊢
        renameᵗ (toRenameⁱ (keepⁱ (ηᴸᶜ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameⁱ (keepⁱ (ηᴿᶜ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) A))
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) B))
      (lift-old-representation represented)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
            ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Yᴿ)
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
      → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑X (marksᶜ W)
        (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
        ≢ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero () entry Xᴿ aligned
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ
    (W ▻ᶜ bind-right-changeᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      B fresh eqᴿ) no-rebase =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W no-rebase

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
          ≡ toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
        ≡ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
    → instᵐ (marksᶜ W) ⊢
        renameᵗ (toRenameⁱ (skipⁱ (ηᴸᶜ W)))
          (lookupStore Σᴸ Xᴸ)
        ⊑ renameᵗ (toRenameⁱ (keepⁱ (ηᴿᶜ W)))
          (lookupStore (store-bind Σᴿ B) Xᴿ)
  reps {Xᴸ} {Fin.zero} ()
  reps {Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skipⁱ (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-keep-shiftⁱ (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ)
    → lookupStore (store-bind Σᴿ B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind Σᴿ B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
            ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) Yᴿ)
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
      → toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (keepⁱ (ηᴿᶜ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore Σᴸ Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameⁱ (keepⁱ (ηᴿᶜ W)) Xᴿ
        ≢ toRenameⁱ (skipⁱ (ηᴸᶜ W)) Xᴸ
  unoccupied Xᴸ mark entry Fin.zero ()
  unoccupied Xᴸ mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)

directInvariantsᶜ
    (W ▻ᶜ bind-left-changeᶜ {Σᴸ = Σᴸ} {Σᴿ = Σᴿ}
      A eqᴸ) no-rebase =
  direct-world-invariantsᶜ precise reps unmatched unoccupied
  where
  inv = directInvariantsᶜ W no-rebase

  precise : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
          ≡ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAlignedᶜ inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≡ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
    → instᵐ (marksᶜ W) ⊢
        renameᵗ (toRenameⁱ (keepⁱ (ηᴸᶜ W)))
          (lookupStore (store-bind Σᴸ A) Xᴸ)
        ⊑ renameᵗ (toRenameⁱ (skipⁱ (ηᴿᶜ W)))
          (lookupStore Σᴿ Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shiftⁱ (ηᴸᶜ W) (lookupStore Σᴸ Xᴸ)))
      (sym (renameᵗ-skipⁱ (ηᴿᶜ W) (lookupStore Σᴿ Xᴿ)))
      (lift-old-representation
        (representationsImpreciseᶜ inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ)
    → lookupStore Σᴿ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ] (lookupStore Σᴿ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
            ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamicᶜ inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
        ≢ toRenameⁱ (skipⁱ (ηᴿᶜ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (marksᶜ W) (toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind Σᴸ A) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameⁱ (skipⁱ (ηᴿᶜ W)) Xᴿ
        ≢ toRenameⁱ (keepⁱ (ηᴸᶜ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ ()
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupiedᶜ inv Xᴸ mark
      (unshift-star entry) Xᴿ (fin-suc-injective aligned)

directInvariantsᶜ
    (W ▻ᶜ rebase-source-changeᶜ X Y update role represented) ()


-- Endpoint indices make both stores and both term contexts definitionally
-- fixed across this graph.  Its last premise compares the direct store
-- entries; there is deliberately no representation-chain closure.

data RebaseSourceᶜ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Cᴸ ⊑ᶜ Cᴿ → TyVar (Δᵉ Cᴸ) → TyVar (Δᵉ Cᴿ) → Set where
  rebase-sourceᶜ : ∀ {W′ : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    → (center-same : centerᶜ W′ ≡ centerᶜ W)
    → (∀ {Yᴸ} → Yᴸ ≢ Xᴸ
        → toRenameⁱ (ηᴸᶜ W′) Yᴸ
          ≡ subst Fin.Fin (sym center-same) (toRenameⁱ (ηᴸᶜ W) Yᴸ))
    → (∀ Yᴿ → toRenameⁱ (ηᴿᶜ W′) Yᴿ
        ≡ subst Fin.Fin (sym center-same) (toRenameⁱ (ηᴿᶜ W) Yᴿ))
    → toRenameⁱ (ηᴸᶜ W′) Xᴸ ≡ toRenameⁱ (ηᴿᶜ W′) Xᴿ
    → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W′ ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
    → RebaseSourceᶜ W W′ Xᴸ Xᴿ


sameWorldRebaseSourceᶜ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Xᴸ : TyVar (Δᵉ Cᴸ)} {Xᴿ : TyVar (Δᵉ Cᴿ)}
  → toRenameⁱ (ηᴸᶜ W) Xᴸ ≡ toRenameⁱ (ηᴿᶜ W) Xᴿ
  → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
  → RebaseSourceᶜ W W Xᴸ Xᴿ
sameWorldRebaseSourceᶜ aligned represented =
  rebase-sourceᶜ refl (λ _ → refl) (λ _ → refl) aligned represented
