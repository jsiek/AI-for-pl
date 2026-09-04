{-# OPTIONS --safe #-}

module proof.DGG.notes.ArbitraryInjectionWorldProbe where

-- File Charter:
--   * Exercises the live arbitrary endpoint-injection and pivot-update API in
--     a small world model, without changing the CTI relation.
--   * Checks the empty, center-skip, endpoint-lift, source-only allocation,
--     paired allocation, and one-pivot source-rebase operations.
--   * Reconstructs the two protected-binder critical geometries reached by
--     SourceBindLiftLeftTrustedProbe and checks that both post-allocation
--     source rebases exist.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym)

open import Types using (Ty; TyCtx; TyVar; ＇_; ‵_; ★; `ℕ; renameᵗ)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; _⊢_⊑_; ι⊑★)
open import proof.DGG.World using
  (Injectionᵗ; injectionᵗ; toRenameⁱ; emptyⁱ; skipⁱ; keepⁱ;
   PivotUpdateᵗ; pivot-updateᵗ; pivot-afterᵗ)


------------------------------------------------------------------------
-- A minimal world surface
------------------------------------------------------------------------

record InjectionWorld (Deltaᴸ Deltaᴿ Delta : TyCtx) : Set where
  constructor injection-world
  field
    source-injection : Injectionᵗ Deltaᴸ Delta
    target-injection : Injectionᵗ Deltaᴿ Delta
    marks : ImpEnv Delta

open InjectionWorld public


empty-world : InjectionWorld zero zero zero
empty-world = injection-world emptyⁱ emptyⁱ (λ ())


skip-center : ∀ {Deltaᴸ Deltaᴿ Delta}
  → InjectionWorld Deltaᴸ Deltaᴿ Delta
  → InjectionWorld Deltaᴸ Deltaᴿ (suc Delta)
skip-center W = injection-world
  (skipⁱ (source-injection W))
  (skipⁱ (target-injection W))
  (extendᵐ X⊑★ (marks W))


lift-both : ∀ {Deltaᴸ Deltaᴿ Delta}
  → VarImp
  → InjectionWorld Deltaᴸ Deltaᴿ Delta
  → InjectionWorld (suc Deltaᴸ) (suc Deltaᴿ) (suc Delta)
lift-both v W = injection-world
  (keepⁱ (source-injection W))
  (keepⁱ (target-injection W))
  (extendᵐ v (marks W))


lift-left : ∀ {Deltaᴸ Deltaᴿ Delta}
  → InjectionWorld Deltaᴸ Deltaᴿ Delta
  → InjectionWorld (suc Deltaᴸ) Deltaᴿ (suc Delta)
lift-left W = injection-world
  (keepⁱ (source-injection W))
  (skipⁱ (target-injection W))
  (extendᵐ X⊑★ (marks W))


target-only-bind : ∀ {Deltaᴸ Deltaᴿ Delta}
  → InjectionWorld Deltaᴸ Deltaᴿ Delta
  → InjectionWorld Deltaᴸ (suc Deltaᴿ) (suc Delta)
target-only-bind W = injection-world
  (skipⁱ (source-injection W))
  (keepⁱ (target-injection W))
  (extendᵐ X⊑★ (marks W))


source-only-bind : ∀ {Deltaᴸ Deltaᴿ Delta}
  → InjectionWorld Deltaᴸ Deltaᴿ Delta
  → InjectionWorld (suc Deltaᴸ) Deltaᴿ (suc Delta)
source-only-bind W = injection-world
  (keepⁱ (source-injection W))
  (skipⁱ (target-injection W))
  (extendᵐ X⊑★ (marks W))


infix 4 _⊢ᵀ_⊑_

_⊢ᵀ_⊑_ : ∀ {Deltaᴸ Deltaᴿ Delta}
  → InjectionWorld Deltaᴸ Deltaᴿ Delta
  → Ty Deltaᴸ → Ty Deltaᴿ → Set
W ⊢ᵀ A ⊑ B =
  marks W ⊢
    renameᵗ (toRenameⁱ (source-injection W)) A
      ⊑ renameᵗ (toRenameⁱ (target-injection W)) B


paired-bind : ∀ {Deltaᴸ Deltaᴿ Delta}
    {A : Ty Deltaᴸ} {B : Ty Deltaᴿ}
  → (v : VarImp)
  → (W : InjectionWorld Deltaᴸ Deltaᴿ Delta)
  → W ⊢ᵀ A ⊑ B
  → InjectionWorld (suc Deltaᴸ) (suc Deltaᴿ) (suc Delta)
paired-bind v W represented = injection-world
  (keepⁱ (source-injection W))
  (keepⁱ (target-injection W))
  (extendᵐ v (marks W))


rebase-source : ∀ {Deltaᴸ Deltaᴿ Delta}
    (W : InjectionWorld Deltaᴸ Deltaᴿ Delta)
    (X : TyVar Deltaᴸ) (Y : TyVar Deltaᴿ)
  → PivotUpdateᵗ (source-injection W) X
      (toRenameⁱ (target-injection W) Y)
  → InjectionWorld Deltaᴸ Deltaᴿ Delta
rebase-source W X Y update = injection-world
  (pivot-afterᵗ update) (target-injection W) (marks W)


------------------------------------------------------------------------
-- The two trusted protected-binder critical geometries
------------------------------------------------------------------------

-- This is checkpoint 1 before the protected source binder is restored:
-- there are no source variables and the target contains beta, then alpha.
checkpoint₁-base : InjectionWorld zero 2 2
checkpoint₁-base = target-only-bind (target-only-bind empty-world)


-- Source-only crossing: allocate A on the source, then restore protected X.
--
--   source: X↦0, A↦1
--   target: beta↦2, alpha↦3
source-critical : InjectionWorld 2 2 4
source-critical = lift-left (source-only-bind checkpoint₁-base)


source-critical-X :
  toRenameⁱ (source-injection source-critical) Fin.zero ≡ Fin.zero
source-critical-X = refl


source-critical-A :
  toRenameⁱ (source-injection source-critical) (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
source-critical-A = refl


source-critical-beta :
  toRenameⁱ (target-injection source-critical) Fin.zero
    ≡ Fin.suc (Fin.suc Fin.zero)
source-critical-beta = refl


source-critical-alpha :
  toRenameⁱ (target-injection source-critical) (Fin.suc Fin.zero)
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
source-critical-alpha = refl


-- Paired crossing: allocate A ⊑ A′, then restore protected X.
--
--   source: X↦0, A↦1
--   target: A′↦1, beta↦2, alpha↦3
paired-critical : InjectionWorld 2 3 4
paired-critical =
  lift-left (paired-bind {A = ‵ `ℕ} {B = ★}
    X⊑★ checkpoint₁-base ι⊑★)


paired-critical-X :
  toRenameⁱ (source-injection paired-critical) Fin.zero ≡ Fin.zero
paired-critical-X = refl


paired-critical-A :
  toRenameⁱ (source-injection paired-critical) (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
paired-critical-A = refl


paired-critical-A′ :
  toRenameⁱ (target-injection paired-critical) Fin.zero
    ≡ Fin.suc Fin.zero
paired-critical-A′ = refl


paired-critical-beta :
  toRenameⁱ (target-injection paired-critical) (Fin.suc Fin.zero)
    ≡ Fin.suc (Fin.suc Fin.zero)
paired-critical-beta = refl


paired-critical-alpha :
  toRenameⁱ (target-injection paired-critical)
      (Fin.suc (Fin.suc Fin.zero))
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
paired-critical-alpha = refl


------------------------------------------------------------------------
-- The crossing injection and the two post-allocation rebases
------------------------------------------------------------------------

crossing-map : TyVar 2 → TyVar 4
crossing-map Fin.zero = Fin.suc (Fin.suc (Fin.suc Fin.zero))
crossing-map (Fin.suc Fin.zero) = Fin.suc Fin.zero


crossing-map-injective : ∀ {X Y : TyVar 2}
  → crossing-map X ≡ crossing-map Y
  → X ≡ Y
crossing-map-injective {Fin.zero} {Fin.zero} eq = refl
crossing-map-injective {Fin.zero} {Fin.suc Fin.zero} ()
crossing-map-injective {Fin.suc Fin.zero} {Fin.zero} ()
crossing-map-injective {Fin.suc Fin.zero} {Fin.suc Fin.zero} eq = refl


crossing-injection : Injectionᵗ 2 4
crossing-injection = injectionᵗ crossing-map crossing-map-injective


critical-off-pivot : ∀
    (before : Injectionᵗ 2 4)
  → toRenameⁱ before (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero
  → ∀ Y → Y ≢ Fin.zero
  → toRenameⁱ crossing-injection Y ≡ toRenameⁱ before Y
critical-off-pivot before A-at-one Fin.zero Y≠X =
  ⊥-elim (Y≠X refl)
critical-off-pivot before A-at-one (Fin.suc Fin.zero) Y≠X = sym A-at-one


source-critical-update : PivotUpdateᵗ
  (source-injection source-critical) Fin.zero
  (toRenameⁱ (target-injection source-critical) (Fin.suc Fin.zero))
source-critical-update = pivot-updateᵗ (λ ()) crossing-injection refl
  (critical-off-pivot (source-injection source-critical) refl)


source-critical-rebased : InjectionWorld 2 2 4
source-critical-rebased = rebase-source source-critical Fin.zero
  (Fin.suc Fin.zero) source-critical-update


source-rebase-aligns-alpha :
  toRenameⁱ (source-injection source-critical-rebased) Fin.zero
    ≡ toRenameⁱ (target-injection source-critical-rebased)
        (Fin.suc Fin.zero)
source-rebase-aligns-alpha = refl


source-rebase-preserves-A :
  toRenameⁱ (source-injection source-critical-rebased)
      (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
source-rebase-preserves-A = refl


paired-critical-update : PivotUpdateᵗ
  (source-injection paired-critical) Fin.zero
  (toRenameⁱ (target-injection paired-critical)
    (Fin.suc (Fin.suc Fin.zero)))
paired-critical-update = pivot-updateᵗ (λ ()) crossing-injection refl
  (critical-off-pivot (source-injection paired-critical) refl)


paired-critical-rebased : InjectionWorld 2 3 4
paired-critical-rebased = rebase-source paired-critical Fin.zero
  (Fin.suc (Fin.suc Fin.zero)) paired-critical-update


paired-rebase-aligns-alpha :
  toRenameⁱ (source-injection paired-critical-rebased) Fin.zero
    ≡ toRenameⁱ (target-injection paired-critical-rebased)
        (Fin.suc (Fin.suc Fin.zero))
paired-rebase-aligns-alpha = refl


paired-rebase-preserves-A-A′ :
  toRenameⁱ (source-injection paired-critical-rebased)
      (Fin.suc Fin.zero)
    ≡ toRenameⁱ (target-injection paired-critical-rebased) Fin.zero
paired-rebase-preserves-A-A′ = refl


-- Central type imprecision continues to read by ordinary renaming.  The
-- protected X now occupies alpha's X⊑★ cell, while the paired allocation
-- remains aligned at center 1.
source-protected-imprecision :
  source-critical-rebased ⊢ᵀ (＇ Fin.zero) ⊑ ★
source-protected-imprecision = Imprecision.X⊑★ refl


paired-protected-imprecision :
  paired-critical-rebased ⊢ᵀ (＇ Fin.zero) ⊑ ★
paired-protected-imprecision = Imprecision.X⊑★ refl


paired-allocation-imprecision :
  paired-critical-rebased ⊢ᵀ (‵ `ℕ) ⊑ ★
paired-allocation-imprecision = ι⊑★
