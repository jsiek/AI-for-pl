module D16PairedSealRecalibrationProbe where

-- File Charter:
--   * Expands the live Examples2 YZ paired-seal stores and alignment.
--   * Checks that changing only the Z center from X⊑★ to X⊑X makes
--     the live variable-to-dynamic type-imprecision judgment empty.
--   * Drafts store-mediated and seal-boundary recalibration candidates
--     without changing the live type- or term-imprecision relations.
--   * Checks the recalibrated fixture against all four landed world
--     invariants and records why boundary dynamization fails invariant (5).

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (TyCtx; Ty; TyVar; ★; ＇_; ‵_; `ℕ; _⇒_)
open import TyStore using
  (TyStore; store-empty; store-bind; lookupStore)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Imprecision using
  (ImpEnv; X⊑X; X⊑★; ★⊑★; ⇒⊑⇒)
import Imprecision as I
import proof.DGG.CtxImp as CTX
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.DGG.WorldInvariants as WI

------------------------------------------------------------------------
-- The fully expanded YZ fixture at Examples2 checkpoints 3 and 4
------------------------------------------------------------------------

yz-source-store : TyStore 3
yz-source-store =
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) (‵ `ℕ)

yz-target-store : TyStore 2
yz-target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

examples2-source-store₃-expanded : Ex.right-store₃ ≡ yz-source-store
examples2-source-store₃-expanded = refl

examples2-source-store₄-expanded : Ex.right-store₄ ≡ yz-source-store
examples2-source-store₄-expanded = refl

examples2-target-store₃-expanded :
  Ex2.left-path-target-store₃ ≡ yz-target-store
examples2-target-store₃-expanded = refl

examples2-target-store₄-expanded :
  Ex2.left-path-target-store₄ ≡ yz-target-store
examples2-target-store₄-expanded = refl

yz-source-η : 3 ↪ᵗ 3
yz-source-η = keep (keep (keep empty))

yz-target-η : 2 ↪ᵗ 3
yz-target-η = skip (keep (keep empty))

yz-dynamic-env : ImpEnv 3
yz-dynamic-env Fin.zero = X⊑★
yz-dynamic-env (Fin.suc Fin.zero) = X⊑★
yz-dynamic-env (Fin.suc (Fin.suc Fin.zero)) = X⊑★

yz-precise-Z-env : ImpEnv 3
yz-precise-Z-env Fin.zero = X⊑★
yz-precise-Z-env (Fin.suc Fin.zero) = X⊑★
yz-precise-Z-env (Fin.suc (Fin.suc Fin.zero)) = X⊑X

yz-dynamic-world : CTX.World 3 2 3
yz-dynamic-world =
  CTX.world yz-source-η yz-target-η yz-dynamic-env
    yz-source-store yz-target-store

yz-precise-Z-world : CTX.World 3 2 3
yz-precise-Z-world =
  CTX.world yz-source-η yz-target-η yz-precise-Z-env
    yz-source-store yz-target-store

------------------------------------------------------------------------
-- The forcing judgment
------------------------------------------------------------------------

yz-Z-to-star-dynamic :
  (＇ (Fin.suc (Fin.suc Fin.zero)))
    CTX.⊑ᵂ⟨ yz-dynamic-world ⟩ ★
yz-Z-to-star-dynamic = I.X⊑★ refl

yz-Z-function-to-star-dynamic :
  ((＇ (Fin.suc (Fin.suc Fin.zero)))
    ⇒ (＇ (Fin.suc (Fin.suc Fin.zero))))
    CTX.⊑ᵂ⟨ yz-dynamic-world ⟩ (★ ⇒ ★)
yz-Z-function-to-star-dynamic =
  ⇒⊑⇒ yz-Z-to-star-dynamic yz-Z-to-star-dynamic

yz-Z-to-star-precise-empty :
  (＇ (Fin.suc (Fin.suc Fin.zero)))
    CTX.⊑ᵂ⟨ yz-precise-Z-world ⟩ ★
  → ⊥
yz-Z-to-star-precise-empty (I.X⊑★ ())

yz-Z-function-to-star-precise-empty :
  ((＇ (Fin.suc (Fin.suc Fin.zero)))
    ⇒ (＇ (Fin.suc (Fin.suc Fin.zero))))
    CTX.⊑ᵂ⟨ yz-precise-Z-world ⟩ (★ ⇒ ★)
  → ⊥
yz-Z-function-to-star-precise-empty
    (I.⇒⊑⇒ Z-domain-to-star Z-codomain-to-star) =
  yz-Z-to-star-precise-empty Z-domain-to-star

------------------------------------------------------------------------
-- Candidate A: store-mediated variable-to-dynamic imprecision
------------------------------------------------------------------------

infix 4 _⊑ˢ⟨_⟩_

data _⊑ˢ⟨_⟩_ { Δᴸ Δᴿ Δ : TyCtx}
    : Ty Δᴸ → CTX.World Δᴸ Δᴿ Δ → Ty Δᴿ → Set where
  live : ∀ {A B} {W : CTX.World Δᴸ Δᴿ Δ}
    → A CTX.⊑ᵂ⟨ W ⟩ B
    → A ⊑ˢ⟨ W ⟩ B

  ⇒⊑⇒-store : ∀ {A A′ B B′} {W : CTX.World Δᴸ Δᴿ Δ}
    → A ⊑ˢ⟨ W ⟩ A′
    → B ⊑ˢ⟨ W ⟩ B′
    → (A ⇒ B) ⊑ˢ⟨ W ⟩ (A′ ⇒ B′)

  X⊑★-store : ∀ {W : CTX.World Δᴸ Δᴿ Δ} {Xᴸ : TyVar Δᴸ}
    → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
    → lookupStore (CTX.sourceStoreʷ W) Xᴸ ≡ ★
    → (＇ Xᴸ) ⊑ˢ⟨ W ⟩ ★

yz-Z-to-star-store-mediated :
  (＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ˢ⟨ yz-precise-Z-world ⟩ ★
yz-Z-to-star-store-mediated = X⊑★-store refl refl

yz-Z-function-to-star-store-mediated :
  ((＇ (Fin.suc (Fin.suc Fin.zero)))
    ⇒ (＇ (Fin.suc (Fin.suc Fin.zero))))
    ⊑ˢ⟨ yz-precise-Z-world ⟩ (★ ⇒ ★)
yz-Z-function-to-star-store-mediated =
  ⇒⊑⇒-store yz-Z-to-star-store-mediated yz-Z-to-star-store-mediated

------------------------------------------------------------------------
-- Candidate B: a target-unseal exception to mark monotonicity
------------------------------------------------------------------------

RevealMarkTransition : ∀ { Δᴸ Δᴿ Δ}
  → CTX.World Δᴸ Δᴿ Δ
  → CTX.World Δᴸ Δᴿ Δ
  → TyVar Δᴿ
  → Set
RevealMarkTransition W Wᵖ Xᴿ = ∀ Z
  → CTX.impEnvʷ W Z ≡ X⊑★
  → CTX.impEnvʷ Wᵖ Z ≡ X⊑★
    ⊎ (Z ≡ toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
      × CTX.impEnvʷ Wᵖ Z ≡ X⊑X)

yz-target-Z-unseal-transition :
  RevealMarkTransition yz-dynamic-world yz-precise-Z-world
    (Fin.suc Fin.zero)
yz-target-Z-unseal-transition Fin.zero refl = inj₁ refl
yz-target-Z-unseal-transition (Fin.suc Fin.zero) refl = inj₁ refl
yz-target-Z-unseal-transition (Fin.suc (Fin.suc Fin.zero)) refl =
  inj₂ (refl , refl)

yz-dynamic-world-rejects-invariant5 :
  WI.WorldInvariants yz-dynamic-world → ⊥
yz-dynamic-world-rejects-invariant5 inv =
  WI.dynamicStarSourcesUnoccupied inv
    (Fin.suc (Fin.suc Fin.zero)) refl refl
    (Fin.suc Fin.zero) refl

------------------------------------------------------------------------
-- The X⊑X recalibration satisfies all four live world invariants
------------------------------------------------------------------------

yz-precise-Z-world-invariants : WI.WorldInvariants yz-precise-Z-world
yz-precise-Z-world-invariants =
  WI.world-invariants precise representations unmatched no-dynamic-star
  where
  precise : ∀ Xᴸ
    → CTX.impEnvʷ yz-precise-Z-world
        (toRenameᵗ (CTX.ηᴸʷ yz-precise-Z-world) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 2 ]
        toRenameᵗ (CTX.ηᴿʷ yz-precise-Z-world) Xᴿ ≡
        toRenameᵗ (CTX.ηᴸʷ yz-precise-Z-world) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) refl =
    Fin.suc Fin.zero , refl

  representations : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 2}
    → toRenameᵗ (CTX.ηᴸʷ yz-precise-Z-world) Xᴸ ≡
        toRenameᵗ (CTX.ηᴿʷ yz-precise-Z-world) Xᴿ
    → I._⊢_⊑_ (CTX.impEnvʷ yz-precise-Z-world)
        (CTX.embedᴸ yz-precise-Z-world
          (lookupStore (CTX.sourceStoreʷ yz-precise-Z-world) Xᴸ))
        (CTX.embedᴿ yz-precise-Z-world
          (lookupStore (CTX.targetStoreʷ yz-precise-Z-world) Xᴿ))
  representations {Fin.zero} {Fin.zero} ()
  representations {Fin.zero} {Fin.suc Fin.zero} ()
  representations {Fin.suc Fin.zero} {Fin.zero} refl = I.X⊑X
  representations {Fin.suc Fin.zero} {Fin.suc Fin.zero} ()
  representations {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()
  representations {Fin.suc (Fin.suc Fin.zero)}
      {Fin.suc Fin.zero} refl = ★⊑★

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
      → toRenameᵗ (CTX.ηᴸʷ yz-precise-Z-world) Xᴸ
        ≢ toRenameᵗ (CTX.ηᴿʷ yz-precise-Z-world) Xᴿ)
    → lookupStore (CTX.targetStoreʷ yz-precise-Z-world) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
          lookupStore (CTX.targetStoreʷ yz-precise-Z-world) Xᴿ
            ≡ ＇ Yᴿ
        × (∀ Xᴸ
          → toRenameᵗ (CTX.ηᴸʷ yz-precise-Z-world) Xᴸ
            ≢ toRenameᵗ (CTX.ηᴿʷ yz-precise-Z-world) Yᴿ)
  unmatched Fin.zero no-source =
    ⊥-elim (no-source (Fin.suc Fin.zero) refl)
  unmatched (Fin.suc Fin.zero) no-source =
    ⊥-elim (no-source (Fin.suc (Fin.suc Fin.zero)) refl)

  no-dynamic-star : ∀ Xᴸ
    → CTX.impEnvʷ yz-precise-Z-world
        (toRenameᵗ (CTX.ηᴸʷ yz-precise-Z-world) Xᴸ) ≡ X⊑★
    → lookupStore (CTX.sourceStoreʷ yz-precise-Z-world) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ yz-precise-Z-world) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ yz-precise-Z-world) Xᴸ
  no-dynamic-star Fin.zero refl () Xᴿ
  no-dynamic-star (Fin.suc Fin.zero) refl () Xᴿ
  no-dynamic-star (Fin.suc (Fin.suc Fin.zero)) () entry Xᴿ

------------------------------------------------------------------------
-- Candidate C: raw reinterpretation of X⊑X (rejected by the probe)
------------------------------------------------------------------------

infix 4 _⊑ʳ⟨_⟩_

data _⊑ʳ⟨_⟩_ { Δᴸ Δᴿ Δ : TyCtx}
    : Ty Δᴸ → CTX.World Δᴸ Δᴿ Δ → Ty Δᴿ → Set where
  X⊑★-raw : ∀ {W : CTX.World Δᴸ Δᴿ Δ} {Xᴸ : TyVar Δᴸ}
    → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
    → (＇ Xᴸ) ⊑ʳ⟨ W ⟩ ★

raw-precise-env : ImpEnv 1
raw-precise-env Fin.zero = X⊑X

raw-counterexample-world : CTX.World 1 1 1
raw-counterexample-world =
  CTX.world (keep empty) (keep empty) raw-precise-env
    (store-bind store-empty (‵ `ℕ))
    (store-bind store-empty (‵ `ℕ))

raw-rule-ignores-nondynamic-store :
  (＇ Fin.zero) ⊑ʳ⟨ raw-counterexample-world ⟩ ★
  × lookupStore (CTX.sourceStoreʷ raw-counterexample-world) Fin.zero
      ≡ ‵ `ℕ
raw-rule-ignores-nondynamic-store = X⊑★-raw refl , refl
