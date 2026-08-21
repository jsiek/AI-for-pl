module proof.DGG.CtxImp where

-- File Charter:
--   * Defines the local world layer shared by cast-term imprecision and its
--     metatheory: endpoint embeddings, world builders, and world invariants.
--   * Defines world-indexed term-context imprecision and its lift/transport
--     operations.
--   * Defines canonical store representations, local rebasing, occupancy,
--     and wrapper-partner predicates used at cast boundaries.
--   * Exports no term-imprecision relation and depends only on the underlying
--     type, store, consistency, conversion, and cast-term syntax layers.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; lookupStore;
   _∋_⦂_; Z∋; S-bind∋)
open import TermCtx using (TermCtx)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _∼_; _↪ᵗ_; empty; keep; skip;
   id↪ᵗ; toRenameᵗ; id; _!)
open import Conversion using (Conv↑; Conv↓; _⊢↑_; _⊢↓_)
open import Conversion using
  (unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_; `∀↓_; id↓;
   ⊢↑-∀; ⊢↑-id; PivotJoin; join-none; join-left; join-right; join-both;
   _⊢↑[_]_; ⊢↑-unsealˣ; ⊢↑-⇒ˣ; ⊢↑-∀ˣ; ⊢↑-∀-idˣ; ⊢↑-idˣ;
   _⊢↓[_]_; ⊢↓-sealˣ; ⊢↓-⇒ˣ; ⊢↓-∀ˣ; ⊢↓-∀-idˣ; ⊢↓-idˣ)
open import Imprecision
open import Primitives using (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms
  using
    (Term; Var; Value; Ctx; ⟨_,_,_⟩; _⊢_⦂_; `_ ; ƛ_; _·_; Λ_;
     _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame; ⇑ᵗᵐ;
     ⊢·; ⊢⟨⟩; ⊢•; ⊢reveal)
open import proof.ImprecisionConsistency using
  (refl⊑; rename-⊑; toRenameᵗ-injective; imp-env-weaken)
open import proof.TypeInTermSubst using
  (toRename-keep-eq)

------------------------------------------------------------------------
-- Local worlds
------------------------------------------------------------------------

infixr 9 _∘↪_

_∘↪_ : ∀ {Δ₁ Δ₂ Δ₃}
  → Δ₂ ↪ᵗ Δ₃
  → Δ₁ ↪ᵗ Δ₂
  → Δ₁ ↪ᵗ Δ₃
π ∘↪ empty = empty
(skip π) ∘↪ η = skip (π ∘↪ η)
(keep π) ∘↪ (keep η) = keep (π ∘↪ η)
(keep π) ∘↪ (skip η) = skip (π ∘↪ η)

toRenameᵗ-∘ : ∀ {Δ₁ Δ₂ Δ₃}
  → (π : Δ₂ ↪ᵗ Δ₃)
  → (η : Δ₁ ↪ᵗ Δ₂)
  → ∀ X
  → toRenameᵗ (π ∘↪ η) X ≡ toRenameᵗ π (toRenameᵗ η X)
toRenameᵗ-∘ π empty ()
toRenameᵗ-∘ (skip π) (keep η) X =
  cong Fin.suc (toRenameᵗ-∘ π (keep η) X)
toRenameᵗ-∘ (skip π) (skip η) X =
  cong Fin.suc (toRenameᵗ-∘ π (skip η) X)
toRenameᵗ-∘ (keep π) (keep η) Fin.zero = refl
toRenameᵗ-∘ (keep π) (keep η) (Fin.suc X) =
  cong Fin.suc (toRenameᵗ-∘ π η X)
toRenameᵗ-∘ (keep π) (skip η) X =
  cong Fin.suc (toRenameᵗ-∘ π η X)

renameEnv : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → ImpEnv Δ → ImpEnv Δ′
renameEnv empty μ = λ Z → X⊑★
renameEnv (keep π) μ =
  extendᵐ (μ Fin.zero) (renameEnv π (λ X → μ (Fin.suc X)))
renameEnv (skip π) μ = extendᵐ X⊑★ (renameEnv π μ)

renameEnv-image : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) (μ : ImpEnv Δ)
  → ∀ Z → renameEnv π μ (toRenameᵗ π Z) ≡ μ Z
renameEnv-image empty μ ()
renameEnv-image (keep π) μ Fin.zero = refl
renameEnv-image (keep π) μ (Fin.suc Z) =
  renameEnv-image π (λ X → μ (Fin.suc X)) Z
renameEnv-image (skip π) μ Z = renameEnv-image π μ Z

renameEnv-precise-preimage : ∀ {Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (μ : ImpEnv Δ) (Z′ : TyVar Δ′)
  → renameEnv π μ Z′ ≡ X⊑X
  → Σ[ Z ∈ TyVar Δ ] toRenameᵗ π Z ≡ Z′ × μ Z ≡ X⊑X
renameEnv-precise-preimage empty μ Z′ ()
renameEnv-precise-preimage (keep π) μ Fin.zero mark =
  Fin.zero , refl , mark
renameEnv-precise-preimage (keep π) μ (Fin.suc Z′) mark
    with renameEnv-precise-preimage π (λ X → μ (Fin.suc X)) Z′ mark
renameEnv-precise-preimage (keep π) μ (Fin.suc Z′) mark
    | Z , image , old-mark =
  Fin.suc Z , cong Fin.suc image , old-mark
renameEnv-precise-preimage (skip π) μ Fin.zero ()
renameEnv-precise-preimage (skip π) μ (Fin.suc Z′) mark
    with renameEnv-precise-preimage π μ Z′ mark
renameEnv-precise-preimage (skip π) μ (Fin.suc Z′) mark
    | Z , image , old-mark =
  Z , cong Fin.suc image , old-mark

target-fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
  → Fin.suc X ≡ Fin.suc Y
  → X ≡ Y
target-fin-suc-injective refl = refl

targetAligned? : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ) (Z : TyVar Δ)
  → Dec (Σ[ Xᴿ ∈ TyVar Δᴿ ] toRenameᵗ ηᴿ Xᴿ ≡ Z)
targetAligned? empty Z = no λ { (() , eq) }
targetAligned? (keep ηᴿ) Fin.zero = yes (Fin.zero , refl)
targetAligned? (keep ηᴿ) (Fin.suc Z) with targetAligned? ηᴿ Z
targetAligned? (keep ηᴿ) (Fin.suc Z) | yes (Xᴿ , eq) =
  yes (Fin.suc Xᴿ , cong Fin.suc eq)
targetAligned? (keep ηᴿ) (Fin.suc Z) | no unaligned =
  no λ
    { (Fin.zero , ())
    ; (Fin.suc Xᴿ , eq) →
        unaligned (Xᴿ , target-fin-suc-injective eq)
    }
targetAligned? (skip ηᴿ) Fin.zero = no λ { (Xᴿ , ()) }
targetAligned? (skip ηᴿ) (Fin.suc Z) with targetAligned? ηᴿ Z
targetAligned? (skip ηᴿ) (Fin.suc Z) | yes (Xᴿ , eq) =
  yes (Xᴿ , cong Fin.suc eq)
targetAligned? (skip ηᴿ) (Fin.suc Z) | no unaligned =
  no λ { (Xᴿ , eq) →
    unaligned (Xᴿ , target-fin-suc-injective eq) }

honestEnv : ∀ {Δᴿ Δ} → Δᴿ ↪ᵗ Δ → ImpEnv Δ → ImpEnv Δ
honestEnv ηᴿ μ Z with targetAligned? ηᴿ Z
honestEnv ηᴿ μ Z | yes aligned = μ Z
honestEnv ηᴿ μ Z | no unaligned = X⊑★

honestEnv-mono : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ) (μ : ImpEnv Δ) (Z : TyVar Δ)
  → μ Z ≡ X⊑★
  → honestEnv ηᴿ μ Z ≡ X⊑★
honestEnv-mono ηᴿ μ Z dynamic with targetAligned? ηᴿ Z
honestEnv-mono ηᴿ μ Z dynamic | yes aligned = dynamic
honestEnv-mono ηᴿ μ Z dynamic | no unaligned = refl

honestEnv-aligned : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ) (μ : ImpEnv Δ)
    (Z : TyVar Δ)
  → (Σ[ Xᴿ ∈ TyVar Δᴿ ] toRenameᵗ ηᴿ Xᴿ ≡ Z)
  → honestEnv ηᴿ μ Z ≡ μ Z
honestEnv-aligned ηᴿ μ Z target with targetAligned? ηᴿ Z
honestEnv-aligned ηᴿ μ Z target | yes aligned = refl
honestEnv-aligned ηᴿ μ Z target | no unaligned =
  ⊥-elim (unaligned target)

honestEnv-unaligned : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ) (μ : ImpEnv Δ)
    (Z : TyVar Δ)
  → (∀ Xᴿ → toRenameᵗ ηᴿ Xᴿ ≢ Z)
  → honestEnv ηᴿ μ Z ≡ X⊑★
honestEnv-unaligned ηᴿ μ Z no-target with targetAligned? ηᴿ Z
honestEnv-unaligned ηᴿ μ Z no-target | yes (Xᴿ , aligned) =
  ⊥-elim (no-target Xᴿ aligned)
honestEnv-unaligned ηᴿ μ Z no-target | no unaligned = refl

record WorldInvariants {Δᴸ Δᴿ Δ : TyCtx}
    (ηᴸ : Δᴸ ↪ᵗ Δ) (ηᴿ : Δᴿ ↪ᵗ Δ)
    (μ : ImpEnv Δ) (Σᴸ : TyStore Δᴸ) (Σᴿ : TyStore Δᴿ) : Set where
  constructor world-invariants
  field
    preciseMarksAligned :
      ∀ (Xᴸ : TyVar Δᴸ)
      → μ (toRenameᵗ ηᴸ Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar Δᴿ ]
          toRenameᵗ ηᴿ Xᴿ ≡ toRenameᵗ ηᴸ Xᴸ

    representationsImprecise :
      ∀ {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → toRenameᵗ ηᴸ Xᴸ ≡ toRenameᵗ ηᴿ Xᴿ
      → μ ⊢
          renameᵗ (toRenameᵗ ηᴸ) (lookupStore Σᴸ Xᴸ)
          ⊑ renameᵗ (toRenameᵗ ηᴿ) (lookupStore Σᴿ Xᴿ)

    unmatchedTargetsDynamic :
      ∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ ηᴸ Xᴸ ≢ toRenameᵗ ηᴿ Xᴿ)
      → lookupStore Σᴿ Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar Δᴿ ]
            (lookupStore Σᴿ Xᴿ ≡ ＇ Yᴿ)
          × (∀ (Xᴸ : TyVar Δᴸ)
              → toRenameᵗ ηᴸ Xᴸ ≢ toRenameᵗ ηᴿ Yᴿ)

    dynamicStarSourcesUnoccupied :
      ∀ (Xᴸ : TyVar Δᴸ)
      → μ (toRenameᵗ ηᴸ Xᴸ) ≡ X⊑★
      → lookupStore Σᴸ Xᴸ ≡ ★
      → ∀ (Xᴿ : TyVar Δᴿ)
      → toRenameᵗ ηᴿ Xᴿ ≢ toRenameᵗ ηᴸ Xᴸ

open WorldInvariants public

mutual
  data World : TyCtx → TyCtx → TyCtx → Set where
    emptyʷ : World Nat.zero Nat.zero Nat.zero

    skip-centerʷ : ∀ {Δᴸ Δᴿ Δ}
      → World Δᴸ Δᴿ Δ
      → World Δᴸ Δᴿ (Nat.suc Δ)

    honestifyʷ : ∀ {Δᴸ Δᴿ Δ}
      → World Δᴸ Δᴿ Δ
      → World Δᴸ Δᴿ Δ

    lift-bothʷ : ∀ {Δᴸ Δᴿ Δ}
      → VarImp
      → World Δᴸ Δᴿ Δ
      → World (Nat.suc Δᴸ) (Nat.suc Δᴿ) (Nat.suc Δ)

    lift-leftʷ : ∀ {Δᴸ Δᴿ Δ}
      → World Δᴸ Δᴿ Δ
      → World (Nat.suc Δᴸ) Δᴿ (Nat.suc Δ)

    bind-leftʷ : ∀ {Δᴸ Δᴿ Δ}
      → (W : World Δᴸ Δᴿ Δ)
      → Ty Δᴸ
      → World (Nat.suc Δᴸ) Δᴿ (Nat.suc Δ)

    bind-rightʷ : ∀ {Δᴸ Δᴿ Δ}
      → (W : World Δᴸ Δᴿ Δ)
      → (B : Ty Δᴿ)
      → ⇑ᵗ B ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar (Nat.suc Δᴿ) ]
            (⇑ᵗ B ≡ ＇ Yᴿ)
          × (∀ Xᴸ
              → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
                ≢ toRenameᵗ (keep (ηᴿʷ W)) Yᴿ)
      → World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ)

    bind-bothʷ : ∀ {Δᴸ Δᴿ Δ}
      → (W : World Δᴸ Δᴿ Δ)
      → (A : Ty Δᴸ)
      → (B : Ty Δᴿ)
      → impEnvʷ W ⊢
          renameᵗ (toRenameᵗ (ηᴸʷ W)) A
          ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W)) B
      → World (Nat.suc Δᴸ) (Nat.suc Δᴿ) (Nat.suc Δ)

    bind-both-starʷ : ∀ {Δᴸ Δᴿ Δ}
      → (W : World Δᴸ Δᴿ Δ)
      → (A : Ty Δᴸ)
      → (B : Ty Δᴿ)
      → impEnvʷ W ⊢
          renameᵗ (toRenameᵗ (ηᴸʷ W)) A
          ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W)) B
      → ⇑ᵗ A ≢ ★
      → World (Nat.suc Δᴸ) (Nat.suc Δᴿ) (Nat.suc Δ)

    lower-leftʷ : ∀ {Δᴸ Δᴿ Δ}
      → (W₁ : World Δᴸ Δᴿ Δ)
      → (Wᴸ : World (Nat.suc Δᴸ) Δᴿ (Nat.suc Δ))
      → (ηᴸ : Δᴸ ↪ᵗ Δ)
      → (ηᴿ : Δᴿ ↪ᵗ Δ)
      → keep ηᴸ ≡ ηᴸʷ Wᴸ
      → skip ηᴿ ≡ ηᴿʷ Wᴸ
      → store-lift (sourceStoreʷ W₁) ≡ sourceStoreʷ Wᴸ
      → WorldInvariants ηᴸ ηᴿ (λ Z → impEnvʷ Wᴸ (Fin.suc Z))
          (sourceStoreʷ W₁) (targetStoreʷ Wᴸ)
      → World Δᴸ Δᴿ Δ

    mix-targetʷ : ∀ {Δᴸ Δᴿˢ Δˢ Δᴸᵗ Δᴿ Δᵗ}
      → (π : Δˢ ↪ᵗ Δᵗ)
      → (Wˢ : World Δᴸ Δᴿˢ Δˢ)
      → (Wᵗ : World Δᴸᵗ Δᴿ Δᵗ)
      → WorldInvariants (π ∘↪ ηᴸʷ Wˢ) (ηᴿʷ Wᵗ)
          (renameEnv π (impEnvʷ Wˢ))
          (sourceStoreʷ Wˢ) (targetStoreʷ Wᵗ)
      → World Δᴸ Δᴿ Δᵗ

    mix-renamed-targetʷ : ∀ {Δᴸ Δᴿˢ Δˢ Δᴸᵗ Δᴿ Δᵗ Δ}
      → (πˢ : Δˢ ↪ᵗ Δ)
      → (πᵗ : Δᵗ ↪ᵗ Δ)
      → (Wˢ : World Δᴸ Δᴿˢ Δˢ)
      → (Wᵗ : World Δᴸᵗ Δᴿ Δᵗ)
      → WorldInvariants (πˢ ∘↪ ηᴸʷ Wˢ) (πᵗ ∘↪ ηᴿʷ Wᵗ)
          (renameEnv πˢ (impEnvʷ Wˢ))
          (sourceStoreʷ Wˢ) (targetStoreʷ Wᵗ)
      → World Δᴸ Δᴿ Δ

  ηᴸʷ : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → Δᴸ ↪ᵗ Δ
  ηᴸʷ emptyʷ = empty
  ηᴸʷ (skip-centerʷ W) = skip (ηᴸʷ W)
  ηᴸʷ (honestifyʷ W) = ηᴸʷ W
  ηᴸʷ (lift-bothʷ v W) = keep (ηᴸʷ W)
  ηᴸʷ (lift-leftʷ W) = keep (ηᴸʷ W)
  ηᴸʷ (bind-leftʷ W A) = keep (ηᴸʷ W)
  ηᴸʷ (bind-rightʷ W B fresh) = skip (ηᴸʷ W)
  ηᴸʷ (bind-bothʷ W A B A⊑B) = keep (ηᴸʷ W)
  ηᴸʷ (bind-both-starʷ W A B A⊑B A≢★) = keep (ηᴸʷ W)
  ηᴸʷ (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) = ηᴸ
  ηᴸʷ (mix-targetʷ π Wˢ Wᵗ inv) = π ∘↪ ηᴸʷ Wˢ
  ηᴸʷ (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) =
    πˢ ∘↪ ηᴸʷ Wˢ

  ηᴿʷ : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → Δᴿ ↪ᵗ Δ
  ηᴿʷ emptyʷ = empty
  ηᴿʷ (skip-centerʷ W) = skip (ηᴿʷ W)
  ηᴿʷ (honestifyʷ W) = ηᴿʷ W
  ηᴿʷ (lift-bothʷ v W) = keep (ηᴿʷ W)
  ηᴿʷ (lift-leftʷ W) = skip (ηᴿʷ W)
  ηᴿʷ (bind-leftʷ W A) = skip (ηᴿʷ W)
  ηᴿʷ (bind-rightʷ W B fresh) = keep (ηᴿʷ W)
  ηᴿʷ (bind-bothʷ W A B A⊑B) = keep (ηᴿʷ W)
  ηᴿʷ (bind-both-starʷ W A B A⊑B A≢★) = keep (ηᴿʷ W)
  ηᴿʷ (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) = ηᴿ
  ηᴿʷ (mix-targetʷ π Wˢ Wᵗ inv) = ηᴿʷ Wᵗ
  ηᴿʷ (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) =
    πᵗ ∘↪ ηᴿʷ Wᵗ

  impEnvʷ : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → ImpEnv Δ
  impEnvʷ emptyʷ = λ ()
  impEnvʷ (skip-centerʷ W) = extendᵐ X⊑★ (impEnvʷ W)
  impEnvʷ (honestifyʷ W) = honestEnv (ηᴿʷ W) (impEnvʷ W)
  impEnvʷ (lift-bothʷ v W) = extendᵐ v (impEnvʷ W)
  impEnvʷ (lift-leftʷ W) = instᵐ (impEnvʷ W)
  impEnvʷ (bind-leftʷ W A) = instᵐ (impEnvʷ W)
  impEnvʷ (bind-rightʷ W B fresh) = instᵐ (impEnvʷ W)
  impEnvʷ (bind-bothʷ W A B A⊑B) = extendᵐ X⊑X (impEnvʷ W)
  impEnvʷ (bind-both-starʷ W A B A⊑B A≢★) =
    extendᵐ X⊑★ (impEnvʷ W)
  impEnvʷ (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) =
    λ Z → impEnvʷ Wᴸ (Fin.suc Z)
  impEnvʷ (mix-targetʷ π Wˢ Wᵗ inv) = renameEnv π (impEnvʷ Wˢ)
  impEnvʷ (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) =
    renameEnv πˢ (impEnvʷ Wˢ)

  sourceStoreʷ : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → TyStore Δᴸ
  sourceStoreʷ emptyʷ = store-empty
  sourceStoreʷ (skip-centerʷ W) = sourceStoreʷ W
  sourceStoreʷ (honestifyʷ W) = sourceStoreʷ W
  sourceStoreʷ (lift-bothʷ v W) = store-lift (sourceStoreʷ W)
  sourceStoreʷ (lift-leftʷ W) = store-lift (sourceStoreʷ W)
  sourceStoreʷ (bind-leftʷ W A) = store-bind (sourceStoreʷ W) A
  sourceStoreʷ (bind-rightʷ W B fresh) = sourceStoreʷ W
  sourceStoreʷ (bind-bothʷ W A B A⊑B) = store-bind (sourceStoreʷ W) A
  sourceStoreʷ (bind-both-starʷ W A B A⊑B A≢★) =
    store-bind (sourceStoreʷ W) A
  sourceStoreʷ
      (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) =
    sourceStoreʷ W₁
  sourceStoreʷ (mix-targetʷ π Wˢ Wᵗ inv) = sourceStoreʷ Wˢ
  sourceStoreʷ (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) =
    sourceStoreʷ Wˢ

  targetStoreʷ : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → TyStore Δᴿ
  targetStoreʷ emptyʷ = store-empty
  targetStoreʷ (skip-centerʷ W) = targetStoreʷ W
  targetStoreʷ (honestifyʷ W) = targetStoreʷ W
  targetStoreʷ (lift-bothʷ v W) = store-lift (targetStoreʷ W)
  targetStoreʷ (lift-leftʷ W) = targetStoreʷ W
  targetStoreʷ (bind-leftʷ W A) = targetStoreʷ W
  targetStoreʷ (bind-rightʷ W B fresh) = store-bind (targetStoreʷ W) B
  targetStoreʷ (bind-bothʷ W A B A⊑B) = store-bind (targetStoreʷ W) B
  targetStoreʷ (bind-both-starʷ W A B A⊑B A≢★) =
    store-bind (targetStoreʷ W) B
  targetStoreʷ
      (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) =
    targetStoreʷ Wᴸ
  targetStoreʷ (mix-targetʷ π Wˢ Wᵗ inv) = targetStoreʷ Wᵗ
  targetStoreʷ (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) =
    targetStoreʷ Wᵗ

RightBindFresh : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → Set
RightBindFresh W B =
  ⇑ᵗ B ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar _ ]
        (⇑ᵗ B ≡ ＇ Yᴿ)
      × (∀ Xᴸ
          → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
            ≢ toRenameᵗ (keep (ηᴿʷ W)) Yᴿ)

variable≢star : ∀ {Δ} {X : TyVar Δ}
  → _≡_ {A = Ty Δ} (＇ X) ★ → ⊥
variable≢star ()

variableHeadsAlign : ∀ {Δ} {μ : ImpEnv Δ} {X Y : TyVar Δ}
  → μ ⊢ ＇ X ⊑ ＇ Y
  → X ≡ Y
variableHeadsAlign X⊑X = refl

emptyStore : (Δ : TyCtx) → TyStore Δ
emptyStore Nat.zero = store-empty
emptyStore (Nat.suc Δ) = store-lift (emptyStore Δ)

emptyStore-lookup-variable : ∀ {Δ} (X : TyVar Δ)
  → lookupStore (emptyStore Δ) X ≡ ＇ X
emptyStore-lookup-variable {Nat.suc Δ} Fin.zero = refl
emptyStore-lookup-variable {Nat.suc Δ} (Fin.suc X) =
  cong ⇑ᵗ (emptyStore-lookup-variable X)

initialWorld-invariants : ∀ {Δ} (μ : ImpEnv Δ)
  → WorldInvariants id↪ᵗ id↪ᵗ μ (emptyStore Δ) (emptyStore Δ)
initialWorld-invariants μ =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → μ (toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ id↪ᵗ Xᴿ ≡ toRenameᵗ id↪ᵗ Xᴸ
  precise Xᴸ mark = Xᴸ , refl

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ id↪ᵗ Xᴸ ≡ toRenameᵗ id↪ᵗ Xᴿ
    → μ ⊢
        renameᵗ (toRenameᵗ id↪ᵗ) (lookupStore (emptyStore _) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ id↪ᵗ) (lookupStore (emptyStore _) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned
      with toRenameᵗ-injective id↪ᵗ aligned
  reps {Xᴸ} {.Xᴸ} aligned | refl
      rewrite emptyStore-lookup-variable Xᴸ =
    X⊑X

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ id↪ᵗ Xᴸ ≢ toRenameᵗ id↪ᵗ Xᴿ)
    → lookupStore (emptyStore _) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (emptyStore _) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ id↪ᵗ Xᴸ ≢ toRenameᵗ id↪ᵗ Yᴿ)
  unmatched Xᴿ no-source = ⊥-elim (no-source Xᴿ refl)

  unoccupied : ∀ Xᴸ
    → μ (toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑★
    → lookupStore (emptyStore _) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ id↪ᵗ Xᴿ ≢ toRenameᵗ id↪ᵗ Xᴸ
  unoccupied Xᴸ mark entry Xᴿ aligned =
    ⊥-elim
      (variable≢star
        (trans (sym (emptyStore-lookup-variable Xᴸ)) entry))

initialWorld : ∀ {Δ} → ImpEnv Δ → World Δ Δ Δ
initialWorld {Nat.zero} μ = emptyʷ
initialWorld {Nat.suc Δ} μ =
  lift-bothʷ (μ Fin.zero) (initialWorld (λ X → μ (Fin.suc X)))

initialWorld-ηᴸ : ∀ {Δ} (μ : ImpEnv Δ)
  → ηᴸʷ (initialWorld μ) ≡ id↪ᵗ
initialWorld-ηᴸ {Nat.zero} μ = refl
initialWorld-ηᴸ {Nat.suc Δ} μ =
  cong keep (initialWorld-ηᴸ (λ X → μ (Fin.suc X)))

initialWorld-ηᴿ : ∀ {Δ} (μ : ImpEnv Δ)
  → ηᴿʷ (initialWorld μ) ≡ id↪ᵗ
initialWorld-ηᴿ {Nat.zero} μ = refl
initialWorld-ηᴿ {Nat.suc Δ} μ =
  cong keep (initialWorld-ηᴿ (λ X → μ (Fin.suc X)))

initialWorld-sourceStore : ∀ {Δ} (μ : ImpEnv Δ)
  → sourceStoreʷ (initialWorld μ) ≡ emptyStore Δ
initialWorld-sourceStore {Nat.zero} μ = refl
initialWorld-sourceStore {Nat.suc Δ} μ =
  cong store-lift
    (initialWorld-sourceStore (λ X → μ (Fin.suc X)))

initialWorld-targetStore : ∀ {Δ} (μ : ImpEnv Δ)
  → targetStoreʷ (initialWorld μ) ≡ emptyStore Δ
initialWorld-targetStore {Nat.zero} μ = refl
initialWorld-targetStore {Nat.suc Δ} μ =
  cong store-lift
    (initialWorld-targetStore (λ X → μ (Fin.suc X)))

initialWorld-env : ∀ {Δ} (μ : ImpEnv Δ) (X : TyVar Δ)
  → impEnvʷ (initialWorld μ) X ≡ μ X
initialWorld-env {Nat.zero} μ ()
initialWorld-env {Nat.suc Δ} μ Fin.zero = refl
initialWorld-env {Nat.suc Δ} μ (Fin.suc X) =
  initialWorld-env (λ Y → μ (Fin.suc Y)) X

emptyCenterWorld : (Delta : TyCtx) → World Nat.zero Nat.zero Delta
emptyCenterWorld Nat.zero = emptyʷ
emptyCenterWorld (Nat.suc Delta) = skip-centerʷ (emptyCenterWorld Delta)

embedᴸ : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Ty Δᴸ
  → Ty Δ
embedᴸ W = renameᵗ (toRenameᵗ (ηᴸʷ W))

embedᴿ : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → Ty Δ
embedᴿ W = renameᵗ (toRenameᵗ (ηᴿʷ W))

infix 4 _⊑ᵂ⟨_⟩_

_⊑ᵂ⟨_⟩_ : ∀ {Δᴸ Δᴿ Δ}
  → Ty Δᴸ
  → World Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → Set
A ⊑ᵂ⟨ W ⟩ B = impEnvʷ W ⊢ embedᴸ W A ⊑ embedᴿ W B

imprecision-cong : ∀ {Δ} {μ : ImpEnv Δ} {A A′ B B′ : Ty Δ}
  → A ≡ A′
  → B ≡ B′
  → μ ⊢ A ⊑ B
  → μ ⊢ A′ ⊑ B′
imprecision-cong refl refl A⊑B = A⊑B

honestify-invariants : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (honestEnv (ηᴿʷ W) (impEnvʷ W))
      (sourceStoreʷ W) (targetStoreʷ W)
honestify-invariants W inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → honestEnv (ηᴿʷ W) (impEnvʷ W)
        (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (ηᴿʷ W) Xᴿ ≡ toRenameᵗ (ηᴸʷ W) Xᴸ
  precise Xᴸ mark
      with targetAligned? (ηᴿʷ W) (toRenameᵗ (ηᴸʷ W) Xᴸ)
  precise Xᴸ mark | yes aligned = aligned
  precise Xᴸ () | no unaligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
    → honestEnv (ηᴿʷ W) (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (ηᴸʷ W))
          (lookupStore (sourceStoreʷ W) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W))
          (lookupStore (targetStoreʷ W) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned
      with targetAligned? (ηᴿʷ W) (toRenameᵗ (ηᴸʷ W) Xᴸ)
  reps {Xᴸ} {Xᴿ} aligned | yes target =
    imp-env-weaken (honestEnv-mono (ηᴿʷ W) (impEnvʷ W))
      (representationsImprecise inv aligned)
  reps {Xᴸ} {Xᴿ} aligned | no unaligned =
    ⊥-elim (unaligned (Xᴿ , sym aligned))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ → toRenameᵗ (ηᴸʷ W) Xᴸ ≢ toRenameᵗ (ηᴿʷ W) Xᴿ)
    → lookupStore (targetStoreʷ W) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ →
            toRenameᵗ (ηᴸʷ W) Xᴸ ≢ toRenameᵗ (ηᴿʷ W) Yᴿ)
  unmatched = unmatchedTargetsDynamic inv

  unoccupied : ∀ Xᴸ
    → honestEnv (ηᴿʷ W) (impEnvʷ W)
        (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
    → lookupStore (sourceStoreʷ W) Xᴸ ≡ ★
    → ∀ Xᴿ → toRenameᵗ (ηᴿʷ W) Xᴿ ≢ toRenameᵗ (ηᴸʷ W) Xᴸ
  unoccupied Xᴸ mark entry Xᴿ aligned
      with targetAligned? (ηᴿʷ W) (toRenameᵗ (ηᴸʷ W) Xᴸ)
  unoccupied Xᴸ mark entry Xᴿ aligned | yes target =
    dynamicStarSourcesUnoccupied inv Xᴸ mark entry Xᴿ aligned
  unoccupied Xᴸ mark entry Xᴿ aligned | no unaligned =
    unaligned (Xᴿ , aligned)

private
  fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

  fin-zero-not-suc : ∀ {n} {X : Fin.Fin n}
    → Fin.zero ≢ Fin.suc X
  fin-zero-not-suc ()

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

  inst-old-representation : ∀ {Δ} {μ : ImpEnv Δ} {A B : Ty Δ}
    → μ ⊢ A ⊑ B
    → instᵐ μ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
  inst-old-representation A⊑B =
    rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) A⊑B

  unshift-star : ∀ {Δ} {A : Ty Δ}
    → ⇑ᵗ A ≡ ★
    → A ≡ ★
  unshift-star {A = ＇ X} ()
  unshift-star {A = ‵ ι} ()
  unshift-star {A = ★} refl = refl
  unshift-star {A = A ⇒ B} ()
  unshift-star {A = `∀ A} ()

liftWorldBoth-invariants : ∀ {Δᴸ Δᴿ Δ}
    (v : VarImp) (W : World Δᴸ Δᴿ Δ)
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (keep (ηᴸʷ W)) (keep (ηᴿʷ W))
      (extendᵐ v (impEnvʷ W))
      (store-lift (sourceStoreʷ W))
      (store-lift (targetStoreʷ W))
liftWorldBoth-invariants v W inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → extendᵐ v (impEnvʷ W) (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ ≡ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
    → extendᵐ v (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸʷ W)))
          (lookupStore (store-lift (sourceStoreʷ W)) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿʷ W)))
          (lookupStore (store-lift (targetStoreʷ W)) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned = X⊑X
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸʷ W)
        (lookupStore (sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿʷ W)
        (lookupStore (targetStoreʷ W) Xᴿ)))
      (lift-old-representation
        (representationsImprecise inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ)
    → lookupStore (store-lift (targetStoreʷ W)) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-lift (targetStoreʷ W)) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (keep (ηᴿʷ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿʷ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ v (impEnvʷ W) (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-lift (sourceStoreʷ W)) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
      ≢ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark (unshift-star entry) Xᴿ
      (fin-suc-injective aligned)

liftWorldBoth : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (Nat.suc Δᴸ) (Nat.suc Δᴿ) (Nat.suc Δ)
liftWorldBoth v W =
  lift-bothʷ v W

-- A universal binder on the source side only: the target context, its
-- store, and its embedding stay fixed, so target terms and types cross
-- the binder unweakened.

liftWorldLeft-invariants : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (keep (ηᴸʷ W)) (skip (ηᴿʷ W))
      (instᵐ (impEnvʷ W))
      (store-lift (sourceStoreʷ W))
      (targetStoreʷ W)
liftWorldLeft-invariants W inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → instᵐ (impEnvʷ W) (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ ≡ toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
    → instᵐ (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸʷ W)))
          (lookupStore (store-lift (sourceStoreʷ W)) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿʷ W)))
          (lookupStore (targetStoreʷ W) Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸʷ W)
        (lookupStore (sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-skip (ηᴿʷ W) (lookupStore (targetStoreʷ W) Xᴿ)))
      (inst-old-representation
        (representationsImprecise inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (skip (ηᴿʷ W)) Xᴿ)
    → lookupStore (targetStoreʷ W) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (skip (ηᴿʷ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿʷ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (impEnvʷ W) (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-lift (sourceStoreʷ W)) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
      ≢ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = variable≢star entry
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark (unshift-star entry) Xᴿ
      (fin-suc-injective aligned)

liftWorldLeft : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World (Nat.suc Δᴸ) Δᴿ (Nat.suc Δ)
liftWorldLeft W =
  lift-leftʷ W

leftOnlyWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (A : Ty Δᴸ)
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (keep (ηᴸʷ W)) (skip (ηᴿʷ W))
      (instᵐ (impEnvʷ W))
      (store-bind (sourceStoreʷ W) A)
      (targetStoreʷ W)
leftOnlyWorld-invariants W A inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → instᵐ (impEnvʷ W) (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ ≡ toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
    → instᵐ (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸʷ W)))
          (lookupStore (store-bind (sourceStoreʷ W) A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿʷ W)))
          (lookupStore (targetStoreʷ W) Xᴿ)
  reps {Fin.zero} {Xᴿ} ()
  reps {Fin.suc Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸʷ W)
        (lookupStore (sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-skip (ηᴿʷ W) (lookupStore (targetStoreʷ W) Xᴿ)))
      (inst-old-representation
        (representationsImprecise inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (skip (ηᴿʷ W)) Xᴿ)
    → lookupStore (targetStoreʷ W) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (skip (ηᴿʷ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿʷ W)) Yᴿ
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (impEnvʷ W) (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind (sourceStoreʷ W) A) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
      ≢ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ ()
  unoccupied (Fin.suc Xᴸ) mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark (unshift-star entry) Xᴿ
      (fin-suc-injective aligned)

leftOnlyWorld : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Ty Δᴸ
  → World (Nat.suc Δᴸ) Δᴿ (Nat.suc Δ)
leftOnlyWorld W A =
  bind-leftʷ W A

rightOnlyWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (B : Ty Δᴿ)
  → RightBindFresh W B
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (skip (ηᴸʷ W)) (keep (ηᴿʷ W))
      (instᵐ (impEnvʷ W))
      (sourceStoreʷ W)
      (store-bind (targetStoreʷ W) B)
rightOnlyWorld-invariants W B fresh-classification inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → instᵐ (impEnvʷ W) (toRenameᵗ (skip (ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAligned inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ ≡ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
    → instᵐ (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (skip (ηᴸʷ W)))
          (lookupStore (sourceStoreʷ W) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿʷ W)))
          (lookupStore (store-bind (targetStoreʷ W) B) Xᴿ)
  reps {Xᴸ} {Fin.zero} ()
  reps {Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skip (ηᴸʷ W) (lookupStore (sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿʷ W)
        (lookupStore (targetStoreʷ W) Xᴿ)))
      (inst-old-representation
        (representationsImprecise inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ)
    → lookupStore (store-bind (targetStoreʷ W) B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind (targetStoreʷ W) B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (keep (ηᴿʷ W)) Yᴿ)
  unmatched Fin.zero no-source = fresh-classification
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿʷ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → instᵐ (impEnvʷ W) (toRenameᵗ (skip (ηᴸʷ W)) Xᴸ) ≡ X⊑★
    → lookupStore (sourceStoreʷ W) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
      ≢ toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
  unoccupied Xᴸ mark entry Fin.zero ()
  unoccupied Xᴸ mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)

rightOnlyWorld : ∀ {Δᴸ Δᴿ Δ}
  → (W : World Δᴸ Δᴿ Δ)
  → (B : Ty Δᴿ)
  → RightBindFresh W B
  → World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ)
rightOnlyWorld W B fresh-classification =
  bind-rightʷ W B fresh-classification

bothBindWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (A : Ty Δᴸ) (B : Ty Δᴿ)
  → A ⊑ᵂ⟨ W ⟩ B
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (keep (ηᴸʷ W)) (keep (ηᴿʷ W))
      (extendᵐ X⊑X (impEnvʷ W))
      (store-bind (sourceStoreʷ W) A)
      (store-bind (targetStoreʷ W) B)
bothBindWorld-invariants W A B A⊑B inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → extendᵐ X⊑X (impEnvʷ W)
        (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  precise Fin.zero mark = Fin.zero , refl
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ ≡ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
    → extendᵐ X⊑X (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸʷ W)))
          (lookupStore (store-bind (sourceStoreʷ W) A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿʷ W)))
          (lookupStore (store-bind (targetStoreʷ W) B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸʷ W) A))
      (sym (renameᵗ-keep-shift (ηᴿʷ W) B))
      (lift-old-representation A⊑B)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸʷ W)
        (lookupStore (sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿʷ W)
        (lookupStore (targetStoreʷ W) Xᴿ)))
      (lift-old-representation
        (representationsImprecise inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ)
    → lookupStore (store-bind (targetStoreʷ W) B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind (targetStoreʷ W) B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (keep (ηᴿʷ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿʷ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑X (impEnvʷ W)
        (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind (sourceStoreʷ W) A) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
      ≢ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  unoccupied Fin.zero () entry Xᴿ aligned
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark (unshift-star entry) Xᴿ
      (fin-suc-injective aligned)

bothBindStarWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (A : Ty Δᴸ) (B : Ty Δᴿ)
  → A ⊑ᵂ⟨ W ⟩ B
  → ⇑ᵗ A ≢ ★
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (keep (ηᴸʷ W)) (keep (ηᴿʷ W))
      (extendᵐ X⊑★ (impEnvʷ W))
      (store-bind (sourceStoreʷ W) A)
      (store-bind (targetStoreʷ W) B)
bothBindStarWorld-invariants W A B A⊑B A≢★ inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (impEnvʷ W)
        (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Xᴸ) mark with preciseMarksAligned inv Xᴸ mark
  precise (Fin.suc Xᴸ) mark | Xᴿ , aligned =
    Fin.suc Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ ≡ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
    → extendᵐ X⊑★ (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (keep (ηᴸʷ W)))
          (lookupStore (store-bind (sourceStoreʷ W) A) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (keep (ηᴿʷ W)))
          (lookupStore (store-bind (targetStoreʷ W) B) Xᴿ)
  reps {Fin.zero} {Fin.zero} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸʷ W) A))
      (sym (renameᵗ-keep-shift (ηᴿʷ W) B))
      (lift-old-representation A⊑B)
  reps {Fin.zero} {Fin.suc Xᴿ} ()
  reps {Fin.suc Xᴸ} {Fin.zero} ()
  reps {Fin.suc Xᴸ} {Fin.suc Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-keep-shift (ηᴸʷ W)
        (lookupStore (sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-keep-shift (ηᴿʷ W)
        (lookupStore (targetStoreʷ W) Xᴿ)))
      (lift-old-representation
        (representationsImprecise inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (keep (ηᴿʷ W)) Xᴿ)
    → lookupStore (store-bind (targetStoreʷ W) B) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (store-bind (targetStoreʷ W) B) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (keep (ηᴿʷ W)) Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Xᴿ) no-source
      with unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source (Fin.suc Xᴸ) (cong Fin.suc aligned))
  unmatched (Fin.suc Xᴿ) no-source | inj₁ dynamic =
    inj₁ (cong ⇑ᵗ dynamic)
  unmatched (Fin.suc Xᴿ) no-source
      | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Fin.suc Yᴿ , cong ⇑ᵗ entry , lifted-head-no-source)
    where
    lifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
        ≢ toRenameᵗ (keep (ηᴿʷ W)) (Fin.suc Yᴿ)
    lifted-head-no-source Fin.zero ()
    lifted-head-no-source (Fin.suc Xᴸ) aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (impEnvʷ W)
        (toRenameᵗ (keep (ηᴸʷ W)) Xᴸ) ≡ X⊑★
    → lookupStore (store-bind (sourceStoreʷ W) A) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (keep (ηᴿʷ W)) Xᴿ
      ≢ toRenameᵗ (keep (ηᴸʷ W)) Xᴸ
  unoccupied Fin.zero mark entry Xᴿ aligned = ⊥-elim (A≢★ entry)
  unoccupied (Fin.suc Xᴸ) mark entry Fin.zero ()
  unoccupied (Fin.suc Xᴸ) mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark (unshift-star entry) Xᴿ
      (fin-suc-injective aligned)

bothBindWorld : ∀ {Δᴸ Δᴿ Δ}
  → (W : World Δᴸ Δᴿ Δ)
  → (A : Ty Δᴸ)
  → (B : Ty Δᴿ)
  → A ⊑ᵂ⟨ W ⟩ B
  → World (Nat.suc Δᴸ) (Nat.suc Δᴿ) (Nat.suc Δ)
bothBindWorld W A B A⊑B =
  bind-bothʷ W A B A⊑B

skipCenter-invariants : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
  → WorldInvariants
      (skip (ηᴸʷ W)) (skip (ηᴿʷ W))
      (extendᵐ X⊑★ (impEnvʷ W))
      (sourceStoreʷ W) (targetStoreʷ W)
skipCenter-invariants W inv =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → extendᵐ X⊑★ (impEnvʷ W)
        (toRenameᵗ (skip (ηᴸʷ W)) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
          ≡ toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
  precise Xᴸ mark with preciseMarksAligned inv Xᴸ mark
  precise Xᴸ mark | Xᴿ , aligned = Xᴿ , cong Fin.suc aligned

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
        ≡ toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
    → extendᵐ X⊑★ (impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (skip (ηᴸʷ W)))
          (lookupStore (sourceStoreʷ W) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (skip (ηᴿʷ W)))
          (lookupStore (targetStoreʷ W) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned =
    imprecision-cong
      (sym (renameᵗ-skip (ηᴸʷ W) (lookupStore (sourceStoreʷ W) Xᴸ)))
      (sym (renameᵗ-skip (ηᴿʷ W) (lookupStore (targetStoreʷ W) Xᴿ)))
      (lift-old-representation
        (representationsImprecise inv (fin-suc-injective aligned)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
          ≢ toRenameᵗ (skip (ηᴿʷ W)) Xᴿ)
    → lookupStore (targetStoreʷ W) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (skip (ηᴿʷ W)) Yᴿ)
  unmatched Xᴿ no-source
      with unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ (cong Fin.suc aligned))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , shifted-head-no-source)
    where
    shifted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
        ≢ toRenameᵗ (skip (ηᴿʷ W)) Yᴿ
    shifted-head-no-source Xᴸ aligned =
      head-no-source Xᴸ (fin-suc-injective aligned)

  unoccupied : ∀ Xᴸ
    → extendᵐ X⊑★ (impEnvʷ W)
        (toRenameᵗ (skip (ηᴸʷ W)) Xᴸ) ≡ X⊑★
    → lookupStore (sourceStoreʷ W) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (skip (ηᴿʷ W)) Xᴿ
      ≢ toRenameᵗ (skip (ηᴸʷ W)) Xᴸ
  unoccupied Xᴸ mark entry Xᴿ aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)

invariantsʷ : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
  → WorldInvariants
      (ηᴸʷ W) (ηᴿʷ W) (impEnvʷ W)
      (sourceStoreʷ W) (targetStoreʷ W)
invariantsʷ emptyʷ = world-invariants (λ ()) (λ { {()} }) (λ ()) (λ ())
invariantsʷ (skip-centerʷ W) = skipCenter-invariants W (invariantsʷ W)
invariantsʷ (honestifyʷ W) = honestify-invariants W (invariantsʷ W)
invariantsʷ (lift-bothʷ v W) =
  liftWorldBoth-invariants v W (invariantsʷ W)
invariantsʷ (lift-leftʷ W) =
  liftWorldLeft-invariants W (invariantsʷ W)
invariantsʷ (bind-leftʷ W A) =
  leftOnlyWorld-invariants W A (invariantsʷ W)
invariantsʷ (bind-rightʷ W B fresh-classification) =
  rightOnlyWorld-invariants W B fresh-classification (invariantsʷ W)
invariantsʷ (bind-bothʷ W A B A⊑B) =
  bothBindWorld-invariants W A B A⊑B (invariantsʷ W)
invariantsʷ (bind-both-starʷ W A B A⊑B A≢★) =
  bothBindStarWorld-invariants W A B A⊑B A≢★ (invariantsʷ W)
invariantsʷ
    (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) = inv
invariantsʷ (mix-targetʷ π Wˢ Wᵗ inv) = inv
invariantsʷ (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) = inv

precise-center-has-source : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (Z : TyVar Δ)
  → impEnvʷ W Z ≡ X⊑X
  → Σ[ Xᴸ ∈ TyVar Δᴸ ] toRenameᵗ (ηᴸʷ W) Xᴸ ≡ Z
precise-center-has-source emptyʷ () mark
precise-center-has-source (skip-centerʷ W) Fin.zero ()
precise-center-has-source (skip-centerʷ W) (Fin.suc Z) mark
    with precise-center-has-source W Z mark
precise-center-has-source (skip-centerʷ W) (Fin.suc Z) mark
    | Xᴸ , aligned =
  Xᴸ , cong Fin.suc aligned
precise-center-has-source (honestifyʷ W) Z mark
    with targetAligned? (ηᴿʷ W) Z
precise-center-has-source (honestifyʷ W) Z mark | yes target =
  precise-center-has-source W Z mark
precise-center-has-source (honestifyʷ W) Z () | no unaligned
precise-center-has-source (lift-bothʷ X⊑X W) Fin.zero refl =
  Fin.zero , refl
precise-center-has-source (lift-bothʷ X⊑★ W) Fin.zero ()
precise-center-has-source (lift-bothʷ v W) (Fin.suc Z) mark
    with precise-center-has-source W Z mark
precise-center-has-source (lift-bothʷ v W) (Fin.suc Z) mark
    | Xᴸ , aligned =
  Fin.suc Xᴸ , cong Fin.suc aligned
precise-center-has-source (lift-leftʷ W) Fin.zero ()
precise-center-has-source (lift-leftʷ W) (Fin.suc Z) mark
    with precise-center-has-source W Z mark
precise-center-has-source (lift-leftʷ W) (Fin.suc Z) mark
    | Xᴸ , aligned =
  Fin.suc Xᴸ , cong Fin.suc aligned
precise-center-has-source (bind-leftʷ W A) Fin.zero ()
precise-center-has-source (bind-leftʷ W A) (Fin.suc Z) mark
    with precise-center-has-source W Z mark
precise-center-has-source (bind-leftʷ W A) (Fin.suc Z) mark
    | Xᴸ , aligned =
  Fin.suc Xᴸ , cong Fin.suc aligned
precise-center-has-source (bind-rightʷ W B fresh) Fin.zero ()
precise-center-has-source (bind-rightʷ W B fresh) (Fin.suc Z) mark
    with precise-center-has-source W Z mark
precise-center-has-source (bind-rightʷ W B fresh) (Fin.suc Z) mark
    | Xᴸ , aligned =
  Xᴸ , cong Fin.suc aligned
precise-center-has-source (bind-bothʷ W A B A⊑B) Fin.zero refl =
  Fin.zero , refl
precise-center-has-source (bind-bothʷ W A B A⊑B) (Fin.suc Z) mark
    with precise-center-has-source W Z mark
precise-center-has-source (bind-bothʷ W A B A⊑B) (Fin.suc Z) mark
    | Xᴸ , aligned =
  Fin.suc Xᴸ , cong Fin.suc aligned
precise-center-has-source
    (bind-both-starʷ W A B A⊑B A≢★) Fin.zero ()
precise-center-has-source
    (bind-both-starʷ W A B A⊑B A≢★) (Fin.suc Z) mark
    with precise-center-has-source W Z mark
precise-center-has-source
    (bind-both-starʷ W A B A⊑B A≢★) (Fin.suc Z) mark
    | Xᴸ , aligned =
  Fin.suc Xᴸ , cong Fin.suc aligned
precise-center-has-source
    (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) Z mark
    with precise-center-has-source Wᴸ (Fin.suc Z) mark
precise-center-has-source
    (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) Z mark
    | Fin.zero , aligned =
  ⊥-elim (fin-zero-not-suc
    (trans (cong (λ η → toRenameᵗ η Fin.zero) keep-eq) aligned))
precise-center-has-source
    (lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) Z mark
    | Fin.suc Xᴸ , aligned =
  Xᴸ , fin-suc-injective
    (trans (cong (λ η → toRenameᵗ η (Fin.suc Xᴸ)) keep-eq) aligned)
precise-center-has-source (mix-targetʷ π Wˢ Wᵗ inv) Z′ mark
    with renameEnv-precise-preimage π (impEnvʷ Wˢ) Z′ mark
precise-center-has-source (mix-targetʷ π Wˢ Wᵗ inv) Z′ mark
    | Z , image , old-mark
    with precise-center-has-source Wˢ Z old-mark
precise-center-has-source (mix-targetʷ π Wˢ Wᵗ inv) Z′ mark
    | Z , image , old-mark | Xᴸ , source =
  Xᴸ , trans (toRenameᵗ-∘ π (ηᴸʷ Wˢ) Xᴸ)
    (trans (cong (toRenameᵗ π) source) image)
precise-center-has-source
    (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) Z′ mark
    with renameEnv-precise-preimage πˢ (impEnvʷ Wˢ) Z′ mark
precise-center-has-source
    (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) Z′ mark
    | Z , image , old-mark
    with precise-center-has-source Wˢ Z old-mark
precise-center-has-source
    (mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) Z′ mark
    | Z , image , old-mark | Xᴸ , source =
  Xᴸ , trans (toRenameᵗ-∘ πˢ (ηᴸʷ Wˢ) Xᴸ)
    (trans (cong (toRenameᵗ πˢ) source) image)

record SameRuntime {Δᴸ Δᴿ Δ}
    (W W′ : World Δᴸ Δᴿ Δ) : Set where
  constructor same-runtime
  field
    sourceStore-same : sourceStoreʷ W′ ≡ sourceStoreʷ W
    targetStore-same : targetStoreʷ W′ ≡ targetStoreʷ W

-- Imprecision marks may only decay toward the dynamic type as a rule
-- descends into its premise: every center the conclusion world marks
-- X⊑★ stays X⊑★ in the premise world, while precise marks may weaken
-- to X⊑★.  Equality is too strong: a rebase that displaces a target
-- variable leaves its old partner precise but unaligned, and the
-- stale mark blocks tag cancellation (see
-- proof.DGG.ExtraCastRight2Counterexample).  Each wrapper rule
-- carries this premise from its conclusion world to its premise
-- world; the rebase records no longer constrain the marks.

record ImpEnvMono {Δᴸ Δᴿ Δ}
    (W W′ : World Δᴸ Δᴿ Δ) : Set where
  constructor imp-env-mono
  field
    dynamic-preserved : ∀ Z
      → impEnvʷ W Z ≡ X⊑★
      → impEnvʷ W′ Z ≡ X⊑★

    precise-preserved : ∀ Z
      → impEnvʷ W Z ≡ X⊑X
      → impEnvʷ W′ Z ≡ X⊑X

open ImpEnvMono public

impEnvMono-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → ImpEnvMono W W
impEnvMono-refl = imp-env-mono (λ Z mark → mark) (λ Z mark → mark)

impEnvMono-trans : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₂ W₃ : World Δᴸ Δᴿ Δ}
  → ImpEnvMono W₁ W₂
  → ImpEnvMono W₂ W₃
  → ImpEnvMono W₁ W₃
impEnvMono-trans mono₁ mono₂ =
  imp-env-mono
    (λ Z mark → dynamic-preserved mono₂ Z
      (dynamic-preserved mono₁ Z mark))
    (λ Z mark → precise-preserved mono₂ Z
      (precise-preserved mono₁ Z mark))

impEnvMono-sym : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
  → ImpEnvMono W W′
  → ImpEnvMono W′ W
impEnvMono-sym {W = W} {W′ = W′} mono =
  imp-env-mono reflect-dynamic reflect-precise
  where
  reflect-dynamic : ∀ Z
    → impEnvʷ W′ Z ≡ X⊑★
    → impEnvʷ W Z ≡ X⊑★
  reflect-dynamic Z dynamic with impEnvʷ W Z in old-mark
  reflect-dynamic Z dynamic | X⊑★ = refl
  reflect-dynamic Z dynamic | X⊑X
      with trans (sym (precise-preserved mono Z old-mark)) dynamic
  reflect-dynamic Z dynamic | X⊑X | ()

  reflect-precise : ∀ Z
    → impEnvʷ W′ Z ≡ X⊑X
    → impEnvʷ W Z ≡ X⊑X
  reflect-precise Z precise with impEnvʷ W Z in old-mark
  reflect-precise Z precise | X⊑X = refl
  reflect-precise Z precise | X⊑★
      with trans (sym (dynamic-preserved mono Z old-mark)) precise
  reflect-precise Z precise | X⊑★ | ()

impEnvMono-reflect-dynamic : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
  → ImpEnvMono W W′
  → ∀ Z
  → impEnvʷ W′ Z ≡ X⊑★
  → impEnvʷ W Z ≡ X⊑★
impEnvMono-reflect-dynamic {W = W} mono Z dynamic
    with impEnvʷ W Z in old-mark
impEnvMono-reflect-dynamic mono Z dynamic | X⊑★ = refl
impEnvMono-reflect-dynamic mono Z dynamic | X⊑X
    with trans (sym (precise-preserved mono Z old-mark)) dynamic
impEnvMono-reflect-dynamic mono Z dynamic | X⊑X | ()

------------------------------------------------------------------------
-- Term-context imprecision in local worlds
------------------------------------------------------------------------

record CtxImpEntry {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ) : Set where
  constructor ctx-imp
  field
    srcTyʷ : Ty Δᴸ
    tgtTyʷ : Ty Δᴿ
    impTyʷ : srcTyʷ ⊑ᵂ⟨ W ⟩ tgtTyʷ

open CtxImpEntry public

CtxImp : ∀ {Δᴸ Δᴿ Δ} → World Δᴸ Δᴿ Δ → Set
CtxImp W = List (CtxImpEntry W)

srcCtxʷ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CtxImp W
  → TermCtx Δᴸ
srcCtxʷ = map srcTyʷ

tgtCtxʷ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CtxImp W
  → TermCtx Δᴿ
tgtCtxʷ = map tgtTyʷ

infix 4 _∋ʷ_⦂_

data _∋ʷ_⦂_ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} :
    CtxImp W → Var → CtxImpEntry W → Set where
  Zʷ : ∀ {γ A B p}
      ----------------------------------------------
    → (ctx-imp A B p ∷ γ) ∋ʷ Nat.zero ⦂ ctx-imp A B p

  Sʷ : ∀ {γ e e′ x}
    → γ ∋ʷ x ⦂ e
      -----------------------------
    → (e′ ∷ γ) ∋ʷ Nat.suc x ⦂ e

data SameCtx {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ Δ′} :
    CtxImp W → CtxImp W′ → Set where
  same-[] : SameCtx [] []

  same-∷ : ∀ {γ γ′ A B p p′}
    → SameCtx γ γ′
      ------------------------------------------------------
    → SameCtx (ctx-imp A B p ∷ γ) (ctx-imp A B p′ ∷ γ′)

data LiftCtx {Δᴸ Δᴿ Δ} (v : VarImp) {W : World Δᴸ Δᴿ Δ} :
    CtxImp W → CtxImp (liftWorldBoth v W) → Set where
  lift-[] : LiftCtx v [] []

  lift-∷ : ∀ {γ γ′ A B p p′}
    → LiftCtx v γ γ′
      -------------------------------------------------------------
    → LiftCtx v (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) (⇑ᵗ B) p′ ∷ γ′)

data LiftCtxᴸ {Δᴸ Δᴿ Δ} (v : VarImp) {W : World Δᴸ Δᴿ Δ} :
    CtxImp W → CtxImp (liftWorldLeft W) → Set where
  liftᴸ-[] : LiftCtxᴸ v [] []

  liftᴸ-∷ : ∀ {γ γ′ A B p p′}
    → LiftCtxᴸ v γ γ′
      -------------------------------------------------------------
    → LiftCtxᴸ v (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) B p′ ∷ γ′)

-- Smart-comma left lifts are the guarded non-front source-only premise
-- worlds used by the M5 instantiation catch-up.  The alias case merges the
-- pending source binder with an existing target alias center; the fresh-behind
-- case keeps remaining source-only binders behind the generated target window.

data SmartLiftCtxᴸ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ} :
    CtxImp W → CtxImp Wᵐ → Set where
  smart-lift-[] : SmartLiftCtxᴸ [] []

  smart-lift-∷ : ∀ {γ γᵐ A B p pᵐ}
    → SmartLiftCtxᴸ γ γᵐ
      -------------------------------------------------------------
    → SmartLiftCtxᴸ (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) B pᵐ ∷ γᵐ)


record SmartFreshBehindGuard {Δᴸ Δᴿ Δ Δᵐ}
    (W : World Δᴸ Δᴿ Δ)
    (Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ) : Set where
  constructor smart-fresh-behind-guard
  field
    oldCenters : Δ ↪ᵗ Δᵐ
    sourceStore-lifted :
      sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)
    targetStore-same :
      targetStoreʷ Wᵐ ≡ targetStoreʷ W
    transport⊑ᵂ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ liftWorldLeft W ⟩ B
      → A ⊑ᵂ⟨ Wᵐ ⟩ B
    old-mark-mono : ∀ Z
      → impEnvʷ W Z ≡ X⊑★
      → impEnvʷ Wᵐ (toRenameᵗ oldCenters Z) ≡ X⊑★
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ
        ≡ toRenameᵗ oldCenters (toRenameᵗ (ηᴿʷ W) Xᴿ)
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ oldCenters (toRenameᵗ (ηᴸʷ W) Xᴸ)
    fresh-not-target : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ
        ≢ toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero
    fresh-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero) ≡ X⊑★
    target-mark-mono : ∀ Xᴿ
      → impEnvʷ W (toRenameᵗ (ηᴿʷ W) Xᴿ) ≡ X⊑★
      → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★


record SmartAliasMergeGuard {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ)
    (β α : Fin.Fin Δᴿ) : Set where
  constructor smart-alias-merge-guard
  field
    β:=＇α : targetStoreʷ W ∋ β ⦂ ＇ α
    α:=★ : targetStoreʷ W ∋ α ⦂ ★
    sourceStore-lifted :
      sourceStoreʷ Wᵐ ≡ store-lift (sourceStoreʷ W)
    targetStore-same :
      targetStoreʷ Wᵐ ≡ targetStoreʷ W
    transport⊑ᵂ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ liftWorldLeft W ⟩ B
      → A ⊑ᵂ⟨ Wᵐ ⟩ B
    old-mark-mono : ∀ Z
      → impEnvʷ W Z ≡ X⊑★
      → impEnvʷ Wᵐ Z ≡ X⊑★
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
    pending-at-alias :
      toRenameᵗ (ηᴸʷ Wᵐ) Fin.zero ≡ toRenameᵗ (ηᴿʷ W) β
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ (ηᴸʷ W) Xᴸ
    no-old-source-at-alias : ∀ Xᴸ
      → toRenameᵗ (ηᴸʷ W) Xᴸ ≢ toRenameᵗ (ηᴿʷ W) β
    alias-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) β) ≡ X⊑★
    name-mark-dynamic :
      impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) α) ≡ X⊑★
    target-mark-off-footprint : ∀ Xᴿ
      → Xᴿ ≢ β
      → Xᴿ ≢ α
      → impEnvʷ W (toRenameᵗ (ηᴿʷ W) Xᴿ) ≡ X⊑★
      → impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ Wᵐ) Xᴿ) ≡ X⊑★


data SmartCommaLiftᴸ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    ∀ {Δᵐ} → World (Nat.suc Δᴸ) Δᴿ Δᵐ → Set where
  smart-fresh-behind :
    ∀ {Δᵐ} {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    → SmartFreshBehindGuard W Wᵐ
    → SmartCommaLiftᴸ W Wᵐ

  smart-merge-alias :
    ∀ {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
    → SmartAliasMergeGuard W Wᵐ β α
    → SmartCommaLiftᴸ W Wᵐ

smartCommaLift-transport⊑ᵂ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → SmartCommaLiftᴸ W Wᵐ
  → ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ liftWorldLeft W ⟩ B
  → A ⊑ᵂ⟨ Wᵐ ⟩ B
smartCommaLift-transport⊑ᵂ (smart-fresh-behind guard) =
  SmartFreshBehindGuard.transport⊑ᵂ guard
smartCommaLift-transport⊑ᵂ (smart-merge-alias guard) =
  SmartAliasMergeGuard.transport⊑ᵂ guard

------------------------------------------------------------------------
-- Store representations and local rebasing
------------------------------------------------------------------------

-- A type variable's canonical store representation: follow the store's
-- representation chain until it ends at a non-variable type or at a
-- store-lift (universally bound) variable.  Chains terminate because a
-- store-bind entry mentions only strictly older variables, so both
-- functions recurse on the tail of the store.

resolveVar : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
resolveRep : ∀ {Δ} → TyStore Δ → Ty Δ → Ty Δ

resolveVar (store-lift Σ) Fin.zero = ＇ Fin.zero
resolveVar (store-lift Σ) (Fin.suc X) = ⇑ᵗ (resolveVar Σ X)
resolveVar (store-bind Σ A) Fin.zero = ⇑ᵗ (resolveRep Σ A)
resolveVar (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (resolveVar Σ X)

resolveRep Σ (＇ X) = resolveVar Σ X
resolveRep Σ (‵ ι) = ‵ ι
resolveRep Σ ★ = ★
resolveRep Σ (A ⇒ B) = A ⇒ B
resolveRep Σ (`∀ A) = `∀ A

record StoreRepImp {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor store-rep-imp
  field
    represented :
      resolveVar (sourceStoreʷ W) Xᴸ
        ⊑ᵂ⟨ W ⟩ resolveVar (targetStoreʷ W) Xᴿ

-- RebaseAt W W′ Xᴸ Xᴿ is an asymmetric source re-parking update.
-- Reduction only introduces one reveal or conceal wrapper per fresh
-- type variable, so descending through one wrapper may change the
-- source pivot's center.  The stores, the center context, and the
-- imprecision environment stay fixed; every old target variable's
-- center is frozen; the pivots are aligned in W′; and their canonical
-- store representations are related in W′.

record RebaseAt {Δᴸ Δᴿ Δ} (W W′ : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    sameRuntime : SameRuntime W W′
    ηᴸ-off-pivot : ∀ {Y} → Y ≢ Xᴸ
      → toRenameᵗ (ηᴸʷ W′) Y ≡ toRenameᵗ (ηᴸʷ W) Y
    ηᴿ-frozen : ∀ Y
      → toRenameᵗ (ηᴿʷ W′) Y ≡ toRenameᵗ (ηᴿʷ W) Y
    pivotAligned : toRenameᵗ (ηᴸʷ W′) Xᴸ ≡ toRenameᵗ (ηᴿʷ W′) Xᴿ
    storeRepresentations : StoreRepImp W′ Xᴸ Xᴿ

sameWorldRebaseAt : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
  → StoreRepImp W Xᴸ Xᴿ
    --------------------
  → RebaseAt W W Xᴸ Xᴿ
sameWorldRebaseAt aligned reps =
  rebase-at (same-runtime refl refl)
    (λ _ → refl) (λ _ → refl) aligned reps

-- One-sided wrappers carry an optional pivot: a conversion with no
-- pivot (an identity-shaped conversion) keeps the world fixed, and a
-- conversion pivoted on a variable may rebase exactly there.

data RebaseAtᴸ {Δᴸ Δᴿ Δ} : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Set where
  rebase-idᴸ : ∀ {W}
      ------------------------
    → RebaseAtᴸ W W nothing

  rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------
    → RebaseAtᴸ W W′ (just Xᴸ)

  -- A source pivot with no aligned target variable.  The target views
  -- the pivot's center as dynamic, so its canonical representation
  -- must sit below ★; there is no alignment to change, so the world
  -- stays fixed.  Type imprecision has no rule with a bare variable on
  -- the imprecise side, so RebaseAtᴿ needs no mirror constructor.
  -- The disalignment premise makes "no aligned target variable"
  -- explicit: no target variable embeds at the pivot's center, which
  -- lets inversion refute the X⊑X view of a concealed pivot.
  rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (ηᴿʷ W) Xᴿ ≢ toRenameᵗ (ηᴸʷ W) Xᴸ)
    → resolveVar (sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
      -------------------------
    → RebaseAtᴸ W W (just Xᴸ)

CenterAligned : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned W X Y =
  toRenameᵗ (ηᴸʷ W) X ≡ toRenameᵗ (ηᴿʷ W) Y

Occupied : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δ
  → Set
Occupied {Δᴿ = Δᴿ} W Z =
  Σ[ Y ∈ TyVar Δᴿ ] toRenameᵗ (ηᴿʷ W) Y ≡ Z

NoTargetOccupant : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δ
  → Set
NoTargetOccupant W Z = Occupied W Z → ⊥

NoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → Set
NoTargetOccupantAtSource W X =
  NoTargetOccupant W (toRenameᵗ (ηᴸʷ W) X)

world-no-target-at-dynamic-star : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → impEnvʷ W (toRenameᵗ (ηᴸʷ W) X) ≡ X⊑★
  → lookupStore (sourceStoreʷ W) X ≡ ★
  → NoTargetOccupantAtSource W X
world-no-target-at-dynamic-star {W = W} {X = X} mark entry
    (Y , aligned) =
  dynamicStarSourcesUnoccupied (invariantsʷ W) X mark entry Y aligned

data TagRebaseAtᴸ {Δᴸ Δᴿ Δ}
    : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Maybe (TyVar Δᴿ) → Set where
  tag-rebase-idᴸ : ∀ {W}
      ----------------------------------
    → TagRebaseAtᴸ W W nothing nothing

  tag-rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------------------
    → TagRebaseAtᴸ W W′ (just Xᴸ) (just Xᴿ)

  tag-rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (ηᴿʷ W) Xᴿ
            ≢ toRenameᵗ (ηᴸʷ W) Xᴸ)
    → resolveVar (sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
      -------------------------------------------------
    → TagRebaseAtᴸ W W (just Xᴸ) nothing

forgetTagRebaseᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
    --------------------------
  → RebaseAtᴸ W W′ Xᴸ?
forgetTagRebaseᴸ tag-rebase-idᴸ = rebase-idᴸ
forgetTagRebaseᴸ (tag-rebase-varᴸ rb) = rebase-varᴸ rb
forgetTagRebaseᴸ (tag-rebase-onlyᴸ to-star disaligned represented) =
  rebase-onlyᴸ to-star disaligned represented

data RebaseAtᴿ {Δᴸ Δᴿ Δ} : World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴿ) → Set where
  rebase-idᴿ : ∀ {W}
      ------------------------
    → RebaseAtᴿ W W nothing

  rebase-varᴿ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt W W′ Xᴸ Xᴿ
      ---------------------------
    → RebaseAtᴿ W W′ (just Xᴿ)
