module proof.DGG.Example12Worlds where

-- File Charter:
--   * Provides fixtures exercising representation chains and world variants
--     for Example 12.
--   * Records the Example 12 alignments Xᴸ≅Xᴿ, Xᴸ≅Zᴿ, and Xᴸ≅Yᴿ as first-class
--     store-representation witnesses.
--   * Records a left-hand analogue of Example 12 where the source store, not
--     the target store, has the representation path to ★.
--   * Records a variant where the target store has a representation path to
--     ℕ, showing that representation paths are not only a ★ phenomenon.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; lookupStore;
   _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; id; _!)
open import Conversion using
  (Conv↑; _⊢↑_; `∀↑_; id↑; ⊢↑-∀; ⊢↑-id;
   _⊢↑[_]_; ⊢↑-∀-idˣ; ⊢↑-idˣ)
open import Imprecision using
  (ImpEnv; _⊢_⊑_; X⊑X; X⊑★; ★⊑★; ι⊑ι; ι⊑★; ⇒⊑⇒)
open import CastTerms using
  (Term; _⊢_⦂_; _·_; _⦂∀_[_]; _⟨_⟩; _↑_;
   ⊢·; ⊢⟨⟩; ⊢•; ⊢reveal)
open import proof.DGG.CtxImp using
  (World; WorldInvariants; emptyʷ; bind-leftʷ; bind-rightʷ;
   bind-bothʷ; bind-both-starʷ; world-invariants;
   unmatchedTargetsDynamic; _⊑ᵂ⟨_⟩_;
   StoreRepImp; store-rep-imp; resolveVar;
   RebaseAt; rebase-at; same-runtime)
import proof.DGG.ExampleTerms as Ex

record RejectedWorldFixture {Δᴸ Δᴿ Δ : TyCtx}
    (ηᴸ : Δᴸ ↪ᵗ Δ) (ηᴿ : Δᴿ ↪ᵗ Δ)
    (μ : ImpEnv Δ) (Σᴸ : TyStore Δᴸ) (Σᴿ : TyStore Δᴿ) : Set where
  constructor rejected-world-fixture
  field
    violates-invariants : WorldInvariants ηᴸ ηᴿ μ Σᴸ Σᴿ → ⊥

open RejectedWorldFixture public

------------------------------------------------------------------------
-- Example 12 local alignments
------------------------------------------------------------------------

example12-source-store : TyStore 1
example12-source-store = store-bind store-empty (‵ `ℕ)

example12-target-store : TyStore 3
example12-target-store =
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) (‵ `ℕ)

example12-imp-env : ImpEnv 3
example12-imp-env Fin.zero = X⊑★
example12-imp-env (Fin.suc Fin.zero) = X⊑★
example12-imp-env (Fin.suc (Fin.suc Fin.zero)) = X⊑★

example12-ηᴿ : 3 ↪ᵗ 3
example12-ηᴿ = keep (keep (keep empty))

example12-ηᴸ-X : 1 ↪ᵗ 3
example12-ηᴸ-X = keep (skip (skip empty))

example12-ηᴸ-Y : 1 ↪ᵗ 3
example12-ηᴸ-Y = skip (keep empty)

example12-ηᴸ-Z : 1 ↪ᵗ 3
example12-ηᴸ-Z = skip (skip (keep empty))

example12-ηᴸ-X-maps : toRenameᵗ example12-ηᴸ-X Fin.zero ≡ Fin.zero
example12-ηᴸ-X-maps = refl

example12-ηᴸ-Y-maps :
  toRenameᵗ example12-ηᴸ-Y Fin.zero ≡ Fin.suc Fin.zero
example12-ηᴸ-Y-maps = refl

example12-ηᴸ-Z-maps :
  toRenameᵗ example12-ηᴸ-Z Fin.zero ≡ Fin.suc (Fin.suc Fin.zero)
example12-ηᴸ-Z-maps = refl

example12-world-X-invariants :
  WorldInvariants example12-ηᴸ-X example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store
example12-world-X-invariants =
  world-invariants precise representations unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → example12-imp-env (toRenameᵗ example12-ηᴸ-X Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 3 ]
        toRenameᵗ example12-ηᴿ Xᴿ
          ≡ toRenameᵗ example12-ηᴸ-X Xᴸ
  precise Fin.zero ()

  representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 3}
    → toRenameᵗ example12-ηᴸ-X Xᴸ ≡ toRenameᵗ example12-ηᴿ Xᴿ
    → example12-imp-env ⊢
        renameᵗ (toRenameᵗ example12-ηᴸ-X)
          (lookupStore example12-source-store Xᴸ)
        ⊑ renameᵗ (toRenameᵗ example12-ηᴿ)
          (lookupStore example12-target-store Xᴿ)
  representations {Fin.zero} {Fin.zero} aligned = ι⊑ι
  representations {Fin.zero} {Fin.suc Fin.zero} ()
  representations {Fin.zero} {Fin.suc (Fin.suc Fin.zero)} ()

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ example12-ηᴸ-X Xᴸ
          ≢ toRenameᵗ example12-ηᴿ Xᴿ)
    → lookupStore example12-target-store Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 3 ]
          (lookupStore example12-target-store Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ example12-ηᴸ-X Xᴸ
              ≢ toRenameᵗ example12-ηᴿ Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Fin.zero) no-source =
    inj₂ (Fin.suc (Fin.suc Fin.zero) , refl , λ { Fin.zero () })
  unmatched (Fin.suc (Fin.suc Fin.zero)) no-source = inj₁ refl

  unoccupied : ∀ Xᴸ
    → example12-imp-env (toRenameᵗ example12-ηᴸ-X Xᴸ) ≡ X⊑★
    → lookupStore example12-source-store Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ example12-ηᴿ Xᴿ
      ≢ toRenameᵗ example12-ηᴸ-X Xᴸ
  unoccupied Fin.zero mark () Xᴿ aligned

example12-world-X : World 1 3 3
example12-world-X =
  bind-both-starʷ
    (bind-rightʷ
      (bind-rightʷ emptyʷ ★ (inj₁ refl))
      (＇ Fin.zero)
      (inj₂ (Fin.suc Fin.zero , refl , λ ())))
    (‵ `ℕ) (‵ `ℕ) ι⊑ι (λ ())

example12-world-Y :
  RejectedWorldFixture example12-ηᴸ-Y example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store
example12-world-Y = rejected-world-fixture rejected
  where
  rejected :
    WorldInvariants example12-ηᴸ-Y example12-ηᴿ example12-imp-env
      example12-source-store example12-target-store
    → ⊥
  rejected inv
      with unmatchedTargetsDynamic inv Fin.zero (λ { Fin.zero () })
  rejected inv | inj₁ ()
  rejected inv | inj₂ (Xᴿ , () , head-unmatched)

example12-world-Z :
  RejectedWorldFixture example12-ηᴸ-Z example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store
example12-world-Z = rejected-world-fixture rejected
  where
  rejected :
    WorldInvariants example12-ηᴸ-Z example12-ηᴿ example12-imp-env
      example12-source-store example12-target-store
    → ⊥
  rejected inv
      with unmatchedTargetsDynamic inv Fin.zero (λ { Fin.zero () })
  rejected inv | inj₁ ()
  rejected inv | inj₂ (Xᴿ , () , head-unmatched)

example12-source-X∋ :
  example12-source-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-source-X∋ = Z∋ refl

example12-target-X∋ :
  example12-target-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-target-X∋ = Z∋ refl

example12-target-Y∋ :
  example12-target-store ∋ Fin.suc Fin.zero
    ⦂ ＇ (Fin.suc (Fin.suc Fin.zero))
example12-target-Y∋ = S-bind∋ (Z∋ refl) refl

example12-target-Z∋ :
  example12-target-store ∋ Fin.suc (Fin.suc Fin.zero) ⦂ ★
example12-target-Z∋ = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

example12-X-representation : StoreRepImp example12-world-X Fin.zero Fin.zero
example12-X-representation = store-rep-imp ι⊑ι

example12-Z-representation : example12-imp-env ⊢
    renameᵗ (toRenameᵗ example12-ηᴸ-Z)
      (resolveVar example12-source-store Fin.zero)
    ⊑ renameᵗ (toRenameᵗ example12-ηᴿ)
      (resolveVar example12-target-store
        (Fin.suc (Fin.suc Fin.zero)))
example12-Z-representation = ι⊑★

example12-Y-representation : example12-imp-env ⊢
    renameᵗ (toRenameᵗ example12-ηᴸ-Y)
      (resolveVar example12-source-store Fin.zero)
    ⊑ renameᵗ (toRenameᵗ example12-ηᴿ)
      (resolveVar example12-target-store (Fin.suc Fin.zero))
example12-Y-representation = ι⊑★

example12-rebase-X-to-Z :
  WorldInvariants example12-ηᴸ-Z example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store
  → ⊥
example12-rebase-X-to-Z = violates-invariants example12-world-Z

example12-rebase-X-to-Y :
  WorldInvariants example12-ηᴸ-Y example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store
  → ⊥
example12-rebase-X-to-Y = violates-invariants example12-world-Y

example12-outer-function :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ example12-world-X ⟩ (＇ Fin.zero ⇒ ＇ Fin.zero)
example12-outer-function = ⇒⊑⇒ X⊑X X⊑X

example12-Z-function : example12-imp-env ⊢
    (＇ (Fin.suc (Fin.suc Fin.zero))
      ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ (＇ (Fin.suc (Fin.suc Fin.zero))
      ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
example12-Z-function = ⇒⊑⇒ X⊑X X⊑X

example12-Y-function : example12-imp-env ⊢
    (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
    ⊑ (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
example12-Y-function = ⇒⊑⇒ X⊑X X⊑X

example12-Z-function-to-star : example12-imp-env ⊢
    (＇ (Fin.suc (Fin.suc Fin.zero))
      ⇒ ＇ (Fin.suc (Fin.suc Fin.zero))) ⊑ (★ ⇒ ★)
example12-Z-function-to-star = ⇒⊑⇒ (X⊑★ refl) (X⊑★ refl)

example12-Y-function-to-star : example12-imp-env ⊢
    (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero)) ⊑ (★ ⇒ ★)
example12-Y-function-to-star = ⇒⊑⇒ (X⊑★ refl) (X⊑★ refl)

------------------------------------------------------------------------
-- β-reveal-∀ followed by β-Λ: a path to ℕ, not ★
------------------------------------------------------------------------

-- The target wraps the polymorphic identity in an explicit universal reveal.
-- When applied at ℕ, β-reveal-∀ first allocates X ↦ ℕ.  The β-Λ exposed under
-- that reveal then instantiates at the fresh X and allocates Y ↦ X.  Comparing
-- the source's ordinary X ↦ ℕ cell against target Y therefore needs the
-- representation path Y ↦ X ↦ ℕ, not a path to ★.

example12-nat-chain-source : Term 0
example12-nat-chain-source = Ex.example12-left

example12-nat-chain-source-⊢ :
  Ex.∅ ⊢ example12-nat-chain-source ⦂ Ex.ℕᵗ
example12-nat-chain-source-⊢ = Ex.example12-left-⊢

example12-nat-chain-reveal :
  Conv↑ 0 (`∀ Ex.X⇒X) (`∀ Ex.X⇒X)
example12-nat-chain-reveal = `∀↑ (id↑ Ex.X⇒X)

example12-nat-chain-reveal-⊢ :
  store-empty ⊢↑ example12-nat-chain-reveal
example12-nat-chain-reveal-⊢ = ⊢↑-∀ ⊢↑-id

example12-nat-chain-reveal-⊢ˣ :
  store-empty ⊢↑[ nothing ] example12-nat-chain-reveal
example12-nat-chain-reveal-⊢ˣ = ⊢↑-∀-idˣ ⊢↑-idˣ

example12-nat-chain-target : Term 0
example12-nat-chain-target =
  ((Ex.polyId ↑ example12-nat-chain-reveal)
    ⦂∀ Ex.X⇒X [ Ex.ℕᵗ ]) · Ex.c

example12-nat-chain-target-⊢ :
  Ex.∅ ⊢ example12-nat-chain-target ⦂ Ex.ℕᵗ
example12-nat-chain-target-⊢ =
  ⊢· (⊢• (⊢reveal example12-nat-chain-reveal-⊢ Ex.polyId-⊢))
    Ex.c-⊢

example12-nat-chain-source-store : TyStore 1
example12-nat-chain-source-store = store-bind store-empty (‵ `ℕ)

example12-nat-chain-target-store : TyStore 2
example12-nat-chain-target-store =
  store-bind (store-bind store-empty (‵ `ℕ)) (＇ Fin.zero)

example12-nat-chain-imp-env : ImpEnv 2
example12-nat-chain-imp-env Fin.zero = X⊑X
example12-nat-chain-imp-env (Fin.suc Fin.zero) = X⊑X

example12-nat-chain-ηᴿ : 2 ↪ᵗ 2
example12-nat-chain-ηᴿ = keep (keep empty)

example12-nat-chain-ηᴸ-X : 1 ↪ᵗ 2
example12-nat-chain-ηᴸ-X = skip (keep empty)

example12-nat-chain-ηᴸ-Y : 1 ↪ᵗ 2
example12-nat-chain-ηᴸ-Y = keep empty

example12-nat-chain-world-X :
  RejectedWorldFixture example12-nat-chain-ηᴸ-X
    example12-nat-chain-ηᴿ example12-nat-chain-imp-env
    example12-nat-chain-source-store example12-nat-chain-target-store
example12-nat-chain-world-X = rejected-world-fixture rejected
  where
  rejected :
    WorldInvariants example12-nat-chain-ηᴸ-X
      example12-nat-chain-ηᴿ example12-nat-chain-imp-env
      example12-nat-chain-source-store example12-nat-chain-target-store
    → ⊥
  rejected inv
      with unmatchedTargetsDynamic inv Fin.zero (λ { Fin.zero () })
  rejected inv | inj₁ ()
  rejected inv | inj₂ (Fin.zero , () , head-unmatched)
  rejected inv | inj₂ (Fin.suc Fin.zero , refl , head-unmatched) =
    head-unmatched Fin.zero refl

example12-nat-chain-world-Y :
  RejectedWorldFixture example12-nat-chain-ηᴸ-Y
    example12-nat-chain-ηᴿ example12-nat-chain-imp-env
    example12-nat-chain-source-store example12-nat-chain-target-store
example12-nat-chain-world-Y = rejected-world-fixture rejected
  where
  rejected :
    WorldInvariants example12-nat-chain-ηᴸ-Y
      example12-nat-chain-ηᴿ example12-nat-chain-imp-env
      example12-nat-chain-source-store example12-nat-chain-target-store
    → ⊥
  rejected inv
      with unmatchedTargetsDynamic inv (Fin.suc Fin.zero)
        (λ { Fin.zero () })
  rejected inv | inj₁ ()
  rejected inv | inj₂ (Xᴿ , () , head-unmatched)

example12-nat-chain-source-X∋ :
  example12-nat-chain-source-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-nat-chain-source-X∋ = Z∋ refl

example12-nat-chain-target-Y∋ :
  example12-nat-chain-target-store ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
example12-nat-chain-target-Y∋ = Z∋ refl

example12-nat-chain-target-X∋ :
  example12-nat-chain-target-store ∋ Fin.suc Fin.zero ⦂ ‵ `ℕ
example12-nat-chain-target-X∋ = S-bind∋ (Z∋ refl) refl

example12-nat-chain-X-representation : example12-nat-chain-imp-env ⊢
    renameᵗ (toRenameᵗ example12-nat-chain-ηᴸ-X)
      (resolveVar example12-nat-chain-source-store Fin.zero)
    ⊑ renameᵗ (toRenameᵗ example12-nat-chain-ηᴿ)
      (resolveVar example12-nat-chain-target-store (Fin.suc Fin.zero))
example12-nat-chain-X-representation = ι⊑ι

example12-nat-chain-Y-representation : example12-nat-chain-imp-env ⊢
    renameᵗ (toRenameᵗ example12-nat-chain-ηᴸ-Y)
      (resolveVar example12-nat-chain-source-store Fin.zero)
    ⊑ renameᵗ (toRenameᵗ example12-nat-chain-ηᴿ)
      (resolveVar example12-nat-chain-target-store Fin.zero)
example12-nat-chain-Y-representation = ι⊑ι

example12-nat-chain-rebase-X-to-Y :
  WorldInvariants example12-nat-chain-ηᴸ-Y
    example12-nat-chain-ηᴿ example12-nat-chain-imp-env
    example12-nat-chain-source-store example12-nat-chain-target-store
  → ⊥
example12-nat-chain-rebase-X-to-Y =
  violates-invariants example12-nat-chain-world-Y

------------------------------------------------------------------------
-- Example 12 variant with the representation path on the left
------------------------------------------------------------------------

-- The source is Example 12's up/down detour.  The target stops after the
-- upcast to ★ ⇒ ★ and casts the argument to ★, so the pair still has the
-- source on the more precise side: ℕ ⊑ ★.

example12-left-path-source : Term 0
example12-left-path-source = Ex.example12-right

example12-left-path-source-⊢ :
  Ex.∅ ⊢ example12-left-path-source ⦂ Ex.ℕᵗ
example12-left-path-source-⊢ = Ex.example12-right-⊢

example12-ℕ! : Ex.ℕᵗ ∼ ★
example12-ℕ! = id (‵ `ℕ) !

example12-left-path-target : Term 0
example12-left-path-target =
  (Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩)
    · (Ex.c ⟨ example12-ℕ! ⟩)

example12-left-path-target-⊢ :
  Ex.∅ ⊢ example12-left-path-target ⦂ ★
example12-left-path-target-⊢ =
  ⊢· (⊢⟨⟩ Ex.polyId-⊢ Ex.ν̅α-α♯→α♭)
    (⊢⟨⟩ Ex.c-⊢ example12-ℕ!)

example12-left-path-source-store : TyStore 3
example12-left-path-source-store =
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) (‵ `ℕ)

example12-left-path-target-store : TyStore 1
example12-left-path-target-store = store-bind store-empty ★

example12-left-path-imp-env : ImpEnv 3
example12-left-path-imp-env Fin.zero = X⊑★
example12-left-path-imp-env (Fin.suc Fin.zero) = X⊑★
example12-left-path-imp-env (Fin.suc (Fin.suc Fin.zero)) = X⊑★

example12-left-path-Z-imp-env : ImpEnv 3
example12-left-path-Z-imp-env Fin.zero = X⊑★
example12-left-path-Z-imp-env (Fin.suc Fin.zero) = X⊑★
example12-left-path-Z-imp-env (Fin.suc (Fin.suc Fin.zero)) = X⊑X

example12-left-path-ηᴸ : 3 ↪ᵗ 3
example12-left-path-ηᴸ = keep (keep (keep empty))

example12-left-path-ηᴿ-X : 1 ↪ᵗ 3
example12-left-path-ηᴿ-X = keep (skip (skip empty))

example12-left-path-ηᴿ-Y : 1 ↪ᵗ 3
example12-left-path-ηᴿ-Y = skip (keep empty)

example12-left-path-ηᴿ-Z : 1 ↪ᵗ 3
example12-left-path-ηᴿ-Z = skip (skip (keep empty))

example12-left-path-world-X-invariants :
  WorldInvariants example12-left-path-ηᴸ example12-left-path-ηᴿ-X
    example12-left-path-imp-env example12-left-path-source-store
    example12-left-path-target-store
example12-left-path-world-X-invariants =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → example12-left-path-imp-env
        (toRenameᵗ example12-left-path-ηᴸ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 1 ]
        toRenameᵗ example12-left-path-ηᴿ-X Xᴿ
          ≡ toRenameᵗ example12-left-path-ηᴸ Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) ()

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 1}
    → toRenameᵗ example12-left-path-ηᴸ Xᴸ
        ≡ toRenameᵗ example12-left-path-ηᴿ-X Xᴿ
    → example12-left-path-imp-env ⊢
        renameᵗ (toRenameᵗ example12-left-path-ηᴸ)
          (lookupStore example12-left-path-source-store Xᴸ)
        ⊑ renameᵗ (toRenameᵗ example12-left-path-ηᴿ-X)
          (lookupStore example12-left-path-target-store Xᴿ)
  reps {Fin.zero} {Fin.zero} refl = ι⊑★
  reps {Fin.suc Fin.zero} {Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ example12-left-path-ηᴸ Xᴸ
          ≢ toRenameᵗ example12-left-path-ηᴿ-X Xᴿ)
    → lookupStore example12-left-path-target-store Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 1 ]
          (lookupStore example12-left-path-target-store Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ example12-left-path-ηᴸ Xᴸ
              ≢ toRenameᵗ example12-left-path-ηᴿ-X Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)

  unoccupied : ∀ Xᴸ
    → example12-left-path-imp-env
        (toRenameᵗ example12-left-path-ηᴸ Xᴸ) ≡ X⊑★
    → lookupStore example12-left-path-source-store Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ example12-left-path-ηᴿ-X Xᴿ
      ≢ toRenameᵗ example12-left-path-ηᴸ Xᴸ
  unoccupied Fin.zero mark () Xᴿ aligned
  unoccupied (Fin.suc Fin.zero) mark () Xᴿ aligned
  unoccupied (Fin.suc (Fin.suc Fin.zero)) mark entry Fin.zero ()

example12-left-path-world-X : World 3 1 3
example12-left-path-world-X =
  bind-both-starʷ
    (bind-leftʷ (bind-leftʷ emptyʷ ★) (＇ Fin.zero))
    (‵ `ℕ) ★ ι⊑★ (λ ())

example12-left-path-world-Y-invariants :
  WorldInvariants example12-left-path-ηᴸ example12-left-path-ηᴿ-Y
    example12-left-path-imp-env example12-left-path-source-store
    example12-left-path-target-store
example12-left-path-world-Y-invariants =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → example12-left-path-imp-env
        (toRenameᵗ example12-left-path-ηᴸ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 1 ]
        toRenameᵗ example12-left-path-ηᴿ-Y Xᴿ
          ≡ toRenameᵗ example12-left-path-ηᴸ Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) ()

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 1}
    → toRenameᵗ example12-left-path-ηᴸ Xᴸ
        ≡ toRenameᵗ example12-left-path-ηᴿ-Y Xᴿ
    → example12-left-path-imp-env ⊢
        renameᵗ (toRenameᵗ example12-left-path-ηᴸ)
          (lookupStore example12-left-path-source-store Xᴸ)
        ⊑ renameᵗ (toRenameᵗ example12-left-path-ηᴿ-Y)
          (lookupStore example12-left-path-target-store Xᴿ)
  reps {Fin.zero} {Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.zero} refl = X⊑★ refl
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ example12-left-path-ηᴸ Xᴸ
          ≢ toRenameᵗ example12-left-path-ηᴿ-Y Xᴿ)
    → lookupStore example12-left-path-target-store Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 1 ]
          (lookupStore example12-left-path-target-store Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ example12-left-path-ηᴸ Xᴸ
              ≢ toRenameᵗ example12-left-path-ηᴿ-Y Yᴿ)
  unmatched Fin.zero no-source =
    ⊥-elim (no-source (Fin.suc Fin.zero) refl)

  unoccupied : ∀ Xᴸ
    → example12-left-path-imp-env
        (toRenameᵗ example12-left-path-ηᴸ Xᴸ) ≡ X⊑★
    → lookupStore example12-left-path-source-store Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ example12-left-path-ηᴿ-Y Xᴿ
      ≢ toRenameᵗ example12-left-path-ηᴸ Xᴸ
  unoccupied Fin.zero mark () Xᴿ aligned
  unoccupied (Fin.suc Fin.zero) mark () Xᴿ aligned
  unoccupied (Fin.suc (Fin.suc Fin.zero)) mark entry Fin.zero ()

example12-left-path-world-Y : World 3 1 3
example12-left-path-world-Y =
  bind-leftʷ
    (bind-both-starʷ (bind-leftʷ emptyʷ ★)
      (＇ Fin.zero) ★ (X⊑★ refl) (λ ()))
    (‵ `ℕ)

example12-left-path-world-Z-invariants :
  WorldInvariants example12-left-path-ηᴸ example12-left-path-ηᴿ-Z
    example12-left-path-Z-imp-env example12-left-path-source-store
    example12-left-path-target-store
example12-left-path-world-Z-invariants =
  world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → example12-left-path-Z-imp-env
        (toRenameᵗ example12-left-path-ηᴸ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 1 ]
        toRenameᵗ example12-left-path-ηᴿ-Z Xᴿ
          ≡ toRenameᵗ example12-left-path-ηᴸ Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) mark = Fin.zero , refl

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 1}
    → toRenameᵗ example12-left-path-ηᴸ Xᴸ
        ≡ toRenameᵗ example12-left-path-ηᴿ-Z Xᴿ
    → example12-left-path-Z-imp-env ⊢
        renameᵗ (toRenameᵗ example12-left-path-ηᴸ)
          (lookupStore example12-left-path-source-store Xᴸ)
        ⊑ renameᵗ (toRenameᵗ example12-left-path-ηᴿ-Z)
          (lookupStore example12-left-path-target-store Xᴿ)
  reps {Fin.zero} {Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} refl = ★⊑★

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ example12-left-path-ηᴸ Xᴸ
          ≢ toRenameᵗ example12-left-path-ηᴿ-Z Xᴿ)
    → lookupStore example12-left-path-target-store Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 1 ]
          (lookupStore example12-left-path-target-store Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ example12-left-path-ηᴸ Xᴸ
              ≢ toRenameᵗ example12-left-path-ηᴿ-Z Yᴿ)
  unmatched Fin.zero no-source =
    ⊥-elim (no-source (Fin.suc (Fin.suc Fin.zero)) refl)

  unoccupied : ∀ Xᴸ
    → example12-left-path-Z-imp-env
        (toRenameᵗ example12-left-path-ηᴸ Xᴸ) ≡ X⊑★
    → lookupStore example12-left-path-source-store Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ example12-left-path-ηᴿ-Z Xᴿ
      ≢ toRenameᵗ example12-left-path-ηᴸ Xᴸ
  unoccupied Fin.zero mark () Xᴿ aligned
  unoccupied (Fin.suc Fin.zero) mark () Xᴿ aligned
  unoccupied (Fin.suc (Fin.suc Fin.zero)) () entry Xᴿ aligned

example12-left-path-world-Z : World 3 1 3
example12-left-path-world-Z =
  bind-leftʷ
    (bind-leftʷ (bind-bothʷ emptyʷ ★ ★ ★⊑★) (＇ Fin.zero))
    (‵ `ℕ)

example12-left-path-source-X∋ :
  example12-left-path-source-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-left-path-source-X∋ = Z∋ refl

example12-left-path-source-Y∋ :
  example12-left-path-source-store ∋ Fin.suc Fin.zero
    ⦂ ＇ (Fin.suc (Fin.suc Fin.zero))
example12-left-path-source-Y∋ = S-bind∋ (Z∋ refl) refl

example12-left-path-source-Z∋ :
  example12-left-path-source-store ∋ Fin.suc (Fin.suc Fin.zero) ⦂ ★
example12-left-path-source-Z∋ =
  S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

example12-left-path-target-U∋ :
  example12-left-path-target-store ∋ Fin.zero ⦂ ★
example12-left-path-target-U∋ = Z∋ refl

example12-left-path-X-representation :
  StoreRepImp example12-left-path-world-X Fin.zero Fin.zero
example12-left-path-X-representation = store-rep-imp ι⊑★

example12-left-path-Z-representation :
  StoreRepImp example12-left-path-world-Z
    (Fin.suc (Fin.suc Fin.zero)) Fin.zero
example12-left-path-Z-representation = store-rep-imp ★⊑★

example12-left-path-Y-representation :
  StoreRepImp example12-left-path-world-Y (Fin.suc Fin.zero) Fin.zero
example12-left-path-Y-representation = store-rep-imp ★⊑★
