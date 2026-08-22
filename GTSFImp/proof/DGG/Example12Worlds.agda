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

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; id; _!)
open import Conversion using
  (Conv↑; _⊢↑_; `∀↑_; id↑; ⊢↑-∀; ⊢↑-id;
   _⊢↑[_]_; ⊢↑-∀-idˣ; ⊢↑-idˣ)
open import Imprecision using
  (ImpEnv; X⊑X; X⊑★; ★⊑★; ι⊑ι; ι⊑★; ⇒⊑⇒)
open import CastTerms using
  (Term; _⊢_⦂_; _·_; _⦂∀_[_]; _⟨_⟩; _↑_;
   ⊢·; ⊢⟨⟩; ⊢•; ⊢reveal)
open import proof.DGG.CtxImp using
  (World; world; _⊑ᵂ⟨_⟩_; StoreRepImp; store-rep-imp;
   RebaseAt; rebase-at; same-runtime)
import proof.DGG.ExampleTerms as Ex

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

example12-world-X : World 1 3 3
example12-world-X =
  world example12-ηᴸ-X example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store

example12-world-Y : World 1 3 3
example12-world-Y =
  world example12-ηᴸ-Y example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store

example12-world-Z : World 1 3 3
example12-world-Z =
  world example12-ηᴸ-Z example12-ηᴿ example12-imp-env
    example12-source-store example12-target-store

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

example12-Z-representation :
  StoreRepImp example12-world-Z Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-Z-representation = store-rep-imp ι⊑★

example12-Y-representation :
  StoreRepImp example12-world-Y Fin.zero (Fin.suc Fin.zero)
example12-Y-representation = store-rep-imp ι⊑★

example12-rebase-X-to-Z :
  RebaseAt example12-world-X example12-world-Z
    Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-rebase-X-to-Z =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) }) (λ _ → refl)
    refl example12-Z-representation

example12-rebase-X-to-Y :
  RebaseAt example12-world-X example12-world-Y Fin.zero (Fin.suc Fin.zero)
example12-rebase-X-to-Y =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) }) (λ _ → refl)
    refl example12-Y-representation

example12-outer-function :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ example12-world-X ⟩ (＇ Fin.zero ⇒ ＇ Fin.zero)
example12-outer-function = ⇒⊑⇒ X⊑X X⊑X

example12-Z-function :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ example12-world-Z ⟩
      (＇ (Fin.suc (Fin.suc Fin.zero))
        ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
example12-Z-function = ⇒⊑⇒ X⊑X X⊑X

example12-Y-function :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ example12-world-Y ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
example12-Y-function = ⇒⊑⇒ X⊑X X⊑X

example12-Z-function-to-star :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ example12-world-Z ⟩ (★ ⇒ ★)
example12-Z-function-to-star = ⇒⊑⇒ (X⊑★ refl) (X⊑★ refl)

example12-Y-function-to-star :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ example12-world-Y ⟩ (★ ⇒ ★)
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

example12-nat-chain-world-X : World 1 2 2
example12-nat-chain-world-X =
  world example12-nat-chain-ηᴸ-X example12-nat-chain-ηᴿ
    example12-nat-chain-imp-env
    example12-nat-chain-source-store
    example12-nat-chain-target-store

example12-nat-chain-world-Y : World 1 2 2
example12-nat-chain-world-Y =
  world example12-nat-chain-ηᴸ-Y example12-nat-chain-ηᴿ
    example12-nat-chain-imp-env
    example12-nat-chain-source-store
    example12-nat-chain-target-store

example12-nat-chain-source-X∋ :
  example12-nat-chain-source-store ∋ Fin.zero ⦂ ‵ `ℕ
example12-nat-chain-source-X∋ = Z∋ refl

example12-nat-chain-target-Y∋ :
  example12-nat-chain-target-store ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
example12-nat-chain-target-Y∋ = Z∋ refl

example12-nat-chain-target-X∋ :
  example12-nat-chain-target-store ∋ Fin.suc Fin.zero ⦂ ‵ `ℕ
example12-nat-chain-target-X∋ = S-bind∋ (Z∋ refl) refl

example12-nat-chain-X-representation :
  StoreRepImp example12-nat-chain-world-X Fin.zero (Fin.suc Fin.zero)
example12-nat-chain-X-representation = store-rep-imp ι⊑ι

example12-nat-chain-Y-representation :
  StoreRepImp example12-nat-chain-world-Y Fin.zero Fin.zero
example12-nat-chain-Y-representation = store-rep-imp ι⊑ι

example12-nat-chain-rebase-X-to-Y :
  RebaseAt example12-nat-chain-world-X example12-nat-chain-world-Y
    Fin.zero Fin.zero
example12-nat-chain-rebase-X-to-Y =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) }) (λ _ → refl)
    refl example12-nat-chain-Y-representation

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
example12-left-path-imp-env Fin.zero = X⊑X
example12-left-path-imp-env (Fin.suc Fin.zero) = X⊑X
example12-left-path-imp-env (Fin.suc (Fin.suc Fin.zero)) = X⊑X

example12-left-path-ηᴸ : 3 ↪ᵗ 3
example12-left-path-ηᴸ = keep (keep (keep empty))

example12-left-path-ηᴿ-X : 1 ↪ᵗ 3
example12-left-path-ηᴿ-X = keep (skip (skip empty))

example12-left-path-ηᴿ-Y : 1 ↪ᵗ 3
example12-left-path-ηᴿ-Y = skip (keep empty)

example12-left-path-ηᴿ-Z : 1 ↪ᵗ 3
example12-left-path-ηᴿ-Z = skip (skip (keep empty))

example12-left-path-world-X : World 3 1 3
example12-left-path-world-X =
  world example12-left-path-ηᴸ example12-left-path-ηᴿ-X
    example12-left-path-imp-env
    example12-left-path-source-store
    example12-left-path-target-store

example12-left-path-world-Y : World 3 1 3
example12-left-path-world-Y =
  world example12-left-path-ηᴸ example12-left-path-ηᴿ-Y
    example12-left-path-imp-env
    example12-left-path-source-store
    example12-left-path-target-store

example12-left-path-world-Z : World 3 1 3
example12-left-path-world-Z =
  world example12-left-path-ηᴸ example12-left-path-ηᴿ-Z
    example12-left-path-imp-env
    example12-left-path-source-store
    example12-left-path-target-store

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
