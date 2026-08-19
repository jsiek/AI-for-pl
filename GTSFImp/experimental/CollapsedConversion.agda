module experimental.CollapsedConversion where

-- File Charter:
--   * Defines store-independent raw conversion syntax and two directional,
--     pivot-indexed typing judgments for it.
--   * Collapses intrinsic endpoints, store validity, and pivot validity into
--     the typing judgments while keeping raw conversions suitable for terms.
--   * Relates the experiment to all three live conversion layers without
--     changing any live relation.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types renaming (`∀ to `∀ᵗ)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
import Conversion as Live
open Live using (Conv↑; Conv↓)
  renaming
    ( unseal to live-unseal
    ; seal to live-seal
    ; _↦↑_ to _live↦↑_
    ; _↦↓_ to _live↦↓_
    ; `∀↑_ to live-∀↑_
    ; `∀↓_ to live-∀↓_
    ; id↑ to live-id↑
    ; id↓ to live-id↓
    ; _⊢↑_ to _live⊢↑_
    ; _⊢↓_ to _live⊢↓_
    ; ⊢↑-unseal to live⊢↑-unseal
    ; ⊢↑-⇒ to live⊢↑-⇒
    ; ⊢↑-∀ to live⊢↑-∀
    ; ⊢↑-id to live⊢↑-id
    ; ⊢↓-seal to live⊢↓-seal
    ; ⊢↓-⇒ to live⊢↓-⇒
    ; ⊢↓-∀ to live⊢↓-∀
    ; ⊢↓-id to live⊢↓-id
    )
import Conversion as Live²
open Live² using ()
  renaming
    ( _⊢↑[_]_ to _live⊢↑[_]_
    ; _⊢↓[_]_ to _live⊢↓[_]_
    ; ⊢↑-unsealˣ to live⊢↑-unsealˣ
    ; ⊢↑-⇒ˣ to live⊢↑-⇒ˣ
    ; ⊢↑-∀ˣ to live⊢↑-∀ˣ
    ; ⊢↑-∀-idˣ to live⊢↑-∀-idˣ
    ; ⊢↑-idˣ to live⊢↑-idˣ
    ; ⊢↓-sealˣ to live⊢↓-sealˣ
    ; ⊢↓-⇒ˣ to live⊢↓-⇒ˣ
    ; ⊢↓-∀ˣ to live⊢↓-∀ˣ
    ; ⊢↓-∀-idˣ to live⊢↓-∀-idˣ
    ; ⊢↓-idˣ to live⊢↓-idˣ
    ; join-none to live-join-none
    ; join-left to live-join-left
    ; join-right to live-join-right
    ; join-both to live-join-both
    )

private
  variable
    Δ Δ′ : TyCtx
    Σ : TyStore Δ
    X? : Maybe (TyVar Δ)
    A A′ B B′ : Ty Δ

------------------------------------------------------------------------
-- Store-independent raw conversions
------------------------------------------------------------------------

infixr 7 _↦_

data Conversion (Δ : TyCtx) : Set where
  id : Conversion Δ
  unseal : TyVar Δ → Conversion Δ
  seal : TyVar Δ → Conversion Δ
  _↦_ : Conversion Δ → Conversion Δ → Conversion Δ
  `∀_ : Conversion (Nat.suc Δ) → Conversion Δ

private
  variable
    c d : Conversion Δ

rename : ∀ (rho : Δ ⇒ʳ Δ′) → Conversion Δ → Conversion Δ′
rename rho id = id
rename rho (unseal X) = unseal (rho X)
rename rho (seal X) = seal (rho X)
rename rho (c ↦ d) = rename rho c ↦ rename rho d
rename rho (`∀ c) = `∀ (rename (extᵗ rho) c)

------------------------------------------------------------------------
-- Raw structural conversion generation
------------------------------------------------------------------------

mutual
  〖_↑_〗 : TyVar Δ → Ty Δ → Conversion Δ
  〖 X ↑ ＇ Y 〗 with X ≟ Y
  〖 X ↑ ＇ .X 〗 | yes refl = unseal X
  〖 X ↑ ＇ Y 〗 | no X≠Y = id
  〖 X ↑ ‵ ι 〗 = id
  〖 X ↑ ★ 〗 = id
  〖 X ↑ A ⇒ B 〗 = 〖 X ↓ A 〗 ↦ 〖 X ↑ B 〗
  〖 X ↑ `∀ᵗ A 〗 = `∀ 〖 Fin.suc X ↑ A 〗

  〖_↓_〗 : TyVar Δ → Ty Δ → Conversion Δ
  〖 X ↓ ＇ Y 〗 with X ≟ Y
  〖 X ↓ ＇ .X 〗 | yes refl = seal X
  〖 X ↓ ＇ Y 〗 | no X≠Y = id
  〖 X ↓ ‵ ι 〗 = id
  〖 X ↓ ★ 〗 = id
  〖 X ↓ A ⇒ B 〗 = 〖 X ↑ A 〗 ↦ 〖 X ↓ B 〗
  〖 X ↓ `∀ᵗ A 〗 = `∀ 〖 Fin.suc X ↓ A 〗

------------------------------------------------------------------------
-- The two final conversion typing judgments
------------------------------------------------------------------------

infix 4 _⊢↑[_]_∶_⇒_ _⊢↓[_]_∶_⇒_

mutual
  data _⊢↑[_]_∶_⇒_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Maybe (TyVar Δ) → Conversion Δ → Ty Δ → Ty Δ → Set where
    ↑-unseal : ∀ {X R}
      → Σ ∋ X ⦂ R
        --------------------------------------
      → Σ ⊢↑[ just X ] unseal X ∶ ＇ X ⇒ R

    ↑-↦-none : ∀ {c d A A′ B B′}
      → Σ ⊢↓[ nothing ] c ∶ A′ ⇒ A
      → Σ ⊢↑[ nothing ] d ∶ B ⇒ B′
        --------------------------------------------------
      → Σ ⊢↑[ nothing ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↑-↦-left : ∀ {X c d A A′ B B′}
      → Σ ⊢↓[ just X ] c ∶ A′ ⇒ A
      → Σ ⊢↑[ nothing ] d ∶ B ⇒ B′
        -------------------------------------------------
      → Σ ⊢↑[ just X ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↑-↦-right : ∀ {X c d A A′ B B′}
      → Σ ⊢↓[ nothing ] c ∶ A′ ⇒ A
      → Σ ⊢↑[ just X ] d ∶ B ⇒ B′
        -------------------------------------------------
      → Σ ⊢↑[ just X ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↑-↦-both : ∀ {X c d A A′ B B′}
      → Σ ⊢↓[ just X ] c ∶ A′ ⇒ A
      → Σ ⊢↑[ just X ] d ∶ B ⇒ B′
        -------------------------------------------------
      → Σ ⊢↑[ just X ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↑-∀ : ∀ {X c A B}
      → store-lift Σ ⊢↑[ just (Fin.suc X) ] c ∶ A ⇒ B
        --------------------------------------------------
      → Σ ⊢↑[ just X ] `∀ c ∶ `∀ᵗ A ⇒ `∀ᵗ B

    ↑-∀-id : ∀ {c A B}
      → store-lift Σ ⊢↑[ nothing ] c ∶ A ⇒ B
        ----------------------------------------------
      → Σ ⊢↑[ nothing ] `∀ c ∶ `∀ᵗ A ⇒ `∀ᵗ B

    ↑-id : ∀ {A}
        --------------------------
      → Σ ⊢↑[ nothing ] id ∶ A ⇒ A

  data _⊢↓[_]_∶_⇒_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Maybe (TyVar Δ) → Conversion Δ → Ty Δ → Ty Δ → Set where
    ↓-seal : ∀ {X R}
      → Σ ∋ X ⦂ R
        ------------------------------------
      → Σ ⊢↓[ just X ] seal X ∶ R ⇒ ＇ X

    ↓-↦-none : ∀ {c d A A′ B B′}
      → Σ ⊢↑[ nothing ] c ∶ A′ ⇒ A
      → Σ ⊢↓[ nothing ] d ∶ B ⇒ B′
        --------------------------------------------------
      → Σ ⊢↓[ nothing ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↓-↦-left : ∀ {X c d A A′ B B′}
      → Σ ⊢↑[ just X ] c ∶ A′ ⇒ A
      → Σ ⊢↓[ nothing ] d ∶ B ⇒ B′
        -------------------------------------------------
      → Σ ⊢↓[ just X ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↓-↦-right : ∀ {X c d A A′ B B′}
      → Σ ⊢↑[ nothing ] c ∶ A′ ⇒ A
      → Σ ⊢↓[ just X ] d ∶ B ⇒ B′
        -------------------------------------------------
      → Σ ⊢↓[ just X ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↓-↦-both : ∀ {X c d A A′ B B′}
      → Σ ⊢↑[ just X ] c ∶ A′ ⇒ A
      → Σ ⊢↓[ just X ] d ∶ B ⇒ B′
        -------------------------------------------------
      → Σ ⊢↓[ just X ] c ↦ d ∶ (A ⇒ B) ⇒ (A′ ⇒ B′)

    ↓-∀ : ∀ {X c A B}
      → store-lift Σ ⊢↓[ just (Fin.suc X) ] c ∶ A ⇒ B
        --------------------------------------------------
      → Σ ⊢↓[ just X ] `∀ c ∶ `∀ᵗ A ⇒ `∀ᵗ B

    ↓-∀-id : ∀ {c A B}
      → store-lift Σ ⊢↓[ nothing ] c ∶ A ⇒ B
        ----------------------------------------------
      → Σ ⊢↓[ nothing ] `∀ c ∶ `∀ᵗ A ⇒ `∀ᵗ B

    ↓-id : ∀ {A}
        --------------------------
      → Σ ⊢↓[ nothing ] id ∶ A ⇒ A

------------------------------------------------------------------------
-- Forgetting live intrinsic annotations
------------------------------------------------------------------------

mutual
  forget↑ : Conv↑ Δ A B → Conversion Δ
  forget↑ (live-unseal X R) = unseal X
  forget↑ (c live↦↑ d) = forget↓ c ↦ forget↑ d
  forget↑ (live-∀↑ c) = `∀ (forget↑ c)
  forget↑ (live-id↑ A) = id

  forget↓ : Conv↓ Δ A B → Conversion Δ
  forget↓ (live-seal X R) = seal X
  forget↓ (c live↦↓ d) = forget↑ c ↦ forget↓ d
  forget↓ (live-∀↓ c) = `∀ (forget↓ c)
  forget↓ (live-id↓ A) = id

------------------------------------------------------------------------
-- Recovering live intrinsic conversions and ordinary validity
------------------------------------------------------------------------

mutual
  intrinsic↑ : Σ ⊢↑[ X? ] c ∶ A ⇒ B → Conv↑ Δ A B
  intrinsic↑ (↑-unseal {X = X} {R = R} X∈) = live-unseal X R
  intrinsic↑ (↑-↦-none c⊢ d⊢) =
    intrinsic↓ c⊢ live↦↑ intrinsic↑ d⊢
  intrinsic↑ (↑-↦-left c⊢ d⊢) =
    intrinsic↓ c⊢ live↦↑ intrinsic↑ d⊢
  intrinsic↑ (↑-↦-right c⊢ d⊢) =
    intrinsic↓ c⊢ live↦↑ intrinsic↑ d⊢
  intrinsic↑ (↑-↦-both c⊢ d⊢) =
    intrinsic↓ c⊢ live↦↑ intrinsic↑ d⊢
  intrinsic↑ (↑-∀ c⊢) = live-∀↑ (intrinsic↑ c⊢)
  intrinsic↑ (↑-∀-id c⊢) = live-∀↑ (intrinsic↑ c⊢)
  intrinsic↑ ↑-id = live-id↑ _

  intrinsic↓ : Σ ⊢↓[ X? ] c ∶ A ⇒ B → Conv↓ Δ A B
  intrinsic↓ (↓-seal {X = X} {R = R} X∈) = live-seal X R
  intrinsic↓ (↓-↦-none c⊢ d⊢) =
    intrinsic↑ c⊢ live↦↓ intrinsic↓ d⊢
  intrinsic↓ (↓-↦-left c⊢ d⊢) =
    intrinsic↑ c⊢ live↦↓ intrinsic↓ d⊢
  intrinsic↓ (↓-↦-right c⊢ d⊢) =
    intrinsic↑ c⊢ live↦↓ intrinsic↓ d⊢
  intrinsic↓ (↓-↦-both c⊢ d⊢) =
    intrinsic↑ c⊢ live↦↓ intrinsic↓ d⊢
  intrinsic↓ (↓-∀ c⊢) = live-∀↓ (intrinsic↓ c⊢)
  intrinsic↓ (↓-∀-id c⊢) = live-∀↓ (intrinsic↓ c⊢)
  intrinsic↓ ↓-id = live-id↓ _

mutual
  valid↑ : (c⊢ : Σ ⊢↑[ X? ] c ∶ A ⇒ B)
    → Σ live⊢↑ intrinsic↑ c⊢
  valid↑ (↑-unseal X∈) = live⊢↑-unseal X∈
  valid↑ (↑-↦-none c⊢ d⊢) =
    live⊢↑-⇒ (valid↓ c⊢) (valid↑ d⊢)
  valid↑ (↑-↦-left c⊢ d⊢) =
    live⊢↑-⇒ (valid↓ c⊢) (valid↑ d⊢)
  valid↑ (↑-↦-right c⊢ d⊢) =
    live⊢↑-⇒ (valid↓ c⊢) (valid↑ d⊢)
  valid↑ (↑-↦-both c⊢ d⊢) =
    live⊢↑-⇒ (valid↓ c⊢) (valid↑ d⊢)
  valid↑ (↑-∀ c⊢) = live⊢↑-∀ (valid↑ c⊢)
  valid↑ (↑-∀-id c⊢) = live⊢↑-∀ (valid↑ c⊢)
  valid↑ ↑-id = live⊢↑-id

  valid↓ : (c⊢ : Σ ⊢↓[ X? ] c ∶ A ⇒ B)
    → Σ live⊢↓ intrinsic↓ c⊢
  valid↓ (↓-seal X∈) = live⊢↓-seal X∈
  valid↓ (↓-↦-none c⊢ d⊢) =
    live⊢↓-⇒ (valid↑ c⊢) (valid↓ d⊢)
  valid↓ (↓-↦-left c⊢ d⊢) =
    live⊢↓-⇒ (valid↑ c⊢) (valid↓ d⊢)
  valid↓ (↓-↦-right c⊢ d⊢) =
    live⊢↓-⇒ (valid↑ c⊢) (valid↓ d⊢)
  valid↓ (↓-↦-both c⊢ d⊢) =
    live⊢↓-⇒ (valid↑ c⊢) (valid↓ d⊢)
  valid↓ (↓-∀ c⊢) = live⊢↓-∀ (valid↓ c⊢)
  valid↓ (↓-∀-id c⊢) = live⊢↓-∀ (valid↓ c⊢)
  valid↓ ↓-id = live⊢↓-id

------------------------------------------------------------------------
-- Correspondence with the live pivot-indexed judgments
------------------------------------------------------------------------

mutual
  embed↑ : (c⊢ : Σ ⊢↑[ X? ] c ∶ A ⇒ B)
    → Σ live⊢↑[ X? ] intrinsic↑ c⊢
  embed↑ (↑-unseal X∈) = live⊢↑-unsealˣ X∈
  embed↑ (↑-↦-none c⊢ d⊢) =
    live⊢↑-⇒ˣ live-join-none (embed↓ c⊢) (embed↑ d⊢)
  embed↑ (↑-↦-left c⊢ d⊢) =
    live⊢↑-⇒ˣ live-join-left (embed↓ c⊢) (embed↑ d⊢)
  embed↑ (↑-↦-right c⊢ d⊢) =
    live⊢↑-⇒ˣ live-join-right (embed↓ c⊢) (embed↑ d⊢)
  embed↑ (↑-↦-both c⊢ d⊢) =
    live⊢↑-⇒ˣ live-join-both (embed↓ c⊢) (embed↑ d⊢)
  embed↑ (↑-∀ c⊢) = live⊢↑-∀ˣ (embed↑ c⊢)
  embed↑ (↑-∀-id c⊢) = live⊢↑-∀-idˣ (embed↑ c⊢)
  embed↑ ↑-id = live⊢↑-idˣ

  embed↓ : (c⊢ : Σ ⊢↓[ X? ] c ∶ A ⇒ B)
    → Σ live⊢↓[ X? ] intrinsic↓ c⊢
  embed↓ (↓-seal X∈) = live⊢↓-sealˣ X∈
  embed↓ (↓-↦-none c⊢ d⊢) =
    live⊢↓-⇒ˣ live-join-none (embed↑ c⊢) (embed↓ d⊢)
  embed↓ (↓-↦-left c⊢ d⊢) =
    live⊢↓-⇒ˣ live-join-left (embed↑ c⊢) (embed↓ d⊢)
  embed↓ (↓-↦-right c⊢ d⊢) =
    live⊢↓-⇒ˣ live-join-right (embed↑ c⊢) (embed↓ d⊢)
  embed↓ (↓-↦-both c⊢ d⊢) =
    live⊢↓-⇒ˣ live-join-both (embed↑ c⊢) (embed↓ d⊢)
  embed↓ (↓-∀ c⊢) = live⊢↓-∀ˣ (embed↓ c⊢)
  embed↓ (↓-∀-id c⊢) = live⊢↓-∀-idˣ (embed↓ c⊢)
  embed↓ ↓-id = live⊢↓-idˣ

mutual
  flatten↑ : ∀ {c : Conv↑ Δ A B}
    → Σ live⊢↑[ X? ] c
    → Σ ⊢↑[ X? ] forget↑ c ∶ A ⇒ B
  flatten↑ (live⊢↑-unsealˣ X∈) = ↑-unseal X∈
  flatten↑ (live⊢↑-⇒ˣ live-join-none c⊢ d⊢) =
    ↑-↦-none (flatten↓ c⊢) (flatten↑ d⊢)
  flatten↑ (live⊢↑-⇒ˣ live-join-left c⊢ d⊢) =
    ↑-↦-left (flatten↓ c⊢) (flatten↑ d⊢)
  flatten↑ (live⊢↑-⇒ˣ live-join-right c⊢ d⊢) =
    ↑-↦-right (flatten↓ c⊢) (flatten↑ d⊢)
  flatten↑ (live⊢↑-⇒ˣ live-join-both c⊢ d⊢) =
    ↑-↦-both (flatten↓ c⊢) (flatten↑ d⊢)
  flatten↑ (live⊢↑-∀ˣ c⊢) = ↑-∀ (flatten↑ c⊢)
  flatten↑ (live⊢↑-∀-idˣ c⊢) = ↑-∀-id (flatten↑ c⊢)
  flatten↑ live⊢↑-idˣ = ↑-id

  flatten↓ : ∀ {c : Conv↓ Δ A B}
    → Σ live⊢↓[ X? ] c
    → Σ ⊢↓[ X? ] forget↓ c ∶ A ⇒ B
  flatten↓ (live⊢↓-sealˣ X∈) = ↓-seal X∈
  flatten↓ (live⊢↓-⇒ˣ live-join-none c⊢ d⊢) =
    ↓-↦-none (flatten↑ c⊢) (flatten↓ d⊢)
  flatten↓ (live⊢↓-⇒ˣ live-join-left c⊢ d⊢) =
    ↓-↦-left (flatten↑ c⊢) (flatten↓ d⊢)
  flatten↓ (live⊢↓-⇒ˣ live-join-right c⊢ d⊢) =
    ↓-↦-right (flatten↑ c⊢) (flatten↓ d⊢)
  flatten↓ (live⊢↓-⇒ˣ live-join-both c⊢ d⊢) =
    ↓-↦-both (flatten↑ c⊢) (flatten↓ d⊢)
  flatten↓ (live⊢↓-∀ˣ c⊢) = ↓-∀ (flatten↓ c⊢)
  flatten↓ (live⊢↓-∀-idˣ c⊢) = ↓-∀-id (flatten↓ c⊢)
  flatten↓ live⊢↓-idˣ = ↓-id

mutual
  intrinsic-flatten↑ : ∀ {c : Conv↑ Δ A B}
    → (c⊢ : Σ live⊢↑[ X? ] c)
    → intrinsic↑ (flatten↑ c⊢) ≡ c
  intrinsic-flatten↑ (live⊢↑-unsealˣ X∈) = refl
  intrinsic-flatten↑ (live⊢↑-⇒ˣ live-join-none c⊢ d⊢)
    rewrite intrinsic-flatten↓ c⊢ | intrinsic-flatten↑ d⊢ = refl
  intrinsic-flatten↑ (live⊢↑-⇒ˣ live-join-left c⊢ d⊢)
    rewrite intrinsic-flatten↓ c⊢ | intrinsic-flatten↑ d⊢ = refl
  intrinsic-flatten↑ (live⊢↑-⇒ˣ live-join-right c⊢ d⊢)
    rewrite intrinsic-flatten↓ c⊢ | intrinsic-flatten↑ d⊢ = refl
  intrinsic-flatten↑ (live⊢↑-⇒ˣ live-join-both c⊢ d⊢)
    rewrite intrinsic-flatten↓ c⊢ | intrinsic-flatten↑ d⊢ = refl
  intrinsic-flatten↑ (live⊢↑-∀ˣ c⊢)
    rewrite intrinsic-flatten↑ c⊢ = refl
  intrinsic-flatten↑ (live⊢↑-∀-idˣ c⊢)
    rewrite intrinsic-flatten↑ c⊢ = refl
  intrinsic-flatten↑ live⊢↑-idˣ = refl

  intrinsic-flatten↓ : ∀ {c : Conv↓ Δ A B}
    → (c⊢ : Σ live⊢↓[ X? ] c)
    → intrinsic↓ (flatten↓ c⊢) ≡ c
  intrinsic-flatten↓ (live⊢↓-sealˣ X∈) = refl
  intrinsic-flatten↓ (live⊢↓-⇒ˣ live-join-none c⊢ d⊢)
    rewrite intrinsic-flatten↑ c⊢ | intrinsic-flatten↓ d⊢ = refl
  intrinsic-flatten↓ (live⊢↓-⇒ˣ live-join-left c⊢ d⊢)
    rewrite intrinsic-flatten↑ c⊢ | intrinsic-flatten↓ d⊢ = refl
  intrinsic-flatten↓ (live⊢↓-⇒ˣ live-join-right c⊢ d⊢)
    rewrite intrinsic-flatten↑ c⊢ | intrinsic-flatten↓ d⊢ = refl
  intrinsic-flatten↓ (live⊢↓-⇒ˣ live-join-both c⊢ d⊢)
    rewrite intrinsic-flatten↑ c⊢ | intrinsic-flatten↓ d⊢ = refl
  intrinsic-flatten↓ (live⊢↓-∀ˣ c⊢)
    rewrite intrinsic-flatten↓ c⊢ = refl
  intrinsic-flatten↓ (live⊢↓-∀-idˣ c⊢)
    rewrite intrinsic-flatten↓ c⊢ = refl
  intrinsic-flatten↓ live⊢↓-idˣ = refl

mutual
  forget-intrinsic↑ : (c⊢ : Σ ⊢↑[ X? ] c ∶ A ⇒ B)
    → forget↑ (intrinsic↑ c⊢) ≡ c
  forget-intrinsic↑ (↑-unseal X∈) = refl
  forget-intrinsic↑ (↑-↦-none c⊢ d⊢)
    rewrite forget-intrinsic↓ c⊢ | forget-intrinsic↑ d⊢ = refl
  forget-intrinsic↑ (↑-↦-left c⊢ d⊢)
    rewrite forget-intrinsic↓ c⊢ | forget-intrinsic↑ d⊢ = refl
  forget-intrinsic↑ (↑-↦-right c⊢ d⊢)
    rewrite forget-intrinsic↓ c⊢ | forget-intrinsic↑ d⊢ = refl
  forget-intrinsic↑ (↑-↦-both c⊢ d⊢)
    rewrite forget-intrinsic↓ c⊢ | forget-intrinsic↑ d⊢ = refl
  forget-intrinsic↑ (↑-∀ c⊢) rewrite forget-intrinsic↑ c⊢ = refl
  forget-intrinsic↑ (↑-∀-id c⊢) rewrite forget-intrinsic↑ c⊢ = refl
  forget-intrinsic↑ ↑-id = refl

  forget-intrinsic↓ : (c⊢ : Σ ⊢↓[ X? ] c ∶ A ⇒ B)
    → forget↓ (intrinsic↓ c⊢) ≡ c
  forget-intrinsic↓ (↓-seal X∈) = refl
  forget-intrinsic↓ (↓-↦-none c⊢ d⊢)
    rewrite forget-intrinsic↑ c⊢ | forget-intrinsic↓ d⊢ = refl
  forget-intrinsic↓ (↓-↦-left c⊢ d⊢)
    rewrite forget-intrinsic↑ c⊢ | forget-intrinsic↓ d⊢ = refl
  forget-intrinsic↓ (↓-↦-right c⊢ d⊢)
    rewrite forget-intrinsic↑ c⊢ | forget-intrinsic↓ d⊢ = refl
  forget-intrinsic↓ (↓-↦-both c⊢ d⊢)
    rewrite forget-intrinsic↑ c⊢ | forget-intrinsic↓ d⊢ = refl
  forget-intrinsic↓ (↓-∀ c⊢) rewrite forget-intrinsic↓ c⊢ = refl
  forget-intrinsic↓ (↓-∀-id c⊢) rewrite forget-intrinsic↓ c⊢ = refl
  forget-intrinsic↓ ↓-id = refl

------------------------------------------------------------------------
-- Ordinary validity remains strictly broader
------------------------------------------------------------------------

multi-store : TyStore (Nat.suc (Nat.suc Nat.zero))
multi-store = store-bind (store-bind store-empty ★) ★

multi-pivot : Conversion (Nat.suc (Nat.suc Nat.zero))
multi-pivot = seal Fin.zero ↦ unseal (Fin.suc Fin.zero)

multi-pivot↑ : Conv↑ (Nat.suc (Nat.suc Nat.zero))
    (＇ Fin.zero ⇒ ＇ Fin.suc Fin.zero) (★ ⇒ ★)
multi-pivot↑ =
  live-seal Fin.zero ★ live↦↑ live-unseal (Fin.suc Fin.zero) ★

multi-pivot↑-valid : multi-store live⊢↑ multi-pivot↑
multi-pivot↑-valid =
  live⊢↑-⇒ (live⊢↓-seal (Z∋ refl))
    (live⊢↑-unseal (S-bind∋ (Z∋ refl) refl))

multi-pivot↑-not-typed : ∀ {X?}
  → multi-store ⊢↑[ X? ] multi-pivot
      ∶ (＇ Fin.zero ⇒ ＇ Fin.suc Fin.zero) ⇒ (★ ⇒ ★)
  → ⊥
multi-pivot↑-not-typed (↑-↦-none () d⊢)
multi-pivot↑-not-typed (↑-↦-left c⊢ ())
multi-pivot↑-not-typed (↑-↦-right () d⊢)
multi-pivot↑-not-typed (↑-↦-both (↓-seal X∈) ())
