module proof.Occurs where

-- File Charter:
--   * THE BOOLEAN OCCURRENCE CHECK `occurs` VERSUS THE OCCURRENCE
--     RELATION `_∈ᵗ_` (both Coercion.agda §3; design.md D24).
--   * `∈→occurs` and `occurs→∈`: the two agree.  `∈-⇒ʳ′`: the
--     unconditional right-of-arrow occurrence (picks `∈-⇒ˡ` when X also
--     occurs in the domain), for proofs that build occurrences along
--     a map that may identify variables (renaming).
--   * `occurs` under renaming (`occurs-renameᵗ`, `occurs-renameᵗ-miss`,
--     hence `occurs-⇑ᵗ`, `occurs-zero-⇑ᵗ`) and under closing a variable
--     above X at ★ (`occurs-close-before`, Coercion's `closeTy`).
--   * Imports Types, Coercion and the standard library only.

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<_; s≤s)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Types
open import Coercion
  using (occurs; _∈ᵗ_; ∈-var; ∈-⇒ˡ; ∈-⇒ʳ; ∈-∀; closeEnv; closeTy)

------------------------------------------------------------------------
-- Boolean equality on ℕ
------------------------------------------------------------------------

≡ᵇ-refl : ∀ X → (X ≡ᵇ X) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc X) = ≡ᵇ-refl X

≡ᵇ-true : ∀ X Y → (X ≡ᵇ Y) ≡ true → X ≡ Y
≡ᵇ-true zero zero eq = refl
≡ᵇ-true zero (suc Y) ()
≡ᵇ-true (suc X) zero ()
≡ᵇ-true (suc X) (suc Y) eq = cong suc (≡ᵇ-true X Y eq)

------------------------------------------------------------------------
-- The check agrees with the relation
------------------------------------------------------------------------

∈→occurs : ∀ {X A} → X ∈ᵗ A → occurs X A ≡ true
∈→occurs {X} ∈-var = ≡ᵇ-refl X
∈→occurs (∈-⇒ˡ {B = B} i) = cong (_∨ occurs _ B) (∈→occurs i)
∈→occurs (∈-⇒ʳ eq i) = cong₂ _∨_ eq (∈→occurs i)
∈→occurs (∈-∀ i) = ∈→occurs i

occurs→∈ : ∀ {X} A → occurs X A ≡ true → X ∈ᵗ A
occurs→∈ {X} (` Y) eq with ≡ᵇ-true X Y eq
... | refl = ∈-var
occurs→∈ `ℕ ()
occurs→∈ `𝔹 ()
occurs→∈ ★ ()
occurs→∈ {X} (A ⇒ B) eq with occurs X A in eqA
occurs→∈ {X} (A ⇒ B) eq | true = ∈-⇒ˡ (occurs→∈ A eqA)
occurs→∈ {X} (A ⇒ B) eq | false = ∈-⇒ʳ eqA (occurs→∈ B eq)
occurs→∈ (`∀ A) eq = ∈-∀ (occurs→∈ A eq)

-- the right-of-arrow occurrence without the side condition
∈-⇒ʳ′ : ∀ {X A B} → X ∈ᵗ B → X ∈ᵗ A ⇒ B
∈-⇒ʳ′ {X} {A} i with occurs X A in eqA
∈-⇒ʳ′ {X} {A} i | true = ∈-⇒ˡ (occurs→∈ A eqA)
∈-⇒ʳ′ {X} {A} i | false = ∈-⇒ʳ eqA i

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

occurs-renameᵗ : ∀ (ρ : Renameᵗ) {X Z} A
  → (∀ Y → (Z ≡ᵇ ρ Y) ≡ (X ≡ᵇ Y))
  → occurs Z (renameᵗ ρ A) ≡ occurs X A
occurs-renameᵗ ρ (` Y) h = h Y
occurs-renameᵗ ρ `ℕ h = refl
occurs-renameᵗ ρ `𝔹 h = refl
occurs-renameᵗ ρ ★ h = refl
occurs-renameᵗ ρ (A ⇒ B) h =
  cong₂ _∨_ (occurs-renameᵗ ρ A h) (occurs-renameᵗ ρ B h)
occurs-renameᵗ ρ (`∀ A) h = occurs-renameᵗ (extᵗ ρ) A h′
  where
  h′ : ∀ Y → (suc _ ≡ᵇ extᵗ ρ Y) ≡ (suc _ ≡ᵇ Y)
  h′ zero = refl
  h′ (suc Y) = h Y

occurs-renameᵗ-miss : ∀ (ρ : Renameᵗ) {Z} A
  → (∀ Y → (Z ≡ᵇ ρ Y) ≡ false)
  → occurs Z (renameᵗ ρ A) ≡ false
occurs-renameᵗ-miss ρ (` Y) h = h Y
occurs-renameᵗ-miss ρ `ℕ h = refl
occurs-renameᵗ-miss ρ `𝔹 h = refl
occurs-renameᵗ-miss ρ ★ h = refl
occurs-renameᵗ-miss ρ (A ⇒ B) h =
  cong₂ _∨_ (occurs-renameᵗ-miss ρ A h) (occurs-renameᵗ-miss ρ B h)
occurs-renameᵗ-miss ρ (`∀ A) h = occurs-renameᵗ-miss (extᵗ ρ) A h′
  where
  h′ : ∀ Y → (suc _ ≡ᵇ extᵗ ρ Y) ≡ false
  h′ zero = refl
  h′ (suc Y) = h Y

occurs-⇑ᵗ : ∀ X A → occurs (suc X) (⇑ᵗ A) ≡ occurs X A
occurs-⇑ᵗ X A = occurs-renameᵗ suc A (λ Y → refl)

occurs-zero-⇑ᵗ : ∀ A → occurs zero (⇑ᵗ A) ≡ false
occurs-zero-⇑ᵗ A = occurs-renameᵗ-miss suc A (λ Y → refl)

------------------------------------------------------------------------
-- Closing a variable above X at ★
------------------------------------------------------------------------

occurs-closeEnv : ∀ {X k} Y → X < k → occurs X (closeEnv k Y) ≡ (X ≡ᵇ Y)
occurs-closeEnv {X} {suc k} zero lt = refl
occurs-closeEnv {zero} {suc k} (suc Y) lt = occurs-zero-⇑ᵗ (closeEnv k Y)
occurs-closeEnv {suc X} {suc k} (suc Y) (s≤s lt)
    rewrite occurs-⇑ᵗ X (closeEnv k Y) =
  occurs-closeEnv Y lt

occurs-close-before : ∀ {X k} A → X < k
  → occurs X (closeTy k A) ≡ occurs X A
occurs-close-before (` Y) lt = occurs-closeEnv Y lt
occurs-close-before `ℕ lt = refl
occurs-close-before `𝔹 lt = refl
occurs-close-before ★ lt = refl
occurs-close-before (A ⇒ B) lt =
  cong₂ _∨_ (occurs-close-before A lt) (occurs-close-before B lt)
occurs-close-before (`∀ A) lt = occurs-close-before A (s≤s lt)
