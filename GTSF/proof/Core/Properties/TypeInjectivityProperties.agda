module proof.Core.Properties.TypeInjectivityProperties where

-- File Charter:
--   * Generic constructor injectivity for GTSF types.
--   * Injectivity of type renaming when the variable renaming is injective.
--   * Independent of reduction, coercions, term imprecision, and stores.

open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (suc-injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl)

open import Types

＇-injective :
  ∀ {X Y : TyVar} →
  _≡_ {A = Ty} (＇ X) (＇ Y) →
  X ≡ Y
＇-injective refl = refl

‵-injective :
  ∀ {ι ι′ : Base} →
  _≡_ {A = Ty} (‵ ι) (‵ ι′) →
  ι ≡ ι′
‵-injective refl = refl

⇒-injective-left :
  ∀ {A B C D} →
  A ⇒ B ≡ C ⇒ D →
  A ≡ C
⇒-injective-left refl = refl

⇒-injective-right :
  ∀ {A B C D} →
  A ⇒ B ≡ C ⇒ D →
  B ≡ D
⇒-injective-right refl = refl

∀-injective :
  ∀ {A B : Ty} →
  `∀ A ≡ `∀ B →
  A ≡ B
∀-injective refl = refl

RenameInjective : Renameᵗ → Set
RenameInjective ρ = ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y

extᵗ-injective :
  ∀ {ρ} →
  RenameInjective ρ →
  RenameInjective (extᵗ ρ)
extᵗ-injective inj {zero} {zero} eq = refl
extᵗ-injective inj {zero} {suc Y} ()
extᵗ-injective inj {suc X} {zero} ()
extᵗ-injective inj {suc X} {suc Y} eq =
  cong suc (inj (suc-injective eq))

renameᵗ-injective :
  ∀ {ρ A B} →
  RenameInjective ρ →
  renameᵗ ρ A ≡ renameᵗ ρ B →
  A ≡ B
renameᵗ-injective {A = ＇ X} {B = ＇ Y} inj eq =
  cong ＇_ (inj (＇-injective eq))
renameᵗ-injective {A = ＇ X} {B = ‵ ι} inj ()
renameᵗ-injective {A = ＇ X} {B = ★} inj ()
renameᵗ-injective {A = ＇ X} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ＇ X} {B = `∀ B} inj ()
renameᵗ-injective {A = ‵ ι} {B = ＇ X} inj ()
renameᵗ-injective {A = ‵ ι} {B = ‵ ι′} inj eq =
  cong ‵_ (‵-injective eq)
renameᵗ-injective {A = ‵ ι} {B = ★} inj ()
renameᵗ-injective {A = ‵ ι} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ‵ ι} {B = `∀ B} inj ()
renameᵗ-injective {A = ★} {B = ＇ X} inj ()
renameᵗ-injective {A = ★} {B = ‵ ι} inj ()
renameᵗ-injective {A = ★} {B = ★} inj eq = refl
renameᵗ-injective {A = ★} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ★} {B = `∀ B} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ＇ X} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ‵ ι} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ★} inj ()
renameᵗ-injective {A = A ⇒ B} {B = C ⇒ D} inj eq =
  cong₂ _⇒_
    (renameᵗ-injective inj (⇒-injective-left eq))
    (renameᵗ-injective inj (⇒-injective-right eq))
renameᵗ-injective {A = A ⇒ B} {B = `∀ C} inj ()
renameᵗ-injective {A = `∀ A} {B = ＇ X} inj ()
renameᵗ-injective {A = `∀ A} {B = ‵ ι} inj ()
renameᵗ-injective {A = `∀ A} {B = ★} inj ()
renameᵗ-injective {A = `∀ A} {B = B ⇒ C} inj ()
renameᵗ-injective {A = `∀ A} {B = `∀ B} inj eq =
  cong `∀ (renameᵗ-injective (extᵗ-injective inj) (∀-injective eq))
