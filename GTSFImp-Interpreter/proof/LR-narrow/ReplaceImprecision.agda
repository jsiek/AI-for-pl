module proof.LR-narrow.ReplaceImprecision where

-- File Charter:
--   * Replacing a paired-mode variable by related representation types
--     on the two sides of a center imprecision derivation preserves the
--     derivation.
--   * Below `★` the variable cannot occur, so nothing changes there; at
--     the variable itself the representation imprecision is inserted.
--   * Supplies the target relation of the second reveal in the paired
--     universal case.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

open import Types
open import Conversion using (replaceTy)
import Imprecision as I
open import LR-narrow.Atoms using (shift-⊑)
open import proof.ImprecisionConsistency using (fin-suc-injective)
open import proof.LR-narrow.StarNoOccurrence using (renameᵗ-∉ᵗ)
open import proof.LR-narrow.RevealLifting using (shift-replace)

------------------------------------------------------------------------
-- Shape preservation
------------------------------------------------------------------------

replaceTy-nonvar : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ) {A : Ty Δ}
  → NonVar A → NonVar (replaceTy X R A)
replaceTy-nonvar X R nonvar-base = nonvar-base
replaceTy-nonvar X R nonvar-star = nonvar-star
replaceTy-nonvar X R nonvar-fun = nonvar-fun
replaceTy-nonvar X R nonvar-all = nonvar-all

-- A variable outside a renaming's image does not occur in the renamed
-- type.

rename-not-in-image : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (X : TyVar Δ′)
  → (∀ Y → ρ Y ≢ X)
  → (A : Ty Δ) → X ∉ᵗ renameᵗ ρ A
rename-not-in-image ρ X h (＇ Y) = ∉-var (≢→≢ᶠ (λ eq → h Y (sym eq)))
rename-not-in-image ρ X h (‵ ι) = ∉-base
rename-not-in-image ρ X h ★ = ∉-star
rename-not-in-image ρ X h (A ⇒ B) =
  ∉-fun (rename-not-in-image ρ X h A) (rename-not-in-image ρ X h B)
rename-not-in-image ρ X h (`∀ A) =
  ∉-all (rename-not-in-image (extᵗ ρ) (Fin.suc X) ext-h A)
  where
  ext-h : ∀ Y → extᵗ ρ Y ≢ Fin.suc X
  ext-h Fin.zero ()
  ext-h (Fin.suc Y) eq = h Y (suc-injective′ eq)
    where
    suc-injective′ : ∀ {n} {V W : TyVar n}
      → Fin.suc V ≡ Fin.suc W → V ≡ W
    suc-injective′ refl = refl

-- A shifted representation does not contain the zero variable.

shift-no-zero : ∀ {Δ} (R : Ty Δ) → Fin.zero ∉ᵗ ⇑ᵗ R
shift-no-zero R =
  rename-not-in-image Fin.suc Fin.zero (λ Y ()) R

-- Replacement preserves and reflects occurrences of another variable,
-- when the replacing type does not contain it.

suc-injective″ : ∀ {n} {V W : TyVar n}
  → Fin.suc V ≡ Fin.suc W → V ≡ W
suc-injective″ refl = refl

shift-preserves-∉ : ∀ {Δ} (R : Ty Δ) {X : TyVar Δ}
  → X ∉ᵗ R → Fin.suc X ∉ᵗ ⇑ᵗ R
shift-preserves-∉ R = renameᵗ-∉ᵗ Fin.suc fin-suc-injective

mutual
  replaceTy-occurs : ∀ {Δ} (Z : TyVar Δ) (R : Ty Δ) {X : TyVar Δ}
      {A : Ty Δ}
    → X ≢ Z → X ∉ᵗ R
    → X ∈ᵗ A → X ∈ᵗ replaceTy Z R A
  replaceTy-occurs Z R {X = X} X≢Z X∉R (var-∈ {X = .X})
      with Z ≟ X
  replaceTy-occurs Z R X≢Z X∉R var-∈ | yes refl =
    ⊥-elim (X≢Z refl)
  replaceTy-occurs Z R X≢Z X∉R var-∈ | no _ = var-∈
  replaceTy-occurs Z R X≢Z X∉R (∈-fun-left X∈A) =
    ∈-fun-left (replaceTy-occurs Z R X≢Z X∉R X∈A)
  replaceTy-occurs Z R X≢Z X∉R (∈-fun-right X∉A X∈B) =
    ∈-fun-right (replaceTy-not-occurs Z R X≢Z X∉R X∉A)
      (replaceTy-occurs Z R X≢Z X∉R X∈B)
  replaceTy-occurs Z R X≢Z X∉R (∈-all X∈A) =
    ∈-all (replaceTy-occurs (Fin.suc Z) (⇑ᵗ R)
      (λ eq → X≢Z (suc-injective″ eq))
      (shift-preserves-∉ R X∉R) X∈A)

  replaceTy-not-occurs : ∀ {Δ} (Z : TyVar Δ) (R : Ty Δ) {X : TyVar Δ}
      {A : Ty Δ}
    → X ≢ Z → X ∉ᵗ R
    → X ∉ᵗ A → X ∉ᵗ replaceTy Z R A
  replaceTy-not-occurs Z R {X = X} X≢Z X∉R (∉-var {Y = Y} X≢Y)
      with Z ≟ Y
  replaceTy-not-occurs Z R X≢Z X∉R (∉-var X≢Y) | yes refl = X∉R
  replaceTy-not-occurs Z R X≢Z X∉R (∉-var X≢Y) | no _ = ∉-var X≢Y
  replaceTy-not-occurs Z R X≢Z X∉R ∉-base = ∉-base
  replaceTy-not-occurs Z R X≢Z X∉R ∉-star = ∉-star
  replaceTy-not-occurs Z R X≢Z X∉R (∉-fun X∉A X∉B) =
    ∉-fun (replaceTy-not-occurs Z R X≢Z X∉R X∉A)
      (replaceTy-not-occurs Z R X≢Z X∉R X∉B)
  replaceTy-not-occurs Z R X≢Z X∉R (∉-all X∉A) =
    ∉-all (replaceTy-not-occurs (Fin.suc Z) (⇑ᵗ R)
      (λ eq → X≢Z (suc-injective″ eq))
      (shift-preserves-∉ R X∉R) X∉A)


------------------------------------------------------------------------
-- Replacement preserves imprecision at a paired-mode variable
------------------------------------------------------------------------

-- Below `★` the paired variable cannot occur, so those sub-derivations
-- are untouched.

open import proof.LR-narrow.StarNoOccurrence using
  (star-no-occurrence; replaceTy-absent)

replace-star : ∀ {Δ} {μ : I.ImpEnv Δ} (Z : TyVar Δ) (R : Ty Δ)
    {A : Ty Δ}
  → μ Z ≡ I.X⊑X
  → μ I.⊢ A ⊑ ★
  → μ I.⊢ replaceTy Z R A ⊑ ★
replace-star Z R {A = A} mode p =
  subst≡ (λ T → _ I.⊢ T ⊑ ★)
    (sym (replaceTy-absent Z R (star-no-occurrence Z mode p))) p

replace-⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} (Z : TyVar Δ)
    {Rᴾ Rᴵ : Ty Δ} {A B : Ty Δ}
  → μ Z ≡ I.X⊑X
  → μ I.⊢ Rᴾ ⊑ Rᴵ
  → μ I.⊢ A ⊑ B
  → μ I.⊢ replaceTy Z Rᴾ A ⊑ replaceTy Z Rᴵ B
replace-⊑ Z mode r I.★⊑★ = I.★⊑★
replace-⊑ Z mode r I.ι⊑ι = I.ι⊑ι
replace-⊑ Z mode r (I.X⊑X {X = X}) with Z ≟ X
replace-⊑ Z mode r I.X⊑X | yes refl = r
replace-⊑ Z mode r I.X⊑X | no _ = I.X⊑X
replace-⊑ Z mode r (I.⇒⊑⇒ p q) =
  I.⇒⊑⇒ (replace-⊑ Z mode r p) (replace-⊑ Z mode r q)
replace-⊑ Z {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} mode r (I.∀⊑∀ p) =
  I.∀⊑∀ (replace-⊑ (Fin.suc Z) mode (shift-⊑ I.X⊑X r) p)
replace-⊑ Z {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} mode r (I.⇒⊑★ p q) =
  I.⇒⊑★ (replace-star Z Rᴾ mode p) (replace-star Z Rᴾ mode q)
replace-⊑ Z mode r I.ι⊑★ = I.ι⊑★
replace-⊑ Z mode r (I.X⊑★ {X = X} eq) with Z ≟ X
replace-⊑ Z mode r (I.X⊑★ eq) | yes refl
    with trans (sym mode) eq
replace-⊑ Z mode r (I.X⊑★ eq) | yes refl | ()
replace-⊑ Z mode r (I.X⊑★ eq) | no _ = I.X⊑★ eq
replace-⊑ Z {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} mode r
    (I.∀⊑ {A = A} {B = B} nonvar occurs p) =
  I.∀⊑ (replaceTy-nonvar (Fin.suc Z) (⇑ᵗ Rᴾ) nonvar)
    (replaceTy-occurs (Fin.suc Z) (⇑ᵗ Rᴾ) (λ ())
      (shift-no-zero Rᴾ) occurs)
    (subst≡ (λ T → I.instᵐ _ I.⊢ replaceTy (Fin.suc Z) (⇑ᵗ Rᴾ) A ⊑ T)
      (sym (shift-replace Z Rᴵ B))
      (replace-⊑ (Fin.suc Z) mode (shift-⊑ I.X⊑★ r) p))
replace-⊑ Z mode r I.∀★⊑★ = I.∀★⊑★
replace-⊑ {μ = μ} Z {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} mode r
    (I.∀⊑★ {A = A} nonstar p) =
  subst≡ (λ T → μ I.⊢ T ⊑ ★)
    (sym (replaceTy-absent Z Rᴾ
      (∉-all (star-no-occurrence (Fin.suc Z) mode p))))
    (I.∀⊑★ nonstar p)
replace-⊑ Z mode r I.bot-elim = I.bot-elim
replace-⊑ Z mode r I.bot⊑★ = I.bot⊑★

------------------------------------------------------------------------
-- Replacement as a simultaneous substitution
------------------------------------------------------------------------

replaceSubᵗ : ∀ {Δ} → TyVar Δ → Ty Δ → Δ ⇒ˢ Δ
replaceSubᵗ X R Y with X ≟ Y
replaceSubᵗ X R Y | yes _ = R
replaceSubᵗ X R Y | no _ = ＇ Y

replaceSubᵗ-ext : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ) (Y : TyVar (suc Δ))
  → extsᵗ (replaceSubᵗ X R) Y ≡ replaceSubᵗ (Fin.suc X) (⇑ᵗ R) Y
replaceSubᵗ-ext X R Fin.zero = refl
replaceSubᵗ-ext X R (Fin.suc Y) with X ≟ Y
replaceSubᵗ-ext X R (Fin.suc Y) | yes _ = refl
replaceSubᵗ-ext X R (Fin.suc Y) | no _ = refl

replaceTy-as-subst : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ) (B : Ty Δ)
  → replaceTy X R B ≡ substᵗ (replaceSubᵗ X R) B
replaceTy-as-subst X R (＇ Y) with X ≟ Y
replaceTy-as-subst X R (＇ Y) | yes refl = refl
replaceTy-as-subst X R (＇ Y) | no _ = refl
replaceTy-as-subst X R (‵ ι) = refl
replaceTy-as-subst X R ★ = refl
replaceTy-as-subst X R (A ⇒ B) =
  cong₂ _⇒_ (replaceTy-as-subst X R A) (replaceTy-as-subst X R B)
replaceTy-as-subst X R (`∀ A) = cong `∀
  (trans (replaceTy-as-subst (Fin.suc X) (⇑ᵗ R) A)
    (substᵗ-cong A (λ Y → sym (replaceSubᵗ-ext X R Y))))

------------------------------------------------------------------------
-- Replacing the zero variable by a shifted type opens the body
------------------------------------------------------------------------

replace-zero-open : ∀ {Δ} (S : Ty Δ) (B : Ty (suc Δ))
  → replaceTy Fin.zero (⇑ᵗ S) B ≡ ⇑ᵗ (B [ S ]ᵗ)
replace-zero-open S B =
  trans (replaceTy-as-subst Fin.zero (⇑ᵗ S) B)
    (trans (substᵗ-cong B pointwise)
      (sym (renameᵗ-subst Fin.suc (singleSubᵗ S) B)))
  where
  pointwise : ∀ Y → replaceSubᵗ Fin.zero (⇑ᵗ S) Y
      ≡ renameᵗ Fin.suc (singleSubᵗ S Y)
  pointwise Fin.zero = refl
  pointwise (Fin.suc Y) = refl

------------------------------------------------------------------------
-- Instantiating a shifted body at the zero variable is the identity
------------------------------------------------------------------------

open-shifted-body : ∀ {Δ} (B : Ty (suc Δ))
  → renameᵗ (extᵗ Fin.suc) B [ ＇ Fin.zero ]ᵗ ≡ B
open-shifted-body B =
  trans (substᵗ-rename (singleSubᵗ (＇ Fin.zero)) (extᵗ Fin.suc) B)
    (trans (substᵗ-cong B pointwise) (substᵗ-id B))
  where
  pointwise : ∀ X → singleSubᵗ (＇ Fin.zero) (extᵗ Fin.suc X) ≡ ＇ X
  pointwise Fin.zero = refl
  pointwise (Fin.suc X) = refl
