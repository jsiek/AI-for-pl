module proof.ImprecisionConsistency where

-- File Charter:
--   * Proves that type consistency is equivalent to existence of a common
--     lower bound in the type-imprecision relation.
--   * Relates consistency environments to the two imprecision environments
--     used by a common lower bound.
--   * Depends only on Types, Consistency, and Imprecision.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Nat as Nat
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; cong₂; refl; subst; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types
open import Consistency
open import Imprecision using (_⊢_⊑_)
import Consistency as C
import Imprecision as I

private
  variable
    Δ : TyCtx

------------------------------------------------------------------------
-- Environment alignment
------------------------------------------------------------------------

data VarLower : Var∼ → I.VarImp → I.VarImp → Set where
  var-refl : VarLower X∼X I.X⊑X I.X⊑X
  cross-refl : VarLower ★∼X∼★ I.X⊑X I.X⊑X
  var-to-star : VarLower X∼★ I.X⊑X I.X⊑★
  var-from-star : VarLower ★∼X I.X⊑★ I.X⊑X
  both-to-star : VarLower X∼X I.X⊑★ I.X⊑★

LowerEnv : ∀ {Δ}
  → Env∼ Δ
  → I.ImpEnv Δ
  → I.ImpEnv Δ
  → Set
LowerEnv μ φ ψ = ∀ X → VarLower (μ X) (φ X) (ψ X)

extend-lower-env : ∀ {μ : Env∼ Δ} {φ ψ}
  → LowerEnv μ φ ψ
  → LowerEnv (extᵐ μ) (I.extᵐ φ) (I.extᵐ ψ)
extend-lower-env h zero = var-refl
extend-lower-env h (suc X) = h X

instantiate-right-lower-env : ∀ {μ : Env∼ Δ} {φ ψ}
  → LowerEnv μ φ ψ
  → LowerEnv (instᵐ μ) (I.extᵐ φ) (I.instᵐ ψ)
instantiate-right-lower-env h zero = var-to-star
instantiate-right-lower-env h (suc X) = h X

instantiate-left-lower-env : ∀ {μ : Env∼ Δ} {φ ψ}
  → LowerEnv μ φ ψ
  → LowerEnv (genᵐ μ) (I.instᵐ φ) (I.extᵐ ψ)
instantiate-left-lower-env h zero = var-from-star
instantiate-left-lower-env h (suc X) = h X

instantiate-both-lower-env : ∀ {μ : Env∼ Δ} {φ ψ}
  → LowerEnv μ φ ψ
  → LowerEnv (extᵐ μ) (I.instᵐ φ) (I.instᵐ ψ)
instantiate-both-lower-env h zero = both-to-star
instantiate-both-lower-env h (suc X) = h X

identity-lower-env : ∀ {Δ}
  → LowerEnv (idᶜ {Δ}) (I.idᵐ {Δ}) (I.idᵐ {Δ})
identity-lower-env X = cross-refl

flip-var-lower : ∀ {r φ ψ}
  → VarLower r φ ψ
  → VarLower (flipVar∼ r) ψ φ
flip-var-lower var-refl = var-refl
flip-var-lower cross-refl = cross-refl
flip-var-lower var-to-star = var-from-star
flip-var-lower var-from-star = var-to-star
flip-var-lower both-to-star = both-to-star

flip-lower-env : ∀ {μ : Env∼ Δ} {φ ψ}
  → LowerEnv μ φ ψ
  → LowerEnv (flipᵐ μ) ψ φ
flip-lower-env h X = flip-var-lower (h X)

right-star-from-var-lower : ∀ {r l u}
  → VarLower r l u
  → r ≡ X∼★
  → u ≡ I.X⊑★
right-star-from-var-lower var-refl ()
right-star-from-var-lower cross-refl ()
right-star-from-var-lower var-to-star refl = refl
right-star-from-var-lower var-from-star ()
right-star-from-var-lower both-to-star ()

left-star-from-var-lower : ∀ {r l u}
  → VarLower r l u
  → r ≡ ★∼X
  → l ≡ I.X⊑★
left-star-from-var-lower var-refl ()
left-star-from-var-lower cross-refl ()
left-star-from-var-lower var-to-star ()
left-star-from-var-lower var-from-star refl = refl
left-star-from-var-lower both-to-star ()

------------------------------------------------------------------------
-- Basic imprecision properties
------------------------------------------------------------------------

refl⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} (A : Ty Δ)
  → I._⊢_⊑_ μ A A
refl⊑ (＇ X) = I.X⊑X
refl⊑ (‵ ι) = I.ι⊑ι
refl⊑ ★ = I.★⊑★
refl⊑ (A ⇒ B) = I.⇒⊑⇒ (refl⊑ A) (refl⊑ B)
refl⊑ (`∀ A) = I.∀⊑∀ (refl⊑ A)

fin-suc-injective : ∀ {n} {X Y : TyVar n}
  → suc X ≡ suc Y
  → X ≡ Y
fin-suc-injective refl = refl

ext-injective : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
  → (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → ∀ {X Y} → extᵗ ρ X ≡ extᵗ ρ Y → X ≡ Y
ext-injective injective {zero} {zero} eq = refl
ext-injective injective {zero} {suc Y} ()
ext-injective injective {suc X} {zero} ()
ext-injective injective {suc X} {suc Y} eq =
  cong suc (injective (fin-suc-injective eq))

toRenameᵗ-injective : ∀ {Δ Δ′}
  → (η : Δ ↪ᵗ Δ′)
  → ∀ {X Y} → toRenameᵗ η X ≡ toRenameᵗ η Y → X ≡ Y
toRenameᵗ-injective empty {()}
toRenameᵗ-injective (keep η) {zero} {zero} eq = refl
toRenameᵗ-injective (keep η) {zero} {suc Y} ()
toRenameᵗ-injective (keep η) {suc X} {zero} ()
toRenameᵗ-injective (keep η) {suc X} {suc Y} eq =
  cong suc (toRenameᵗ-injective η (fin-suc-injective eq))
toRenameᵗ-injective (skip η) eq =
  toRenameᵗ-injective η (fin-suc-injective eq)

ty-var-injective : ∀ {Δ : TyCtx} {X Y : TyVar Δ}
  → _≡_ {A = Ty Δ} (＇ X) (＇ Y)
  → X ≡ Y
ty-var-injective {X = X} {.X} refl = refl

ty-fun-left-injective : ∀ {Δ} {A A′ B B′ : Ty Δ}
  → A ⇒ B ≡ A′ ⇒ B′
  → A ≡ A′
ty-fun-left-injective refl = refl

ty-fun-right-injective : ∀ {Δ} {A A′ B B′ : Ty Δ}
  → A ⇒ B ≡ A′ ⇒ B′
  → B ≡ B′
ty-fun-right-injective refl = refl

ty-all-injective : ∀ {Δ} {A B : Ty (Nat.suc Δ)}
  → `∀ A ≡ `∀ B
  → A ≡ B
ty-all-injective refl = refl

renameᵗ-injective : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
  → (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → ∀ {A B : Ty Δ}
  → renameᵗ ρ A ≡ renameᵗ ρ B
  → A ≡ B
renameᵗ-injective {ρ = ρ} injective {A = ＇ X} {B = ＇ Y} eq =
  cong ＇_ (injective (ty-var-injective {X = ρ X} {Y = ρ Y} eq))
renameᵗ-injective injective {A = ＇ X} {B = ‵ ι} ()
renameᵗ-injective injective {A = ＇ X} {B = ★} ()
renameᵗ-injective injective {A = ＇ X} {B = B ⇒ B′} ()
renameᵗ-injective injective {A = ＇ X} {B = `∀ B} ()
renameᵗ-injective injective {A = ‵ ι} {B = ＇ X} ()
renameᵗ-injective injective {A = ‵ ι} {B = ‵ ι′} refl = refl
renameᵗ-injective injective {A = ‵ ι} {B = ★} ()
renameᵗ-injective injective {A = ‵ ι} {B = B ⇒ B′} ()
renameᵗ-injective injective {A = ‵ ι} {B = `∀ B} ()
renameᵗ-injective injective {A = ★} {B = ＇ X} ()
renameᵗ-injective injective {A = ★} {B = ‵ ι} ()
renameᵗ-injective injective {A = ★} {B = ★} eq = refl
renameᵗ-injective injective {A = ★} {B = B ⇒ B′} ()
renameᵗ-injective injective {A = ★} {B = `∀ B} ()
renameᵗ-injective injective {A = A ⇒ A′} {B = ＇ X} ()
renameᵗ-injective injective {A = A ⇒ A′} {B = ‵ ι} ()
renameᵗ-injective injective {A = A ⇒ A′} {B = ★} ()
renameᵗ-injective injective {A = A ⇒ A′} {B = B ⇒ B′} eq =
  cong₂ _⇒_ (renameᵗ-injective injective (ty-fun-left-injective eq))
    (renameᵗ-injective injective (ty-fun-right-injective eq))
renameᵗ-injective injective {A = A ⇒ A′} {B = `∀ B} ()
renameᵗ-injective injective {A = `∀ A} {B = ＇ X} ()
renameᵗ-injective injective {A = `∀ A} {B = ‵ ι} ()
renameᵗ-injective injective {A = `∀ A} {B = ★} ()
renameᵗ-injective injective {A = `∀ A} {B = B ⇒ B′} ()
renameᵗ-injective injective {A = `∀ A} {B = `∀ B} eq =
  cong `∀
    (renameᵗ-injective (ext-injective injective) (ty-all-injective eq))

rename-not-occurs : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → X ∉ᵗ A
  → ρ X ∉ᵗ renameᵗ ρ A
rename-not-occurs ρ injective (∉-var X≢Y) =
  ∉-var (≢→≢ᶠ (λ eq → ≢ᶠ→≢ X≢Y (injective eq)))
rename-not-occurs ρ injective ∉-base = ∉-base
rename-not-occurs ρ injective ∉-star = ∉-star
rename-not-occurs ρ injective (∉-fun X∉A X∉B) =
  ∉-fun (rename-not-occurs ρ injective X∉A)
    (rename-not-occurs ρ injective X∉B)
rename-not-occurs ρ injective (∉-all X∉A) =
  ∉-all (rename-not-occurs (extᵗ ρ) (ext-injective injective) X∉A)

rename-occurs : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → X ∈ᵗ A
  → ρ X ∈ᵗ renameᵗ ρ A
rename-occurs ρ injective var-∈ = var-∈
rename-occurs ρ injective (∈-fun-left X∈A) =
  ∈-fun-left (rename-occurs ρ injective X∈A)
rename-occurs ρ injective (∈-fun-right X∉A X∈B) =
  ∈-fun-right (rename-not-occurs ρ injective X∉A)
    (rename-occurs ρ injective X∈B)
rename-occurs ρ injective (∈-all X∈A) =
  ∈-all (rename-occurs (extᵗ ρ) (ext-injective injective) X∈A)

shift-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∈ᵗ A
  → suc X ∈ᵗ ⇑ᵗ A
shift-occurs = rename-occurs suc fin-suc-injective

data RenamePreimage {Δ Δ′ : TyCtx} (ρ : Δ ⇒ʳ Δ′)
    (Y : TyVar Δ′) (A : Ty Δ) : Set where
  found : (X : TyVar Δ)
    → ρ X ≡ Y
    → X ∈ᵗ A
    → RenamePreimage ρ Y A

rename-preimage : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {Y : TyVar Δ′}
    {A : Ty Δ}
  → Y ∈ᵗ renameᵗ ρ A
  → RenamePreimage ρ Y A
rename-preimage {A = ＇ X} var-∈ = found X refl var-∈
rename-preimage {A = ‵ ι} ()
rename-preimage {A = ★} ()
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    with rename-preimage Y∈A
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    | found X eq X∈A = found X eq (∈-fun-left X∈A)
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    with rename-preimage Y∈B
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | found X eq X∈B with occurs? X A
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | found X eq X∈B | present X∈A =
  found X eq (∈-fun-left X∈A)
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | found X eq X∈B | absent X∉A =
  found X eq (∈-fun-right X∉A X∈B)
rename-preimage {A = `∀ A} (∈-all Y∈A)
    with rename-preimage Y∈A
rename-preimage {A = `∀ A} (∈-all Y∈A)
    | found zero () X∈A
rename-preimage {A = `∀ A} (∈-all Y∈A)
    | found (suc X) eq X∈A =
  found X (fin-suc-injective eq) (∈-all X∈A)

unrename-occurs : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → ρ X ∈ᵗ renameᵗ ρ A
  → X ∈ᵗ A
unrename-occurs {X = X} ρ injective X∈ with rename-preimage X∈
unrename-occurs {X = X} ρ injective X∈ | found Y eq Y∈
    with injective eq
unrename-occurs {X = X} ρ injective X∈ | found .X eq Y∈ | refl = Y∈

unshift-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → suc X ∈ᵗ ⇑ᵗ A
  → X ∈ᵗ A
unshift-occurs = unrename-occurs suc fin-suc-injective

target-occurs-source : ∀ {Δ} {μ : I.ImpEnv Δ}
    {X : TyVar Δ} {A B : Ty Δ}
  → I._⊢_⊑_ μ A B
  → X ∈ᵗ B
  → X ∈ᵗ A
target-occurs-source I.★⊑★ ()
target-occurs-source I.ι⊑ι ()
target-occurs-source I.X⊑X X∈ = X∈
target-occurs-source (I.⇒⊑⇒ p q) (∈-fun-left X∈A) =
  ∈-fun-left (target-occurs-source p X∈A)
target-occurs-source {X = X} {A = A ⇒ B}
    (I.⇒⊑⇒ p q) (∈-fun-right X∉A X∈B)
    with occurs? X A
target-occurs-source {X = X} {A = A ⇒ B}
    (I.⇒⊑⇒ p q) (∈-fun-right X∉A X∈B)
    | present X∈A′ = ∈-fun-left X∈A′
target-occurs-source {X = X} {A = A ⇒ B}
    (I.⇒⊑⇒ p q) (∈-fun-right X∉A X∈B)
    | absent X∉A′ =
  ∈-fun-right X∉A′ (target-occurs-source q X∈B)
target-occurs-source (I.∀⊑∀ p) (∈-all X∈A) =
  ∈-all (target-occurs-source p X∈A)
target-occurs-source (I.⇒⊑★ p q) ()
target-occurs-source I.ι⊑★ ()
target-occurs-source (I.X⊑★ eq) ()
target-occurs-source (I.∀⊑ Anv z∈A p) X∈B =
  ∈-all (target-occurs-source p (shift-occurs X∈B))
target-occurs-source I.∀★⊑★ ()
target-occurs-source (I.∀⊑★ Ans p) ()
target-occurs-source I.bot-elim (∈-all ())
target-occurs-source I.bot⊑★ ()

source-nonvar-from-target : ∀ {Δ} {μ : I.ImpEnv (Nat.suc Δ)}
    {A B : Ty (Nat.suc Δ)}
  → I._⊢_⊑_ μ A B
  → NonVar B
  → zero ∈ᵗ B
  → NonVar A
source-nonvar-from-target I.★⊑★ Anv ()
source-nonvar-from-target I.ι⊑ι Anv ()
source-nonvar-from-target I.X⊑X () z∈B
source-nonvar-from-target (I.⇒⊑⇒ p q) Anv z∈B = nonvar-fun
source-nonvar-from-target (I.∀⊑∀ p) Anv z∈B = nonvar-all
source-nonvar-from-target (I.⇒⊑★ p q) Anv ()
source-nonvar-from-target I.ι⊑★ Anv ()
source-nonvar-from-target (I.X⊑★ eq) Anv ()
source-nonvar-from-target (I.∀⊑ Anv z∈A p) Bnv z∈B =
  nonvar-all
source-nonvar-from-target I.∀★⊑★ Anv ()
source-nonvar-from-target (I.∀⊑★ Ans p) Anv ()
source-nonvar-from-target I.bot-elim Anv (∈-all ())
source-nonvar-from-target I.bot⊑★ Anv ()

arrow-right-to-star : ∀ {Δ} {μ : Env∼ Δ} {φ ψ} {D : Ty Δ}
  → LowerEnv μ φ ψ
  → I._⊢_⊑_ ψ D (★ ⇒ ★)
  → I._⊢_⊑_ ψ D ★
arrow-right-to-star h (I.⇒⊑⇒ p q) = I.⇒⊑★ p q
arrow-right-to-star h (I.∀⊑ Anv z∈A p) =
  I.∀⊑ Anv z∈A
    (arrow-right-to-star (instantiate-right-lower-env h) p)

base-right-to-star : ∀ {Δ} {μ : Env∼ Δ} {φ ψ} {D : Ty Δ}
    {ι}
  → LowerEnv μ φ ψ
  → I._⊢_⊑_ ψ D (‵ ι)
  → I._⊢_⊑_ ψ D ★
base-right-to-star h I.ι⊑ι = I.ι⊑★
base-right-to-star h (I.∀⊑ Anv z∈A p) =
  I.∀⊑ Anv z∈A
    (base-right-to-star (instantiate-right-lower-env h) p)

var-right-to-star : ∀ {Δ} {μ : Env∼ Δ} {φ ψ} {D : Ty Δ}
    {X}
  → LowerEnv μ φ ψ
  → μ X ≡ X∼★
  → I._⊢_⊑_ ψ D (＇ X)
  → I._⊢_⊑_ ψ D ★
var-right-to-star {X = X} h eq I.X⊑X =
  I.X⊑★ (right-star-from-var-lower (h X) eq)
var-right-to-star h eq (I.∀⊑ Anv z∈A p) =
  I.∀⊑ Anv z∈A
    (var-right-to-star (instantiate-right-lower-env h) eq p)

arrow-left-to-star : ∀ {Δ} {μ : Env∼ Δ} {φ ψ} {D : Ty Δ}
  → LowerEnv μ φ ψ
  → I._⊢_⊑_ φ D (★ ⇒ ★)
  → I._⊢_⊑_ φ D ★
arrow-left-to-star h (I.⇒⊑⇒ p q) = I.⇒⊑★ p q
arrow-left-to-star h (I.∀⊑ Anv z∈A p) =
  I.∀⊑ Anv z∈A
    (arrow-left-to-star (instantiate-left-lower-env h) p)

base-left-to-star : ∀ {Δ} {μ : Env∼ Δ} {φ ψ} {D : Ty Δ}
    {ι}
  → LowerEnv μ φ ψ
  → I._⊢_⊑_ φ D (‵ ι)
  → I._⊢_⊑_ φ D ★
base-left-to-star h I.ι⊑ι = I.ι⊑★
base-left-to-star h (I.∀⊑ Anv z∈A p) =
  I.∀⊑ Anv z∈A
    (base-left-to-star (instantiate-left-lower-env h) p)

var-left-to-star : ∀ {Δ} {μ : Env∼ Δ} {φ ψ} {D : Ty Δ}
    {X}
  → LowerEnv μ φ ψ
  → μ X ≡ ★∼X
  → I._⊢_⊑_ φ D (＇ X)
  → I._⊢_⊑_ φ D ★
var-left-to-star {X = X} h eq I.X⊑X =
  I.X⊑★ (left-star-from-var-lower (h X) eq)
var-left-to-star h eq (I.∀⊑ Anv z∈A p) =
  I.∀⊑ Anv z∈A
    (var-left-to-star (instantiate-left-lower-env h) eq p)

nonstar-from-≢★ : ∀ {Δ} {A : Ty Δ}
  → A ≢ ★
  → NonStar A
nonstar-from-≢★ {A = ＇ X} A≢★ = nonstar-X
nonstar-from-≢★ {A = ‵ ι} A≢★ = nonstar-ι
nonstar-from-≢★ {A = ★} A≢★ = ⊥-elim (A≢★ refl)
nonstar-from-≢★ {A = A ⇒ B} A≢★ = nonstar-⇒
nonstar-from-≢★ {A = `∀ A} A≢★ = nonstar-∀

universal-right-to-star : ∀ {Δ} {μ : I.ImpEnv Δ} {D}
  → I._⊢_⊑_ μ D (`∀ ★)
  → I._⊢_⊑_ μ D ★
universal-right-to-star {D = `∀ A} (I.∀⊑∀ p) with A ≟Ty ★
universal-right-to-star {D = `∀ A} (I.∀⊑∀ p) | yes refl =
  I.∀★⊑★
universal-right-to-star {D = `∀ A} (I.∀⊑∀ p) | no A≢★ =
  I.∀⊑★ (nonstar-from-≢★ A≢★) p
universal-right-to-star (I.∀⊑ Anv z∈A p) =
  I.∀⊑ Anv z∈A (universal-right-to-star p)
universal-right-to-star I.bot-elim = I.bot⊑★

------------------------------------------------------------------------
-- Consistency implies a common lower bound
------------------------------------------------------------------------

data CrossFree∼★ : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    → μ ⊢ G ∼★ → Set where
  cf-⇒∼★ : ∀ {Δ} {μ : Env∼ Δ}
    → CrossFree∼★ (⇒∼★ {μ = μ})
  cf-ι∼★ : ∀ {Δ} {μ : Env∼ Δ} {ι}
    → CrossFree∼★ (ι∼★ {μ = μ} {ι = ι})
  cf-X∼★ᵍ : ∀ {Δ} {μ : Env∼ Δ} {X} {eq : μ X ≡ X∼★}
    → CrossFree∼★ (X∼★ᵍ {μ = μ} {X = X} eq)
  cf-∀∼★ : ∀ {Δ} {μ : Env∼ Δ}
    → CrossFree∼★ (∀∼★ {μ = μ})

data CrossFree★∼ : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    → μ ⊢★∼ G → Set where
  cf-★∼⇒ : ∀ {Δ} {μ : Env∼ Δ}
    → CrossFree★∼ (★∼⇒ {μ = μ})
  cf-★∼ι : ∀ {Δ} {μ : Env∼ Δ} {ι}
    → CrossFree★∼ (★∼ι {μ = μ} {ι = ι})
  cf-★∼Xᵍ : ∀ {Δ} {μ : Env∼ Δ} {X} {eq : μ X ≡ ★∼X}
    → CrossFree★∼ (★∼Xᵍ {μ = μ} {X = X} eq)
  cf-★∼∀ : ∀ {Δ} {μ : Env∼ Δ}
    → CrossFree★∼ (★∼∀ {μ = μ})

data CrossFree : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  cf-id : ∀ {Δ} {μ : Env∼ Δ} {A} {a : Atom A}
    → CrossFree (id {μ = μ} a)
  cf-↦ : ∀ {Δ} {μ : Env∼ Δ} {A A′ B B′}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → CrossFree c
    → CrossFree d
    → CrossFree (c ↦ d)
  cf-∀ᶜ : ∀ {Δ} {μ : Env∼ Δ} {A B}
      {c : extᵐ μ ⊢ A ∼ B}
    → CrossFree c
    → CrossFree (∀ᶜ c)
  cf-! : ∀ {Δ} {μ : Env∼ Δ} {A G}
      {g : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → CrossFree∼★ G∼★
    → CrossFree c
    → CrossFree (_! ⦃ g ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)
  cf-？ : ∀ {Δ} {μ : Env∼ Δ} {G B}
      {g : Ground G} {★∼G : μ ⊢★∼ G}
      {c : μ ⊢ G ∼ B} {Bns : NonStar B}
    → CrossFree★∼ ★∼G
    → CrossFree c
    → CrossFree (？_ ⦃ g ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄)
  cf-inst : ∀ {Δ} {μ : Env∼ Δ} {A B}
      {Anv : NonVar A} {z∈A : zero ∈ᵗ A}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B} {B≢★ : B ≢ ★}
    → CrossFree c
    → CrossFree (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
  cf-gen : ∀ {Δ} {μ : Env∼ Δ} {A B}
      {Bnv : NonVar B} {z∈B : zero ∈ᵗ B}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B} {A≢★ : A ≢ ★}
    → CrossFree c
    → CrossFree (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
  cf-bot-elim : ∀ {Δ} {μ : Env∼ Δ}
    → CrossFree (bot-elim {μ = μ})
  cf-bot-intro : ∀ {Δ} {μ : Env∼ Δ}
    → CrossFree (bot-intro {μ = μ})

consistent-common-lowerᵐ : ∀ {Δ} {μ : Env∼ Δ} {φ ψ}
    {A B : Ty Δ}
  → LowerEnv μ φ ψ
  → (c : μ ⊢ A ∼ B)
  → CrossFree c
  → ∃[ D ] I._⊢_⊑_ φ D A × I._⊢_⊑_ ψ D B
consistent-common-lowerᵐ h (id ★) cf-id = ★ , I.★⊑★ , I.★⊑★
consistent-common-lowerᵐ h (id (‵ ι)) cf-id =
  ‵ ι , I.ι⊑ι , I.ι⊑ι
consistent-common-lowerᵐ h (id (＇ X)) cf-id = ＇ X , I.X⊑X , I.X⊑X
consistent-common-lowerᵐ h (c ↦ d) (cf-↦ c-free d-free)
    with consistent-common-lowerᵐ (flip-lower-env h) c c-free
       | consistent-common-lowerᵐ h d d-free
consistent-common-lowerᵐ h (c ↦ d) (cf-↦ c-free d-free)
    | A , A⊑R , A⊑L | B , B⊑L , B⊑R =
  A ⇒ B , I.⇒⊑⇒ A⊑L B⊑L , I.⇒⊑⇒ A⊑R B⊑R
consistent-common-lowerᵐ h (∀ᶜ c) (cf-∀ᶜ c-free)
    with consistent-common-lowerᵐ (extend-lower-env h) c c-free
consistent-common-lowerᵐ h (∀ᶜ c) (cf-∀ᶜ c-free)
    | D , D⊑A , D⊑B =
  `∀ D , I.∀⊑∀ D⊑A , I.∀⊑∀ D⊑B
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) (cf-! cf-⇒∼★ c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) (cf-! cf-⇒∼★ c-free)
    | D , D⊑A , D⊑G =
  D , D⊑A , arrow-right-to-star h D⊑G
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) (cf-! cf-ι∼★ c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) (cf-! cf-ι∼★ c-free)
    | D , D⊑A , D⊑G =
  D , D⊑A , base-right-to-star h D⊑G
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄)
    (cf-! cf-X∼★ᵍ c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄)
    (cf-! cf-X∼★ᵍ c-free)
    | D , D⊑A , D⊑G =
  D , D⊑A , var-right-to-star h eq D⊑G
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) (cf-! cf-∀∼★ c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) (cf-! cf-∀∼★ c-free)
    | D , D⊑A , D⊑G =
  D , D⊑A , universal-right-to-star D⊑G
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) (cf-？ cf-★∼⇒ c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) (cf-？ cf-★∼⇒ c-free)
    | D , D⊑G , D⊑B =
  D , arrow-left-to-star h D⊑G , D⊑B
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) (cf-？ cf-★∼ι c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) (cf-？ cf-★∼ι c-free)
    | D , D⊑G , D⊑B =
  D , base-left-to-star h D⊑G , D⊑B
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
    (cf-？ cf-★∼Xᵍ c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
    (cf-？ cf-★∼Xᵍ c-free)
    | D , D⊑G , D⊑B =
  D , var-left-to-star h eq D⊑G , D⊑B
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) (cf-？ cf-★∼∀ c-free)
    with consistent-common-lowerᵐ h c c-free
consistent-common-lowerᵐ h
    (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) (cf-？ cf-★∼∀ c-free)
    | D , D⊑G , D⊑B =
  D , universal-right-to-star D⊑G , D⊑B
consistent-common-lowerᵐ h
    (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) (cf-inst c-free)
    with consistent-common-lowerᵐ
      (instantiate-right-lower-env h) c c-free
consistent-common-lowerᵐ h
    (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    (cf-inst c-free)
    | D , D⊑A , D⊑B =
  `∀ D , I.∀⊑∀ D⊑A ,
  I.∀⊑ (source-nonvar-from-target D⊑A Anv z∈A)
    (target-occurs-source D⊑A z∈A) D⊑B
consistent-common-lowerᵐ h
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) (cf-gen c-free)
    with consistent-common-lowerᵐ
      (instantiate-left-lower-env h) c c-free
consistent-common-lowerᵐ h
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    (cf-gen c-free)
    | D , D⊑A , D⊑B =
  `∀ D ,
  I.∀⊑ (source-nonvar-from-target D⊑B Bnv z∈B)
    (target-occurs-source D⊑B z∈B) D⊑A ,
  I.∀⊑∀ D⊑B
consistent-common-lowerᵐ h bot-elim cf-bot-elim =
  `∀ (＇ zero) , refl⊑ (`∀ (＇ zero)) , I.bot-elim
consistent-common-lowerᵐ h bot-intro cf-bot-intro =
  `∀ (＇ zero) , I.bot-elim , refl⊑ (`∀ (＇ zero))

consistent-common-lower : ∀ {Δ} {A B : Ty Δ}
  → (c : A ∼ B)
  → CrossFree c
  → ∃[ D ] I._⊑_ D A × I._⊑_ D B
consistent-common-lower c =
  consistent-common-lowerᵐ identity-lower-env c

------------------------------------------------------------------------
-- Properties used to reconstruct consistency from lower bounds
------------------------------------------------------------------------

var-identity-not-star :
  _≡_ {A = I.VarImp} I.X⊑X I.X⊑★ → ⊥
var-identity-not-star ()

unshift-nonvar : ∀ {Δ} {A : Ty Δ}
  → NonVar (⇑ᵗ A)
  → NonVar A
unshift-nonvar {A = ＇ X} ()
unshift-nonvar {A = ‵ ι} nonvar-base = nonvar-base
unshift-nonvar {A = ★} nonvar-star = nonvar-star
unshift-nonvar {A = A ⇒ B} nonvar-fun = nonvar-fun
unshift-nonvar {A = `∀ A} nonvar-all = nonvar-all

source-nonvar-target : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → I._⊢_⊑_ μ A B
  → NonVar A
  → NonVar B
source-nonvar-target I.★⊑★ nonvar-star = nonvar-star
source-nonvar-target I.ι⊑ι nonvar-base = nonvar-base
source-nonvar-target I.X⊑X ()
source-nonvar-target (I.⇒⊑⇒ p q) nonvar-fun = nonvar-fun
source-nonvar-target (I.∀⊑∀ p) nonvar-all = nonvar-all
source-nonvar-target (I.⇒⊑★ p q) nonvar-fun = nonvar-star
source-nonvar-target I.ι⊑★ nonvar-base = nonvar-star
source-nonvar-target (I.X⊑★ eq) ()
source-nonvar-target (I.∀⊑ Anv z∈A p) nonvar-all =
  unshift-nonvar (source-nonvar-target p Anv)
source-nonvar-target I.∀★⊑★ nonvar-all = nonvar-star
source-nonvar-target (I.∀⊑★ Ans p) nonvar-all = nonvar-star
source-nonvar-target I.bot-elim nonvar-all = nonvar-all
source-nonvar-target I.bot⊑★ nonvar-all = nonvar-star

source-occurs-target : ∀ {Δ} {μ : I.ImpEnv Δ}
    {X : TyVar Δ} {A B : Ty Δ}
  → μ X ≡ I.X⊑X
  → I._⊢_⊑_ μ A B
  → X ∈ᵗ A
  → X ∈ᵗ B
source-occurs-target focus I.★⊑★ ()
source-occurs-target focus I.ι⊑ι ()
source-occurs-target focus I.X⊑X X∈A = X∈A
source-occurs-target focus (I.⇒⊑⇒ p q) (∈-fun-left X∈A) =
  ∈-fun-left (source-occurs-target focus p X∈A)
source-occurs-target {X = X} focus (I.⇒⊑⇒ p q)
    (∈-fun-right X∉A X∈B) with occurs? X _
source-occurs-target {X = X} focus (I.⇒⊑⇒ p q)
    (∈-fun-right X∉A X∈B) | present X∈A′ = ∈-fun-left X∈A′
source-occurs-target {X = X} focus (I.⇒⊑⇒ p q)
    (∈-fun-right X∉A X∈B) | absent X∉A′ =
  ∈-fun-right X∉A′ (source-occurs-target focus q X∈B)
source-occurs-target {X = X} focus (I.∀⊑∀ p) (∈-all X∈A) =
  ∈-all (source-occurs-target {X = suc X} focus p X∈A)
source-occurs-target focus (I.⇒⊑★ p q) (∈-fun-left X∈A)
    with source-occurs-target focus p X∈A
source-occurs-target focus (I.⇒⊑★ p q) (∈-fun-left X∈A) | ()
source-occurs-target focus (I.⇒⊑★ p q)
    (∈-fun-right X∉A X∈B) with source-occurs-target focus q X∈B
source-occurs-target focus (I.⇒⊑★ p q)
    (∈-fun-right X∉A X∈B) | ()
source-occurs-target focus I.ι⊑★ ()
source-occurs-target focus (I.X⊑★ eq) var-∈ =
  ⊥-elim (var-identity-not-star (trans (sym focus) eq))
source-occurs-target {X = X} focus (I.∀⊑ Anv z∈A p)
    (∈-all X∈A) =
  unshift-occurs
    (source-occurs-target {X = suc X} focus p X∈A)
source-occurs-target focus I.∀★⊑★ (∈-all ())
source-occurs-target {X = X} focus (I.∀⊑★ Ans p) (∈-all X∈A)
    with source-occurs-target {X = suc X} focus p X∈A
source-occurs-target {X = X} focus (I.∀⊑★ Ans p) (∈-all X∈A)
    | ()
source-occurs-target focus I.bot-elim (∈-all ())
source-occurs-target focus I.bot⊑★ (∈-all ())

all-ground-body : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A : Ty (Nat.suc Δ)} {H : Ty Δ}
  → NonVar A
  → zero ∈ᵗ A
  → Ground H
  → I._⊢_⊑_ μ (`∀ A) H
  → I._⊢_⊑_ (I.instᵐ μ) A (⇑ᵗ H)
all-ground-body Anv zero∈A (＇ X)
    (I.∀⊑ Anv′ zero∈A′ body) = body
all-ground-body Anv zero∈A (‵ ι)
    (I.∀⊑ Anv′ zero∈A′ body) = body
all-ground-body Anv zero∈A ★⇒★
    (I.∀⊑ Anv′ zero∈A′ body) = body
all-ground-body Anv zero∈A ∀★
    (I.∀⊑ Anv′ zero∈A′ body) = body
all-ground-body Anv zero∈A ∀★ (I.∀⊑∀ body)
    with source-occurs-target refl body zero∈A
all-ground-body Anv zero∈A ∀★ (I.∀⊑∀ body) | ()
all-ground-body () zero∈A ∀★ I.bot-elim

------------------------------------------------------------------------
-- Ground targets and consistency
------------------------------------------------------------------------

consistency-var-self-not-star : X∼X ≡ X∼★ → ⊥
consistency-var-self-not-star ()

consistency-var-self-not-from-star : X∼X ≡ ★∼X → ⊥
consistency-var-self-not-from-star ()

consistency-var-self-not-cross : X∼X ≡ ★∼X∼★ → ⊥
consistency-var-self-not-cross ()

flip-self-mode : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {X : TyVar Δ}
  → ν X ≡ X∼X
  → flipᵐ ν X ≡ X∼X
flip-self-mode same = cong flipVar∼ same

flip-flip-self-mode : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {X : TyVar Δ}
  → ν X ≡ X∼X
  → flipᵐ (flipᵐ ν) X ≡ X∼X
flip-flip-self-mode same = cong flipVar∼ (cong flipVar∼ same)

ground-self-occurs⊥ : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {X : TyVar Δ}
    {G : Ty Δ}
  → ν X ≡ X∼X
  → ν ⊢ G ∼★
  → X ∈ᵗ G
  → ⊥
ground-self-occurs⊥ same ⇒∼★ (∈-fun-left ())
ground-self-occurs⊥ same ⇒∼★ (∈-fun-right X∉A ())
ground-self-occurs⊥ same ι∼★ ()
ground-self-occurs⊥ same (X∼★ᵍ eq) var-∈ =
  consistency-var-self-not-star (trans (sym same) eq)
ground-self-occurs⊥ same (X∼★ᶜ eq) var-∈ =
  consistency-var-self-not-cross (trans (sym same) eq)
ground-self-occurs⊥ same ∀∼★ (∈-all ())

ground-self-occurs★∼⊥ : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {X : TyVar Δ}
    {G : Ty Δ}
  → ν X ≡ X∼X
  → ν ⊢★∼ G
  → X ∈ᵗ G
  → ⊥
ground-self-occurs★∼⊥ same ★∼⇒ (∈-fun-left ())
ground-self-occurs★∼⊥ same ★∼⇒ (∈-fun-right X∉A ())
ground-self-occurs★∼⊥ same ★∼ι ()
ground-self-occurs★∼⊥ same (★∼Xᵍ eq) var-∈ =
  consistency-var-self-not-from-star (trans (sym same) eq)
ground-self-occurs★∼⊥ same (★∼Xᶜ eq) var-∈ =
  consistency-var-self-not-cross (trans (sym same) eq)
ground-self-occurs★∼⊥ same ★∼∀ (∈-all ())

mutual
  consistency-source-occurs-target : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → ν X ≡ X∼X
    → ν ⊢ A ∼ B
    → X ∈ᵗ A
    → X ∈ᵗ B
  consistency-source-occurs-target same (id a) X∈A = X∈A
  consistency-source-occurs-target {ν = ν} {X = X}
      {A = A ⇒ B} {B = A′ ⇒ B′} same (c ↦ d)
      (∈-fun-left X∈A) =
    ∈-fun-left
      (consistency-target-occurs-source {ν = flipᵐ ν} {X = X}
        (flip-self-mode {ν = ν} {X = X} same) c X∈A)
  consistency-source-occurs-target {X = X} {A = A ⇒ B}
      {B = A′ ⇒ B′} same (c ↦ d) (∈-fun-right X∉A X∈B)
      with occurs? X A′
  consistency-source-occurs-target {X = X} {A = A ⇒ B}
      {B = A′ ⇒ B′} same (c ↦ d) (∈-fun-right X∉A X∈B)
      | present X∈A′ = ∈-fun-left X∈A′
  consistency-source-occurs-target {X = X} {A = A ⇒ B}
      {B = A′ ⇒ B′} same (c ↦ d) (∈-fun-right X∉A X∈B)
      | absent X∉A′ =
    ∈-fun-right X∉A′
      (consistency-source-occurs-target same d X∈B)
  consistency-source-occurs-target {X = X} {A = `∀ A} {B = `∀ B}
      same (∀ᶜ c) (∈-all X∈A) =
    ∈-all (consistency-source-occurs-target {X = suc X} same c X∈A)
  consistency-source-occurs-target {B = ★} same
      (_! ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄) X∈A =
    ⊥-elim (ground-self-occurs⊥ same G∼★
      (consistency-source-occurs-target same c X∈A))
  consistency-source-occurs-target {A = ★} same
      (？_ ⦃ g ⦄ c ⦃ Bns ⦄) ()
  consistency-source-occurs-target {X = X} {A = `∀ A} same
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) (∈-all X∈A) =
    unshift-occurs
      (consistency-source-occurs-target {X = suc X} same c X∈A)
  consistency-source-occurs-target {X = X} {B = `∀ B} same
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) X∈A =
    ∈-all (consistency-source-occurs-target {X = suc X} same c
      (shift-occurs X∈A))
  consistency-source-occurs-target {A = `∀ (＇ zero)}
      same bot-elim (∈-all ())
  consistency-source-occurs-target {A = `∀ ★}
      same bot-intro (∈-all ())

  consistency-target-occurs-source : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → ν X ≡ X∼X
    → ν ⊢ A ∼ B
    → X ∈ᵗ B
    → X ∈ᵗ A
  consistency-target-occurs-source same (id a) X∈B = X∈B
  consistency-target-occurs-source {ν = ν} {X = X}
      {A = A ⇒ B} {B = A′ ⇒ B′} same (c ↦ d)
      (∈-fun-left X∈A′) =
    ∈-fun-left
      (consistency-source-occurs-target {ν = flipᵐ ν} {X = X}
        (flip-self-mode {ν = ν} {X = X} same) c X∈A′)
  consistency-target-occurs-source {X = X} {A = A ⇒ B}
      {B = A′ ⇒ B′} same (c ↦ d) (∈-fun-right X∉A′ X∈B′)
      with occurs? X A
  consistency-target-occurs-source {X = X} {A = A ⇒ B}
      {B = A′ ⇒ B′} same (c ↦ d) (∈-fun-right X∉A′ X∈B′)
      | present X∈A = ∈-fun-left X∈A
  consistency-target-occurs-source {X = X} {A = A ⇒ B}
      {B = A′ ⇒ B′} same (c ↦ d) (∈-fun-right X∉A′ X∈B′)
      | absent X∉A =
    ∈-fun-right X∉A
      (consistency-target-occurs-source same d X∈B′)
  consistency-target-occurs-source {X = X} {A = `∀ A} {B = `∀ B}
      same (∀ᶜ c) (∈-all X∈B) =
    ∈-all (consistency-target-occurs-source {X = suc X} same c X∈B)
  consistency-target-occurs-source {B = ★} same
      (_! ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄) ()
  consistency-target-occurs-source {A = ★} same
      (？_ ⦃ ★∼G = ★∼G ⦄ c ⦃ Bns ⦄) X∈B =
    ⊥-elim (ground-self-occurs★∼⊥ same ★∼G
      (consistency-target-occurs-source same c X∈B))
  consistency-target-occurs-source {X = X} {A = `∀ A} same
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) X∈B =
    ∈-all
      (consistency-target-occurs-source {X = suc X} same c
        (shift-occurs X∈B))
  consistency-target-occurs-source {X = X} {B = `∀ B} same
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) (∈-all X∈B) =
    unshift-occurs
      (consistency-target-occurs-source {X = suc X} same c X∈B)
  consistency-target-occurs-source {B = `∀ ★}
      same bot-elim (∈-all ())
  consistency-target-occurs-source {B = `∀ (＇ zero)}
      same bot-intro (∈-all ())

shift-ground : ∀ {Δ G}
  → Ground {Δ} G
  → Ground (⇑ᵗ G)
shift-ground ★⇒★ = ★⇒★
shift-ground (‵ ι) = ‵ ι
shift-ground (＇ X) = ＇ suc X
shift-ground ∀★ = ∀★

inst-shift-∼★ : ∀ {Δ μ G}
  → μ ⊢ G ∼★
  → C.instᵐ {Δ} μ ⊢ ⇑ᵗ G ∼★
inst-shift-∼★ ⇒∼★ = ⇒∼★
inst-shift-∼★ ι∼★ = ι∼★
inst-shift-∼★ (X∼★ᵍ eq) = X∼★ᵍ eq
inst-shift-∼★ (X∼★ᶜ eq) = X∼★ᶜ eq
inst-shift-∼★ ∀∼★ = ∀∼★

inst-shift-★∼ : ∀ {Δ μ G}
  → μ ⊢★∼ G
  → C.instᵐ {Δ} μ ⊢★∼ ⇑ᵗ G
inst-shift-★∼ ★∼⇒ = ★∼⇒
inst-shift-★∼ ★∼ι = ★∼ι
inst-shift-★∼ (★∼Xᵍ eq) = ★∼Xᵍ eq
inst-shift-★∼ (★∼Xᶜ eq) = ★∼Xᶜ eq
inst-shift-★∼ ★∼∀ = ★∼∀

ground-target-nonvar-to-star⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {A G : Ty Δ}
  → Ground G
  → NonVar A
  → μ ⊢ A ⊑ G
  → μ ⊢ A ⊑ ★
ground-target-nonvar-to-star⊑ () Anv I.★⊑★
ground-target-nonvar-to-star⊑ (‵ ι) nonvar-base I.ι⊑ι = I.ι⊑★
ground-target-nonvar-to-star⊑ g () I.X⊑X
ground-target-nonvar-to-star⊑ ★⇒★ nonvar-fun
    (I.⇒⊑⇒ A⊑★ B⊑★) =
  I.⇒⊑★ A⊑★ B⊑★
ground-target-nonvar-to-star⊑ ∀★ nonvar-all (I.∀⊑∀ A⊑G) =
  universal-right-to-star (I.∀⊑∀ A⊑G)
ground-target-nonvar-to-star⊑ () nonvar-fun
    (I.⇒⊑★ A⊑★ B⊑★)
ground-target-nonvar-to-star⊑ () nonvar-base I.ι⊑★
ground-target-nonvar-to-star⊑ () () (I.X⊑★ eq)
ground-target-nonvar-to-star⊑ g nonvar-all
    (I.∀⊑ Anv zero∈A A⊑G) =
  I.∀⊑ Anv zero∈A
    (ground-target-nonvar-to-star⊑ (shift-ground g) Anv A⊑G)
ground-target-nonvar-to-star⊑ () nonvar-all I.∀★⊑★
ground-target-nonvar-to-star⊑ () nonvar-all (I.∀⊑★ Ans A⊑★)
ground-target-nonvar-to-star⊑ ∀★ nonvar-all I.bot-elim =
  I.bot⊑★
ground-target-nonvar-to-star⊑ () nonvar-all I.bot⊑★

weaken-star-map-ext : ∀ {Δ} {μ ν : I.ImpEnv Δ}
  → (∀ X → μ X ≡ I.X⊑★ → ν X ≡ I.X⊑★)
  → ∀ X → I.extᵐ μ X ≡ I.X⊑★ → I.extᵐ ν X ≡ I.X⊑★
weaken-star-map-ext h zero ()
weaken-star-map-ext h (suc X) eq = h X eq

weaken-star-map-inst : ∀ {Δ} {μ ν : I.ImpEnv Δ}
  → (∀ X → μ X ≡ I.X⊑★ → ν X ≡ I.X⊑★)
  → ∀ X → I.instᵐ μ X ≡ I.X⊑★ → I.instᵐ ν X ≡ I.X⊑★
weaken-star-map-inst h zero eq = refl
weaken-star-map-inst h (suc X) eq = h X eq

imp-env-weaken : ∀ {Δ} {μ ν : I.ImpEnv Δ} {A B : Ty Δ}
  → (∀ X → μ X ≡ I.X⊑★ → ν X ≡ I.X⊑★)
  → μ ⊢ A ⊑ B
  → ν ⊢ A ⊑ B
imp-env-weaken h I.★⊑★ = I.★⊑★
imp-env-weaken h I.ι⊑ι = I.ι⊑ι
imp-env-weaken h I.X⊑X = I.X⊑X
imp-env-weaken h (I.⇒⊑⇒ A⊑B C⊑D) =
  I.⇒⊑⇒ (imp-env-weaken h A⊑B) (imp-env-weaken h C⊑D)
imp-env-weaken h (I.∀⊑∀ A⊑B) =
  I.∀⊑∀ (imp-env-weaken (weaken-star-map-ext h) A⊑B)
imp-env-weaken h (I.⇒⊑★ A⊑★ B⊑★) =
  I.⇒⊑★ (imp-env-weaken h A⊑★) (imp-env-weaken h B⊑★)
imp-env-weaken h I.ι⊑★ = I.ι⊑★
imp-env-weaken h (I.X⊑★ x⊑★) = I.X⊑★ (h _ x⊑★)
imp-env-weaken h (I.∀⊑ Anv zero∈A A⊑B) =
  I.∀⊑ Anv zero∈A
    (imp-env-weaken (weaken-star-map-inst h) A⊑B)
imp-env-weaken h I.∀★⊑★ = I.∀★⊑★
imp-env-weaken h (I.∀⊑★ Ans A⊑★) =
  I.∀⊑★ Ans (imp-env-weaken (weaken-star-map-ext h) A⊑★)
imp-env-weaken h I.bot-elim = I.bot-elim
imp-env-weaken h I.bot⊑★ = I.bot⊑★

rename-star-map-ext : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {μ′ : I.ImpEnv Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
  → ∀ X → I.extᵐ μ X ≡ I.X⊑★
      → I.extᵐ μ′ (extᵗ ρ X) ≡ I.X⊑★
rename-star-map-ext ρ h zero ()
rename-star-map-ext ρ h (suc X) eq = h X eq

rename-star-map-inst : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {μ′ : I.ImpEnv Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
  → ∀ X → I.instᵐ μ X ≡ I.X⊑★
      → I.instᵐ μ′ (extᵗ ρ X) ≡ I.X⊑★
rename-star-map-inst ρ h zero eq = refl
rename-star-map-inst ρ h (suc X) eq = h X eq

rename-⊑ : ∀ {Δ Δ′} {μ : I.ImpEnv Δ} {μ′ : I.ImpEnv Δ′}
    {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → (∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
  → μ ⊢ A ⊑ B
  → μ′ ⊢ renameᵗ ρ A ⊑ renameᵗ ρ B
rename-⊑ ρ injective h I.★⊑★ = I.★⊑★
rename-⊑ ρ injective h I.ι⊑ι = I.ι⊑ι
rename-⊑ ρ injective h I.X⊑X = I.X⊑X
rename-⊑ ρ injective h (I.⇒⊑⇒ A⊑B C⊑D) =
  I.⇒⊑⇒ (rename-⊑ ρ injective h A⊑B)
    (rename-⊑ ρ injective h C⊑D)
rename-⊑ ρ injective h (I.∀⊑∀ A⊑B) =
  I.∀⊑∀ (rename-⊑ (extᵗ ρ) (ext-injective injective)
    (rename-star-map-ext ρ h) A⊑B)
rename-⊑ ρ injective h (I.⇒⊑★ A⊑★ B⊑★) =
  I.⇒⊑★ (rename-⊑ ρ injective h A⊑★)
    (rename-⊑ ρ injective h B⊑★)
rename-⊑ ρ injective h I.ι⊑★ = I.ι⊑★
rename-⊑ ρ injective h (I.X⊑★ x⊑★) =
  I.X⊑★ (h _ x⊑★)
rename-⊑ ρ injective h (I.∀⊑ Anv zero∈A A⊑B) =
  I.∀⊑ (renameNonVar (extᵗ ρ) Anv)
    (rename-occurs (extᵗ ρ) (ext-injective injective) zero∈A)
    (subst (λ T → _ ⊢ renameᵗ (extᵗ ρ) _ ⊑ T)
      (renameᵗ-shift ρ _)
      (rename-⊑ (extᵗ ρ) (ext-injective injective)
        (rename-star-map-inst ρ h) A⊑B))
rename-⊑ ρ injective h I.∀★⊑★ = I.∀★⊑★
rename-⊑ ρ injective h (I.∀⊑★ Ans A⊑★) =
  I.∀⊑★ (C.renameNonStar (extᵗ ρ) Ans)
    (rename-⊑ (extᵗ ρ) (ext-injective injective)
      (rename-star-map-ext ρ h) A⊑★)
rename-⊑ ρ injective h I.bot-elim = I.bot-elim
rename-⊑ ρ injective h I.bot⊑★ = I.bot⊑★

subst-occurs-preserve : ∀ {Δ Δ′} {σ : Δ ⇒ˢ Δ′}
    {X : TyVar Δ′} {Y : TyVar Δ} {A : Ty Δ}
  → (∀ {Z} → Y ≡ Z → X ∈ᵗ σ Z)
  → Y ∈ᵗ A
  → X ∈ᵗ substᵗ σ A
subst-occurs-preserve h var-∈ = h refl
subst-occurs-preserve h (∈-fun-left X∈A) =
  ∈-fun-left (subst-occurs-preserve h X∈A)
subst-occurs-preserve {X = X} h (∈-fun-right Y∉A Y∈B)
    with occurs? X _
subst-occurs-preserve {X = X} h (∈-fun-right Y∉A Y∈B)
    | present X∈A′ = ∈-fun-left X∈A′
subst-occurs-preserve {X = X} h (∈-fun-right Y∉A Y∈B)
    | absent X∉A′ =
  ∈-fun-right X∉A′ (subst-occurs-preserve h Y∈B)
subst-occurs-preserve {σ = σ} {X = X} {Y = Y} h (∈-all Y∈A) =
  ∈-all (subst-occurs-preserve h′ Y∈A)
  where
  h′ : ∀ {Z} → suc Y ≡ Z → suc X ∈ᵗ extsᵗ σ Z
  h′ {zero} ()
  h′ {suc Z} eq = shift-occurs (h (fin-suc-injective eq))

subst-zero-occurs-exts : ∀ {Δ Δ′} {σ : Δ ⇒ˢ Δ′}
    {A : Ty (Nat.suc Δ)}
  → zero ∈ᵗ A
  → zero ∈ᵗ substᵗ (extsᵗ σ) A
subst-zero-occurs-exts =
  subst-occurs-preserve λ { {zero} refl → var-∈ ; {suc Y} () }

subst-star-map-exts : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {ν : I.ImpEnv Δ′} {σ : Δ ⇒ˢ Δ′}
  → (∀ X → μ X ≡ I.X⊑★ → ν ⊢ σ X ⊑ ★)
  → ∀ X → I.extᵐ μ X ≡ I.X⊑★
      → I.extᵐ ν ⊢ extsᵗ σ X ⊑ ★
subst-star-map-exts h zero ()
subst-star-map-exts h (suc X) eq =
  rename-⊑ suc fin-suc-injective (λ Y eq′ → eq′) (h X eq)

subst-star-map-insts : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {ν : I.ImpEnv Δ′} {σ : Δ ⇒ˢ Δ′}
  → (∀ X → μ X ≡ I.X⊑★ → ν ⊢ σ X ⊑ ★)
  → ∀ X → I.instᵐ μ X ≡ I.X⊑★
      → I.instᵐ ν ⊢ extsᵗ σ X ⊑ ★
subst-star-map-insts h zero eq = I.X⊑★ refl
subst-star-map-insts h (suc X) eq =
  rename-⊑ suc fin-suc-injective (λ Y eq′ → eq′) (h X eq)

subst-⊑ : ∀ {Δ Δ′} {μ : I.ImpEnv Δ} {ν : I.ImpEnv Δ′}
    {σ : Δ ⇒ˢ Δ′} {A B : Ty Δ}
  → (∀ X → μ X ≡ I.X⊑★ → ν ⊢ σ X ⊑ ★)
  → μ ⊢ A ⊑ B
  → ν ⊢ substᵗ σ A ⊑ substᵗ σ B
subst-⊑ h I.★⊑★ = I.★⊑★
subst-⊑ h I.ι⊑ι = I.ι⊑ι
subst-⊑ h I.X⊑X = refl⊑ _
subst-⊑ h (I.⇒⊑⇒ A⊑B C⊑D) =
  I.⇒⊑⇒ (subst-⊑ h A⊑B) (subst-⊑ h C⊑D)
subst-⊑ h (I.∀⊑∀ A⊑B) =
  I.∀⊑∀ (subst-⊑ (subst-star-map-exts h) A⊑B)
subst-⊑ h (I.⇒⊑★ A⊑★ B⊑★) =
  I.⇒⊑★ (subst-⊑ h A⊑★) (subst-⊑ h B⊑★)
subst-⊑ h I.ι⊑★ = I.ι⊑★
subst-⊑ h (I.X⊑★ x⊑★) = h _ x⊑★
subst-⊑ {ν = ν} {σ = σ} h
    (I.∀⊑ {A = A} {B = B} Anv zero∈A A⊑B) =
  I.∀⊑ (substNonVar (extsᵗ σ) Anv)
    (subst-zero-occurs-exts {σ = σ} zero∈A)
    (subst (λ T → I.instᵐ ν ⊢ substᵗ (extsᵗ σ) A ⊑ T)
      (substᵗ-shift σ B)
      (subst-⊑ {ν = I.instᵐ ν} {σ = extsᵗ σ}
        (subst-star-map-insts h) A⊑B))
subst-⊑ h I.∀★⊑★ = I.∀★⊑★
subst-⊑ {σ = σ} h (I.∀⊑★ {A = A} Ans A⊑★)
    with substᵗ (extsᵗ σ) A ≟Ty ★
subst-⊑ {σ = σ} h (I.∀⊑★ {A = A} Ans A⊑★)
    | yes Aσ≡★ =
  subst (λ T → _ ⊢ `∀ T ⊑ ★) (sym Aσ≡★) I.∀★⊑★
subst-⊑ {σ = σ} h (I.∀⊑★ {A = A} Ans A⊑★)
    | no Aσ≢★ =
  I.∀⊑★ (nonstar-from-≢★ Aσ≢★)
    (subst-⊑ (subst-star-map-exts h) A⊑★)
subst-⊑ h I.bot-elim = I.bot-elim
subst-⊑ h I.bot⊑★ = I.bot⊑★

open-star-map : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X → I.instᵐ μ X ≡ I.X⊑★
      → μ ⊢ singleSubᵗ ★ X ⊑ ★
open-star-map zero eq = I.★⊑★
open-star-map (suc X) eq = I.X⊑★ eq

unshift-⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → I.instᵐ μ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
  → μ ⊢ A ⊑ B
unshift-⊑ {A = A} {B = B} p =
  subst (λ L → _ ⊢ L ⊑ B) (shift-openᵗ A ★)
    (subst (λ R → _ ⊢ (⇑ᵗ A) [ ★ ]ᵗ ⊑ R)
      (shift-openᵗ B ★)
      (subst-⊑ open-star-map p))

shift-injectiveᵗ : ∀ {Δ} {A B : Ty Δ}
  → ⇑ᵗ A ≡ ⇑ᵗ B
  → A ≡ B
shift-injectiveᵗ {A = A} {B = B} eq =
  trans (sym (shift-openᵗ A ★))
    (trans (cong (λ T → T [ ★ ]ᵗ) eq) (shift-openᵗ B ★))

ext-to-inst-star-map : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X → I.extᵐ μ X ≡ I.X⊑★ → I.instᵐ μ X ≡ I.X⊑★
ext-to-inst-star-map zero ()
ext-to-inst-star-map (suc X) eq = eq

nonvar-occurs-nonstar : ∀ {Δ X} {A : Ty Δ}
  → NonVar A
  → X ∈ᵗ A
  → NonStar A
nonvar-occurs-nonstar nonvar-base ()
nonvar-occurs-nonstar nonvar-star ()
nonvar-occurs-nonstar nonvar-fun X∈A = nonstar-⇒
nonvar-occurs-nonstar nonvar-all X∈A = nonstar-∀

zero-not-consistent-shift-ground : ∀ {Δ ν G}
  → Ground {Δ} G
  → C.instᵐ ν ⊢ ＇ zero ∼ ⇑ᵗ G
  → ⊥
zero-not-consistent-shift-ground ★⇒★ ()
zero-not-consistent-shift-ground (‵ ι) ()
zero-not-consistent-shift-ground (＇ X) ()
zero-not-consistent-shift-ground ∀★
    (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≢★)

consistent-self-var-nonvar-occurs⊥ : ∀ {Δ} {ν : Env∼ Δ}
    {X : TyVar Δ} {B : Ty Δ}
  → ν X ≡ X∼X
  → ν ⊢ ＇ X ∼ B
  → NonVar B
  → X ∈ᵗ B
  → ⊥
consistent-self-var-nonvar-occurs⊥ same (id (＇ X)) () var-∈
consistent-self-var-nonvar-occurs⊥ same
    (_! ⦃ g ⦄ c ⦃ Bns ⦄) nonvar-star ()
consistent-self-var-nonvar-occurs⊥ same
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) nonvar-all
    (∈-all X∈B) =
  consistent-self-var-nonvar-occurs⊥ same c Bnv X∈B

var-star-universal-ground : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {X : TyVar Δ} {A : Ty Δ}
  → φ X ≡ I.X⊑X
  → ψ X ≡ I.X⊑★
  → φ ⊢ A ⊑ ＇ X
  → ψ ⊢ A ⊑ ★
  → NonVar A
  → ψ ⊢ A ⊑ `∀ ★
var-star-universal-ground same to-star I.X⊑X A⊑★ ()
var-star-universal-ground same to-star
    (I.∀⊑ Anv () A⊑X) I.∀★⊑★ nonvar-all
var-star-universal-ground same to-star
    (I.∀⊑ Anv zero∈A A⊑X) (I.∀⊑★ Ans A⊑★) nonvar-all =
  I.∀⊑∀ A⊑★
var-star-universal-ground same to-star
    (I.∀⊑ Anv zero∈A A⊑X)
    (I.∀⊑ Bnv zero∈B A⊑★) nonvar-all =
  I.∀⊑ Bnv zero∈B
    (var-star-universal-ground same to-star A⊑X A⊑★ Bnv)
var-star-universal-ground same to-star
    (I.∀⊑ () zero∈A A⊑X) I.bot⊑★ nonvar-all

ground-cast-target⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {ν : Env∼ Δ}
    {A B G : Ty Δ}
  → (g : Ground G)
  → NonStar B
  → ν ⊢ B ∼ G
  → μ ⊢ A ⊑ B
  → μ ⊢ A ⊑ ★
  → μ ⊢ A ⊑ G
ground-cast-target⊑ g () c I.★⊑★ I.★⊑★
ground-cast-target⊑ g Bns (id (‵ ι)) I.ι⊑ι I.ι⊑★ =
  I.ι⊑ι
ground-cast-target⊑ g () c I.ι⊑★ I.ι⊑★
ground-cast-target⊑ g Bns (id (＇ X)) I.X⊑X (I.X⊑★ x⊑★) =
  I.X⊑X
ground-cast-target⊑ g () c (I.X⊑★ x⊑★) (I.X⊑★ x⊑★′)
ground-cast-target⊑ ★⇒★ Bns (c₁ ↦ c₂)
    (I.⇒⊑⇒ A⊑B C⊑D) (I.⇒⊑★ A⊑★ C⊑★) =
  I.⇒⊑⇒ A⊑★ C⊑★
ground-cast-target⊑ g () c (I.⇒⊑★ A⊑★ B⊑★)
    (I.⇒⊑★ A⊑★′ B⊑★′)
ground-cast-target⊑ {ν = ν} g Bns c
    (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑ Anv′ zero∈A′ A⊑★) =
  I.∀⊑ Anv zero∈A
    (ground-cast-target⊑ {ν = C.extᵐ ν}
      (shift-ground g) (C.renameNonStar suc Bns)
      (C.renameEnvᶜ {ν = C.extᵐ ν} suc (λ X → refl) c) A⊑B A⊑★)
ground-cast-target⊑ g Bns c
    (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑★ Ans A⊑★)
    with source-occurs-target refl A⊑★ zero∈A
ground-cast-target⊑ g Bns c
    (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑★ Ans A⊑★)
    | ()
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★) =
  I.∀⊑ Anv zero∈A
    (ground-cast-target⊑ (shift-ground g)
      (nonvar-occurs-nonstar Bnv zero∈B) c
      (imp-env-weaken ext-to-inst-star-map A⊑B) A⊑★)
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) I.∀★⊑★
    with target-occurs-source A⊑B zero∈B
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) I.∀★⊑★
    | ()
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    with target-occurs-source A⊑B zero∈B
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A with source-occurs-target refl A⊑★ zero∈A
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A | ()
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ I.X⊑X) I.bot⊑★ =
  ⊥-elim (zero-not-consistent-shift-ground g c)
ground-cast-target⊑ ∀★ Bns
    (C.gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≢★) A⊑B A⊑★
ground-cast-target⊑ ∀★ Bns (∀ᶜ c)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★)
    with source-occurs-target refl A⊑B zero∈A
ground-cast-target⊑ ∀★ Bns (∀ᶜ c)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★)
    | zero∈B with consistency-source-occurs-target refl c zero∈B
ground-cast-target⊑ ∀★ Bns (∀ᶜ c)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★)
    | zero∈B | ()
ground-cast-target⊑ ∀★ Bns (∀ᶜ c)
    A⊑B I.∀★⊑★ =
  I.∀⊑∀ I.★⊑★
ground-cast-target⊑ ∀★ Bns (∀ᶜ c)
    A⊑B (I.∀⊑★ Ans A⊑★) =
  I.∀⊑∀ A⊑★
ground-cast-target⊑ ∀★ Bns (∀ᶜ c)
    A⊑B I.bot⊑★ =
  I.bot-elim
ground-cast-target⊑ ∀★ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    with target-occurs-source A⊑B var-∈
ground-cast-target⊑ ∀★ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A with source-occurs-target refl A⊑★ zero∈A
ground-cast-target⊑ ∀★ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A | ()
ground-cast-target⊑ ∀★ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★) =
  I.∀⊑ Anv zero∈A
    (var-star-universal-ground refl refl A⊑B A⊑★ Anv)
ground-cast-target⊑ ∀★ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) I.bot⊑★ =
  I.bot-elim

ground-cast-source⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {κ : Env∼ Δ}
    {A B G : Ty Δ}
  → (g : Ground G)
  → NonStar A
  → κ ⊢ A ∼ B
  → μ ⊢ A ⊑ ★
  → μ ⊢ B ⊑ ★
  → μ ⊢ B ⊑ G
  → μ ⊢ A ⊑ G
ground-cast-source⊑ g Ans (id x) A⊑★ B⊑★ B⊑G = B⊑G
ground-cast-source⊑ ★⇒★ Ans (c ↦ d)
    (I.⇒⊑★ A⊑★ B⊑★) _ (I.⇒⊑⇒ A′⊑G B′⊑G) =
  I.⇒⊑⇒ A⊑★ B⊑★
ground-cast-source⊑ ∀★ Ans (∀ᶜ c)
    (I.∀⊑ Anv zero∈A A⊑★) B⊑★ (I.∀⊑∀ B⊑G)
    with consistency-source-occurs-target refl c zero∈A
ground-cast-source⊑ ∀★ Ans (∀ᶜ c)
    (I.∀⊑ Anv zero∈A A⊑★) B⊑★ (I.∀⊑∀ B⊑G)
    | zero∈B with source-occurs-target refl B⊑G zero∈B
ground-cast-source⊑ ∀★ Ans (∀ᶜ c)
    (I.∀⊑ Anv zero∈A A⊑★) B⊑★ (I.∀⊑∀ B⊑G)
    | zero∈B | ()
ground-cast-source⊑ ∀★ Ans (∀ᶜ c)
    I.∀★⊑★ B⊑★ (I.∀⊑∀ B⊑G) =
  I.∀⊑∀ I.★⊑★
ground-cast-source⊑ ∀★ Ans (∀ᶜ c)
    (I.∀⊑★ Ans′ A⊑★) B⊑★ (I.∀⊑∀ B⊑G) =
  I.∀⊑∀ A⊑★
ground-cast-source⊑ ∀★ Ans (∀ᶜ c)
    I.bot⊑★ B⊑★ (I.∀⊑∀ B⊑G) =
  I.bot-elim
ground-cast-source⊑ g Ans (∀ᶜ c) A⊑★ B⊑★
    (I.∀⊑ Bnv zero∈B B⊑G) =
  all-imp {g = g} {c = c} {Bnv = Bnv}
    {zero∈B = zero∈B} {B⊑G = B⊑G} A⊑★ B⊑★
  where
  all-imp : ∀ {A B G μ κ}
      {g : Ground G}
      {c : C.extᵐ κ ⊢ A ∼ B}
      {Bnv : NonVar B}
      {zero∈B : zero ∈ᵗ B}
      {B⊑G : I.instᵐ μ ⊢ B ⊑ ⇑ᵗ G}
    → μ ⊢ `∀ A ⊑ ★
    → μ ⊢ `∀ B ⊑ ★
    → μ ⊢ `∀ A ⊑ G
  all-imp {A = A} {B = B} {G = G} {g = g} {c = c}
      {B⊑G = B⊑G} (I.∀⊑ Anv zero∈A A⊑★)
      (I.∀⊑ Bnv′ zero∈B′ B⊑★) =
    I.∀⊑ Anv zero∈A
      (ground-cast-source⊑ {A = A} {B = B} {G = ⇑ᵗ G}
        (shift-ground g)
        (nonvar-occurs-nonstar Anv zero∈A) c A⊑★ B⊑★ B⊑G)
  all-imp {zero∈B = zero∈B}
      (I.∀⊑ Anv zero∈A A⊑★)
      (I.∀⊑★ Bns B⊑★)
      with source-occurs-target refl B⊑★ zero∈B
  all-imp {zero∈B = zero∈B}
      (I.∀⊑ Anv zero∈A A⊑★)
      (I.∀⊑★ Bns B⊑★)
      | ()
  all-imp {c = c} {zero∈B = zero∈B} I.∀★⊑★ B⊑★
      with consistency-source-occurs-target refl (C.sym∼ c) zero∈B
  all-imp {c = c} {zero∈B = zero∈B} I.∀★⊑★ B⊑★ | ()
  all-imp {c = c} {zero∈B = zero∈B}
      (I.∀⊑★ Ans′ A⊑★) B⊑★
      with consistency-source-occurs-target refl (C.sym∼ c) zero∈B
  all-imp {c = c} {zero∈B = zero∈B}
      (I.∀⊑★ Ans′ A⊑★) B⊑★
      | zero∈A with source-occurs-target refl A⊑★ zero∈A
  all-imp {c = c} {zero∈B = zero∈B}
      (I.∀⊑★ Ans′ A⊑★) B⊑★ | zero∈A | ()
  all-imp {c = c} {Bnv = Bnv} {zero∈B = zero∈B}
      I.bot⊑★ B⊑★ =
    ⊥-elim (consistent-self-var-nonvar-occurs⊥ refl c Bnv zero∈B)
ground-cast-source⊑ g Ans (∀ᶜ c)
    (I.∀⊑ Anv zero∈A A⊑★) B⊑★ I.bot-elim =
  ⊥-elim
    (consistent-self-var-nonvar-occurs⊥ refl (C.sym∼ c) Anv zero∈A)
ground-cast-source⊑ g Ans (∀ᶜ c) I.∀★⊑★ B⊑★ I.bot-elim
    with consistency-source-occurs-target refl (C.sym∼ c) var-∈
ground-cast-source⊑ g Ans (∀ᶜ c) I.∀★⊑★ B⊑★ I.bot-elim
    | ()
ground-cast-source⊑ g Ans (∀ᶜ c)
    (I.∀⊑★ Ans′ A⊑★) B⊑★ I.bot-elim
    with consistency-source-occurs-target refl (C.sym∼ c) var-∈
ground-cast-source⊑ g Ans (∀ᶜ c)
    (I.∀⊑★ Ans′ A⊑★) B⊑★ I.bot-elim
    | zero∈A with source-occurs-target refl A⊑★ zero∈A
ground-cast-source⊑ g Ans (∀ᶜ c)
    (I.∀⊑★ Ans′ A⊑★) B⊑★ I.bot-elim
    | zero∈A | ()
ground-cast-source⊑ g Ans (∀ᶜ c) I.bot⊑★ B⊑★ I.bot-elim =
  I.bot-elim
ground-cast-source⊑ () Ans (c !) A⊑★ B⊑★ I.★⊑★
ground-cast-source⊑ {G = G} g Ans
    (C.inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★)
    (I.∀⊑ Anv′ zero∈A′ A⊑★) B⊑★ B⊑G =
  I.∀⊑ Anv′ zero∈A′
    (ground-cast-source⊑ {G = ⇑ᵗ G} (shift-ground g)
      (nonvar-occurs-nonstar Anv′ zero∈A′) c A⊑★
      (rename-⊑ suc fin-suc-injective (λ X eq → eq) B⊑★)
      (rename-⊑ suc fin-suc-injective (λ X eq → eq) B⊑G))
ground-cast-source⊑ g Ans
    (C.inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★)
    (I.∀⊑★ Ans′ A⊑★) B⊑★ B⊑G
    with source-occurs-target refl A⊑★ zero∈A
ground-cast-source⊑ g Ans
    (C.inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★)
    (I.∀⊑★ Ans′ A⊑★) B⊑★ B⊑G
    | ()
ground-cast-source⊑ ∀★ Ans
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★)
    A⊑★ B⊑★ (I.∀⊑∀ B⊑G)
    with source-occurs-target refl B⊑G zero∈B
ground-cast-source⊑ ∀★ Ans
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★)
    A⊑★ B⊑★ (I.∀⊑∀ B⊑G)
    | ()
ground-cast-source⊑ {A = A} {G = G} g Ans
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★)
    A⊑★ (I.∀⊑ Bnv′ zero∈B′ B⊑★) (I.∀⊑ Bnv″ zero∈B″ B⊑G) =
  unshift-⊑
    (ground-cast-source⊑ {A = ⇑ᵗ A} {B = _} {G = ⇑ᵗ G}
      (shift-ground g) (C.renameNonStar suc Ans) c
      (rename-⊑ suc fin-suc-injective (λ X eq → eq) A⊑★)
      B⊑★ B⊑G)
ground-cast-source⊑ g Ans
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★)
    A⊑★ (I.∀⊑★ Bns B⊑★) (I.∀⊑ Bnv′ zero∈B′ B⊑G)
    with source-occurs-target refl B⊑★ zero∈B
ground-cast-source⊑ g Ans
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★)
    A⊑★ (I.∀⊑★ Bns B⊑★) (I.∀⊑ Bnv′ zero∈B′ B⊑G)
    | ()
ground-cast-source⊑ ∀★ Ans bot-elim A⊑★ B⊑★ (I.∀⊑∀ B⊑G) =
  I.bot-elim
ground-cast-source⊑ ∀★ Ans bot-intro A⊑★ B⊑★ (I.∀⊑∀ B⊑G) =
  I.∀⊑∀ I.★⊑★
ground-cast-source⊑ ∀★ Ans bot-intro A⊑★ B⊑★ I.bot-elim =
  I.∀⊑∀ I.★⊑★

expand-cast-source⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {ν : Env∼ Δ}
    {A B G : Ty Δ}
  → (g : Ground G)
  → NonStar B
  → ν ⊢ G ∼ B
  → μ ⊢ A ⊑ ★
  → μ ⊢ A ⊑ B
  → μ ⊢ A ⊑ G
expand-cast-source⊑ g Bns c A⊑★ A⊑B =
  ground-cast-target⊑ g Bns (C.sym∼ c) A⊑B A⊑★

nonVar-zero⊥ : ∀ {Δ} → NonVar {Nat.suc Δ} (＇ zero) → ⊥
nonVar-zero⊥ ()

ground-targets-unique⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {A G H : Ty Δ}
  → Ground G
  → Ground H
  → μ ⊢ A ⊑ G
  → μ ⊢ A ⊑ H
  → G ≡ H
ground-targets-unique⊑ () gH I.★⊑★ qH
ground-targets-unique⊑ gG gH I.ι⊑ι I.ι⊑ι = refl
ground-targets-unique⊑ gG () I.ι⊑ι I.ι⊑★
ground-targets-unique⊑ gG gH I.X⊑X I.X⊑X = refl
ground-targets-unique⊑ gG () I.X⊑X (I.X⊑★ eq)
ground-targets-unique⊑ ★⇒★ ★⇒★
    (I.⇒⊑⇒ A⊑★ B⊑★) (I.⇒⊑⇒ A⊑★′ B⊑★′) =
  refl
ground-targets-unique⊑ ∀★ ∀★ (I.∀⊑∀ A⊑★)
    (I.∀⊑∀ A⊑★′) =
  refl
ground-targets-unique⊑ ∀★ gH (I.∀⊑∀ A⊑★)
    (I.∀⊑ Anv zero∈A A⊑H)
    with source-occurs-target refl A⊑★ zero∈A
ground-targets-unique⊑ ∀★ gH (I.∀⊑∀ A⊑★)
    (I.∀⊑ Anv zero∈A A⊑H) | ()
ground-targets-unique⊑ ∀★ ∀★ (I.∀⊑∀ A⊑★) I.bot-elim =
  refl
ground-targets-unique⊑ gG ∀★ (I.∀⊑ Anv zero∈A A⊑G)
    (I.∀⊑∀ A⊑★)
    with source-occurs-target refl A⊑★ zero∈A
ground-targets-unique⊑ gG ∀★ (I.∀⊑ Anv zero∈A A⊑G)
    (I.∀⊑∀ A⊑★) | ()
ground-targets-unique⊑ gG gH (I.∀⊑ Anv zero∈A A⊑G)
    (I.∀⊑ Anv′ zero∈A′ A⊑H) =
  shift-injectiveᵗ
    (ground-targets-unique⊑ (shift-ground gG) (shift-ground gH)
      A⊑G A⊑H)
ground-targets-unique⊑ gG gH (I.∀⊑ () zero∈A A⊑G) I.bot-elim
ground-targets-unique⊑ ∀★ ∀★ I.bot-elim (I.∀⊑∀ A⊑★) =
  refl
ground-targets-unique⊑ gG gH I.bot-elim
    (I.∀⊑ Anv zero∈A A⊑H) =
  ⊥-elim (nonVar-zero⊥ Anv)
ground-targets-unique⊑ ∀★ ∀★ I.bot-elim I.bot-elim = refl

variable-ground-other-impossible : ∀ {Δ} {ν : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → Ground G
  → ν ⊢ ＇ X ∼ G
  → ＇ X ≢ G
  → ⊥
variable-ground-other-impossible (＇ X) (id (＇ .X)) X≢X =
  X≢X refl
variable-ground-other-impossible ∀★
    ((C.gen_ ⦃ _ ⦄ ⦃ () ⦄ c) A≢★) X≢G

ground-cast-target-unique⊑ : ∀ {Δ} {μ : I.ImpEnv Δ}
    {ν : Env∼ Δ} {A B H G : Ty Δ}
  → Ground A
  → Ground H
  → Ground G
  → NonStar B
  → ν ⊢ B ∼ G
  → μ ⊢ A ⊑ H
  → μ ⊢ A ⊑ B
  → H ≡ G
ground-cast-target-unique⊑ {G = G}
    (＇ X) h g Bns c I.X⊑X I.X⊑X
    with G ≟Ty ＇ X
ground-cast-target-unique⊑ {G = G}
    (＇ X) h g Bns c I.X⊑X I.X⊑X
    | yes G≡X = sym G≡X
ground-cast-target-unique⊑ {G = G}
    (＇ X) h g Bns c I.X⊑X I.X⊑X
    | no G≢X =
  ⊥-elim (variable-ground-other-impossible g c
    (λ X≡G → G≢X (sym X≡G)))
ground-cast-target-unique⊑ (‵ ι) h g Bns c p q =
  ground-targets-unique⊑ h g p
    (ground-cast-target⊑ g Bns c q
      (ground-target-nonvar-to-star⊑ h nonvar-base p))
ground-cast-target-unique⊑ ★⇒★ h g Bns c p q =
  ground-targets-unique⊑ h g p
    (ground-cast-target⊑ g Bns c q
      (ground-target-nonvar-to-star⊑ h nonvar-fun p))
ground-cast-target-unique⊑ ∀★ h g Bns c p q =
  ground-targets-unique⊑ h g p
    (ground-cast-target⊑ g Bns c q
      (ground-target-nonvar-to-star⊑ h nonvar-all p))

shift-not-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A
  → suc X ∉ᵗ ⇑ᵗ A
shift-not-occurs = rename-not-occurs suc fin-suc-injective

zero-not-shift : ∀ {Δ} {A : Ty Δ}
  → zero ∈ᵗ ⇑ᵗ A
  → ⊥
zero-not-shift X∈ with rename-preimage X∈
zero-not-shift X∈ | found X () X∈A

zero-absent-shift : ∀ {Δ} (A : Ty Δ) → zero ∉ᵗ ⇑ᵗ A
zero-absent-shift A with occurs? zero (⇑ᵗ A)
zero-absent-shift A | present X∈A = ⊥-elim (zero-not-shift X∈A)
zero-absent-shift A | absent X∉A = X∉A

AvoidBoth : ∀ {Δ}
  → I.ImpEnv Δ
  → I.ImpEnv Δ
  → Ty Δ
  → Ty Δ
  → Set
AvoidBoth φ ψ A B = ∀ X
  → φ X ≡ I.X⊑★
  → ψ X ≡ I.X⊑★
  → (X ∉ᵗ A) × (X ∉ᵗ B)

identity-avoids-both : ∀ {Δ} {A B : Ty Δ}
  → AvoidBoth I.idᵐ I.idᵐ A B
identity-avoids-both X eqL eqR =
  ⊥-elim (var-identity-not-star eqL)

swap-avoid-both : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ A B
  → AvoidBoth ψ φ B A
swap-avoid-both safe X eqL eqR with safe X eqR eqL
swap-avoid-both safe X eqL eqR | X∉A , X∉B = X∉B , X∉A

avoid-arrow-domain : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B C D}
  → AvoidBoth φ ψ (A ⇒ B) (C ⇒ D)
  → AvoidBoth φ ψ A C
avoid-arrow-domain safe X eqL eqR with safe X eqL eqR
avoid-arrow-domain safe X eqL eqR
    | ∉-fun X∉A X∉B , ∉-fun X∉C X∉D = X∉A , X∉C

avoid-arrow-codomain : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B C D}
  → AvoidBoth φ ψ (A ⇒ B) (C ⇒ D)
  → AvoidBoth φ ψ B D
avoid-arrow-codomain safe X eqL eqR with safe X eqL eqR
avoid-arrow-codomain safe X eqL eqR
    | ∉-fun X∉A X∉B , ∉-fun X∉C X∉D = X∉B , X∉D

avoid-arrow-star-domain : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ (A ⇒ B) ★
  → AvoidBoth φ ψ A ★
avoid-arrow-star-domain safe X eqL eqR with safe X eqL eqR
avoid-arrow-star-domain safe X eqL eqR
    | ∉-fun X∉A X∉B , ∉-star = X∉A , ∉-star

avoid-arrow-star-codomain : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ (A ⇒ B) ★
  → AvoidBoth φ ψ B ★
avoid-arrow-star-codomain safe X eqL eqR with safe X eqL eqR
avoid-arrow-star-codomain safe X eqL eqR
    | ∉-fun X∉A X∉B , ∉-star = X∉B , ∉-star

avoid-star-arrow-domain : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ ★ (A ⇒ B)
  → AvoidBoth φ ψ ★ A
avoid-star-arrow-domain safe X eqL eqR with safe X eqL eqR
avoid-star-arrow-domain safe X eqL eqR
    | ∉-star , ∉-fun X∉A X∉B = ∉-star , X∉A

avoid-star-arrow-codomain : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ ★ (A ⇒ B)
  → AvoidBoth φ ψ ★ B
avoid-star-arrow-codomain safe X eqL eqR with safe X eqL eqR
avoid-star-arrow-codomain safe X eqL eqR
    | ∉-star , ∉-fun X∉A X∉B = ∉-star , X∉B

avoid-under-all : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ (`∀ A) (`∀ B)
  → AvoidBoth (I.extᵐ φ) (I.extᵐ ψ) A B
avoid-under-all safe zero eqL eqR =
  ⊥-elim (var-identity-not-star eqL)
avoid-under-all safe (suc X) eqL eqR with safe X eqL eqR
avoid-under-all safe (suc X) eqL eqR
    | ∉-all X∉A , ∉-all X∉B = X∉A , X∉B

avoid-under-all-star : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A}
  → AvoidBoth φ ψ (`∀ A) ★
  → AvoidBoth (I.extᵐ φ) (I.extᵐ ψ) A ★
avoid-under-all-star safe zero eqL eqR =
  ⊥-elim (var-identity-not-star eqL)
avoid-under-all-star safe (suc X) eqL eqR with safe X eqL eqR
avoid-under-all-star safe (suc X) eqL eqR
    | ∉-all X∉A , ∉-star = X∉A , ∉-star

avoid-under-star-all : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {B}
  → AvoidBoth φ ψ ★ (`∀ B)
  → AvoidBoth (I.extᵐ φ) (I.extᵐ ψ) ★ B
avoid-under-star-all safe zero eqL eqR =
  ⊥-elim (var-identity-not-star eqL)
avoid-under-star-all safe (suc X) eqL eqR with safe X eqL eqR
avoid-under-star-all safe (suc X) eqL eqR
    | ∉-star , ∉-all X∉B = ∉-star , X∉B

avoid-under-inst-star-right : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {B}
  → AvoidBoth φ ψ ★ B
  → AvoidBoth (I.extᵐ φ) (I.instᵐ ψ) ★ (⇑ᵗ B)
avoid-under-inst-star-right safe zero eqL eqR =
  ⊥-elim (var-identity-not-star eqL)
avoid-under-inst-star-right safe (suc X) eqL eqR
    with safe X eqL eqR
avoid-under-inst-star-right safe (suc X) eqL eqR
    | ∉-star , X∉B = ∉-star , shift-not-occurs X∉B

avoid-under-inst-star-left : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A}
  → AvoidBoth φ ψ A ★
  → AvoidBoth (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ A) ★
avoid-under-inst-star-left safe zero eqL eqR =
  ⊥-elim (var-identity-not-star eqR)
avoid-under-inst-star-left safe (suc X) eqL eqR
    with safe X eqL eqR
avoid-under-inst-star-left safe (suc X) eqL eqR
    | X∉A , ∉-star = shift-not-occurs X∉A , ∉-star

avoid-under-inst-right : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ (`∀ A) B
  → AvoidBoth (I.extᵐ φ) (I.instᵐ ψ) A (⇑ᵗ B)
avoid-under-inst-right safe zero eqL eqR =
  ⊥-elim (var-identity-not-star eqL)
avoid-under-inst-right safe (suc X) eqL eqR with safe X eqL eqR
avoid-under-inst-right safe (suc X) eqL eqR
    | ∉-all X∉A , X∉B = X∉A , shift-not-occurs X∉B

avoid-under-inst-left : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ A (`∀ B)
  → AvoidBoth (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ A) B
avoid-under-inst-left safe zero eqL eqR =
  ⊥-elim (var-identity-not-star eqR)
avoid-under-inst-left safe (suc X) eqL eqR with safe X eqL eqR
avoid-under-inst-left safe (suc X) eqL eqR
    | X∉A , ∉-all X∉B = shift-not-occurs X∉A , X∉B

avoid-under-inst-both : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A B}
  → AvoidBoth φ ψ A B
  → AvoidBoth (I.instᵐ φ) (I.instᵐ ψ) (⇑ᵗ A) (⇑ᵗ B)
avoid-under-inst-both {A = A} {B = B} safe zero eqL eqR =
  zero-absent-shift A , zero-absent-shift B
avoid-under-inst-both safe (suc X) eqL eqR with safe X eqL eqR
avoid-under-inst-both safe (suc X) eqL eqR | X∉A , X∉B =
  shift-not-occurs X∉A , shift-not-occurs X∉B

variable-to-star : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ X∼★
  → μ ⊢ ＇ X ∼ ★
variable-to-star eq =
  _! ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄

star-to-variable : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X
  → μ ⊢ ★ ∼ ＇ X
star-to-variable eq =
  ？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄

universal-ground-to-star : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ (`∀ ★) ∼ ★
universal-ground-to-star =
  _! ⦃ Gᵍ = ∀★ ⦄ (refl∼ (`∀ ★)) ⦃ nonstar-∀ ⦄

star-to-universal-ground : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ ★ ∼ (`∀ ★)
star-to-universal-ground =
  ？_ ⦃ Gᵍ = ∀★ ⦄ (refl∼ (`∀ ★)) ⦃ nonstar-∀ ⦄

bottom-to-star : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ (`∀ (＇ zero)) ∼ ★
bottom-to-star =
  _! ⦃ Gᵍ = ∀★ ⦄ bot-elim ⦃ nonstar-∀ ⦄

star-to-bottom : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ ★ ∼ (`∀ (＇ zero))
star-to-bottom =
  ？_ ⦃ Gᵍ = ∀★ ⦄ bot-intro ⦃ nonstar-∀ ⦄

factor-inst-star-lower : ∀ {Δ} {μ : Env∼ Δ}
    {A : Ty (Nat.suc Δ)}
  → instᵐ μ ⊢ A ∼ ★
  → NonVar A
  → zero ∈ᵗ A
  → μ ⊢ (`∀ A) ∼ ★
factor-inst-star-lower = C.factor-inst-starᶜ

factor-gen-star-lower : ∀ {Δ} {μ : Env∼ Δ}
    {B : Ty (Nat.suc Δ)}
  → genᵐ μ ⊢ ★ ∼ B
  → NonVar B
  → zero ∈ᵗ B
  → μ ⊢ ★ ∼ (`∀ B)
factor-gen-star-lower = C.factor-gen-starᶜ

right-variable-relation : ∀ {r l u}
  → VarLower r l u
  → (l ≡ I.X⊑★ → ⊥)
  → u ≡ I.X⊑★
  → r ≡ X∼★
right-variable-relation var-refl l≢★ u≡★ =
  ⊥-elim (var-identity-not-star u≡★)
right-variable-relation var-to-star l≢★ refl = refl
right-variable-relation var-from-star l≢★ u≡★ =
  ⊥-elim (var-identity-not-star u≡★)
right-variable-relation both-to-star l≢★ u≡★ =
  ⊥-elim (l≢★ refl)

left-variable-relation : ∀ {r l u}
  → VarLower r l u
  → (u ≡ I.X⊑★ → ⊥)
  → l ≡ I.X⊑★
  → r ≡ ★∼X
left-variable-relation var-refl u≢★ l≡★ =
  ⊥-elim (var-identity-not-star l≡★)
left-variable-relation var-to-star u≢★ l≡★ =
  ⊥-elim (var-identity-not-star l≡★)
left-variable-relation var-from-star u≢★ refl = refl
left-variable-relation both-to-star u≢★ l≡★ =
  ⊥-elim (u≢★ refl)

left-variable-env-not-star : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {X : TyVar Δ}
  → AvoidBoth φ ψ (＇ X) ★
  → ψ X ≡ I.X⊑★
  → φ X ≡ I.X⊑★
  → ⊥
left-variable-env-not-star safe eqR eqL with safe _ eqL eqR
left-variable-env-not-star safe eqR eqL
    | ∉-var X≢X , ∉-star = ≢ᶠ→≢ X≢X refl

right-variable-env-not-star : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {X : TyVar Δ}
  → AvoidBoth φ ψ ★ (＇ X)
  → φ X ≡ I.X⊑★
  → ψ X ≡ I.X⊑★
  → ⊥
right-variable-env-not-star safe eqL eqR with safe _ eqL eqR
right-variable-env-not-star safe eqL eqR
    | ∉-star , ∉-var X≢X = ≢ᶠ→≢ X≢X refl

close-shifted-consistency : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → extᵐ μ ⊢ ⇑ᵗ A ∼ ⇑ᵗ B
  → μ ⊢ A ∼ B
close-shifted-consistency {μ = μ} {A = A} {B = B} c =
  subst (λ B′ → μ ⊢ A ∼ B′) (shift-openᵗ B ★)
    (subst (λ A′ → μ ⊢ A′ ∼ (⇑ᵗ B) [ ★ ]ᵗ)
      (shift-openᵗ A ★) (c [ ★ ]ᶜ))

------------------------------------------------------------------------
-- A common lower bound implies consistency
------------------------------------------------------------------------

lower-bounds-consistentᵐ : ∀ {Δ} {μ : Env∼ Δ} {φ ψ}
    {D A B : Ty Δ}
  → LowerEnv μ φ ψ
  → AvoidBoth φ ψ A B
  → I._⊢_⊑_ φ D A
  → I._⊢_⊑_ ψ D B
  → μ ⊢ A ∼ B
lower-bounds-consistentᵐ h safe I.★⊑★ I.★⊑★ = id ★
lower-bounds-consistentᵐ h safe I.ι⊑ι I.ι⊑ι = id (‵ _)
lower-bounds-consistentᵐ h safe I.ι⊑ι I.ι⊑★ =
  _! ⦃ Gᵍ = ‵ _ ⦄ (id (‵ _)) ⦃ nonstar-ι ⦄
lower-bounds-consistentᵐ h safe I.ι⊑★ I.ι⊑ι =
  ？_ ⦃ Gᵍ = ‵ _ ⦄ (id (‵ _)) ⦃ nonstar-ι ⦄
lower-bounds-consistentᵐ h safe I.ι⊑★ I.ι⊑★ = id ★
lower-bounds-consistentᵐ {D = ＇ X} h safe I.X⊑X I.X⊑X =
  id (＇ X)
lower-bounds-consistentᵐ {D = ＇ X} h safe
    I.X⊑X (I.X⊑★ eqR) =
  variable-to-star
    (right-variable-relation (h X)
      (left-variable-env-not-star safe eqR) eqR)
lower-bounds-consistentᵐ {D = ＇ X} h safe
    (I.X⊑★ eqL) I.X⊑X =
  star-to-variable
    (left-variable-relation (h X)
      (right-variable-env-not-star safe eqL) eqL)
lower-bounds-consistentᵐ h safe (I.X⊑★ eqL) (I.X⊑★ eqR) =
  id ★
lower-bounds-consistentᵐ h safe
    (I.⇒⊑⇒ p₁ p₂) (I.⇒⊑⇒ q₁ q₂) =
  lower-bounds-consistentᵐ (flip-lower-env h)
    (swap-avoid-both (avoid-arrow-domain safe)) q₁ p₁ ↦
  lower-bounds-consistentᵐ h (avoid-arrow-codomain safe) p₂ q₂
lower-bounds-consistentᵐ h safe
    (I.⇒⊑⇒ p₁ p₂) (I.⇒⊑★ q₁ q₂) =
  _! ⦃ Gᵍ = ★⇒★ ⦄
    (lower-bounds-consistentᵐ (flip-lower-env h)
      (swap-avoid-both (avoid-arrow-star-domain safe)) q₁ p₁
      ↦
     lower-bounds-consistentᵐ h
       (avoid-arrow-star-codomain safe) p₂ q₂)
    ⦃ nonstar-⇒ ⦄
lower-bounds-consistentᵐ h safe
    (I.⇒⊑★ p₁ p₂) (I.⇒⊑⇒ q₁ q₂) =
  ？_ ⦃ Gᵍ = ★⇒★ ⦄
    (lower-bounds-consistentᵐ (flip-lower-env h)
      (swap-avoid-both (avoid-star-arrow-domain safe)) q₁ p₁
      ↦
     lower-bounds-consistentᵐ h
       (avoid-star-arrow-codomain safe) p₂ q₂)
    ⦃ nonstar-⇒ ⦄
lower-bounds-consistentᵐ h safe
    (I.⇒⊑★ p₁ p₂) (I.⇒⊑★ q₁ q₂) = id ★
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ p) (I.∀⊑∀ q) =
  ∀ᶜ (lower-bounds-consistentᵐ (extend-lower-env h)
    (avoid-under-all safe) p q)
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ p) (I.∀⊑★ Bns q) =
  _! ⦃ Gᵍ = ∀★ ⦄
    (∀ᶜ (lower-bounds-consistentᵐ (extend-lower-env h)
      (avoid-under-all-star safe) p q))
    ⦃ nonstar-∀ ⦄
lower-bounds-consistentᵐ h safe
    (I.∀⊑★ Ans p) (I.∀⊑∀ q) =
  ？_ ⦃ Gᵍ = ∀★ ⦄
    (∀ᶜ (lower-bounds-consistentᵐ (extend-lower-env h)
      (avoid-under-star-all safe) p q))
    ⦃ nonstar-∀ ⦄
lower-bounds-consistentᵐ {B = B} h safe
    (I.∀⊑∀ p) (I.∀⊑ Dnv z∈D q) with B ≟Ty ★
lower-bounds-consistentᵐ {B = B} h safe
    (I.∀⊑∀ p) (I.∀⊑ Dnv z∈D q) | no B≢★ =
  inst_ ⦃ source-nonvar-target p Dnv ⦄
    ⦃ source-occurs-target refl p z∈D ⦄
    (lower-bounds-consistentᵐ
      (instantiate-right-lower-env h)
      (avoid-under-inst-right safe) p q) B≢★
lower-bounds-consistentᵐ {B = .★} h safe
    (I.∀⊑∀ p) (I.∀⊑ Dnv z∈D q) | yes refl =
  factor-inst-star-lower
    (lower-bounds-consistentᵐ
      (instantiate-right-lower-env h)
      (avoid-under-inst-right safe) p q)
    (source-nonvar-target p Dnv)
    (source-occurs-target refl p z∈D)
lower-bounds-consistentᵐ {A = A} h safe
    (I.∀⊑ Dnv z∈D p) (I.∀⊑∀ q) with A ≟Ty ★
lower-bounds-consistentᵐ {A = A} h safe
    (I.∀⊑ Dnv z∈D p) (I.∀⊑∀ q) | no A≢★ =
  gen_ ⦃ source-nonvar-target q Dnv ⦄
    ⦃ source-occurs-target refl q z∈D ⦄
    (lower-bounds-consistentᵐ
      (instantiate-left-lower-env h)
      (avoid-under-inst-left safe) p q) A≢★
lower-bounds-consistentᵐ {A = .★} h safe
    (I.∀⊑ Dnv z∈D p) (I.∀⊑∀ q) | yes refl =
  factor-gen-star-lower
    (lower-bounds-consistentᵐ
      (instantiate-left-lower-env h)
      (avoid-under-inst-left safe) p q)
    (source-nonvar-target q Dnv)
    (source-occurs-target refl q z∈D)
lower-bounds-consistentᵐ h safe
    (I.∀⊑ Anv z∈D p) (I.∀⊑★ Bns q) =
  close-genᶜ
    (lower-bounds-consistentᵐ
      (instantiate-left-lower-env h)
      (avoid-under-inst-star-left safe) p q)
lower-bounds-consistentᵐ h safe
    (I.∀⊑★ Ans p) (I.∀⊑ Bnv z∈D q) =
  close-instᶜ
    (lower-bounds-consistentᵐ
      (instantiate-right-lower-env h)
      (avoid-under-inst-star-right safe) p q)
lower-bounds-consistentᵐ {A = A} {B = B} h safe
    (I.∀⊑ Anv z∈A p) (I.∀⊑ Bnv z∈B q) =
  close-shifted-consistency
    (lower-bounds-consistentᵐ
      (instantiate-both-lower-env h)
      (avoid-under-inst-both safe) p q)
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ I.★⊑★) I.∀★⊑★ = universal-ground-to-star
lower-bounds-consistentᵐ h safe
    I.∀★⊑★ (I.∀⊑∀ I.★⊑★) = star-to-universal-ground
lower-bounds-consistentᵐ h safe
    I.∀★⊑★ (I.∀⊑★ Bns q) = id ★
lower-bounds-consistentᵐ h safe
    (I.∀⊑★ Ans p) I.∀★⊑★ = id ★
lower-bounds-consistentᵐ h safe
    (I.∀⊑★ Ans p) (I.∀⊑★ Bns q) = id ★
lower-bounds-consistentᵐ h safe I.∀★⊑★ I.∀★⊑★ = id ★
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ I.X⊑X) I.bot-elim = bot-elim
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ I.X⊑X) I.bot⊑★ = bottom-to-star
lower-bounds-consistentᵐ h safe
    I.bot-elim (I.∀⊑∀ I.X⊑X) = bot-intro
lower-bounds-consistentᵐ h safe I.bot-elim I.bot-elim =
  refl∼ (`∀ ★)
lower-bounds-consistentᵐ h safe I.bot-elim (I.∀⊑★ Bns q)
    with source-occurs-target refl q var-∈
lower-bounds-consistentᵐ h safe I.bot-elim (I.∀⊑★ Bns q) | ()
lower-bounds-consistentᵐ h safe I.bot-elim I.bot⊑★ =
  universal-ground-to-star
lower-bounds-consistentᵐ h safe
    I.bot⊑★ (I.∀⊑∀ I.X⊑X) = star-to-bottom
lower-bounds-consistentᵐ h safe I.bot⊑★ I.bot-elim =
  star-to-universal-ground
lower-bounds-consistentᵐ h safe I.bot⊑★ (I.∀⊑★ Bns q)
    with source-occurs-target refl q var-∈
lower-bounds-consistentᵐ h safe I.bot⊑★ (I.∀⊑★ Bns q) | ()
lower-bounds-consistentᵐ h safe (I.∀⊑★ Ans p) I.bot-elim
    with source-occurs-target refl p var-∈
lower-bounds-consistentᵐ h safe (I.∀⊑★ Ans p) I.bot-elim | ()
lower-bounds-consistentᵐ h safe (I.∀⊑★ Ans p) I.bot⊑★
    with source-occurs-target refl p var-∈
lower-bounds-consistentᵐ h safe (I.∀⊑★ Ans p) I.bot⊑★ | ()
lower-bounds-consistentᵐ h safe I.bot⊑★ I.bot⊑★ = id ★

common-lower-consistent : ∀ {Δ} {A B : Ty Δ}
  → (∃[ D ] I._⊑_ D A × I._⊑_ D B)
  → A ∼ B
common-lower-consistent (D , D⊑A , D⊑B) =
  lower-bounds-consistentᵐ identity-lower-env
    identity-avoids-both D⊑A D⊑B

consistency-iff-common-lower : ∀ {Δ} {A B : Ty Δ}
  → ((c : A ∼ B) → CrossFree c
      → ∃[ D ] I._⊑_ D A × I._⊑_ D B)
    × ((∃[ D ] I._⊑_ D A × I._⊑_ D B) → A ∼ B)
consistency-iff-common-lower =
  consistent-common-lower , common-lower-consistent
