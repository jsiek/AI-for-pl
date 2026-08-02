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
  using (_≡_; cong; refl; subst; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types
open import Consistency
import Imprecision as I

private
  variable
    Δ : TyCtx

------------------------------------------------------------------------
-- Environment alignment
------------------------------------------------------------------------

data VarLower : Var∼ → I.VarImp → I.VarImp → Set where
  var-refl : VarLower X∼X I.X⊑X I.X⊑X
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
identity-lower-env X = var-refl

right-star-from-var-lower : ∀ {r l u}
  → VarLower r l u
  → r ≡ X∼★
  → u ≡ I.X⊑★
right-star-from-var-lower var-refl ()
right-star-from-var-lower var-to-star refl = refl
right-star-from-var-lower var-from-star ()
right-star-from-var-lower both-to-star ()

left-star-from-var-lower : ∀ {r l u}
  → VarLower r l u
  → r ≡ ★∼X
  → l ≡ I.X⊑★
left-star-from-var-lower var-refl ()
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

rename-not-occurs : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → X ∉ᵗ A
  → ρ X ∉ᵗ renameᵗ ρ A
rename-not-occurs ρ injective (∉-var X≢Y) =
  ∉-var (λ eq → X≢Y (injective eq))
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

------------------------------------------------------------------------
-- Consistency implies a common lower bound
------------------------------------------------------------------------

consistent-common-lowerᵐ : ∀ {Δ} {μ : Env∼ Δ} {φ ψ}
    {A B : Ty Δ}
  → LowerEnv μ φ ψ
  → μ ⊢ A ∼ B
  → ∃[ D ] I._⊢_⊑_ φ D A × I._⊢_⊑_ ψ D B
consistent-common-lowerᵐ h (id ★) = ★ , I.★⊑★ , I.★⊑★
consistent-common-lowerᵐ h (id (‵ ι)) = ‵ ι , I.ι⊑ι , I.ι⊑ι
consistent-common-lowerᵐ h (id (＇ X)) = ＇ X , I.X⊑X , I.X⊑X
consistent-common-lowerᵐ h (c ↦ d)
    with consistent-common-lowerᵐ h c
       | consistent-common-lowerᵐ h d
consistent-common-lowerᵐ h (c ↦ d)
    | A , A⊑L , A⊑R | B , B⊑L , B⊑R =
  A ⇒ B , I.⇒⊑⇒ A⊑L B⊑L , I.⇒⊑⇒ A⊑R B⊑R
consistent-common-lowerᵐ h (∀ᶜ c)
    with consistent-common-lowerᵐ (extend-lower-env h) c
consistent-common-lowerᵐ h (∀ᶜ c) | D , D⊑A , D⊑B =
  `∀ D , I.∀⊑∀ D⊑A , I.∀⊑∀ D⊑B
consistent-common-lowerᵐ h
    (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match-⇒ ⦄)
    with consistent-common-lowerᵐ h c
consistent-common-lowerᵐ h
    (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match-⇒ ⦄)
    | D , D⊑A , D⊑G =
  D , D⊑A , arrow-right-to-star h D⊑G
consistent-common-lowerᵐ h
    (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match-ι ⦄)
    with consistent-common-lowerᵐ h c
consistent-common-lowerᵐ h
    (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match-ι ⦄)
    | D , D⊑A , D⊑G =
  D , D⊑A , base-right-to-star h D⊑G
consistent-common-lowerᵐ h
    (_! ⦃ g-X eq ⦄ c ⦃ Ans ⦄ ⦃ match-X ⦄)
    with consistent-common-lowerᵐ h c
consistent-common-lowerᵐ h
    (_! ⦃ g-X eq ⦄ c ⦃ Ans ⦄ ⦃ match-X ⦄)
    | D , D⊑A , D⊑G =
  D , D⊑A , var-right-to-star h eq D⊑G
consistent-common-lowerᵐ h
    (_! ⦃ g-∀ ⦄ c ⦃ Ans ⦄ ⦃ match-∀ ⦄) =
  `∀ ★ , refl⊑ (`∀ ★) , I.∀★⊑★
consistent-common-lowerᵐ h
    (_! ⦃ g-∀ ⦄ c ⦃ Ans ⦄ ⦃ match-⊥ ⦄) =
  `∀ (＇ zero) , refl⊑ (`∀ (＇ zero)) , I.bot⊑★
consistent-common-lowerᵐ h
    (？_ ⦃ g-⇒ ⦄ c ⦃ Bns ⦄ ⦃ match-⇒ ⦄)
    with consistent-common-lowerᵐ h c
consistent-common-lowerᵐ h
    (？_ ⦃ g-⇒ ⦄ c ⦃ Bns ⦄ ⦃ match-⇒ ⦄)
    | D , D⊑G , D⊑B =
  D , arrow-left-to-star h D⊑G , D⊑B
consistent-common-lowerᵐ h
    (？_ ⦃ g-ι ⦄ c ⦃ Bns ⦄ ⦃ match-ι ⦄)
    with consistent-common-lowerᵐ h c
consistent-common-lowerᵐ h
    (？_ ⦃ g-ι ⦄ c ⦃ Bns ⦄ ⦃ match-ι ⦄)
    | D , D⊑G , D⊑B =
  D , base-left-to-star h D⊑G , D⊑B
consistent-common-lowerᵐ h
    (？_ ⦃ g-X eq ⦄ c ⦃ Bns ⦄ ⦃ match-X ⦄)
    with consistent-common-lowerᵐ h c
consistent-common-lowerᵐ h
    (？_ ⦃ g-X eq ⦄ c ⦃ Bns ⦄ ⦃ match-X ⦄)
    | D , D⊑G , D⊑B =
  D , var-left-to-star h eq D⊑G , D⊑B
consistent-common-lowerᵐ h
    (？_ ⦃ g-∀ ⦄ c ⦃ Bns ⦄ ⦃ match-∀ ⦄) =
  `∀ ★ , I.∀★⊑★ , refl⊑ (`∀ ★)
consistent-common-lowerᵐ h
    (？_ ⦃ g-∀ ⦄ c ⦃ Bns ⦄ ⦃ match-⊥ ⦄) =
  `∀ (＇ zero) , I.bot⊑★ , refl⊑ (`∀ (＇ zero))
consistent-common-lowerᵐ h
    (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    with consistent-common-lowerᵐ
      (instantiate-right-lower-env h) c
consistent-common-lowerᵐ h
    (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    | D , D⊑A , D⊑B =
  `∀ D , I.∀⊑∀ D⊑A ,
  I.∀⊑ (source-nonvar-from-target D⊑A Anv z∈A)
    (target-occurs-source D⊑A z∈A) D⊑B
consistent-common-lowerᵐ h
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    with consistent-common-lowerᵐ
      (instantiate-left-lower-env h) c
consistent-common-lowerᵐ h
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    | D , D⊑A , D⊑B =
  `∀ D ,
  I.∀⊑ (source-nonvar-from-target D⊑B Bnv z∈B)
    (target-occurs-source D⊑B z∈B) D⊑A ,
  I.∀⊑∀ D⊑B
consistent-common-lowerᵐ h bot-elim =
  `∀ (＇ zero) , refl⊑ (`∀ (＇ zero)) , I.bot-elim
consistent-common-lowerᵐ h bot-intro =
  `∀ (＇ zero) , I.bot-elim , refl⊑ (`∀ (＇ zero))

consistent-common-lower : ∀ {Δ} {A B : Ty Δ}
  → A ∼ B
  → ∃[ D ] I._⊑_ D A × I._⊑_ D B
consistent-common-lower = consistent-common-lowerᵐ identity-lower-env

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
source-occurs-target focus I.bot-elim (∈-all ())
source-occurs-target focus I.bot⊑★ (∈-all ())

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
  _! ⦃ g-X eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄ ⦃ match-X ⦄

star-to-variable : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ}
  → μ X ≡ ★∼X
  → μ ⊢ ★ ∼ ＇ X
star-to-variable eq =
  ？_ ⦃ g-X eq ⦄ (id (＇ _)) ⦃ nonstar-X ⦄ ⦃ match-X ⦄

universal-ground-to-star : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ (`∀ ★) ∼ ★
universal-ground-to-star =
  _! ⦃ g-∀ ⦄ (refl∼ (`∀ ★)) ⦃ nonstar-∀ ⦄ ⦃ match-∀ ⦄

star-to-universal-ground : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ ★ ∼ (`∀ ★)
star-to-universal-ground =
  ？_ ⦃ g-∀ ⦄ (refl∼ (`∀ ★)) ⦃ nonstar-∀ ⦄ ⦃ match-∀ ⦄

bottom-to-star : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ (`∀ (＇ zero)) ∼ ★
bottom-to-star =
  _! ⦃ g-∀ ⦄ bot-elim ⦃ nonstar-∀ ⦄ ⦃ match-⊥ ⦄

star-to-bottom : ∀ {Δ} {μ : Env∼ Δ}
  → μ ⊢ ★ ∼ (`∀ (＇ zero))
star-to-bottom =
  ？_ ⦃ g-∀ ⦄ bot-intro ⦃ nonstar-∀ ⦄ ⦃ match-⊥ ⦄

factor-inst-star-lower : ∀ {Δ} {μ : Env∼ Δ}
    {A : Ty (Nat.suc Δ)}
  → instᵐ μ ⊢ A ∼ ★
  → NonVar A
  → zero ∈ᵗ A
  → μ ⊢ (`∀ A) ∼ ★
factor-inst-star-lower (id ★) Anv ()
factor-inst-star-lower
    (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match-⇒ ⦄) Anv z∈A =
  _! ⦃ g-⇒ ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
    ⦃ nonstar-∀ ⦄ ⦃ match-⇒ ⦄
factor-inst-star-lower
    (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match-ι ⦄) Anv z∈A =
  _! ⦃ g-ι ⦄ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c (λ ()))
    ⦃ nonstar-∀ ⦄ ⦃ match-ι ⦄
factor-inst-star-lower
    (_! ⦃ g-X eq ⦄ c ⦃ Ans ⦄ ⦃ match-X ⦄) () z∈A
factor-inst-star-lower
    (_! ⦃ g-∀ ⦄ c ⦃ Ans ⦄ ⦃ match-∀ ⦄) Anv (∈-all ())
factor-inst-star-lower
    (_! ⦃ g-∀ ⦄ c ⦃ Ans ⦄ ⦃ match-⊥ ⦄) Anv (∈-all ())
factor-inst-star-lower
    (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) Anv ()
factor-inst-star-lower
    (inst_ ⦃ Anv′ ⦄ ⦃ z∈A′ ⦄ c ★≢★) Anv z∈A =
  ⊥-elim (★≢★ refl)

factor-gen-star-lower : ∀ {Δ} {μ : Env∼ Δ}
    {B : Ty (Nat.suc Δ)}
  → genᵐ μ ⊢ ★ ∼ B
  → NonVar B
  → zero ∈ᵗ B
  → μ ⊢ ★ ∼ (`∀ B)
factor-gen-star-lower (id ★) Bnv ()
factor-gen-star-lower
    (_! ⦃ g ⦄ c ⦃ () ⦄ ⦃ match ⦄) Bnv z∈B
factor-gen-star-lower
    (？_ ⦃ g-⇒ ⦄ c ⦃ Bns ⦄ ⦃ match-⇒ ⦄) Bnv z∈B =
  ？_ ⦃ g-⇒ ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
    ⦃ nonstar-∀ ⦄ ⦃ match-⇒ ⦄
factor-gen-star-lower
    (？_ ⦃ g-ι ⦄ c ⦃ Bns ⦄ ⦃ match-ι ⦄) Bnv z∈B =
  ？_ ⦃ g-ι ⦄ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ()))
    ⦃ nonstar-∀ ⦄ ⦃ match-ι ⦄
factor-gen-star-lower
    (？_ ⦃ g-X eq ⦄ c ⦃ Bns ⦄ ⦃ match-X ⦄) () z∈B
factor-gen-star-lower
    (？_ ⦃ g-∀ ⦄ c ⦃ Bns ⦄ ⦃ match-∀ ⦄) Bnv (∈-all ())
factor-gen-star-lower
    (？_ ⦃ g-∀ ⦄ c ⦃ Bns ⦄ ⦃ match-⊥ ⦄) Bnv (∈-all ())
factor-gen-star-lower
    (gen_ ⦃ Bnv′ ⦄ ⦃ z∈B′ ⦄ c ★≢★) Bnv z∈B =
  ⊥-elim (★≢★ refl)

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
    | ∉-var X≢X , ∉-star = X≢X refl

right-variable-env-not-star : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {X : TyVar Δ}
  → AvoidBoth φ ψ ★ (＇ X)
  → φ X ≡ I.X⊑★
  → ψ X ≡ I.X⊑★
  → ⊥
right-variable-env-not-star safe eqL eqR with safe _ eqL eqR
right-variable-env-not-star safe eqL eqR
    | ∉-star , ∉-var X≢X = X≢X refl

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
  _! ⦃ g-ι ⦄ (id (‵ _)) ⦃ nonstar-ι ⦄ ⦃ match-ι ⦄
lower-bounds-consistentᵐ h safe I.ι⊑★ I.ι⊑ι =
  ？_ ⦃ g-ι ⦄ (id (‵ _)) ⦃ nonstar-ι ⦄ ⦃ match-ι ⦄
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
  lower-bounds-consistentᵐ h (avoid-arrow-domain safe) p₁ q₁ ↦
  lower-bounds-consistentᵐ h (avoid-arrow-codomain safe) p₂ q₂
lower-bounds-consistentᵐ h safe
    (I.⇒⊑⇒ p₁ p₂) (I.⇒⊑★ q₁ q₂) =
  _! ⦃ g-⇒ ⦄
    (lower-bounds-consistentᵐ h (avoid-arrow-star-domain safe) p₁ q₁
      ↦
     lower-bounds-consistentᵐ h
       (avoid-arrow-star-codomain safe) p₂ q₂)
    ⦃ nonstar-⇒ ⦄ ⦃ match-⇒ ⦄
lower-bounds-consistentᵐ h safe
    (I.⇒⊑★ p₁ p₂) (I.⇒⊑⇒ q₁ q₂) =
  ？_ ⦃ g-⇒ ⦄
    (lower-bounds-consistentᵐ h (avoid-star-arrow-domain safe) p₁ q₁
      ↦
     lower-bounds-consistentᵐ h
       (avoid-star-arrow-codomain safe) p₂ q₂)
    ⦃ nonstar-⇒ ⦄ ⦃ match-⇒ ⦄
lower-bounds-consistentᵐ h safe
    (I.⇒⊑★ p₁ p₂) (I.⇒⊑★ q₁ q₂) = id ★
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ p) (I.∀⊑∀ q) =
  ∀ᶜ (lower-bounds-consistentᵐ (extend-lower-env h)
    (avoid-under-all safe) p q)
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
lower-bounds-consistentᵐ h safe I.∀★⊑★ I.∀★⊑★ = id ★
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ I.X⊑X) I.bot-elim = bot-elim
lower-bounds-consistentᵐ h safe
    (I.∀⊑∀ I.X⊑X) I.bot⊑★ = bottom-to-star
lower-bounds-consistentᵐ h safe
    I.bot-elim (I.∀⊑∀ I.X⊑X) = bot-intro
lower-bounds-consistentᵐ h safe I.bot-elim I.bot-elim =
  refl∼ (`∀ ★)
lower-bounds-consistentᵐ h safe I.bot-elim I.bot⊑★ =
  universal-ground-to-star
lower-bounds-consistentᵐ h safe
    I.bot⊑★ (I.∀⊑∀ I.X⊑X) = star-to-bottom
lower-bounds-consistentᵐ h safe I.bot⊑★ I.bot-elim =
  star-to-universal-ground
lower-bounds-consistentᵐ h safe I.bot⊑★ I.bot⊑★ = id ★

common-lower-consistent : ∀ {Δ} {A B : Ty Δ}
  → (∃[ D ] I._⊑_ D A × I._⊑_ D B)
  → A ∼ B
common-lower-consistent (D , D⊑A , D⊑B) =
  lower-bounds-consistentᵐ identity-lower-env
    identity-avoids-both D⊑A D⊑B

consistency-iff-common-lower : ∀ {Δ} {A B : Ty Δ}
  → (A ∼ B → ∃[ D ] I._⊑_ D A × I._⊑_ D B)
    × ((∃[ D ] I._⊑_ D A × I._⊑_ D B) → A ∼ B)
consistency-iff-common-lower =
  consistent-common-lower , common-lower-consistent
