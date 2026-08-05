module proof.DGG.CastTermImprecision where

-- File Charter:
--   * Defines the compiler-facing fragment of typed cast-term imprecision.
--   * Indexes related terms by their exact type-imprecision derivation,
--     related term context, and relational runtime store.
--   * The runtime-store relation owns the type-imprecision environment and
--     classifies every type variable as both, left-only, or right-only.
--   * Proves reflexivity from cast typing and exports source/target typing
--     projections.
--   * Deliberately omits runtime-only rules until the DGG requires them.
--   * The more rules in this relation, the more cases to prove in the DGG.
--     So don't add rules unless they are absolutely necessary!
--     Avoid rules that are not syntax directed.

open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Fin using (zero)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-lift∋;
   S-bind∋)
open import TermCtx using (TermCtx; ⇑ᶜ)
import TermCtx as T
import Consistency as Con
open Con using (Env∼; _⊢_∼_; _↪ᵗ_; keep; skip; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; _⊢↑_; _⊢↓_)
open import Imprecision
open import Primitives using (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms
import GradualTermImprecision as GTI
open import proof.ImprecisionConsistency using (refl⊑)
open import proof.TypeInTermSubst using (typing-shiftᵗ-lift-inv)

------------------------------------------------------------------------
-- Relational runtime stores
------------------------------------------------------------------------

data LeadsToStar : ∀ {Δ} → TyStore Δ → Ty Δ → Set where
  leads-star : ∀ {Δ} {Σ : TyStore Δ}
      --------------------------------
    → LeadsToStar Σ ★

  leads-var : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ} {A : Ty Δ}
    → Σ ∋ X ⦂ A
    → LeadsToStar Σ A
      --------------------------------
    → LeadsToStar Σ (＇ X)

leads-zero-star : ∀ {Δ} {Σ : TyStore Δ}
  → LeadsToStar (store-bind Σ ★) (＇ zero)
leads-zero-star = leads-var (Z∋ refl) leads-star

leads-lift : ∀ {Δ} {Σ : TyStore Δ} {A : Ty Δ}
  → LeadsToStar Σ A
  → LeadsToStar (store-lift Σ) (⇑ᵗ A)
leads-lift leads-star = leads-star
leads-lift (leads-var X∈ A⇝★) =
  leads-var (S-lift∋ X∈ refl) (leads-lift A⇝★)

leads-bind : ∀ {Δ} {Σ : TyStore Δ} {A C : Ty Δ}
  → LeadsToStar Σ A
  → LeadsToStar (store-bind Σ C) (⇑ᵗ A)
leads-bind leads-star = leads-star
leads-bind (leads-var X∈ A⇝★) =
  leads-var (S-bind∋ X∈ refl) (leads-bind A⇝★)

data StoreCategories : ∀ {Δ}
    → ImpEnv Δ → TyStore Δ → TyStore Δ → Set where
  categories-empty :
    StoreCategories idᵐ store-empty store-empty

  categories-both-abstract : ∀ {Δ μ}
      {Σᴸ Σᴿ : TyStore Δ}
    → (v : VarImp)
    → StoreCategories μ Σᴸ Σᴿ
      -----------------------------------------------------------
    → StoreCategories (extendᵐ v μ)
        (store-lift Σᴸ) (store-lift Σᴿ)

  categories-both : ∀ {Δ μ} {Σᴸ Σᴿ : TyStore Δ} {A B : Ty Δ}
    → (v : VarImp)
    → StoreCategories μ Σᴸ Σᴿ
    → μ ⊢ A ⊑ B
      -----------------------------------------------------------
    → StoreCategories (extendᵐ v μ)
        (store-bind Σᴸ A) (store-bind Σᴿ B)

  categories-left-only : ∀ {Δ μ}
      {Σᴸ Σᴿ : TyStore Δ} {A : Ty Δ}
    → (v : VarImp)
    → StoreCategories μ Σᴸ Σᴿ
      -----------------------------------------------------------
    → StoreCategories (extendᵐ v μ)
        (store-bind Σᴸ A) (store-lift Σᴿ)

  categories-right-only : ∀ {Δ μ} {Σᴸ Σᴿ : TyStore Δ} {B : Ty Δ}
    → (v : VarImp)
    → StoreCategories μ Σᴸ Σᴿ
    → LeadsToStar Σᴿ B
      -----------------------------------------------------------
    → StoreCategories (extendᵐ v μ)
        (store-lift Σᴸ) (store-bind Σᴿ B)

record StoreImp (Δ : TyCtx) : Set where
  constructor stores
  field
    impEnvⁱ : ImpEnv Δ
    sourceStoreⁱ : TyStore Δ
    targetStoreⁱ : TyStore Δ
    categoriesⁱ :
      StoreCategories impEnvⁱ sourceStoreⁱ targetStoreⁱ

open StoreImp public

liftStoreImp : ∀ {Δ} → VarImp → StoreImp Δ → StoreImp (suc Δ)
liftStoreImp v (stores μ Σᴸ Σᴿ categories) =
  stores (extendᵐ v μ) (store-lift Σᴸ) (store-lift Σᴿ)
    (categories-both-abstract v categories)

rightOnlyStoreImp : ∀ {Δ} (ρ : StoreImp Δ) {B : Ty Δ}
  → LeadsToStar (targetStoreⁱ ρ) B
  → StoreImp (suc Δ)
rightOnlyStoreImp (stores μ Σᴸ Σᴿ categories) {B = B} B⇝★ =
  stores (instᵐ μ) (store-lift Σᴸ) (store-bind Σᴿ B)
    (categories-right-only X⊑★ categories B⇝★)

rightOnly★StoreImp : ∀ {Δ} → StoreImp Δ → StoreImp (suc Δ)
rightOnly★StoreImp ρ = rightOnlyStoreImp ρ leads-star

------------------------------------------------------------------------
-- Typed cast-term imprecision
------------------------------------------------------------------------

infix 4 _∣_⊢ᶜ_⊑_∶_

data _∣_⊢ᶜ_⊑_∶_ {Δ : TyCtx}
    (ρ : StoreImp Δ) (γ : GTI.CtxImp (impEnvⁱ ρ)) :
    Term Δ → Term Δ → {A B : Ty Δ}
    → impEnvⁱ ρ ⊢ A ⊑ B → Set where

  x⊑xᶜ : ∀ {x A B} {p : impEnvⁱ ρ ⊢ A ⊑ B}
    → γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A B p
      ------------------------------------------------
    → ρ ∣ γ ⊢ᶜ ` x ⊑ ` x ∶ p

  ƛ⊑ƛᶜ : ∀ {M M′ A A′ B B′}
      {pA : impEnvⁱ ρ ⊢ A ⊑ A′}
      {pB : impEnvⁱ ρ ⊢ B ⊑ B′}
    → ρ ∣ GTI.ctx-imp A A′ pA ∷ γ ⊢ᶜ M ⊑ M′ ∶ pB
      -----------------------------------------------------
    → ρ ∣ γ ⊢ᶜ ƛ M ⊑ ƛ M′ ∶ ⇒⊑⇒ pA pB

  ·⊑·ᶜ : ∀ {L L′ M M′ A A′ B B′}
      {pA : impEnvⁱ ρ ⊢ A ⊑ A′}
      {pB : impEnvⁱ ρ ⊢ B ⊑ B′}
    → ρ ∣ γ ⊢ᶜ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ pA
      --------------------------------------------------
    → ρ ∣ γ ⊢ᶜ L · M ⊑ L′ · M′ ∶ pB

  Λ⊑Λᶜ : ∀ {γ′ V V′ A B}
      {p : extᵐ (impEnvⁱ ρ) ⊢ A ⊑ B}
    → GTI.LiftCtxⁱ (extᵐ (impEnvⁱ ρ)) γ γ′
    → Value V
    → Value V′
    → liftStoreImp X⊑X ρ ∣ γ′ ⊢ᶜ V ⊑ V′ ∶ p
      -----------------------------------------------------
    → ρ ∣ γ ⊢ᶜ Λ V ⊑ Λ V′ ∶ ∀⊑∀ p

  Λ⊑ᶜ : ∀ {γ′ V M A B}
      {p : instᵐ (impEnvⁱ ρ) ⊢ A ⊑ ⇑ᵗ B}
    → (Anv : NonVar A)
    → (zero∈A : zero ∈ᵗ A)
    → GTI.LiftCtxⁱ (instᵐ (impEnvⁱ ρ)) γ γ′
    → Value V
    → liftStoreImp X⊑★ ρ ∣ γ′ ⊢ᶜ V ⊑ ⇑ᵗᵐ M ∶ p
      --------------------------------------------------
    → ρ ∣ γ ⊢ᶜ Λ V ⊑ M ∶ ∀⊑ Anv zero∈A p

  •⊑•ᶜ : ∀ {M M′ T T′ A B}
      {p : extᵐ (impEnvⁱ ρ) ⊢ A ⊑ B}
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ ∀⊑∀ p
    → (q : impEnvⁱ ρ ⊢ T ⊑ T′)
    → (r : impEnvⁱ ρ ⊢ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ)
      ------------------------------------------------------
    → ρ ∣ γ ⊢ᶜ M ⦂∀ A [ T ] ⊑ M′ ⦂∀ B [ T′ ] ∶ r

  •⊑ᶜ : ∀ {M M′ T A B Anv zero∈A}
      {p : instᵐ (impEnvⁱ ρ) ⊢ A ⊑ ⇑ᵗ B}
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ ∀⊑ Anv zero∈A p
    → (q : impEnvⁱ ρ ⊢ T ⊑ ★)
    → (r : impEnvⁱ ρ ⊢ A [ T ]ᵗ ⊑ B)
      ----------------------------------------------
    → ρ ∣ γ ⊢ᶜ M ⦂∀ A [ T ] ⊑ M′ ∶ r

  κ⊑κᶜ : ∀ (κ : Const)
    → (p : impEnvⁱ ρ ⊢ constTy κ ⊑ constTy κ)
      ------------------------------------------------------
    → ρ ∣ γ ⊢ᶜ $ κ ⊑ $ κ ∶ p

  cast⊑castᶜ : ∀ {M M′ C C′ A A′}
      {p : impEnvⁱ ρ ⊢ C ⊑ C′}
      {ν ν′ : Env∼ Δ}
    → (c : ν ⊢ C ∼ A)
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → (q : impEnvⁱ ρ ⊢ A ⊑ A′)
      ---------------------------------------
    → ρ ∣ γ ⊢ᶜ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑castᶜ : ∀ {M M′ A B B′}
      {p : impEnvⁱ ρ ⊢ A ⊑ B} {ν : Env∼ Δ}
    → (c′ : ν ⊢ B ∼ B′)
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → (q : impEnvⁱ ρ ⊢ A ⊑ B′)
      -------------------------------
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑revealᶜ : ∀ {M M′ A B B′}
      {p : impEnvⁱ ρ ⊢ A ⊑ B}
      {c′ : Conv↑ Δ B B′}
    → targetStoreⁱ ρ ⊢↑ c′
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → (q : impEnvⁱ ρ ⊢ A ⊑ B′)
      -------------------------------
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ↑ c′ ∶ q

  ⊑concealᶜ : ∀ {M M′ A B B′}
      {p : impEnvⁱ ρ ⊢ A ⊑ B}
      {c′ : Conv↓ Δ B B′}
    → targetStoreⁱ ρ ⊢↓ c′
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → (q : impEnvⁱ ρ ⊢ A ⊑ B′)
      -------------------------------
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ↓ c′ ∶ q

  cast⊑ᶜ : ∀ {M M′ A A′ B}
      {p : impEnvⁱ ρ ⊢ A ⊑ B} {ν : Env∼ Δ}
    → (c : ν ⊢ A ∼ A′)
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → (q : impEnvⁱ ρ ⊢ A′ ⊑ B)
      -------------------------------
    → ρ ∣ γ ⊢ᶜ M ⟨ c ⟩ ⊑ M′ ∶ q

  reveal⊑revealᶜ : ∀ {M M′ A A′ B B′}
      {p : impEnvⁱ ρ ⊢ A ⊑ A′}
      {c : Conv↑ Δ A B} {c′ : Conv↑ Δ A′ B′}
    → sourceStoreⁱ ρ ⊢↑ c
    → targetStoreⁱ ρ ⊢↑ c′
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → (q : impEnvⁱ ρ ⊢ B ⊑ B′)
      ---------------------------------------
    → ρ ∣ γ ⊢ᶜ M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑concealᶜ : ∀ {M M′ A A′ B B′}
      {p : impEnvⁱ ρ ⊢ A ⊑ A′}
      {c : Conv↓ Δ A B} {c′ : Conv↓ Δ A′ B′}
    → sourceStoreⁱ ρ ⊢↓ c
    → targetStoreⁱ ρ ⊢↓ c′
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → (q : impEnvⁱ ρ ⊢ B ⊑ B′)
      ---------------------------------------
    → ρ ∣ γ ⊢ᶜ M ↓ c ⊑ M′ ↓ c′ ∶ q

  blame⊑blameᶜ : ∀ {A B} (p : impEnvⁱ ρ ⊢ A ⊑ B)
      ----------------------------------------
    → ρ ∣ γ ⊢ᶜ blame ⊑ blame ∶ p

  ⊕⊑⊕ᶜ : (op : Prim)
    → ∀ {L L′ M M′}
      {p q : impEnvⁱ ρ ⊢ primArgTy op ⊑ primArgTy op}
    → ρ ∣ γ ⊢ᶜ L ⊑ L′ ∶ p
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ q
    → (r : impEnvⁱ ρ ⊢ primResultTy op ⊑ primResultTy op)
      --------------------------------------------------
    → ρ ∣ γ ⊢ᶜ L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ r

------------------------------------------------------------------------
-- Cast-term imprecision across different type contexts
------------------------------------------------------------------------

infix 4 _∣_∣_∣_⊢ᶜ_⊑_∶_

data VarCategory : Set where
  both left-only right-only : VarCategory

categoryAt : ∀ {Δ μ} {Σᴸ Σᴿ : TyStore Δ}
  → StoreCategories μ Σᴸ Σᴿ
  → TyVar Δ
  → VarCategory
categoryAt (categories-both-abstract v categories) zero = both
categoryAt (categories-both v categories p) zero = both
categoryAt (categories-left-only v categories) zero = left-only
categoryAt (categories-right-only v categories B⇝★) zero = right-only
categoryAt (categories-both-abstract v categories) (Fin.suc X) =
  categoryAt categories X
categoryAt (categories-both v categories p) (Fin.suc X) =
  categoryAt categories X
categoryAt (categories-left-only v categories) (Fin.suc X) =
  categoryAt categories X
categoryAt (categories-right-only v categories B⇝★) (Fin.suc X) =
  categoryAt categories X

data InImage {Δ₀ Δ : TyCtx}
    (η : Δ₀ ↪ᵗ Δ) (X : TyVar Δ) : Set where
  image : ∀ Y → toRenameᵗ η Y ≡ X → InImage η X

data ImageCategory {Δᴸ Δᴿ Δ : TyCtx}
    (ηᴸ : Δᴸ ↪ᵗ Δ) (ηᴿ : Δᴿ ↪ᵗ Δ) (X : TyVar Δ) :
    VarCategory → Set where
  image-both :
    InImage ηᴸ X →
    InImage ηᴿ X →
    ImageCategory ηᴸ ηᴿ X both

  image-left-only :
    InImage ηᴸ X →
    (InImage ηᴿ X → ⊥) →
    ImageCategory ηᴸ ηᴿ X left-only

  image-right-only :
    (InImage ηᴸ X → ⊥) →
    InImage ηᴿ X →
    ImageCategory ηᴸ ηᴿ X right-only

RenamingsCategorize : ∀ {Δᴸ Δᴿ Δ μ} {Σᴸ Σᴿ : TyStore Δ}
  → (ηᴸ : Δᴸ ↪ᵗ Δ)
  → (ηᴿ : Δᴿ ↪ᵗ Δ)
  → StoreCategories μ Σᴸ Σᴿ
  → Set
RenamingsCategorize {Δ = Δ} ηᴸ ηᴿ categories =
  (X : TyVar Δ) →
  ImageCategory ηᴸ ηᴿ X (categoryAt categories X)

image-skip-zero⊥ : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
  → InImage (skip η) zero
  → ⊥
image-skip-zero⊥ (image X ())

image-skip-suc : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ} {X : TyVar Δ}
  → InImage (skip η) (Fin.suc X)
  → InImage η X
image-skip-suc (image Y refl) = image Y refl

image-keep-suc : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ} {X : TyVar Δ}
  → InImage (keep η) (Fin.suc X)
  → InImage η X
image-keep-suc (image zero ())
image-keep-suc (image (Fin.suc Y) refl) = image Y refl

image-skip-lift : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ} {X : TyVar Δ}
  → InImage η X
  → InImage (skip η) (Fin.suc X)
image-skip-lift (image Y eq) = image Y (cong Fin.suc eq)

image-keep-lift : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ} {X : TyVar Δ}
  → InImage η X
  → InImage (keep η) (Fin.suc X)
image-keep-lift (image Y eq) = image (Fin.suc Y) (cong Fin.suc eq)

rightOnly-image-category : ∀ {Δᴸ Δᴿ Δ category}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ} {X : TyVar Δ}
  → ImageCategory ηᴸ ηᴿ X category
  → ImageCategory (skip ηᴸ) (keep ηᴿ) (Fin.suc X) category
rightOnly-image-category (image-both left right) =
  image-both (image-skip-lift left) (image-keep-lift right)
rightOnly-image-category (image-left-only left not-right) =
  image-left-only (image-skip-lift left) λ right →
    not-right (image-keep-suc right)
rightOnly-image-category (image-right-only not-left right) =
  image-right-only (λ left → not-left (image-skip-suc left))
    (image-keep-lift right)

rightOnly-renamings-categorize : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : StoreImp Δ} {B : Ty Δ}
  → (B⇝★ : LeadsToStar (targetStoreⁱ ρ) B)
  → RenamingsCategorize ηᴸ ηᴿ (categoriesⁱ ρ)
  → RenamingsCategorize (skip ηᴸ) (keep ηᴿ)
      (categoriesⁱ (rightOnlyStoreImp ρ B⇝★))
rightOnly-renamings-categorize {ρ = stores μ Σᴸ Σᴿ categories}
    B⇝★ categorize zero =
  image-right-only image-skip-zero⊥ (image zero refl)
rightOnly-renamings-categorize {ρ = stores μ Σᴸ Σᴿ categories}
    B⇝★ categorize (Fin.suc X) =
  rightOnly-image-category (categorize X)

data _∣_∣_∣_⊢ᶜ_⊑_∶_ {Δᴸ Δᴿ Δ}
    (ηᴸ : Δᴸ ↪ᵗ Δ) (ηᴿ : Δᴿ ↪ᵗ Δ)
    (ρ : StoreImp Δ) (γ : GTI.CtxImp (impEnvⁱ ρ))
    : Term Δᴸ → Term Δᴿ → {A B : Ty Δ}
    → impEnvⁱ ρ ⊢ A ⊑ B → Set where

  rename⊑renameᶜ : ∀ {M M′ A B}
      {p : impEnvⁱ ρ ⊢ A ⊑ B}
    → RenamingsCategorize ηᴸ ηᴿ (categoriesⁱ ρ)
    → ρ ∣ γ ⊢ᶜ renameᵗᵐ ηᴸ M ⊑ renameᵗᵐ ηᴿ M′ ∶ p
      ------------------------------------------------------
    → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p

------------------------------------------------------------------------
-- Typing projections
------------------------------------------------------------------------

mutual
  cast-term-imprecision-source-typing : ∀ {Δ} {ρ : StoreImp Δ}
      {γ : GTI.CtxImp (impEnvⁱ ρ)} {M M′ A B}
      {p : impEnvⁱ ρ ⊢ A ⊑ B}
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → ⟨ Δ , sourceStoreⁱ ρ , GTI.srcCtxⁱ γ ⟩ ⊢ M ⦂ A

  cast-term-imprecision-target-typing : ∀ {Δ} {ρ : StoreImp Δ}
      {γ : GTI.CtxImp (impEnvⁱ ρ)} {M M′ A B}
      {p : impEnvⁱ ρ ⊢ A ⊑ B}
    → ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
    → ⟨ Δ , targetStoreⁱ ρ , GTI.tgtCtxⁱ γ ⟩ ⊢ M′ ⦂ B

  cast-term-imprecision-source-typing (x⊑xᶜ x∈) =
    ⊢` (GTI.lookup-srcⁱ x∈)
  cast-term-imprecision-source-typing (ƛ⊑ƛᶜ M⊑M′) =
    ⊢ƛ (cast-term-imprecision-source-typing M⊑M′)
  cast-term-imprecision-source-typing (·⊑·ᶜ L⊑L′ M⊑M′) =
    ⊢· (cast-term-imprecision-source-typing L⊑L′)
      (cast-term-imprecision-source-typing M⊑M′)
  cast-term-imprecision-source-typing
      (Λ⊑Λᶜ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (GTI.srcCtxⁱ-lift liftγ)
        (cast-term-imprecision-source-typing V⊑V′))
  cast-term-imprecision-source-typing
      (Λ⊑ᶜ Anv zero∈A liftγ vV V⊑W) =
    ⊢Λ vV
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (GTI.srcCtxⁱ-lift liftγ)
        (cast-term-imprecision-source-typing V⊑W))
  cast-term-imprecision-source-typing (•⊑•ᶜ M⊑M′ q r) =
    ⊢• (cast-term-imprecision-source-typing M⊑M′)
  cast-term-imprecision-source-typing (•⊑ᶜ M⊑M′ q r) =
    ⊢• (cast-term-imprecision-source-typing M⊑M′)
  cast-term-imprecision-source-typing (κ⊑κᶜ κ p) =
    ⊢$ κ
  cast-term-imprecision-source-typing
      (cast⊑castᶜ c c′ M⊑M′ q) =
    ⊢⟨⟩ (cast-term-imprecision-source-typing M⊑M′) c
  cast-term-imprecision-source-typing (⊑castᶜ c′ M⊑M′ q) =
    cast-term-imprecision-source-typing M⊑M′
  cast-term-imprecision-source-typing (⊑revealᶜ c′⊢ M⊑M′ q) =
    cast-term-imprecision-source-typing M⊑M′
  cast-term-imprecision-source-typing (⊑concealᶜ c′⊢ M⊑M′ q) =
    cast-term-imprecision-source-typing M⊑M′
  cast-term-imprecision-source-typing (cast⊑ᶜ c M⊑M′ q) =
    ⊢⟨⟩ (cast-term-imprecision-source-typing M⊑M′) c
  cast-term-imprecision-source-typing
      (reveal⊑revealᶜ c⊢ c′⊢ M⊑M′ q) =
    ⊢reveal c⊢ (cast-term-imprecision-source-typing M⊑M′)
  cast-term-imprecision-source-typing
      (conceal⊑concealᶜ c⊢ c′⊢ M⊑M′ q) =
    ⊢conceal c⊢ (cast-term-imprecision-source-typing M⊑M′)
  cast-term-imprecision-source-typing (blame⊑blameᶜ p) =
    ⊢blame
  cast-term-imprecision-source-typing (⊕⊑⊕ᶜ op L⊑L′ M⊑M′ r) =
    ⊢⊕ op (cast-term-imprecision-source-typing L⊑L′)
      (cast-term-imprecision-source-typing M⊑M′)

  cast-term-imprecision-target-typing (x⊑xᶜ x∈) =
    ⊢` (GTI.lookup-tgtⁱ x∈)
  cast-term-imprecision-target-typing (ƛ⊑ƛᶜ M⊑M′) =
    ⊢ƛ (cast-term-imprecision-target-typing M⊑M′)
  cast-term-imprecision-target-typing (·⊑·ᶜ L⊑L′ M⊑M′) =
    ⊢· (cast-term-imprecision-target-typing L⊑L′)
      (cast-term-imprecision-target-typing M⊑M′)
  cast-term-imprecision-target-typing
      (Λ⊑Λᶜ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV′
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (GTI.tgtCtxⁱ-lift liftγ)
        (cast-term-imprecision-target-typing V⊑V′))
  cast-term-imprecision-target-typing
      (Λ⊑ᶜ Anv zero∈A liftγ vV V⊑W) =
    typing-shiftᵗ-lift-inv
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (GTI.tgtCtxⁱ-lift liftγ)
        (cast-term-imprecision-target-typing V⊑W))
  cast-term-imprecision-target-typing (•⊑•ᶜ M⊑M′ q r) =
    ⊢• (cast-term-imprecision-target-typing M⊑M′)
  cast-term-imprecision-target-typing (•⊑ᶜ M⊑M′ q r) =
    cast-term-imprecision-target-typing M⊑M′
  cast-term-imprecision-target-typing (κ⊑κᶜ κ p) =
    ⊢$ κ
  cast-term-imprecision-target-typing
      (cast⊑castᶜ c c′ M⊑M′ q) =
    ⊢⟨⟩ (cast-term-imprecision-target-typing M⊑M′) c′
  cast-term-imprecision-target-typing (⊑castᶜ c′ M⊑M′ q) =
    ⊢⟨⟩ (cast-term-imprecision-target-typing M⊑M′) c′
  cast-term-imprecision-target-typing (⊑revealᶜ c′⊢ M⊑M′ q) =
    ⊢reveal c′⊢ (cast-term-imprecision-target-typing M⊑M′)
  cast-term-imprecision-target-typing (⊑concealᶜ c′⊢ M⊑M′ q) =
    ⊢conceal c′⊢ (cast-term-imprecision-target-typing M⊑M′)
  cast-term-imprecision-target-typing (cast⊑ᶜ c M⊑M′ q) =
    cast-term-imprecision-target-typing M⊑M′
  cast-term-imprecision-target-typing
      (reveal⊑revealᶜ c⊢ c′⊢ M⊑M′ q) =
    ⊢reveal c′⊢ (cast-term-imprecision-target-typing M⊑M′)
  cast-term-imprecision-target-typing
      (conceal⊑concealᶜ c⊢ c′⊢ M⊑M′ q) =
    ⊢conceal c′⊢ (cast-term-imprecision-target-typing M⊑M′)
  cast-term-imprecision-target-typing (blame⊑blameᶜ p) =
    ⊢blame
  cast-term-imprecision-target-typing (⊕⊑⊕ᶜ op L⊑L′ M⊑M′ r) =
    ⊢⊕ op (cast-term-imprecision-target-typing L⊑L′)
      (cast-term-imprecision-target-typing M⊑M′)

------------------------------------------------------------------------
-- Reflexivity
------------------------------------------------------------------------

reflStoreImp : ∀ {Δ} → TyStore Δ → StoreImp Δ
reflStoreImp store-empty =
  stores idᵐ store-empty store-empty categories-empty
reflStoreImp (store-lift Σ) with reflStoreImp Σ
reflStoreImp (store-lift Σ) | stores μ Σᴸ Σᴿ categories =
  stores (extᵐ μ) (store-lift Σᴸ) (store-lift Σᴿ)
    (categories-both-abstract X⊑X categories)
reflStoreImp (store-bind Σ A) with reflStoreImp Σ
reflStoreImp (store-bind Σ A) | stores μ Σᴸ Σᴿ categories =
  stores (extᵐ μ) (store-bind Σᴸ A) (store-bind Σᴿ A)
    (categories-both X⊑X categories (refl⊑ A))

reflStoreImp-source : ∀ {Δ} (Σ : TyStore Δ)
  → sourceStoreⁱ (reflStoreImp Σ) ≡ Σ
reflStoreImp-source store-empty = refl
reflStoreImp-source (store-lift Σ)
    with reflStoreImp Σ | reflStoreImp-source Σ
reflStoreImp-source (store-lift Σ)
    | stores μ Σᴸ Σᴿ categories | eq =
  cong store-lift eq
reflStoreImp-source (store-bind Σ A)
    with reflStoreImp Σ | reflStoreImp-source Σ
reflStoreImp-source (store-bind Σ A)
    | stores μ Σᴸ Σᴿ categories | eq =
  cong (λ Σ′ → store-bind Σ′ A) eq

reflStoreImp-target : ∀ {Δ} (Σ : TyStore Δ)
  → targetStoreⁱ (reflStoreImp Σ) ≡ Σ
reflStoreImp-target store-empty = refl
reflStoreImp-target (store-lift Σ)
    with reflStoreImp Σ | reflStoreImp-target Σ
reflStoreImp-target (store-lift Σ)
    | stores μ Σᴸ Σᴿ categories | eq =
  cong store-lift eq
reflStoreImp-target (store-bind Σ A)
    with reflStoreImp Σ | reflStoreImp-target Σ
reflStoreImp-target (store-bind Σ A)
    | stores μ Σᴸ Σᴿ categories | eq =
  cong (λ Σ′ → store-bind Σ′ A) eq

reflCtx : ∀ {Δ} (μ : ImpEnv Δ) → TermCtx Δ → GTI.CtxImp μ
reflCtx μ [] = []
reflCtx μ (A ∷ Γ) = GTI.ctx-imp A A (refl⊑ A) ∷ reflCtx μ Γ

reflCtx-lift : ∀ {Δ} (μ : ImpEnv Δ) (Γ : TermCtx Δ)
  → GTI.LiftCtxⁱ (extᵐ μ) (reflCtx μ Γ)
      (reflCtx (extᵐ μ) (⇑ᶜ Γ))
reflCtx-lift μ [] = GTI.lift-[]
reflCtx-lift μ (A ∷ Γ) = GTI.lift-∷ (reflCtx-lift μ Γ)

reflCtx-lookup : ∀ {Δ} {μ : ImpEnv Δ} {Γ : TermCtx Δ} {x A}
  → Γ T.∋ x ⦂ A
  → reflCtx μ Γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A A (refl⊑ A)
reflCtx-lookup T.Z = GTI.Zⁱ
reflCtx-lookup (T.S x∈) = GTI.Sⁱ (reflCtx-lookup x∈)

reflᶜ : ∀ {Δ} {Σ : TyStore Δ}
    {Γ : TermCtx Δ} {M : Term Δ} {A : Ty Δ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → reflStoreImp Σ ∣ reflCtx (impEnvⁱ (reflStoreImp Σ)) Γ
      ⊢ᶜ M ⊑ M ∶ refl⊑ A
reflᶜ (⊢` x∈) = x⊑xᶜ (reflCtx-lookup x∈)
reflᶜ (⊢ƛ M⊢) = ƛ⊑ƛᶜ (reflᶜ M⊢)
reflᶜ (⊢· L⊢ M⊢) = ·⊑·ᶜ (reflᶜ L⊢) (reflᶜ M⊢)
reflᶜ (⊢Λ vM M⊢) =
  Λ⊑Λᶜ (reflCtx-lift _ _) vM vM (reflᶜ M⊢)
reflᶜ (⊢• {C = C} {A = A} M⊢) =
  •⊑•ᶜ (reflᶜ M⊢) (refl⊑ A) (refl⊑ (C [ A ]ᵗ))
reflᶜ (⊢$ κ) = κ⊑κᶜ κ (refl⊑ (constTy κ))
reflᶜ (⊢⊕ op L⊢ M⊢) =
  ⊕⊑⊕ᶜ op (reflᶜ L⊢) (reflᶜ M⊢)
    (refl⊑ (primResultTy op))
reflᶜ (⊢⟨⟩ M⊢ c) =
  cast⊑castᶜ c c (reflᶜ M⊢) (refl⊑ _)
reflᶜ {Σ = Σ} (⊢reveal {c = c} c⊢ M⊢) =
  reveal⊑revealᶜ
    (subst≡ (λ Σ′ → Σ′ ⊢↑ c) (sym (reflStoreImp-source Σ)) c⊢)
    (subst≡ (λ Σ′ → Σ′ ⊢↑ c) (sym (reflStoreImp-target Σ)) c⊢)
    (reflᶜ M⊢) (refl⊑ _)
reflᶜ {Σ = Σ} (⊢conceal {c = c} c⊢ M⊢) =
  conceal⊑concealᶜ
    (subst≡ (λ Σ′ → Σ′ ⊢↓ c) (sym (reflStoreImp-source Σ)) c⊢)
    (subst≡ (λ Σ′ → Σ′ ⊢↓ c) (sym (reflStoreImp-target Σ)) c⊢)
    (reflᶜ M⊢) (refl⊑ _)
reflᶜ ⊢blame = blame⊑blameᶜ (refl⊑ _)

⊑ᶜ-cong : ∀ {Δ} {ρ : StoreImp Δ}
    {γ : GTI.CtxImp (impEnvⁱ ρ)} {L L′ R R′ : Term Δ} {A B}
    {p : impEnvⁱ ρ ⊢ A ⊑ B}
  → L ≡ L′
  → R ≡ R′
  → ρ ∣ γ ⊢ᶜ L ⊑ R ∶ p
  → ρ ∣ γ ⊢ᶜ L′ ⊑ R′ ∶ p
⊑ᶜ-cong refl refl L⊑R = L⊑R
