module proof.Consistency where

-- File Charter:
--   * Proves that every closed type is consistent with the dynamic type.
--   * Derives the result from closed-type imprecision and the common-lower
--     characterization of consistency.
--   * Supplies consistency-side transport facts for renaming inverses.
--   * Supplies consistency-side safety facts for polymorphic generated casts.
--   * Depends on proof.Imprecision and proof.ImprecisionConsistency.

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Level using (0ℓ)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
import Imprecision as I
open import Consistency
open import CastTerms using (GenSafe; safe-⇒; safe-∀; safe-inst; safe-gen)
open import proof.Imprecision using (imprecise-star; ∈ᵗ-unique)
open import proof.ImprecisionConsistency
  using (common-lower-consistent; expand-cast-source⊑;
         consistency-source-occurs-target; ground-cast-source⊑;
         ground-targets-unique⊑; refl⊑)

private

  postulate
    funext : Extensionality 0ℓ 0ℓ

  ¬-unique : ∀ {A : Set} (p q : A → ⊥) → p ≡ q
  ¬-unique p q = funext (λ x → ⊥-elim (p x))

not-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A
  → X ∈ᵗ A
  → ⊥
not-occurs (∉-var X≠Y) var-∈ = X≠Y refl
not-occurs ∉-base ()
not-occurs ∉-star ()
not-occurs (∉-fun X∉A X∉B) (∈-fun-left X∈A) =
  not-occurs X∉A X∈A
not-occurs (∉-fun X∉A X∉B) (∈-fun-right X∉A′ X∈B) =
  not-occurs X∉B X∈B
not-occurs (∉-all X∉A) (∈-all X∈A) =
  not-occurs X∉A X∈A

consistent-star : ∀ (A : Ty 0) → A ∼ ★
consistent-star A = common-lower-consistent
  (A , refl⊑ A , imprecise-star A)

id-subst-env∼ : ∀ {Δ Δ′} {σ : Δ ⇒ˢ Δ′}
  → SubstEnv∼ idᶜ idᶜ σ
id-subst-env∼ {σ = σ} =
  subst-env∼ (λ X → refl∼ (σ X)) (λ X ()) (λ X ())

subst-rename-left-inverse : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {σ : Δ′ ⇒ˢ Δ}
  → (∀ X → σ (ρ X) ≡ ＇ X)
  → (A : Ty Δ)
  → substᵗ σ (renameᵗ ρ A) ≡ A
subst-rename-left-inverse {σ = σ} left A =
  trans (substᵗ-rename σ _ A)
    (trans (substᵗ-cong A left) (substᵗ-id A))

rename-left-inverse-injective : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {σ : Δ′ ⇒ˢ Δ} {A B : Ty Δ}
  → (∀ X → σ (ρ X) ≡ ＇ X)
  → renameᵗ ρ A ≡ renameᵗ ρ B
  → A ≡ B
rename-left-inverse-injective {σ = σ} {A = A} {B = B} left eq =
  trans (sym (subst-rename-left-inverse left A))
    (trans (cong (substᵗ σ) eq) (subst-rename-left-inverse left B))

rename-consistency-left-inverse : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {σ : Δ′ ⇒ˢ Δ} {A B : Ty Δ}
  → (∀ X → σ (ρ X) ≡ ＇ X)
  → renameᵗ ρ A ∼ renameᵗ ρ B
  → A ∼ B
rename-consistency-left-inverse {ρ = ρ} {σ = σ} {A = A} {B = B} left c =
  subst≡ (λ R → idᶜ ⊢ A ∼ R) (subst-rename-left-inverse left B)
    (subst≡ (λ L → idᶜ ⊢ L ∼ substᵗ σ (renameᵗ ρ B))
      (subst-rename-left-inverse left A)
      (subst∼ id-subst-env∼ c))

atom-unique : ∀ {Δ} {A : Ty Δ}
  → (a b : Atom A)
  → a ≡ b
atom-unique (＇ X) (＇ .X) = refl
atom-unique (‵ ι) (‵ .ι) = refl
atom-unique ★ ★ = refl

var∼-eq-X∼★-unique : ∀ {v}
  → (p q : v ≡ X∼★)
  → p ≡ q
var∼-eq-X∼★-unique {v = X∼X} ()
var∼-eq-X∼★-unique {v = X∼★} refl refl = refl
var∼-eq-X∼★-unique {v = ★∼X} ()

var∼-eq-★∼X-unique : ∀ {v}
  → (p q : v ≡ ★∼X)
  → p ≡ q
var∼-eq-★∼X-unique {v = X∼X} ()
var∼-eq-★∼X-unique {v = X∼★} ()
var∼-eq-★∼X-unique {v = ★∼X} refl refl = refl

∼★-unique : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
  → (c d : μ ⊢ A ∼★)
  → c ≡ d
∼★-unique ⇒∼★ ⇒∼★ = refl
∼★-unique ι∼★ ι∼★ = refl
∼★-unique (X∼★ᵍ eq) (X∼★ᵍ eq′)
    rewrite var∼-eq-X∼★-unique eq eq′ =
  refl
∼★-unique ∀∼★ ∀∼★ = refl

★∼-unique : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
  → (c d : μ ⊢★∼ A)
  → c ≡ d
★∼-unique ★∼⇒ ★∼⇒ = refl
★∼-unique ★∼ι ★∼ι = refl
★∼-unique (★∼Xᵍ eq) (★∼Xᵍ eq′)
    rewrite var∼-eq-★∼X-unique eq eq′ =
  refl
★∼-unique ★∼∀ ★∼∀ = refl

all-starᵐ : ∀ {Δ} → I.ImpEnv Δ
all-starᵐ X = I.X⊑★

data Shape : ∀ {Δ} → Ty Δ → Set where
  var-shape : ∀ {Δ X} → Shape {Δ} (＇ X)
  base-shape : ∀ {Δ ι} → Shape {Δ} (‵ ι)
  star-shape : ∀ {Δ} → Shape {Δ} ★
  fun-shape : ∀ {Δ A B}
    → Shape {Δ} A
    → Shape B
    → Shape (A ⇒ B)
  all-shape : ∀ {Δ A}
    → Shape {suc Δ} A
    → Shape (`∀ A)

shape : ∀ {Δ} (A : Ty Δ) → Shape A
shape (＇ X) = var-shape
shape (‵ ι) = base-shape
shape ★ = star-shape
shape (A ⇒ B) = fun-shape (shape A) (shape B)
shape (`∀ A) = all-shape (shape A)

data AllChoice {Δ : TyCtx} : Ty (suc Δ) → Set where
  bottom-choice : AllChoice (＇ Fin.zero)
  star-choice : AllChoice ★
  inst-choice : ∀ {A}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → AllChoice A
  structural-choice : ∀ {A}
    → NonStar A
    → Fin.zero ∉ᵗ A
    → AllChoice A

all-choice : ∀ {Δ} (A : Ty (suc Δ)) → AllChoice A
all-choice (＇ Fin.zero) = bottom-choice
all-choice (＇ (Fin.suc X)) =
  structural-choice nonstar-X (∉-var (λ ()))
all-choice (‵ ι) = structural-choice nonstar-ι ∉-base
all-choice ★ = star-choice
all-choice (A ⇒ B) with occurs? Fin.zero (A ⇒ B)
all-choice (A ⇒ B) | present zero∈A⇒B =
  inst-choice nonvar-fun zero∈A⇒B
all-choice (A ⇒ B) | absent zero∉A⇒B =
  structural-choice nonstar-⇒ zero∉A⇒B
all-choice (`∀ A) with occurs? Fin.zero (`∀ A)
all-choice (`∀ A) | present zero∈∀A =
  inst-choice nonvar-all zero∈∀A
all-choice (`∀ A) | absent zero∉∀A =
  structural-choice nonstar-∀ zero∉∀A

dynamic-domain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → (∀ X → X ∈ᵗ A ⇒ B → μ X ≡ I.X⊑★)
  → ∀ X → X ∈ᵗ A → μ X ≡ I.X⊑★
dynamic-domain dynamic X X∈A = dynamic X (∈-fun-left X∈A)

dynamic-codomain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → (∀ X → X ∈ᵗ A ⇒ B → μ X ≡ I.X⊑★)
  → ∀ X → X ∈ᵗ B → μ X ≡ I.X⊑★
dynamic-codomain {A = A} dynamic X X∈B with occurs? X A
dynamic-codomain dynamic X X∈B | present X∈A =
  dynamic X (∈-fun-left X∈A)
dynamic-codomain dynamic X X∈B | absent X∉A =
  dynamic X (∈-fun-right X∉A X∈B)

dynamic-under-inst : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty (suc Δ)}
  → (∀ X → X ∈ᵗ `∀ A → μ X ≡ I.X⊑★)
  → ∀ X → X ∈ᵗ A → I.instᵐ μ X ≡ I.X⊑★
dynamic-under-inst dynamic Fin.zero X∈A = refl
dynamic-under-inst dynamic (Fin.suc X) X∈A =
  dynamic X (∈-all X∈A)

dynamic-under-ext : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty (suc Δ)}
  → (∀ X → X ∈ᵗ `∀ A → μ X ≡ I.X⊑★)
  → Fin.zero ∉ᵗ A
  → ∀ X → X ∈ᵗ A → I.extᵐ μ X ≡ I.X⊑★
dynamic-under-ext dynamic zero∉A Fin.zero X∈A =
  ⊥-elim (not-occurs zero∉A X∈A)
dynamic-under-ext dynamic zero∉A (Fin.suc X) X∈A =
  dynamic X (∈-all X∈A)

to-star-shape : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ}
  → Shape A
  → (∀ X → X ∈ᵗ A → μ X ≡ I.X⊑★)
  → I._⊢_⊑_ μ A ★
to-star-shape var-shape dynamic = I.X⊑★ (dynamic _ var-∈)
to-star-shape base-shape dynamic = I.ι⊑★
to-star-shape star-shape dynamic = I.★⊑★
to-star-shape (fun-shape shape-A shape-B) dynamic =
  I.⇒⊑★
    (to-star-shape shape-A (dynamic-domain dynamic))
    (to-star-shape shape-B (dynamic-codomain dynamic))
to-star-shape (all-shape {A = A} shape-A) dynamic =
  decide (all-choice A)
  where
  decide : AllChoice A → I._⊢_⊑_ _ (`∀ A) ★
  decide bottom-choice = I.bot⊑★
  decide star-choice = I.∀★⊑★
  decide (inst-choice Anv zero∈A) =
    I.∀⊑ Anv zero∈A
      (to-star-shape shape-A (dynamic-under-inst dynamic))
  decide (structural-choice Ans zero∉A) =
    I.∀⊑★ Ans
      (to-star-shape shape-A (dynamic-under-ext dynamic zero∉A))

all-star-to-star : ∀ {Δ} (A : Ty Δ)
  → I._⊢_⊑_ all-starᵐ A ★
all-star-to-star A = to-star-shape (shape A) (λ X X∈A → refl)

tag-ground-unique : ∀ {Δ} {μ : Env∼ Δ} {A G H : Ty Δ}
  → NonStar A
  → (gG : Ground G)
  → (gH : Ground H)
  → μ ⊢ A ∼ G
  → μ ⊢ A ∼ H
  → G ≡ H
tag-ground-unique {A = A} {G = G} {H = H} Ans gG gH c d =
  ground-targets-unique⊑ gG gH
    (ground-cast-source⊑ {μ = all-starᵐ} gG Ans c
      (all-star-to-star A) (all-star-to-star G) (refl⊑ G))
    (ground-cast-source⊑ {μ = all-starᵐ} gH Ans d
      (all-star-to-star A) (all-star-to-star H) (refl⊑ H))

untag-ground-unique : ∀ {Δ} {μ : Env∼ Δ} {B G H : Ty Δ}
  → NonStar B
  → (gG : Ground G)
  → (gH : Ground H)
  → μ ⊢ G ∼ B
  → μ ⊢ H ∼ B
  → G ≡ H
untag-ground-unique {B = B} Bns gG gH c d =
  ground-targets-unique⊑ gG gH
    (expand-cast-source⊑ {μ = all-starᵐ} gG Bns c
      (all-star-to-star B) (refl⊑ B))
    (expand-cast-source⊑ {μ = all-starᵐ} gH Bns d
      (all-star-to-star B) (refl⊑ B))

------------------------------------------------------------------------
-- Polymorphic generated cast safety
------------------------------------------------------------------------

data Preimage {Δ Δ′ : TyCtx} (ρ : Δ ⇒ʳ Δ′) (Y : TyVar Δ′)
    (A : Ty Δ) : Set where
  found : (X : TyVar Δ) → ρ X ≡ Y → X ∈ᵗ A → Preimage ρ Y A

rename-preimage : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {Y : TyVar Δ′}
    {A : Ty Δ}
  → Y ∈ᵗ renameᵗ ρ A
  → Preimage ρ Y A
rename-preimage {A = ＇ X} var-∈ = found X refl var-∈
rename-preimage {A = ‵ ι} ()
rename-preimage {A = ★} ()
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    with rename-preimage Y∈A
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    | found X eq X∈A =
  found X eq (∈-fun-left X∈A)
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
    | found Fin.zero () X∈A
rename-preimage {A = `∀ A} (∈-all Y∈A)
    | found (Fin.suc X) refl X∈A =
  found X refl (∈-all X∈A)

zero-not-shift : ∀ {Δ} {A : Ty Δ} → Fin.zero ∈ᵗ ⇑ᵗ A → ⊥
zero-not-shift z∈ with rename-preimage z∈
zero-not-shift z∈ | found X () X∈A

shift-star-injective : ∀ {Δ} {A : Ty Δ}
  → ⇑ᵗ A ≡ ★
  → A ≡ ★
shift-star-injective {A = ＇ X} ()
shift-star-injective {A = ‵ ι} ()
shift-star-injective {A = ★} refl = refl
shift-star-injective {A = A ⇒ B} ()
shift-star-injective {A = `∀ A} ()

gen-safe′ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    {C B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ C ∼ B)
  → C ≡ ⇑ᵗ A
  → A ≢ ★
  → NonVar B
  → Fin.zero ∈ᵗ B
  → GenSafe c
gen-safe′ (id a) refl A≢★ Bnv z∈B =
  ⊥-elim (zero-not-shift z∈B)
gen-safe′ (c ↦ d) eq A≢★ Bnv z∈B = safe-⇒
gen-safe′ (∀ᶜ c) eq A≢★ Bnv z∈B = safe-∀
gen-safe′ (_! ⦃ g ⦄ c ⦃ Ans ⦄) eq A≢★ Bnv ()
gen-safe′ (？_ ⦃ g ⦄ c ⦃ Bns ⦄)
    eq A≢★ Bnv z∈B =
  ⊥-elim (A≢★ (shift-star-injective (sym eq)))
gen-safe′ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) eq A≢★ Bnv z∈B =
  safe-inst B≢★
gen-safe′ (gen_ {A = C} ⦃ Cnv ⦄ ⦃ z∈C ⦄ c C≢★)
    eq A≢★ Bnv z∈B =
  safe-gen C≢★ (gen-safe′ c refl C≢★ Cnv z∈C)
gen-safe′ bot-elim eq A≢★ Bnv (∈-all ())
gen-safe′ bot-intro eq A≢★ Bnv (∈-all ())

gen-safe : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ ⇑ᵗ A ∼ B)
  → A ≢ ★
  → NonVar B
  → Fin.zero ∈ᵗ B
  → GenSafe c
gen-safe c A≢★ Bnv z∈B = gen-safe′ c refl A≢★ Bnv z∈B
