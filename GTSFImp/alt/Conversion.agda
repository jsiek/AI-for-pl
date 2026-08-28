module alt.Conversion where

-- File Charter:
--   * Defines raw, endpoint-free reveal and conceal conversion shapes.
--   * Defines the self-contained scoped conversion-typing judgments.
--   * Expands raw identity leaves against a type so shape substitution
--     remains typed when a universal variable becomes structural.
--   * Provides weakening and strengthening views for ground tags.
--   * Provides type-directed shape generators and their typing proofs.
--   * Depends only on Types: stores, anchors, and classifiers are node data.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types

private
  variable
    Δ : TyCtx

------------------------------------------------------------------------
-- Inserting one scoped-variable type variable
------------------------------------------------------------------------

punchIn : ∀ {Δ} → Fin (Nat.suc Δ) → Fin Δ → Fin (Nat.suc Δ)
punchIn zero Y = suc Y
punchIn (suc X) zero = zero
punchIn (suc X) (suc Y) = suc (punchIn X Y)

punchOut : ∀ {n} (Y X : Fin (Nat.suc n)) → Y ≢ X → Fin n
punchOut zero zero Y≢X = ⊥-elim (Y≢X refl)
punchOut zero (suc X) Y≢X = X
punchOut {n = Nat.suc n} (suc Y) zero Y≢X = zero
punchOut {n = Nat.suc n} (suc Y) (suc X) Y≢X =
  suc (punchOut Y X (λ Y≡X → Y≢X (cong suc Y≡X)))

wkᵗ : ∀ {Δ} → Fin (Nat.suc Δ) → Ty Δ → Ty (Nat.suc Δ)
wkᵗ X = renameᵗ (punchIn X)

------------------------------------------------------------------------
-- Replacing one abstract type by its representation
------------------------------------------------------------------------

replaceTy : TyVar Δ → Ty Δ → Ty Δ → Ty Δ
replaceTy X R (＇ Y) with X ≟ Y
replaceTy X R (＇ .X) | yes refl = R
replaceTy X R (＇ Y) | no X≠Y = ＇ Y
replaceTy X R (‵ ι) = ‵ ι
replaceTy X R ★ = ★
replaceTy X R (A ⇒ B) = replaceTy X R A ⇒ replaceTy X R B
replaceTy X R (`∀ A) = `∀ (replaceTy (suc X) (⇑ᵗ R) A)

------------------------------------------------------------------------
-- Resolving one scoped-variable type variable
------------------------------------------------------------------------

-- Resolution removes Y and replaces it by the representation C.  This lives
-- with insertion because telescope deletion and the dynamic rules share the
-- same scoped substitution.

private
  resolved-punchIn≢ : ∀ {n} (Y : Fin (Nat.suc n)) (X : Fin n)
    → Y ≢ punchIn Y X
  resolved-punchIn≢ zero X ()
  resolved-punchIn≢ (suc Y) zero ()
  resolved-punchIn≢ (suc Y) (suc X) eq =
    resolved-punchIn≢ Y X (suc-injective eq)
    where
    suc-injective : ∀ {m} {Z W : Fin m} → suc Z ≡ suc W → Z ≡ W
    suc-injective refl = refl

  resolved-punchOut-punchIn : ∀ {n} (Y : Fin (Nat.suc n))
      (X : Fin n)
      (Y≢X : Y ≢ punchIn Y X)
    → punchOut Y (punchIn Y X) Y≢X ≡ X
  resolved-punchOut-punchIn zero X Y≢X = refl
  resolved-punchOut-punchIn (suc Y) zero Y≢X = refl
  resolved-punchOut-punchIn (suc Y) (suc X) Y≢X =
    cong suc (resolved-punchOut-punchIn Y X _)

  punchIn-resolved-punchOut : ∀ {n} (Y X : Fin (Nat.suc n))
      (Y≢X : Y ≢ X)
    → punchIn Y (punchOut Y X Y≢X) ≡ X
  punchIn-resolved-punchOut zero zero Y≢X = ⊥-elim (Y≢X refl)
  punchIn-resolved-punchOut zero (suc X) Y≢X = refl
  punchIn-resolved-punchOut {n = Nat.suc n} (suc Y) zero Y≢X = refl
  punchIn-resolved-punchOut {n = Nat.suc n} (suc Y) (suc X) Y≢X =
    cong suc (punchIn-resolved-punchOut Y X _)

------------------------------------------------------------------------
-- Removing one unused scoped type variable
------------------------------------------------------------------------

strengthenᵗ? : ∀ {Δ}
  → (Y : TyVar (Nat.suc Δ))
  → Ty (Nat.suc Δ)
  → Maybe (Ty Δ)
strengthenᵗ? Y (＇ X) with Y ≟ X
strengthenᵗ? Y (＇ .Y) | yes refl = nothing
strengthenᵗ? Y (＇ X) | no Y≢X = just (＇ punchOut Y X Y≢X)
strengthenᵗ? Y (‵ ι) = just (‵ ι)
strengthenᵗ? Y ★ = just ★
strengthenᵗ? Y (A ⇒ B) with strengthenᵗ? Y A | strengthenᵗ? Y B
strengthenᵗ? Y (A ⇒ B) | just A₀ | just B₀ = just (A₀ ⇒ B₀)
strengthenᵗ? Y (A ⇒ B) | just A₀ | nothing = nothing
strengthenᵗ? Y (A ⇒ B) | nothing | just B₀ = nothing
strengthenᵗ? Y (A ⇒ B) | nothing | nothing = nothing
strengthenᵗ? Y (`∀ A) with strengthenᵗ? (suc Y) A
strengthenᵗ? Y (`∀ A) | just A₀ = just (`∀ A₀)
strengthenᵗ? Y (`∀ A) | nothing = nothing

wkGround : ∀ {Δ} {H : Ty Δ}
  → (Y : TyVar (Nat.suc Δ))
  → Ground H
  → Ground (wkᵗ Y H)
wkGround Y (＇ X) = ＇ punchIn Y X
wkGround Y (‵ ι) = ‵ ι
wkGround Y ★⇒★ = ★⇒★
wkGround Y ∀★ = ∀★

punchIn-punchOut : ∀ {Δ} (Y X : TyVar (Nat.suc Δ))
    (Y≢X : Y ≢ X)
  → punchIn Y (punchOut Y X Y≢X) ≡ X
punchIn-punchOut = punchIn-resolved-punchOut

strengthenGround : ∀ {Δ} {Y : TyVar (Nat.suc Δ)}
    {H : Ty (Nat.suc Δ)} {H₀ : Ty Δ}
  → Ground H
  → strengthenᵗ? Y H ≡ just H₀
  → Ground H₀
strengthenGround {Y = Y} (＇ X) eq with Y ≟ X
strengthenGround {Y = Y} (＇ .Y) () | yes refl
strengthenGround {Y = Y} (＇ X) refl | no Y≢X =
  ＇ punchOut Y X Y≢X
strengthenGround (‵ ι) refl = ‵ ι
strengthenGround ★⇒★ refl = ★⇒★
strengthenGround ∀★ refl = ∀★

unstrengthenableGround : ∀ {Δ} {Y : TyVar (Nat.suc Δ)}
    {H : Ty (Nat.suc Δ)}
  → Ground H
  → strengthenᵗ? Y H ≡ nothing
  → Y ∈ᵗ H
unstrengthenableGround {Y = Y} (＇ X) eq with Y ≟ X
unstrengthenableGround {Y = Y} (＇ .Y) refl | yes refl = var-∈
unstrengthenableGround {Y = Y} (＇ X) () | no Y≢X
unstrengthenableGround (‵ ι) ()
unstrengthenableGround ★⇒★ ()
unstrengthenableGround ∀★ ()

wkᵗ-under-∀ : ∀ {Δ} (Y : TyVar (Nat.suc Δ))
    (A : Ty (Nat.suc Δ))
  → renameᵗ (extᵗ (punchIn Y)) A ≡ wkᵗ (suc Y) A
wkᵗ-under-∀ Y A = renameᵗ-cong A under
  where
  under : ∀ X → extᵗ (punchIn Y) X ≡ punchIn (suc Y) X
  under zero = refl
  under (suc X) = refl

strengthenᵗ?-wkᵗ : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (A : Ty Δ)
  → strengthenᵗ? Y (wkᵗ Y A) ≡ just A
strengthenᵗ?-wkᵗ Y (＇ X) with Y ≟ punchIn Y X
strengthenᵗ?-wkᵗ Y (＇ X) | yes eq =
  ⊥-elim (resolved-punchIn≢ Y X eq)
strengthenᵗ?-wkᵗ Y (＇ X) | no Y≢X
    rewrite resolved-punchOut-punchIn Y X Y≢X =
  refl
strengthenᵗ?-wkᵗ Y (‵ ι) = refl
strengthenᵗ?-wkᵗ Y ★ = refl
strengthenᵗ?-wkᵗ Y (A ⇒ B)
    rewrite strengthenᵗ?-wkᵗ Y A | strengthenᵗ?-wkᵗ Y B =
  refl
strengthenᵗ?-wkᵗ Y (`∀ A)
    rewrite wkᵗ-under-∀ Y A | strengthenᵗ?-wkᵗ (suc Y) A =
  refl

strengthenᵗ?-sound : ∀ {Δ} {Y : TyVar (Nat.suc Δ)}
    {A : Ty (Nat.suc Δ)} {A₀ : Ty Δ}
  → strengthenᵗ? Y A ≡ just A₀
  → A ≡ wkᵗ Y A₀
strengthenᵗ?-sound {Y = Y} {A = ＇ X} eq with Y ≟ X
strengthenᵗ?-sound {Y = Y} {A = ＇ .Y} () | yes refl
strengthenᵗ?-sound {Y = Y} {A = ＇ X} refl | no Y≢X =
  cong ＇_ (sym (punchIn-resolved-punchOut Y X Y≢X))
strengthenᵗ?-sound {A = ‵ ι} refl = refl
strengthenᵗ?-sound {A = ★} refl = refl
strengthenᵗ?-sound {Y = Y} {A = A ⇒ B} eq
    with strengthenᵗ? Y A in A-eq | strengthenᵗ? Y B in B-eq
strengthenᵗ?-sound {A = A ⇒ B} refl | just A₀ | just B₀ =
  cong₂ _⇒_ (strengthenᵗ?-sound {A = A} A-eq)
    (strengthenᵗ?-sound {A = B} B-eq)
strengthenᵗ?-sound {A = A ⇒ B} () | just A₀ | nothing
strengthenᵗ?-sound {A = A ⇒ B} () | nothing | just B₀
strengthenᵗ?-sound {A = A ⇒ B} () | nothing | nothing
strengthenᵗ?-sound {Y = Y} {A = `∀ A} eq
    with strengthenᵗ? (suc Y) A in A-eq
strengthenᵗ?-sound {Y = Y} {A = `∀ A} refl | just A₀ =
  cong `∀
    (trans (strengthenᵗ?-sound {Y = suc Y} {A = A} A-eq)
      (sym (wkᵗ-under-∀ Y A₀)))
strengthenᵗ?-sound {A = `∀ A} () | nothing

strengthenᵗ?-absent : ∀ {Δ} {Y : TyVar (Nat.suc Δ)}
    {A : Ty (Nat.suc Δ)}
  → Y ∉ᵗ A
  → Σ[ A₀ ∈ Ty Δ ] (strengthenᵗ? Y A ≡ just A₀)
strengthenᵗ?-absent {Y = Y} {A = ＇ X} (∉-var Y≠X) with Y ≟ X
strengthenᵗ?-absent {Y = Y} {A = ＇ .Y} (∉-var Y≠Y) | yes refl =
  ⊥-elim (≢ᶠ→≢ Y≠Y refl)
strengthenᵗ?-absent {Y = Y} {A = ＇ X} (∉-var Y≠X) | no Y≢X =
  ＇ punchOut Y X Y≢X , refl
strengthenᵗ?-absent ∉-base = _ , refl
strengthenᵗ?-absent ∉-star = ★ , refl
strengthenᵗ?-absent (∉-fun Y∉A Y∉B)
    with strengthenᵗ?-absent Y∉A | strengthenᵗ?-absent Y∉B
strengthenᵗ?-absent (∉-fun Y∉A Y∉B)
    | A₀ , A-eq | B₀ , B-eq rewrite A-eq | B-eq =
  A₀ ⇒ B₀ , refl
strengthenᵗ?-absent (∉-all Y∉A) with strengthenᵗ?-absent Y∉A
strengthenᵗ?-absent (∉-all Y∉A) | A₀ , A-eq rewrite A-eq =
  `∀ A₀ , refl

strengthenᵗ?-present : ∀ {Δ} {Y : TyVar (Nat.suc Δ)}
    {A : Ty (Nat.suc Δ)}
  → Y ∈ᵗ A
  → strengthenᵗ? Y A ≡ nothing
strengthenᵗ?-present {Y = Y} var-∈ with Y ≟ Y
strengthenᵗ?-present var-∈ | yes refl = refl
strengthenᵗ?-present {Y = Y} var-∈ | no Y≢Y = ⊥-elim (Y≢Y refl)
strengthenᵗ?-present {Y = Y} {A = A ⇒ B} (∈-fun-left Y∈A)
    rewrite strengthenᵗ?-present Y∈A
    with strengthenᵗ? Y B
strengthenᵗ?-present {A = A ⇒ B} (∈-fun-left Y∈A)
    | just B₀ = refl
strengthenᵗ?-present {A = A ⇒ B} (∈-fun-left Y∈A)
    | nothing = refl
strengthenᵗ?-present {Y = Y} {A = A ⇒ B}
    (∈-fun-right Y∉A Y∈B)
    rewrite strengthenᵗ?-present Y∈B
    with strengthenᵗ? Y A
strengthenᵗ?-present {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | just A₀ = refl
strengthenᵗ?-present {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | nothing = refl
strengthenᵗ?-present (∈-all Y∈A)
    rewrite strengthenᵗ?-present Y∈A =
  refl

resolveSubᵗ : ∀ {Δ} → TyVar (Nat.suc Δ) → Ty Δ → Nat.suc Δ ⇒ˢ Δ
resolveSubᵗ Y C X with Y ≟ X
resolveSubᵗ Y C .Y | yes refl = C
resolveSubᵗ Y C X | no Y≢X = ＇ punchOut Y X Y≢X

resolveSub-punchIn : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
    (X : TyVar Δ)
  → resolveSubᵗ Y C (punchIn Y X) ≡ ＇ X
resolveSub-punchIn Y C X with Y ≟ punchIn Y X
resolveSub-punchIn Y C X | yes eq =
  ⊥-elim (resolved-punchIn≢ Y X eq)
resolveSub-punchIn Y C X | no Y≢X
    rewrite resolved-punchOut-punchIn Y X Y≢X =
  refl

resolveSub-here : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
  → resolveSubᵗ Y C Y ≡ C
resolveSub-here Y C with Y ≟ Y
resolveSub-here Y C | yes refl = refl
resolveSub-here Y C | no Y≢Y = ⊥-elim (Y≢Y refl)

resolveSub-reembed : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
    (X : TyVar (Nat.suc Δ))
  → renameᵗ (punchIn Y) (resolveSubᵗ Y C X)
    ≡ replaceTy Y (wkᵗ Y C) (＇ X)
resolveSub-reembed Y C X with Y ≟ X
resolveSub-reembed Y C .Y | yes refl = refl
resolveSub-reembed Y C X | no Y≢X
    rewrite punchIn-resolved-punchOut Y X Y≢X =
  refl

resolveSub-ext : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C : Ty Δ)
    (X : TyVar (Nat.suc (Nat.suc Δ)))
  → resolveSubᵗ (suc Y) (⇑ᵗ C) X ≡ extsᵗ (resolveSubᵗ Y C) X
resolveSub-ext Y C zero = refl
resolveSub-ext Y C (suc X) with Y ≟ X
resolveSub-ext Y C (suc .Y) | yes refl = refl
resolveSub-ext Y C (suc X) | no Y≢X = refl

resolve-wkᵗ : ∀ {Δ} (Y : TyVar (Nat.suc Δ)) (C A : Ty Δ)
  → substᵗ (resolveSubᵗ Y C) (wkᵗ Y A) ≡ A
resolve-wkᵗ Y C A =
  trans (substᵗ-rename (resolveSubᵗ Y C) (punchIn Y) A)
    (trans (substᵗ-cong A (resolveSub-punchIn Y C))
      (substᵗ-id A))

------------------------------------------------------------------------
-- Raw conversion shapes
------------------------------------------------------------------------

infixr 7 _↦↑_ _↦↓_

mutual
  data Reveal : Set where
    unseal : Reveal
    _↦↑_ : Conceal → Reveal → Reveal
    `∀↑_ : Reveal → Reveal
    id↑ : Reveal

  data Conceal : Set where
    seal : Conceal
    _↦↓_ : Reveal → Conceal → Conceal
    `∀↓_ : Conceal → Conceal
    id↓ : Conceal

------------------------------------------------------------------------
-- Scoped conversion typing
------------------------------------------------------------------------

-- Read `⊢↑[ X ⦂ R ] c ⦂ A ↝ B` as: at pivot X, whose scoped
-- representation is R, the raw reveal shape c converts A to B.  The
-- conceal judgment is dual.  Neither judgment mentions a store, anchor,
-- or scoped-variable classifier.

infix 4 ⊢↑[_⦂_]_⦂_↝_ ⊢↓[_⦂_]_⦂_↝_

mutual
  data ⊢↑[_⦂_]_⦂_↝_ {Δ : TyCtx} :
      TyVar Δ → Ty Δ → Reveal → Ty Δ → Ty Δ → Set where
    ⊢unseal : ∀ {X R}
      → ⊢↑[ X ⦂ R ] unseal ⦂ ＇ X ↝ R

    ⊢↑-⇒ : ∀ {X R c d A A′ B B′}
      → ⊢↓[ X ⦂ R ] c ⦂ A′ ↝ A
      → ⊢↑[ X ⦂ R ] d ⦂ B ↝ B′
      → ⊢↑[ X ⦂ R ] c ↦↑ d ⦂ A ⇒ B ↝ A′ ⇒ B′

    ⊢↑-∀ : ∀ {X R c A B}
      → ⊢↑[ suc X ⦂ ⇑ᵗ R ] c ⦂ A ↝ B
      → ⊢↑[ X ⦂ R ] `∀↑ c ⦂ `∀ A ↝ `∀ B

    ⊢id↑ : ∀ {X R A}
      → Atom A
      → ⊢↑[ X ⦂ R ] id↑ ⦂ A ↝ A

  data ⊢↓[_⦂_]_⦂_↝_ {Δ : TyCtx} :
      TyVar Δ → Ty Δ → Conceal → Ty Δ → Ty Δ → Set where
    ⊢seal : ∀ {X R}
      → ⊢↓[ X ⦂ R ] seal ⦂ R ↝ ＇ X

    ⊢↓-⇒ : ∀ {X R c d A A′ B B′}
      → ⊢↑[ X ⦂ R ] c ⦂ A′ ↝ A
      → ⊢↓[ X ⦂ R ] d ⦂ B ↝ B′
      → ⊢↓[ X ⦂ R ] c ↦↓ d ⦂ A ⇒ B ↝ A′ ⇒ B′

    ⊢↓-∀ : ∀ {X R c A B}
      → ⊢↓[ suc X ⦂ ⇑ᵗ R ] c ⦂ A ↝ B
      → ⊢↓[ X ⦂ R ] `∀↓ c ⦂ `∀ A ↝ `∀ B

    ⊢id↓ : ∀ {X R A}
      → Atom A
      → ⊢↓[ X ⦂ R ] id↓ ⦂ A ↝ A

------------------------------------------------------------------------
-- Total conversion endpoints
------------------------------------------------------------------------

-- On the typed fragment, a reveal's source and a conceal's target need no
-- representation: `unseal` fixes its source to the pivot and `seal` fixes
-- its target to the pivot.  Ill-shaped shape/type pairs are junk inputs;
-- returning the supplied endpoint keeps these functions total without
-- assigning them any dynamic meaning.

mutual
  src↑ : TyVar Δ → Reveal → Ty Δ → Ty Δ
  src↑ X unseal T = ＇ X
  src↑ X (c ↦↑ d) (A ⇒ B) = tgt↓ X c A ⇒ src↑ X d B
  src↑ X (c ↦↑ d) (＇ Y) = ＇ Y
  src↑ X (c ↦↑ d) (‵ ι) = ‵ ι
  src↑ X (c ↦↑ d) ★ = ★
  src↑ X (c ↦↑ d) (`∀ B) = `∀ B
  src↑ X (`∀↑ c) (`∀ B) = `∀ (src↑ (suc X) c B)
  src↑ X (`∀↑ c) (＇ Y) = ＇ Y
  src↑ X (`∀↑ c) (‵ ι) = ‵ ι
  src↑ X (`∀↑ c) ★ = ★
  src↑ X (`∀↑ c) (A ⇒ B) = A ⇒ B
  src↑ X id↑ T = T

  tgt↓ : TyVar Δ → Conceal → Ty Δ → Ty Δ
  tgt↓ X seal A = ＇ X
  tgt↓ X (c ↦↓ d) (A ⇒ B) = src↑ X c A ⇒ tgt↓ X d B
  tgt↓ X (c ↦↓ d) (＇ Y) = ＇ Y
  tgt↓ X (c ↦↓ d) (‵ ι) = ‵ ι
  tgt↓ X (c ↦↓ d) ★ = ★
  tgt↓ X (c ↦↓ d) (`∀ A) = `∀ A
  tgt↓ X (`∀↓ c) (`∀ A) = `∀ (tgt↓ (suc X) c A)
  tgt↓ X (`∀↓ c) (＇ Y) = ＇ Y
  tgt↓ X (`∀↓ c) (‵ ι) = ‵ ι
  tgt↓ X (`∀↓ c) ★ = ★
  tgt↓ X (`∀↓ c) (A ⇒ B) = A ⇒ B
  tgt↓ X id↓ A = A

-- The other two directions must know the pivot's representation: it is the
-- source of `seal` and the target of `unseal`.  They use the same junk-total
-- convention on shape/type mismatches.

mutual
  src↓ : TyVar Δ → Ty Δ → Conceal → Ty Δ → Ty Δ
  src↓ X R seal T = R
  src↓ X R (c ↦↓ d) (A ⇒ B) =
    tgt↑ X R c A ⇒ src↓ X R d B
  src↓ X R (c ↦↓ d) (＇ Y) = ＇ Y
  src↓ X R (c ↦↓ d) (‵ ι) = ‵ ι
  src↓ X R (c ↦↓ d) ★ = ★
  src↓ X R (c ↦↓ d) (`∀ B) = `∀ B
  src↓ X R (`∀↓ c) (`∀ B) =
    `∀ (src↓ (suc X) (⇑ᵗ R) c B)
  src↓ X R (`∀↓ c) (＇ Y) = ＇ Y
  src↓ X R (`∀↓ c) (‵ ι) = ‵ ι
  src↓ X R (`∀↓ c) ★ = ★
  src↓ X R (`∀↓ c) (A ⇒ B) = A ⇒ B
  src↓ X R id↓ T = T

  tgt↑ : TyVar Δ → Ty Δ → Reveal → Ty Δ → Ty Δ
  tgt↑ X R unseal A = R
  tgt↑ X R (c ↦↑ d) (A ⇒ B) =
    src↓ X R c A ⇒ tgt↑ X R d B
  tgt↑ X R (c ↦↑ d) (＇ Y) = ＇ Y
  tgt↑ X R (c ↦↑ d) (‵ ι) = ‵ ι
  tgt↑ X R (c ↦↑ d) ★ = ★
  tgt↑ X R (c ↦↑ d) (`∀ A) = `∀ A
  tgt↑ X R (`∀↑ c) (`∀ A) =
    `∀ (tgt↑ (suc X) (⇑ᵗ R) c A)
  tgt↑ X R (`∀↑ c) (＇ Y) = ＇ Y
  tgt↑ X R (`∀↑ c) (‵ ι) = ‵ ι
  tgt↑ X R (`∀↑ c) ★ = ★
  tgt↑ X R (`∀↑ c) (A ⇒ B) = A ⇒ B
  tgt↑ X R id↑ A = A

------------------------------------------------------------------------
-- Structural conversion generation
------------------------------------------------------------------------

-- Raw shapes carry no endpoints, so the generators depend only on the
-- pivot and the target type's structure; the representation argument of
-- the earlier intrinsic generators is gone.
mutual
  〖_↑_〗 : TyVar Δ → Ty Δ → Reveal
  〖 X ↑ (＇ Y) 〗 with X ≟ Y
  〖 X ↑ (＇ .X) 〗 | yes refl = unseal
  〖 X ↑ (＇ Y) 〗 | no X≠Y = id↑
  〖 X ↑ (‵ ι) 〗 = id↑
  〖 X ↑ ★ 〗 = id↑
  〖 X ↑ (A ⇒ B) 〗 = 〖 X ↓ A 〗 ↦↑ 〖 X ↑ B 〗
  〖 X ↑ (`∀ A) 〗 = `∀↑ 〖 suc X ↑ A 〗

  〖_↓_〗 : TyVar Δ → Ty Δ → Conceal
  〖 X ↓ (＇ Y) 〗 with X ≟ Y
  〖 X ↓ (＇ .X) 〗 | yes refl = seal
  〖 X ↓ (＇ Y) 〗 | no X≠Y = id↓
  〖 X ↓ (‵ ι) 〗 = id↓
  〖 X ↓ ★ 〗 = id↓
  〖 X ↓ (A ⇒ B) 〗 = 〖 X ↑ A 〗 ↦↓ 〖 X ↓ B 〗
  〖 X ↓ (`∀ A) 〗 = `∀↓ 〖 suc X ↓ A 〗

mutual
  generator-typed↑ : (X : TyVar Δ) (R B : Ty Δ)
    → ⊢↑[ X ⦂ R ] 〖 X ↑ B 〗 ⦂ B ↝ replaceTy X R B
  generator-typed↑ X R (＇ Y) with X ≟ Y
  generator-typed↑ X R (＇ .X) | yes refl = ⊢unseal
  generator-typed↑ X R (＇ Y) | no X≠Y = ⊢id↑ (＇ Y)
  generator-typed↑ X R (‵ ι) = ⊢id↑ (‵ ι)
  generator-typed↑ X R ★ = ⊢id↑ ★
  generator-typed↑ X R (A ⇒ B) =
    ⊢↑-⇒ (generator-typed↓ X R A) (generator-typed↑ X R B)
  generator-typed↑ X R (`∀ B) =
    ⊢↑-∀ (generator-typed↑ (suc X) (⇑ᵗ R) B)

  generator-typed↓ : (X : TyVar Δ) (R B : Ty Δ)
    → ⊢↓[ X ⦂ R ] 〖 X ↓ B 〗 ⦂ replaceTy X R B ↝ B
  generator-typed↓ X R (＇ Y) with X ≟ Y
  generator-typed↓ X R (＇ .X) | yes refl = ⊢seal
  generator-typed↓ X R (＇ Y) | no X≠Y = ⊢id↓ (＇ Y)
  generator-typed↓ X R (‵ ι) = ⊢id↓ (‵ ι)
  generator-typed↓ X R ★ = ⊢id↓ ★
  generator-typed↓ X R (A ⇒ B) =
    ⊢↓-⇒ (generator-typed↑ X R A) (generator-typed↓ X R B)
  generator-typed↓ X R (`∀ B) =
    ⊢↓-∀ (generator-typed↓ (suc X) (⇑ᵗ R) B)

------------------------------------------------------------------------
-- Structural delimiters
------------------------------------------------------------------------

mutual
  δ↑ : Ty Δ → Reveal
  δ↑ (＇ X) = id↑
  δ↑ (‵ ι) = id↑
  δ↑ ★ = id↑
  δ↑ (A ⇒ B) = δ↓ A ↦↑ δ↑ B
  δ↑ (`∀ A) = `∀↑ δ↑ A

  δ↓ : Ty Δ → Conceal
  δ↓ (＇ X) = id↓
  δ↓ (‵ ι) = id↓
  δ↓ ★ = id↓
  δ↓ (A ⇒ B) = δ↑ A ↦↓ δ↓ B
  δ↓ (`∀ A) = `∀↓ δ↓ A

mutual
  delimiter-typed↑ : (X : TyVar Δ) (R A : Ty Δ)
    → ⊢↑[ X ⦂ R ] δ↑ A ⦂ A ↝ A
  delimiter-typed↑ X R (＇ Y) = ⊢id↑ (＇ Y)
  delimiter-typed↑ X R (‵ ι) = ⊢id↑ (‵ ι)
  delimiter-typed↑ X R ★ = ⊢id↑ ★
  delimiter-typed↑ X R (A ⇒ B) =
    ⊢↑-⇒ (delimiter-typed↓ X R A) (delimiter-typed↑ X R B)
  delimiter-typed↑ X R (`∀ A) =
    ⊢↑-∀ (delimiter-typed↑ (suc X) (⇑ᵗ R) A)

  delimiter-typed↓ : (X : TyVar Δ) (R A : Ty Δ)
    → ⊢↓[ X ⦂ R ] δ↓ A ⦂ A ↝ A
  delimiter-typed↓ X R (＇ Y) = ⊢id↓ (＇ Y)
  delimiter-typed↓ X R (‵ ι) = ⊢id↓ (‵ ι)
  delimiter-typed↓ X R ★ = ⊢id↓ ★
  delimiter-typed↓ X R (A ⇒ B) =
    ⊢↓-⇒ (delimiter-typed↑ X R A) (delimiter-typed↓ X R B)
  delimiter-typed↓ X R (`∀ A) =
    ⊢↓-∀ (delimiter-typed↓ (suc X) (⇑ᵗ R) A)

------------------------------------------------------------------------
-- Type-directed identity expansion
------------------------------------------------------------------------

-- Reveal expansion is guided by its source endpoint; conceal expansion is
-- guided by its target endpoint.  Those choices are dual at arrow domains.
-- Non-identity leaves remain unchanged, while their structural children are
-- expanded against the corresponding endpoint components.  Mismatched
-- shape/type pairs use the same junk-total convention as the endpoint
-- functions above.

mutual
  expand↑ : Ty Δ → Reveal → Reveal
  expand↑ T unseal = unseal
  expand↑ (＇ X) (c ↦↑ d) = c ↦↑ d
  expand↑ (‵ ι) (c ↦↑ d) = c ↦↑ d
  expand↑ ★ (c ↦↑ d) = c ↦↑ d
  expand↑ (A ⇒ B) (c ↦↑ d) = expand↓ A c ↦↑ expand↑ B d
  expand↑ (`∀ A) (c ↦↑ d) = c ↦↑ d
  expand↑ (＇ X) (`∀↑ c) = `∀↑ c
  expand↑ (‵ ι) (`∀↑ c) = `∀↑ c
  expand↑ ★ (`∀↑ c) = `∀↑ c
  expand↑ (A ⇒ B) (`∀↑ c) = `∀↑ c
  expand↑ (`∀ A) (`∀↑ c) = `∀↑ (expand↑ A c)
  expand↑ T id↑ = δ↑ T

  expand↓ : Ty Δ → Conceal → Conceal
  expand↓ T seal = seal
  expand↓ (＇ X) (c ↦↓ d) = c ↦↓ d
  expand↓ (‵ ι) (c ↦↓ d) = c ↦↓ d
  expand↓ ★ (c ↦↓ d) = c ↦↓ d
  expand↓ (A ⇒ B) (c ↦↓ d) = expand↑ A c ↦↓ expand↓ B d
  expand↓ (`∀ A) (c ↦↓ d) = c ↦↓ d
  expand↓ (＇ X) (`∀↓ c) = `∀↓ c
  expand↓ (‵ ι) (`∀↓ c) = `∀↓ c
  expand↓ ★ (`∀↓ c) = `∀↓ c
  expand↓ (A ⇒ B) (`∀↓ c) = `∀↓ c
  expand↓ (`∀ A) (`∀↓ c) = `∀↓ (expand↓ A c)
  expand↓ T id↓ = δ↓ T

expand↑-typed : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ} (T : Ty Δ)
  → ⊢↑[ X ⦂ R ] expand↑ T id↑ ⦂ T ↝ T
expand↑-typed {X = X} {R = R} T = delimiter-typed↑ X R T

expand↑-strengthen-typed : ∀ {Δ} {Y : TyVar (Nat.suc Δ)}
    {R H : Ty (Nat.suc Δ)} {H₀ : Ty Δ}
  → (strengthens : strengthenᵗ? Y H ≡ just H₀)
  → ⊢↑[ Y ⦂ R ] expand↑ H id↑ ⦂ H ↝ wkᵗ Y H₀
expand↑-strengthen-typed {Y = Y} {R = R} {H = H} strengthens =
  subst (λ T → ⊢↑[ Y ⦂ R ] expand↑ H id↑ ⦂ H ↝ T)
    (strengthenᵗ?-sound strengthens) (expand↑-typed H)

expand↓-typed : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ} (T : Ty Δ)
  → ⊢↓[ X ⦂ R ] expand↓ T id↓ ⦂ T ↝ T
expand↓-typed {X = X} {R = R} T = delimiter-typed↓ X R T
