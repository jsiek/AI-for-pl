module CoercionNormalForm where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Types
open import CoercionReduction

infix 7 _↣_
infix 5 _i⨟s_
infix 5 _g⨟i_
infix 5 _g⨟g_
infix 4 _⇨ⁿ_ _⇨ⁱ_ _⇨ᵍ_
infix 7 _?ⁿ_ _!ⁿ_
infix 6 _?ⁿ_⨾_ ‹_›_⨾_!ⁿ

--------------------------------------------------------------------------------
-- Normal form
--------------------------------------------------------------------------------
mutual
  data _⇨ⁿ_ : Ty → Ty → Set
  data _⇨ⁱ_ : Ty → Ty → Set
  data _⇨ᵍ_ : Ty → Ty → Set

  data _⇨ⁿ_ where
    idⁿ : (A : Ty)
      → A ⇨ⁿ A
    _?ⁿ_ : ∀ (G : Ty)
      → Ground G
      → ★ ⇨ⁿ G
    _?ⁿ_⨾_ : ∀ (G : Ty) {B}
      → Ground G
      → G ⇨ⁱ B
      → ★ ⇨ⁿ B
    ′_ : ∀ {A B}
      → A ⇨ⁱ B
      → A ⇨ⁿ B

  data _⇨ⁱ_ where
    _!ⁿ_ : ∀ (G : Ty)
      → Ground G
      → G ⇨ⁱ ★
    ‹_›_⨾_!ⁿ : ∀ {A} (G : Ty)
      → A ⇨ᵍ G
      → Ground G
      → A ⇨ⁱ ★
    ＇_ : ∀ {A B}
      → A ⇨ᵍ B
      → A ⇨ⁱ B
    ⊥ⁿ_⇨_ : ∀ (A B : Ty)
      → A ⇨ⁱ B

  data _⇨ᵍ_ where
    _↣_ : ∀ {A B C D}
      → C ⇨ⁿ A
      → B ⇨ⁿ D
      → (A ⇒ B) ⇨ᵍ (C ⇒ D)

mutual
  ⌊_⌋ˢ : ∀ {A B}
    → A ⇨ⁿ B
    → Coercion
  ⌊_⌋ⁱ : ∀ {A B}
    → A ⇨ⁱ B
    → Coercion
  ⌊_⌋ᵍ : ∀ {A B}
    → A ⇨ᵍ B
    → Coercion

  ⌊ idⁿ A ⌋ˢ = idᶜ A
  ⌊ G ?ⁿ _ ⌋ˢ = G `?
  ⌊ G ?ⁿ _ ⨾ i ⌋ˢ = G `? ⨟ ⌊ i ⌋ⁱ
  ⌊ ′ i ⌋ˢ = ⌊ i ⌋ⁱ

  ⌊ G !ⁿ _ ⌋ⁱ = G !
  ⌊ ‹ G › g ⨾ _ !ⁿ ⌋ⁱ = ⌊ g ⌋ᵍ ⨟ G !
  ⌊ ＇ g ⌋ⁱ = ⌊ g ⌋ᵍ
  ⌊ ⊥ⁿ A ⇨ B ⌋ⁱ = ⊥ᶜ A ⇨ B

  ⌊ c ↣ d ⌋ᵍ = ⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ

mutual
  wtS : ∀ {A B} (s : A ⇨ⁿ B)
    → ⊢ ⌊ s ⌋ˢ ⦂ A ⇨ B
  wtI : ∀ {A B} (i : A ⇨ⁱ B)
    → ⊢ ⌊ i ⌋ⁱ ⦂ A ⇨ B
  wtG : ∀ {A B} (g : A ⇨ᵍ B)
    → ⊢ ⌊ g ⌋ᵍ ⦂ A ⇨ B

  wtS (idⁿ A) = ⊢idᶜ
  wtS (G ?ⁿ g) = ⊢? g
  wtS (G ?ⁿ g ⨾ i) = ⊢⨟ (⊢? g) (wtI i)
  wtS (′ i) = wtI i

  wtI (G !ⁿ g) = ⊢! g
  wtI (‹ G › g ⨾ gnd !ⁿ) = ⊢⨟ (wtG g) (⊢! gnd)
  wtI (＇ g) = wtG g
  wtI (⊥ⁿ A ⇨ B) = ⊢⊥

  wtG (c ↣ d) = ⊢↦ (wtS c) (wtS d)

★⇨ⁱ-is-⊥ : ∀ {C} (i : ★ ⇨ⁱ C) → i ≡ ⊥ⁿ ★ ⇨ C
★⇨ⁱ-is-⊥ (★ !ⁿ ())
★⇨ⁱ-is-⊥ (‹ _ › () ⨾ _ !ⁿ)
★⇨ⁱ-is-⊥ (＇ ())
★⇨ⁱ-is-⊥ (⊥ⁿ ★ ⇨ C) = refl

--------------------------------------------------------------------------------
-- Strong normalization
--------------------------------------------------------------------------------

mutual
  normalize-seq : ∀ {A B C}
    → (s : A ⇨ⁿ B)
    → (t : B ⇨ⁿ C)
    → Σ[ u ∈ A ⇨ⁿ C ] ((⌊ s ⌋ˢ ⨟ ⌊ t ⌋ˢ) —↠ᶜᶜ ⌊ u ⌋ˢ)

  _i⨟s_ : ∀ {A B C}
    → (i : A ⇨ⁱ B)
    → (t : B ⇨ⁿ C)
    → (Σ[ j ∈ A ⇨ⁱ C ] ((⌊ i ⌋ⁱ ⨟ ⌊ t ⌋ˢ) —↠ᶜᶜ ⌊ j ⌋ⁱ))
      ⊎ (A ≡ C × ((⌊ i ⌋ⁱ ⨟ ⌊ t ⌋ˢ) —↠ᶜᶜ idᶜ A))

  _g⨟i_ : ∀ {A B C}
    → (g : A ⇨ᵍ B)
    → (i : B ⇨ⁱ C)
    → Σ[ j ∈ A ⇨ⁱ C ] ((⌊ g ⌋ᵍ ⨟ ⌊ i ⌋ⁱ) —↠ᶜᶜ ⌊ j ⌋ⁱ)

  _g⨟g_ : ∀ {A B C}
    → (g : A ⇨ᵍ B)
    → (h : B ⇨ᵍ C)
    → Σ[ k ∈ A ⇨ᵍ C ] ((⌊ g ⌋ᵍ ⨟ ⌊ h ⌋ᵍ) —↠ᶜᶜ ⌊ k ⌋ᵍ)

  normalize-seq (idⁿ A) t =
    t
    , (((idᶜ A) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ β-idLᶜ ⟩
      ⌊ t ⌋ˢ
      ∎ᶜᶜ)

  normalize-seq (G ?ⁿ g) (idⁿ G) =
    G ?ⁿ g
    , (((G `?) ⨟ idᶜ G
      —→ᶜᶜ⟨ β-idRᶜ ⟩
      (G `?)
      ∎ᶜᶜ))

  normalize-seq (G ?ⁿ g) (′ i) =
    G ?ⁿ g ⨾ i
    , (((G `?) ⨟ ⌊ i ⌋ⁱ) ∎ᶜᶜ)

  normalize-seq (G ?ⁿ g ⨾ i) t
    with i i⨟s t
  ... | inj₁ (j , i⨟t↠j) =
    G ?ⁿ g ⨾ j
    , ((((G `?) ⨟ ⌊ i ⌋ⁱ) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((G `?) ⨟ (⌊ i ⌋ⁱ ⨟ ⌊ t ⌋ˢ))
      —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ i⨟t↠j ⟩
      ((G `?) ⨟ ⌊ j ⌋ⁱ)
      ∎ᶜᶜ)
  ... | inj₂ (refl , i⨟t↠id) =
    G ?ⁿ g
    , ((((G `?) ⨟ ⌊ i ⌋ⁱ) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((G `?) ⨟ (⌊ i ⌋ⁱ ⨟ ⌊ t ⌋ˢ))
      —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ i⨟t↠id ⟩
      ((G `?) ⨟ idᶜ G)
      —→ᶜᶜ⟨ β-idRᶜ ⟩
      (G `?)
      ∎ᶜᶜ)

  normalize-seq (′ i) t
    with i i⨟s t
  ... | inj₁ (j , i⨟t↠j) =
    ′ j , i⨟t↠j
  ... | inj₂ (refl , i⨟t↠id) =
    idⁿ _ , i⨟t↠id

  _i⨟s_ (G !ⁿ g) (idⁿ ★) =
    inj₁ (G !ⁿ g
    , (((G !) ⨟ (idᶜ ★)
      —→ᶜᶜ⟨ β-idRᶜ ⟩
      (G !)
      ∎ᶜᶜ)))

  _i⨟s_ (ℕ !ⁿ G-ℕ) (ℕ ?ⁿ G-ℕ) =
    inj₂ (refl
    , (((ℕ !) ⨟ (ℕ `?)
      —→ᶜᶜ⟨ β-proj-inj-okᶜ ⟩
      idᶜ ℕ
      ∎ᶜᶜ)))

  _i⨟s_ ((★ ⇒ ★) !ⁿ G-⇒) ((★ ⇒ ★) ?ⁿ G-⇒) =
    inj₂ (refl
    , ((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)
      —→ᶜᶜ⟨ β-proj-inj-okᶜ ⟩
      idᶜ (★ ⇒ ★)
      ∎ᶜᶜ)))

  _i⨟s_ {C = C} (ℕ !ⁿ G-ℕ) ((★ ⇒ ★) ?ⁿ G-⇒) =
    inj₁ (⊥ⁿ ℕ ⇨ C
    , (((ℕ !) ⨟ ((★ ⇒ ★) `?)
      —→ᶜᶜ⟨ β-proj-inj-badᶜ (λ ()) ⟩
      (⊥ᶜ ℕ ⇨ (★ ⇒ ★))
      ∎ᶜᶜ)))

  _i⨟s_ {C = C} ((★ ⇒ ★) !ⁿ G-⇒) (ℕ ?ⁿ G-ℕ) =
    inj₁ (⊥ⁿ (★ ⇒ ★) ⇨ C
    , ((((★ ⇒ ★) !) ⨟ (ℕ `?)
      —→ᶜᶜ⟨ β-proj-inj-badᶜ (λ ()) ⟩
      (⊥ᶜ (★ ⇒ ★) ⇨ ℕ)
      ∎ᶜᶜ)))

  _i⨟s_ (ℕ !ⁿ G-ℕ) (ℕ ?ⁿ G-ℕ ⨾ i) =
    inj₁ (i
    , (((ℕ !) ⨟ (((ℕ `?)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      (((ℕ !) ⨟ (ℕ `?)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-proj-inj-okᶜ ⟩
      ((idᶜ ℕ) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-idLᶜ ⟩
      ⌊ i ⌋ⁱ
      ∎ᶜᶜ)))

  _i⨟s_ ((★ ⇒ ★) !ⁿ G-⇒) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ i) =
    inj₁ (i
    , ((((★ ⇒ ★) !) ⨟ (((★ ⇒ ★) `?) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      ((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-proj-inj-okᶜ ⟩
      ((idᶜ (★ ⇒ ★)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-idLᶜ ⟩
      ⌊ i ⌋ⁱ
      ∎ᶜᶜ)))

  _i⨟s_ {C = C} (ℕ !ⁿ G-ℕ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ i) =
    inj₁ (⊥ⁿ ℕ ⇨ C
    , (((ℕ !) ⨟ (((★ ⇒ ★) `?) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      (((ℕ !) ⨟ ((★ ⇒ ★) `?)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ())) ⟩
      ((⊥ᶜ ℕ ⇨ (★ ⇒ ★)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-⊥Lᶜ (wtI i) ⟩
      (⊥ᶜ ℕ ⇨ C)
      ∎ᶜᶜ)))

  _i⨟s_ {C = C} ((★ ⇒ ★) !ⁿ G-⇒) (ℕ ?ⁿ G-ℕ ⨾ i) =
    inj₁ (⊥ⁿ (★ ⇒ ★) ⇨ C
    , ((((★ ⇒ ★) !) ⨟ (((ℕ `?)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      ((((★ ⇒ ★) !) ⨟ (ℕ `?)) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ())) ⟩
      ((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ ⌊ i ⌋ⁱ)
      —→ᶜᶜ⟨ β-⊥Lᶜ (wtI i) ⟩
      (⊥ᶜ (★ ⇒ ★) ⇨ C)
      ∎ᶜᶜ)))

  _i⨟s_ {C = C} (G !ⁿ g) (′ (⊥ⁿ ★ ⇨ C)) =
    inj₁ (⊥ⁿ G ⇨ C
      , (((G !) ⨟ (⊥ᶜ ★ ⇨ C)
      —→ᶜᶜ⟨ β-!⊥ᶜ ⟩
      (⊥ᶜ G ⇨ C)
      ∎ᶜᶜ)))

  _i⨟s_ (‹ G › g ⨾ gnd !ⁿ) (idⁿ ★) =
    inj₁ (‹ G › g ⨾ gnd !ⁿ
    , (((⌊ g ⌋ᵍ ⨟ (G !)) ⨟ (idᶜ ★))
      —→ᶜᶜ⟨ β-idRᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ (G !))
      ∎ᶜᶜ))

  _i⨟s_ (‹ ℕ › () ⨾ G-ℕ !ⁿ) (ℕ ?ⁿ G-ℕ)

  _i⨟s_ {C = C} (‹ ℕ › () ⨾ G-ℕ !ⁿ) ((★ ⇒ ★) ?ⁿ G-⇒)

  _i⨟s_ (‹ (★ ⇒ ★) › g ⨾ G-⇒ !ⁿ) ((★ ⇒ ★) ?ⁿ G-⇒) =
    inj₁ (＇ g
    , ((((⌊ g ⌋ᵍ ⨟ ((★ ⇒ ★) !)) ⨟ ((★ ⇒ ★) `?))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ (((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-proj-inj-okᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ idᶜ (★ ⇒ ★))
      —→ᶜᶜ⟨ β-idRᶜ ⟩
      ⌊ g ⌋ᵍ
      ∎ᶜᶜ)))

  _i⨟s_ {A = A₁ ⇒ B₁} (‹ (★ ⇒ ★) › (c ↣ d) ⨾ G-⇒ !ⁿ) (ℕ ?ⁿ G-ℕ) =
    inj₁ (⊥ⁿ (A₁ ⇒ B₁) ⇨ ℕ
    , ((((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ ((★ ⇒ ★) !)) ⨟ (ℕ `?))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (((★ ⇒ ★) !) ⨟ (ℕ `?)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (β-proj-inj-badᶜ (λ ())) ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (⊥ᶜ (★ ⇒ ★) ⇨ ℕ))
      —→ᶜᶜ⟨ β-↦⊥ᶜ (wtS c) (wtS d) ⟩
      (⊥ᶜ (A₁ ⇒ B₁) ⇨ ℕ)
      ∎ᶜᶜ))

  _i⨟s_ (‹ ℕ › () ⨾ G-ℕ !ⁿ) (ℕ ?ⁿ G-ℕ ⨾ i)

  _i⨟s_ {C = C} (‹ ℕ › () ⨾ G-ℕ !ⁿ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ i)

  _i⨟s_ {A = A₁ ⇒ B₁} {C = C}
         (‹ (★ ⇒ ★) › (c ↣ d) ⨾ G-⇒ !ⁿ)
         (ℕ ?ⁿ G-ℕ ⨾ i) =
    inj₁ (⊥ⁿ (A₁ ⇒ B₁) ⇨ C
    , ((((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ ((★ ⇒ ★) !)) ⨟ (((ℕ `?)) ⨟ ⌊ i ⌋ⁱ))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (((★ ⇒ ★) !) ⨟ (((ℕ `?)) ⨟ ⌊ i ⌋ⁱ)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-assocLᶜ ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ ((((★ ⇒ ★) !) ⨟ (ℕ `?)) ⨟ ⌊ i ⌋ⁱ))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ()))) ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ ((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ ⌊ i ⌋ⁱ))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (β-⊥Lᶜ (wtI i)) ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (⊥ᶜ (★ ⇒ ★) ⇨ C))
      —→ᶜᶜ⟨ β-↦⊥ᶜ (wtS c) (wtS d) ⟩
      (⊥ᶜ (A₁ ⇒ B₁) ⇨ C)
      ∎ᶜᶜ))

  _i⨟s_ (‹ (★ ⇒ ★) › g ⨾ G-⇒ !ⁿ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ i)
    with g g⨟i i
  ... | j , g⨟i↠j =
    inj₁ (j
    , ((((⌊ g ⌋ᵍ) ⨟ ((★ ⇒ ★) !)) ⨟ (((★ ⇒ ★) `?) ⨟ ⌊ i ⌋ⁱ))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((⌊ g ⌋ᵍ) ⨟ (((★ ⇒ ★) !) ⨟ (((★ ⇒ ★) `?) ⨟ ⌊ i ⌋ⁱ)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-assocLᶜ ⟩
      ((⌊ g ⌋ᵍ) ⨟ ((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)) ⨟ ⌊ i ⌋ⁱ))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ β-proj-inj-okᶜ) ⟩
      ((⌊ g ⌋ᵍ) ⨟ ((idᶜ (★ ⇒ ★)) ⨟ ⌊ i ⌋ⁱ))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-idLᶜ ⟩
      ((⌊ g ⌋ᵍ) ⨟ ⌊ i ⌋ⁱ)
      —↠ᶜᶜ⟨ g⨟i↠j ⟩
      ⌊ j ⌋ⁱ
      ∎ᶜᶜ))

  _i⨟s_ {C = C} (‹ ℕ › () ⨾ G-ℕ !ⁿ) (′ (⊥ⁿ ★ ⇨ C))

  _i⨟s_ {A = A₁ ⇒ B₁} {C = C}
         (‹ (★ ⇒ ★) › (c ↣ d) ⨾ G-⇒ !ⁿ)
         (′ (⊥ⁿ ★ ⇨ C)) =
    inj₁ (⊥ⁿ (A₁ ⇒ B₁) ⇨ C
    , ((((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ ((★ ⇒ ★) !)) ⨟ (⊥ᶜ ★ ⇨ C))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (((★ ⇒ ★) !) ⨟ (⊥ᶜ ★ ⇨ C)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-!⊥ᶜ ⟩
      ((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (⊥ᶜ (★ ⇒ ★) ⇨ C))
      —→ᶜᶜ⟨ β-↦⊥ᶜ (wtS c) (wtS d) ⟩
      (⊥ᶜ (A₁ ⇒ B₁) ⇨ C)
      ∎ᶜᶜ))

  _i⨟s_ {B = B} (＇ g) (idⁿ B) =
    inj₁ (＇ g
    , (((⌊ g ⌋ᵍ) ⨟ (idᶜ B))
      —→ᶜᶜ⟨ β-idRᶜ ⟩
      ⌊ g ⌋ᵍ
      ∎ᶜᶜ))

  _i⨟s_ (＇ g) (′ i)
    with g g⨟i i
  ... | j , g⨟i↠j =
    inj₁ (j , g⨟i↠j)

  _i⨟s_ {A = A} {B = B} {C = C} (⊥ⁿ A ⇨ B) t =
    inj₁ (⊥ⁿ A ⇨ C
    , (((⊥ᶜ A ⇨ B) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ β-⊥Lᶜ (wtS t) ⟩
      (⊥ᶜ A ⇨ C)
      ∎ᶜᶜ))

  _g⨟i_ g (G !ⁿ gnd) =
    ‹ G › g ⨾ gnd !ⁿ
    , ((⌊ g ⌋ᵍ ⨟ (G !)) ∎ᶜᶜ)

  _g⨟i_ g (‹ G › h ⨾ gnd !ⁿ)
    with g g⨟g h
  ... | k , g⨟g↠k =
    ‹ G › k ⨾ gnd !ⁿ
    , ((⌊ g ⌋ᵍ ⨟ (⌊ h ⌋ᵍ ⨟ (G !)))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      (((⌊ g ⌋ᵍ) ⨟ ⌊ h ⌋ᵍ) ⨟ (G !))
      —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ g⨟g↠k ⟩
      (⌊ k ⌋ᵍ ⨟ (G !))
      ∎ᶜᶜ)

  _g⨟i_ {A = A₁ ⇒ B₁} {B = C₁ ⇒ D₁} {C = E} (c ↣ d) (⊥ⁿ (C₁ ⇒ D₁) ⇨ E) =
    ⊥ⁿ (A₁ ⇒ B₁) ⇨ E
    , (((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (⊥ᶜ (C₁ ⇒ D₁) ⇨ E))
      —→ᶜᶜ⟨ β-↦⊥ᶜ (wtS c) (wtS d) ⟩
      (⊥ᶜ (A₁ ⇒ B₁) ⇨ E)
      ∎ᶜᶜ)

  _g⨟i_ g (＇ h)
    with g g⨟g h
  ... | k , g⨟g↠k =
    ＇ k , g⨟g↠k

  _g⨟g_ (c ↣ d) (c′ ↣ d′)
    with normalize-seq c′ c
  ... | lc , c′⨟c↠lc
    with normalize-seq d d′
  ... | rd , d⨟d′↠rd =
    (lc ↣ rd)
    , (((⌊ c ⌋ˢ ↦ ⌊ d ⌋ˢ) ⨟ (⌊ c′ ⌋ˢ ↦ ⌊ d′ ⌋ˢ))
      —→ᶜᶜ⟨ β-↦ᶜ ⟩
      ((⌊ c′ ⌋ˢ ⨟ ⌊ c ⌋ˢ) ↦ (⌊ d ⌋ˢ ⨟ ⌊ d′ ⌋ˢ))
      —↠ᶜᶜ⟨ multi-ξ-↦₁ᶜᶜ c′⨟c↠lc ⟩
      (⌊ lc ⌋ˢ ↦ (⌊ d ⌋ˢ ⨟ ⌊ d′ ⌋ˢ))
      —↠ᶜᶜ⟨ multi-ξ-↦₂ᶜᶜ d⨟d′↠rd ⟩
      (⌊ lc ⌋ˢ ↦ ⌊ rd ⌋ˢ)
      ∎ᶜᶜ)

i⨟sⁿ : ∀ {A B C}
  → (i : A ⇨ⁱ B)
  → (t : B ⇨ⁿ C)
  → A ⇨ⁿ C
i⨟sⁿ {A = A} i t
  with i i⨟s t
... | inj₁ (j , _) = ′ j
... | inj₂ (refl , _) = idⁿ A

g⨟iⁿ : ∀ {A B C}
  → (g : A ⇨ᵍ B)
  → (i : B ⇨ⁱ C)
  → A ⇨ⁿ C
g⨟iⁿ g i = ′ proj₁ (g g⨟i i)

g⨟gⁿ : ∀ {A B C}
  → (g : A ⇨ᵍ B)
  → (h : B ⇨ᵍ C)
  → A ⇨ᵍ C
g⨟gⁿ g h = proj₁ (g g⨟g h)

?ⁿ⨾ⁿ : ∀ {G B}
  → Ground G
  → G ⇨ⁿ B
  → ★ ⇨ⁿ B
?ⁿ⨾ⁿ g (idⁿ G) = G ?ⁿ g
?ⁿ⨾ⁿ g (′ i) = _ ?ⁿ g ⨾ i

normalize-seq-idⁿ-proj
  : ∀ {A C} {t : A ⇨ⁿ C}
  → proj₁ (normalize-seq (idⁿ A) t) ≡ t
normalize-seq-idⁿ-proj = refl

normalize-seq-?ⁿ-proj
  : ∀ {G B} {g : Ground G} {t : G ⇨ⁿ B}
  → proj₁ (normalize-seq (G ?ⁿ g) t) ≡ ?ⁿ⨾ⁿ g t
normalize-seq-?ⁿ-proj {t = idⁿ _} = refl
normalize-seq-?ⁿ-proj {t = ′ _} = refl

normalize-seq-?ⁿ⨾-proj
  : ∀ {G B C} {g : Ground G}
    {i : G ⇨ⁱ B} {t : B ⇨ⁿ C}
  → proj₁ (normalize-seq (G ?ⁿ g ⨾ i) t) ≡ ?ⁿ⨾ⁿ g (i⨟sⁿ i t)
normalize-seq-?ⁿ⨾-proj {i = i} {t = t}
  with i i⨟s t
... | inj₁ _ = refl
... | inj₂ (refl , _) = refl

normalize-seq-?ⁿ⨾!-proj
  : ∀ {G C} {g : Ground G} {t : ★ ⇨ⁿ C}
  → proj₁ (normalize-seq (G ?ⁿ g ⨾ (G !ⁿ g)) t) ≡ ?ⁿ⨾ⁿ g (i⨟sⁿ (G !ⁿ g) t)
normalize-seq-?ⁿ⨾!-proj {g = g} {t = t}
  with ( _ !ⁿ g) i⨟s t
... | inj₁ _ = refl
... | inj₂ (refl , _) = refl

normalize-seq-′-proj
  : ∀ {A B C} {i : A ⇨ⁱ B} {t : B ⇨ⁿ C}
  → proj₁ (normalize-seq (′ i) t) ≡ i⨟sⁿ i t
normalize-seq-′-proj {i = i} {t = t}
  with i i⨟s t
... | inj₁ _ = refl
... | inj₂ (refl , _) = refl

normalize : ∀ {A B}{c}
    → ⊢ c ⦂ A ⇨ B
    → Σ[ t ∈ A ⇨ⁿ B ] (c —↠ᶜᶜ ⌊ t ⌋ˢ)
normalize ⊢idᶜ = (idⁿ _) , (idᶜ _ ∎ᶜᶜ)
normalize (⊢! g) = (′ ( _ !ⁿ g)) , (_ ∎ᶜᶜ)
normalize (⊢? g) = (_ ?ⁿ g) , (_ ∎ᶜᶜ)
normalize {c = c ↦ d} (⊢↦ c⦂ d⦂)
    with normalize c⦂ | normalize d⦂
... | c′ , →c′ | d′ , →d′ = (′ (＇ (c′ ↣ d′))) ,
      (c ↦ d                —↠ᶜᶜ⟨ multi-ξ-↦₁ᶜᶜ →c′ ⟩
       ⌊ c′ ⌋ˢ ↦ d          —↠ᶜᶜ⟨ multi-ξ-↦₂ᶜᶜ →d′ ⟩
       ⌊ c′ ⌋ˢ ↦ ⌊ d′ ⌋ˢ     ∎ᶜᶜ)
      
normalize {c = c ⨟ d} (⊢⨟ c⦂ d⦂)
    with normalize c⦂ | normalize d⦂
... | c′ , →c′ | d′ , →d′
    with normalize-seq c′ d′
... | cd′ , →cd′ =
  cd′ ,
  (c ⨟ d                  —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ →c′ ⟩
   ⌊ c′ ⌋ˢ ⨟ d            —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ →d′ ⟩
   ⌊ c′ ⌋ˢ ⨟ ⌊ d′ ⌋ˢ       —↠ᶜᶜ⟨ →cd′ ⟩
   ⌊ cd′ ⌋ˢ                ∎ᶜᶜ)

normalize {A = A} {B = B} ⊢⊥ =
  ′ (⊥ⁿ A ⇨ B) , ((⊥ᶜ A ⇨ B) ∎ᶜᶜ)

--------------------------------------------------------------------------------
-- Convert from Normalᶜ to A ⇨ⁿ B
--------------------------------------------------------------------------------

inverse-erase
  : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Normalᶜ c
  → Σ[ s ∈ A ⇨ⁿ B ] (⌊ s ⌋ˢ ≡ c)

inverse-erase {c = idᶜ A} ⊢idᶜ nf-id =
  idⁿ A , refl

inverse-erase {c = ℕ `?} (⊢? G-ℕ) (nf-? G-ℕ) =
  ℕ ?ⁿ G-ℕ , refl

inverse-erase {c = (★ ⇒ ★) `?} (⊢? G-⇒) (nf-? G-⇒) =
  (★ ⇒ ★) ?ⁿ G-⇒ , refl

inverse-erase {c = ℕ !} (⊢! G-ℕ) (nf-! G-ℕ) =
  ′ (ℕ !ⁿ G-ℕ) , refl

inverse-erase {c = (★ ⇒ ★) !} (⊢! G-⇒) (nf-! G-⇒) =
  ′ ((★ ⇒ ★) !ⁿ G-⇒) , refl

inverse-erase {c = (ℕ `?) ⨟ (ℕ !)}
  (⊢⨟ (⊢? G-ℕ) (⊢! G-ℕ)) (nf-?! G-ℕ) =
  ℕ ?ⁿ G-ℕ ⨾ (ℕ !ⁿ G-ℕ) , refl

inverse-erase {c = ((★ ⇒ ★) `?) ⨟ ((★ ⇒ ★) !)}
  (⊢⨟ (⊢? G-⇒) (⊢! G-⇒)) (nf-?! G-⇒) =
  (★ ⇒ ★) ?ⁿ G-⇒ ⨾ ((★ ⇒ ★) !ⁿ G-⇒) , refl

inverse-erase {c = c₁ ↦ c₂}
  (⊢↦ cwt dwt) (nf-↦ n₁ n₂)
  with inverse-erase cwt n₁ | inverse-erase dwt n₂
... | s₁ , eq₁ | s₂ , eq₂ =
  ′ (＇ (s₁ ↣ s₂)) , cong₂ _↦_ eq₁ eq₂

inverse-erase {c = (G `?) ⨟ (c₁ ↦ c₂)}
  (⊢⨟ (⊢? g) (⊢↦ cwt dwt)) (nf-?↦ _ n₁ n₂)
  with inverse-erase cwt n₁ | inverse-erase dwt n₂
... | s₁ , eq₁ | s₂ , eq₂ =
  G ?ⁿ g ⨾ (＇ (s₁ ↣ s₂))
  , cong (λ x → (G `?) ⨟ x) (cong₂ _↦_ eq₁ eq₂)

inverse-erase {c = (c₁ ↦ c₂) ⨟ ((★ ⇒ ★) !)}
  (⊢⨟ (⊢↦ cwt dwt) (⊢! G-⇒)) (nf-↦! n₁ n₂ G-⇒)
  with inverse-erase cwt n₁ | inverse-erase dwt n₂
... | s₁ , eq₁ | s₂ , eq₂ =
  ′ (‹ (★ ⇒ ★) › (s₁ ↣ s₂) ⨾ G-⇒ !ⁿ)
  , cong (λ x → x ⨟ ((★ ⇒ ★) !)) (cong₂ _↦_ eq₁ eq₂)

inverse-erase {c = (★ ⇒ ★) `? ⨟ ((c₁ ↦ c₂) ⨟ ((★ ⇒ ★) !))}
  (⊢⨟ (⊢? G-⇒) (⊢⨟ (⊢↦ cwt dwt) (⊢! G-⇒)))
  (nf-?↦! G-⇒ n₁ n₂)
  with inverse-erase cwt n₁ | inverse-erase dwt n₂
... | s₁ , eq₁ | s₂ , eq₂ =
  (★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ (★ ⇒ ★) › (s₁ ↣ s₂) ⨾ G-⇒ !ⁿ)
  , cong (λ x → (★ ⇒ ★) `? ⨟ (x ⨟ ((★ ⇒ ★) !))) (cong₂ _↦_ eq₁ eq₂)

inverse-erase {c = (G `?) ⨟ (⊥ᶜ A ⇨ B)}
  (⊢⨟ (⊢? g) ⊢⊥) (nf-?⊥ _) =
  G ?ⁿ g ⨾ (⊥ⁿ G ⇨ B) , refl

inverse-erase {c = ⊥ᶜ A ⇨ B} ⊢⊥ nf-⊥ =
  ′ (⊥ⁿ A ⇨ B) , refl

mutual
  erase-normal
    : ∀ {A B}
    → (s : A ⇨ⁿ B)
    → Normalᶜ ⌊ s ⌋ˢ

  erase-normalⁱ
    : ∀ {A B}
    → (i : A ⇨ⁱ B)
    → Normalᶜ ⌊ i ⌋ⁱ

  erase-normalᵍ
    : ∀ {A B}
    → (g : A ⇨ᵍ B)
    → Normalᶜ ⌊ g ⌋ᵍ

  erase-normal (idⁿ A) = nf-id
  erase-normal (G ?ⁿ g) = nf-? g
  erase-normal (ℕ ?ⁿ g ⨾ (ℕ !ⁿ _)) = nf-?! g
  erase-normal ((★ ⇒ ★) ?ⁿ g ⨾ ((★ ⇒ ★) !ⁿ _)) = nf-?! g
  erase-normal (ℕ ?ⁿ g ⨾ (‹ _ › () ⨾ _ !ⁿ))
  erase-normal ((★ ⇒ ★) ?ⁿ g ⨾ (‹ (★ ⇒ ★) › (c ↣ d) ⨾ _ !ⁿ)) =
    nf-?↦! g (erase-normal c) (erase-normal d)
  erase-normal (ℕ ?ⁿ g ⨾ (＇ ()))
  erase-normal ((★ ⇒ ★) ?ⁿ g ⨾ (＇ (c ↣ d))) =
    nf-?↦ g (erase-normal c) (erase-normal d)
  erase-normal (G ?ⁿ g ⨾ (⊥ⁿ _ ⇨ _)) = nf-?⊥ g
  erase-normal (G ?ⁿ g ⨾ (G !ⁿ _)) = nf-?! g
  erase-normal (′ i) = erase-normalⁱ i

  erase-normalⁱ (G !ⁿ g) = nf-! g
  erase-normalⁱ (‹ ℕ › () ⨾ _ !ⁿ)
  erase-normalⁱ (‹ (★ ⇒ ★) › (c ↣ d) ⨾ gnd !ⁿ) =
    nf-↦! (erase-normal c) (erase-normal d) gnd
  erase-normalⁱ (＇ g) = erase-normalᵍ g
  erase-normalⁱ (⊥ⁿ A ⇨ B) = nf-⊥

  erase-normalᵍ (c ↣ d) = nf-↦ (erase-normal c) (erase-normal d)

normalizeᶜ : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → ∃[ c′ ] (c —↠ᶜᶜ c′) × Normalᶜ c′
normalizeᶜ cwt
  with normalize cwt
... | s , c↠s =
  ⌊ s ⌋ˢ , c↠s , erase-normal s

mutual
  coerceⁿ : ∀ {A B} → A ~ B → A ⇨ⁿ B
  coerceⁱ-⇒ : ∀ {A B C D}
    → C ~ A
    → B ~ D
    → (A ⇒ B) ⇨ⁱ (C ⇒ D)
  coerceⁱ-★ : ∀ {A B}
    → ★ ~ A
    → B ~ ★
    → (A ⇒ B) ⇨ⁱ ★
  coerceᵍ : ∀ {A B C D}
    → C ~ A
    → B ~ D
    → (A ⇒ B) ⇨ᵍ (C ⇒ D)

  coerceⁿ ~-ℕ = idⁿ ℕ
  coerceⁿ ~-★ = idⁿ ★
  coerceⁿ ★~ℕ = ℕ ?ⁿ G-ℕ
  coerceⁿ ℕ~★ = ′ (ℕ !ⁿ G-ℕ)
  coerceⁿ (★~⇒ c d) = (★ ⇒ ★) ?ⁿ G-⇒ ⨾ coerceⁱ-⇒ c d
  coerceⁿ (⇒~★ c d) = ′ (coerceⁱ-★ c d)
  coerceⁿ (~-⇒ c d) = ′ (coerceⁱ-⇒ c d)

  coerceⁱ-⇒ c d = ＇ (coerceᵍ c d)
  coerceⁱ-★ c d = ‹ (★ ⇒ ★) › (coerceᵍ c d) ⨾ G-⇒ !ⁿ

  coerceᵍ c d = coerceⁿ c ↣ coerceⁿ d

--------------------------------------------------------------------------------
-- Precision of normal forms
--------------------------------------------------------------------------------

infix 4 _⊑ⁿ_
infix 4 _⊑ⁱ_
infix 4 _⊑ᵍ_

-- The more precise side can error more.
mutual
  data _⊑ⁿ_ : ∀ {A B A′ B′} → (A ⇨ⁿ B) → (A′ ⇨ⁿ B′) → Set where
  
    -- id ⊑ ...
    
    id-⊑-id : ∀ {A A′}
      → A ⊑ A′
      → idⁿ A ⊑ⁿ idⁿ A′

    id-⊑-? : ∀ {G} {g : Ground G}
      → idⁿ ★ ⊑ⁿ (G ?ⁿ g)

    id-⊑-! : ∀ {G} {g : Ground G}
      → idⁿ ★ ⊑ⁿ (′ (G !ⁿ g))

    id-⊑-↣ : ∀ {A B C D}{c : C ⇨ⁿ A}{d : B ⇨ⁿ D}
      → idⁿ ★  ⊑ⁿ c
      → idⁿ ★  ⊑ⁿ d
      → idⁿ ★ ⊑ⁿ ′ ＇ (c ↣ d)

    id-⊑-↣-! : ∀ {A}{B}{c : ★ ⇨ⁿ A}{d : B ⇨ⁿ ★}
      → idⁿ ★  ⊑ⁿ c
      → idⁿ ★  ⊑ⁿ d
      → idⁿ ★ ⊑ⁿ (′ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ))

    id-⊑-?-! : ∀ {G} {g : Ground G}
      → idⁿ ★ ⊑ⁿ (G ?ⁿ g ⨾ (G !ⁿ g))

    id-⊑-?-↣ : ∀ {A}{B}{c : A ⇨ⁿ ★}{d : ★ ⇨ⁿ B}
      → idⁿ ★ ⊑ⁿ c
      → idⁿ ★ ⊑ⁿ d
      → idⁿ ★ ⊑ⁿ ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ ＇ (c ↣ d))

    id-⊑-?-↣-! : ∀ {c d : ★ ⇨ⁿ ★}
      → idⁿ ★ ⊑ⁿ c
      → idⁿ ★ ⊑ⁿ d
      → idⁿ ★ ⊑ⁿ ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ))

    -- (G ?) ⊑ ...
    
    ?-⊑-? : ∀ {G} {g g′ : Ground G}
      → (G ?ⁿ g) ⊑ⁿ (G ?ⁿ g′)

    ?-⊑-?-i : ∀ {G B} {g g′ : Ground G}
                {i : G ⇨ⁱ B}
      → G ⊑ B
      → (G ?ⁿ g) ⊑ⁿ (G ?ⁿ g′ ⨾ i)
      
    ?-⊑-↣ : ∀ {A B}{c : A ⇨ⁿ ★}{d : ★ ⇨ⁿ B}
      → (★ ⇒ ★) ?ⁿ G-⇒ ⊑ⁿ ′ ＇ (c ↣ d)

    ?-⊑-id : ∀ {G}{g : Ground G}
      → G ?ⁿ g ⊑ⁿ idⁿ G

    -- (G ? ; i) ⊑ ...

    ?-i-⊑-? : ∀ {G B} {g g′ : Ground G} {i : G ⇨ⁱ B}
      → B ⊑ G
      → (′ i) ⊑ⁿ idⁿ G
      → (G ?ⁿ g ⨾ i) ⊑ⁿ (G ?ⁿ g′)
      
    ?-i-⊑-?-j : ∀ {G B B′} {g g′ : Ground G} {i : G ⇨ⁱ B} {j : G ⇨ⁱ B′}
      → i ⊑ⁱ j
      → (G ?ⁿ g ⨾ i) ⊑ⁿ (G ?ⁿ g′ ⨾ j)

    ?-i-⊑-j : ∀ {G A B B′} {g : Ground G} {i : G ⇨ⁱ B} {j : A ⇨ⁱ B′}
      → i ⊑ⁱ j
      → (G ?ⁿ g ⨾ i) ⊑ⁿ (′ j)

    ?-i-⊑-id : ∀ {G B A} {g : Ground G} {i : G ⇨ⁱ B}
      → G ⊑ A
      → B ⊑ A
      → (′ i) ⊑ⁿ idⁿ A
      → (G ?ⁿ g ⨾ i) ⊑ⁿ idⁿ A
      
    -- (G ? ; c ↣ d ; G !) ⊑ ...

    ?-↣-!-⊑-? : ∀ {c d : ★ ⇨ⁿ ★}
      → c ⊑ⁿ idⁿ ★
      → d ⊑ⁿ idⁿ ★
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ (★ ⇒ ★) ?ⁿ G-⇒

    ?-↣-!-⊑-! : ∀ {c d : ★ ⇨ⁿ ★}
      → c ⊑ⁿ idⁿ ★
      → d ⊑ⁿ idⁿ ★
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ ′ ((★ ⇒ ★) !ⁿ G-⇒)

    ?-↣-!-⊑-↣ : ∀ {c d c′ d′ : ★ ⇨ⁿ ★}
      → c ⊑ⁿ c′
      → d ⊑ⁿ d′
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ ′ ＇ (c′ ↣ d′)
      
    ?-↣-!-⊑-?-↣ : ∀ {c d c′ d′ : ★ ⇨ⁿ ★}
      → c ⊑ⁿ c′
      → d ⊑ⁿ d′
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (＇ (c′ ↣ d′)))

    ?-↣-!-⊑-↣-! : ∀ {c d c′ d′ : ★ ⇨ⁿ ★}
      → c ⊑ⁿ c′
      → d ⊑ⁿ d′
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ (′ (‹ ★ ⇒ ★ › (c′ ↣ d′) ⨾ G-⇒ !ⁿ))

    ?-↣-!-⊑-?-! : ∀ {c d : ★ ⇨ⁿ ★}
      → c ⊑ⁿ idⁿ ★
      → d ⊑ⁿ idⁿ ★
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (★ ⇒ ★) !ⁿ G-⇒)

    ?-↣-!-⊑-?-↣-! : ∀ {c d c′ d′ : ★ ⇨ⁿ ★}
      → c ⊑ⁿ c′
      → d ⊑ⁿ d′
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c′ ↣ d′) ⨾ G-⇒ !ⁿ))

    ?-↣-!-⊑-id : ∀ {A B} {c d : ★ ⇨ⁿ ★}
      → c ⊑ⁿ idⁿ A
      → d ⊑ⁿ idⁿ B
      → ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ idⁿ (A ⇒ B)

    -- (G ? ; G !) ⊑ ...
    
    ?-!-⊑-?-! : ∀ {G} {g g′ : Ground G}
      → (G ?ⁿ g ⨾ (G !ⁿ g)) ⊑ⁿ (G ?ⁿ g′ ⨾ (G !ⁿ g′))

    ?-!-⊑-id : ∀ {A G} {g : Ground G}
      → G ⊑ A
      → (G ?ⁿ g ⨾ (G !ⁿ g)) ⊑ⁿ idⁿ A
      
    -- (G !) ⊑ ...
    
    !-⊑-id : ∀ {A G}{g : Ground G}
      → G ⊑ A
      → (′ (G !ⁿ g)) ⊑ⁿ idⁿ A

    !-⊑-↣ : ∀ {A B}{c : A ⇨ⁿ ★}{d : ★ ⇨ⁿ B}
      → ′ ((★ ⇒ ★) !ⁿ G-⇒) ⊑ⁿ ′ ＇ (c ↣ d)

    !-⊑-↣-! : ∀{c : ★ ⇨ⁿ ★}{d : ★ ⇨ⁿ ★}
      → ′ ((★ ⇒ ★) !ⁿ G-⇒) ⊑ⁿ ′ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)

    -- (c → d ; G!) ⊑ ...

    ↣-!-⊑-id : ∀ {A B C D}{c : ★ ⇨ⁿ A}{d : B ⇨ⁿ ★}
      → A ⊑ C
      → B ⊑ D
      → c  ⊑ⁿ idⁿ C
      → d  ⊑ⁿ idⁿ D
      → (′ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ idⁿ (C ⇒ D)

    ↣-!-⊑-! : ∀ {A B}{c : ★ ⇨ⁿ A}{d : B ⇨ⁿ ★}
      → c  ⊑ⁿ idⁿ ★
      → d  ⊑ⁿ idⁿ ★
      → (′ (‹ ★ ⇒ ★ › (c ↣ d) ⨾ G-⇒ !ⁿ)) ⊑ⁿ (′ ((★ ⇒ ★) !ⁿ G-⇒))

    -- i ⊑ ...

    i-⊑-j : ∀ {A B A′ B′} {i : A ⇨ⁱ B} {j : A′ ⇨ⁱ B′}
      → i ⊑ⁱ j
      → (′ i) ⊑ⁿ (′ j)

    -- (c → d) ⊑ ...
    ↣-⊑-id : ∀{A B C D A′ B′}{c : C ⇨ⁿ A}{d : B ⇨ⁿ D}
      → c ⊑ⁿ idⁿ A′
      → d ⊑ⁿ idⁿ B′
      → ′ ＇ (c ↣ d) ⊑ⁿ idⁿ (A′ ⇒ B′)

    -- error on the right
    s-⊑-?-⊥ : ∀ {A C G C′} {s : A ⇨ⁿ C} {g : Ground G}
      → A ⊑ ★
      → C ⊑ C′
      → s ⊑ⁿ (G ?ⁿ g ⨾ (⊥ⁿ G ⇨ C′))

    s-⊑-⊥ : ∀ {A B A′ B′} {s : A ⇨ⁿ B}
      → A ⊑ A′
      → B ⊑ B′
      → s ⊑ⁿ (′ (⊥ⁿ A′ ⇨ B′))

  data _⊑ⁱ_ : ∀ {A B A′ B′} → (A ⇨ⁱ B) → (A′ ⇨ⁱ B′) → Set where

    !-⊑-! : ∀ {G} {g g′ : Ground G}
      → (G !ⁿ g) ⊑ⁱ (G !ⁿ g′)

    g-!-⊑-h-! : ∀ {A A′ G} {g g′ : Ground G} {h : A ⇨ᵍ G} {k : A′ ⇨ᵍ G}
      → h ⊑ᵍ k
      → (‹ G › h ⨾ g !ⁿ) ⊑ⁱ (‹ G › k ⨾ g′ !ⁿ)

    g-⊑-h : ∀ {A B A′ B′} {g : A ⇨ᵍ B} {h : A′ ⇨ᵍ B′}
      → g ⊑ᵍ h
      → (＇ g) ⊑ⁱ (＇ h)

    -- drop rule
    g-!-⊑-h : ∀ {A A′ B G} {g : Ground G} {h : A ⇨ᵍ G} {k : A′ ⇨ᵍ B}
      → h ⊑ᵍ k
      → (‹ G › h ⨾ g !ⁿ) ⊑ⁱ (＇ k)

    -- error on the right
    i-⊑-⊥ⁱ : ∀ {A B A′ B′}{i : A ⇨ⁱ B}
      → A ⊑ A′
      → B ⊑ B′
      → i ⊑ⁱ (⊥ⁿ A′ ⇨ B′)

  data _⊑ᵍ_ : ∀ {A B A′ B′} → (A ⇨ᵍ B) → (A′ ⇨ᵍ B′) → Set where
    ↣-⊑-↣ : ∀ {A B C D A′ B′ C′ D′}
           {c : C ⇨ⁿ A} {d : B ⇨ⁿ D}
           {c′ : C′ ⇨ⁿ A′} {d′ : B′ ⇨ⁿ D′}
      → c ⊑ⁿ c′
      → d ⊑ⁿ d′
      → (c ↣ d) ⊑ᵍ (c′ ↣ d′)

mutual
  ⊑ⁿ-reflexive : ∀ {A}{B}{c : A ⇨ⁿ B} → c ⊑ⁿ c
  ⊑ⁱ-reflexive : ∀ {A}{B}{c : A ⇨ⁱ B} → c ⊑ⁱ c
  ⊑ᵍ-reflexive : ∀ {A}{B}{c : A ⇨ᵍ B} → c ⊑ᵍ c

  ⊑ⁿ-reflexive {c = idⁿ A} = id-⊑-id ⊑-refl
  ⊑ⁿ-reflexive {c = G ?ⁿ g} = ?-⊑-?
  ⊑ⁿ-reflexive {c = G ?ⁿ g ⨾ i} = ?-i-⊑-?-j ⊑ⁱ-reflexive
  ⊑ⁿ-reflexive {c = ′ i} = i-⊑-j ⊑ⁱ-reflexive

  ⊑ⁱ-reflexive {c = G !ⁿ g} = !-⊑-!
  ⊑ⁱ-reflexive {c = ‹ G › h ⨾ g !ⁿ} = g-!-⊑-h-! ⊑ᵍ-reflexive
  ⊑ⁱ-reflexive {c = ＇ g} = g-⊑-h ⊑ᵍ-reflexive
  ⊑ⁱ-reflexive {c = ⊥ⁿ A ⇨ B} = i-⊑-⊥ⁱ ⊑-refl ⊑-refl

  ⊑ᵍ-reflexive {c = c ↣ d} = ↣-⊑-↣ ⊑ⁿ-reflexive ⊑ⁿ-reflexive

mutual
  ⊑ⁿ→⊑ : ∀ {A B A′ B′}
      → (s : A ⇨ⁿ B) → (t : A′ ⇨ⁿ B′)
      → s ⊑ⁿ t
        ---------------
      → A ⊑ A′ × B ⊑ B′

  ⊑ⁱ→⊑ : ∀ {A B A′ B′}
      → (i : A ⇨ⁱ B) → (j : A′ ⇨ⁱ B′)
      → i ⊑ⁱ j
        ---------------
      → A ⊑ A′ × B ⊑ B′

  ⊑ᵍ→⊑ : ∀ {A B A′ B′}
      → (g : A ⇨ᵍ B) → (h : A′ ⇨ᵍ B′)
      → g ⊑ᵍ h
        ---------------
      → A ⊑ A′ × B ⊑ B′

  ⊑ⁿ→⊑ _ _ (id-⊑-id A⊑A′) = A⊑A′ , A⊑A′
  ⊑ⁿ→⊑ _ _ id-⊑-? = ⊑-★ , ⊑-★
  ⊑ⁿ→⊑ _ _ id-⊑-! = ⊑-★ , ⊑-refl
  ⊑ⁿ→⊑ _ _ (id-⊑-↣ _ _) = ⊑-★ , ⊑-★
  ⊑ⁿ→⊑ _ _ (id-⊑-↣-! _ _) = ⊑-★ , ⊑-★
  ⊑ⁿ→⊑ _ _ id-⊑-?-! = ⊑-refl , ⊑-refl
  ⊑ⁿ→⊑ _ _ (id-⊑-?-↣ _ _) = ⊑-refl , ⊑-★
  ⊑ⁿ→⊑ _ _ (id-⊑-?-↣-! _ _) = ⊑-refl , ⊑-refl
  ⊑ⁿ→⊑ _ _ ?-⊑-? = ⊑-refl , ⊑-refl
  ⊑ⁿ→⊑ _ _ (?-⊑-?-i G⊑B) = ⊑-refl , G⊑B
  ⊑ⁿ→⊑ _ _ ?-⊑-↣ = ⊑-★ , ⊑-⇒ ⊑-★ ⊑-★
  ⊑ⁿ→⊑ _ _ ?-⊑-id = ⊑-★ , ⊑-refl
  ⊑ⁿ→⊑ _ _ (?-i-⊑-? B⊑G _) = ⊑-refl , B⊑G
  ⊑ⁿ→⊑ _ _ (?-i-⊑-?-j i⊑j)
    with ⊑ⁱ→⊑ _ _ i⊑j
  ... | _ , B⊑B′ = ⊑-refl , B⊑B′
  ⊑ⁿ→⊑ _ _ (?-i-⊑-j i⊑j)
    with ⊑ⁱ→⊑ _ _ i⊑j
  ... | _ , B⊑B′ = ⊑-★ , B⊑B′
  ⊑ⁿ→⊑ _ _ (?-i-⊑-id _ B⊑A _) = ⊑-★ , B⊑A
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-? _ _) = ⊑-refl , ⊑-★
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-! _ _) = ⊑-★ , ⊑-refl
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-↣ _ _) = ⊑-★ , ⊑-★
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-?-↣ _ _) = ⊑-refl , ⊑-★
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-↣-! _ _) = ⊑-★ , ⊑-refl
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-?-! _ _) = ⊑-refl , ⊑-refl
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-?-↣-! _ _) = ⊑-refl , ⊑-refl
  ⊑ⁿ→⊑ _ _ (?-↣-!-⊑-id _ _) = ⊑-★ , ⊑-★
  ⊑ⁿ→⊑ _ _ ?-!-⊑-?-! = ⊑-refl , ⊑-refl
  ⊑ⁿ→⊑ _ _ (?-!-⊑-id _) = ⊑-★ , ⊑-★
  ⊑ⁿ→⊑ _ _ (!-⊑-id G⊑A) = G⊑A , ⊑-★
  ⊑ⁿ→⊑ _ _ !-⊑-↣ = ⊑-refl , ⊑-★
  ⊑ⁿ→⊑ _ _ !-⊑-↣-! = ⊑-refl , ⊑-refl
  ⊑ⁿ→⊑ _ _ (↣-!-⊑-id A⊑C B⊑D _ _) = ⊑-⇒ A⊑C B⊑D , ⊑-★
  ⊑ⁿ→⊑ _ _ (↣-!-⊑-! c⊑id★ d⊑id★)
    with ⊑ⁿ→⊑ _ _ c⊑id★ | ⊑ⁿ→⊑ _ _ d⊑id★
  ... | _ , A⊑★ | B⊑★ , _ = ⊑-⇒ A⊑★ B⊑★ , ⊑-refl
  ⊑ⁿ→⊑ _ _ (i-⊑-j i⊑j) = ⊑ⁱ→⊑ _ _ i⊑j
  ⊑ⁿ→⊑ _ _ (s-⊑-?-⊥ A⊑★ C⊑C′) = ⊑-trans A⊑★ ⊑-★ , C⊑C′
  ⊑ⁿ→⊑ _ _ (↣-⊑-id c⊑id d⊑id)
    with ⊑ⁿ→⊑ _ _ c⊑id | ⊑ⁿ→⊑ _ _ d⊑id
  ... | C⊑A′ , A⊑A′ | B⊑B′ , D⊑B′ =
    ⊑-⇒ A⊑A′ B⊑B′ , ⊑-⇒ C⊑A′ D⊑B′
  ⊑ⁿ→⊑ _ _ (s-⊑-⊥ A⊑A′ B⊑B′) = A⊑A′ , B⊑B′

  ⊑ⁱ→⊑ _ _ !-⊑-! = ⊑-refl , ⊑-refl
  ⊑ⁱ→⊑ _ _ (g-!-⊑-h-! h⊑k)
    with ⊑ᵍ→⊑ _ _ h⊑k
  ... | A⊑A′ , _ = A⊑A′ , ⊑-refl
  ⊑ⁱ→⊑ _ _ (g-⊑-h g⊑h) = ⊑ᵍ→⊑ _ _ g⊑h
  ⊑ⁱ→⊑ _ _ (g-!-⊑-h h⊑k)
    with ⊑ᵍ→⊑ _ _ h⊑k
  ... | A⊑A′ , _ = A⊑A′ , ⊑-★
  ⊑ⁱ→⊑ _ _ (i-⊑-⊥ⁱ A⊑A′ B⊑B′) = A⊑A′ , B⊑B′

  ⊑ᵍ→⊑ _ _ (↣-⊑-↣ c⊑c′ d⊑d′)
    with ⊑ⁿ→⊑ _ _ c⊑c′ | ⊑ⁿ→⊑ _ _ d⊑d′
  ... | C⊑C′ , A⊑A′ | B⊑B′ , D⊑D′ =
    ⊑-⇒ A⊑A′ B⊑B′ , ⊑-⇒ C⊑C′ D⊑D′

mutual
  coerceⁿ-monotonic : ∀ {A A′ B B′}
    → A′ ⊑ A
    → (c : A ~ B)
    → B′ ⊑ B
    → (d : A′ ~ B′)
    → coerceⁿ d ⊑ⁿ coerceⁿ c

  coerceⁱ-⇒-monotonic
    : ∀ {A A′ B B′ C C′ D D′}
    → C′ ⊑ C
    → (c : C ~ A)
    → A′ ⊑ A
    → (c′ : C′ ~ A′)
    → B′ ⊑ B
    → (d : B ~ D)
    → D′ ⊑ D
    → (d′ : B′ ~ D′)
    → coerceⁱ-⇒ c′ d′ ⊑ⁱ coerceⁱ-⇒ c d

  coerceⁱ-★-monotonic
    : ∀ {A A′ B B′}
    → A′ ⊑ A
    → (c : ★ ~ A)
    → B′ ⊑ B
    → (d : B ~ ★)
    → (c′ : ★ ~ A′)
    → (d′ : B′ ~ ★)
    → coerceⁱ-★ c′ d′ ⊑ⁱ coerceⁱ-★ c d

  coerceᵍ-monotonic
    : ∀ {A A′ B B′ C C′ D D′}
    → C′ ⊑ C
    → (c : C ~ A)
    → A′ ⊑ A
    → (c′ : C′ ~ A′)
    → B′ ⊑ B
    → (d : B ~ D)
    → D′ ⊑ D
    → (d′ : B′ ~ D′)
    → coerceᵍ c′ d′ ⊑ᵍ coerceᵍ c d

  coerceⁿ-monotonic A′⊑A ~-ℕ B′⊑B ~-ℕ = id-⊑-id ⊑-ℕ
  coerceⁿ-monotonic A′⊑A ~-ℕ B′⊑B ~-★ = id-⊑-id ⊑-★
  coerceⁿ-monotonic A′⊑A ~-ℕ B′⊑B ★~ℕ = ?-⊑-id
  coerceⁿ-monotonic A′⊑A ~-ℕ B′⊑B ℕ~★ = !-⊑-id ⊑-refl
  coerceⁿ-monotonic A′⊑A ~-★ B′⊑B ~-★ = id-⊑-id ⊑-★
  coerceⁿ-monotonic A′⊑A ★~ℕ B′⊑B ~-★ = id-⊑-?
  coerceⁿ-monotonic A′⊑A ★~ℕ B′⊑B ★~ℕ = ?-⊑-?
  coerceⁿ-monotonic A′⊑A ℕ~★ B′⊑B ~-★ = id-⊑-!
  coerceⁿ-monotonic A′⊑A ℕ~★ B′⊑B ℕ~★ = i-⊑-j !-⊑-!
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ ~-★ ~-★) ⊑-★ ~-★ = id-⊑-?-↣ (id-⊑-id ⊑-★) (id-⊑-id ⊑-★)
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ ~-★ ★~ℕ) ⊑-★ ~-★ = id-⊑-?-↣ (id-⊑-id ⊑-★) id-⊑-?
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ ~-★ (★~⇒ ★~B ★~B₁)) ⊑-★ ~-★ =
    id-⊑-?-↣ (id-⊑-id ⊑-★) (coerceⁿ-monotonic ⊑-★ (★~⇒ ★~B ★~B₁) ⊑-★ ~-★)
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ ℕ~★ ~-★) ⊑-★ ~-★ = id-⊑-?-↣ id-⊑-! (id-⊑-id ⊑-★)
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ ℕ~★ ★~ℕ) ⊑-★ ~-★ = id-⊑-?-↣ id-⊑-! id-⊑-?
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ ℕ~★ (★~⇒ ★~B ★~B₁)) ⊑-★ ~-★ =
    id-⊑-?-↣ id-⊑-! (coerceⁿ-monotonic ⊑-★ (★~⇒ ★~B ★~B₁) ⊑-★ ~-★)
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ (⇒~★ A~★ A~★₁) ~-★) ⊑-★ ~-★ =
    id-⊑-?-↣ (coerceⁿ-monotonic ⊑-★ (⇒~★ A~★ A~★₁) ⊑-★ ~-★) (id-⊑-id ⊑-★)
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ (⇒~★ A~★ A~★₁) ★~ℕ) ⊑-★ ~-★ =
    id-⊑-?-↣ (coerceⁿ-monotonic ⊑-★ (⇒~★ A~★ A~★₁) ⊑-★ ~-★) id-⊑-?
  coerceⁿ-monotonic {B′ = ★} ⊑-★ (★~⇒ (⇒~★ A~★ A~★₁) (★~⇒ ★~B ★~B₁)) ⊑-★ ~-★ =
    id-⊑-?-↣ (coerceⁿ-monotonic ⊑-★ (⇒~★ A~★ A~★₁) ⊑-★ ~-★)
             (coerceⁿ-monotonic ⊑-★ (★~⇒ ★~B ★~B₁) ⊑-★ ~-★)
  coerceⁿ-monotonic A′⊑A (★~⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
    ?-i-⊑-?-j (coerceⁱ-⇒-monotonic B′₁⊑B₁ c₁ ⊑-★ d₁ ⊑-★ c₂ B′₂⊑B₂ d₂)
  coerceⁿ-monotonic A′⊑A (⇒~★ c₁ c₂) B′⊑B ~-★ =
    id-⊑-↣-!
      (coerceⁿ-monotonic ⊑-refl c₁ ⊑-★ ~-★)
      (coerceⁿ-monotonic ⊑-★ c₂ ⊑-refl ~-★)
  coerceⁿ-monotonic (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (⇒~★ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
    i-⊑-j (coerceⁱ-★-monotonic A′₁⊑A₁ c₁ A′₂⊑A₂ c₂ d₁ d₂)
  coerceⁿ-monotonic ⊑-★ (~-⇒ c₁ c₂) ⊑-★ ~-★ =
    id-⊑-↣
      (coerceⁿ-monotonic ⊑-★ c₁ ⊑-★ ~-★)
      (coerceⁿ-monotonic ⊑-★ c₂ ⊑-★ ~-★)
  coerceⁿ-monotonic A′⊑A (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
    ?-i-⊑-j (coerceⁱ-⇒-monotonic B′₁⊑B₁ c₁ ⊑-★ d₁ ⊑-★ c₂ B′₂⊑B₂ d₂)
  coerceⁿ-monotonic (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
    i-⊑-j (g-!-⊑-h (coerceᵍ-monotonic ⊑-★ c₁ A′₁⊑A₁ d₁ A′₂⊑A₂ c₂ ⊑-★ d₂))
  coerceⁿ-monotonic (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (~-⇒ d₁ d₂) =
    i-⊑-j (coerceⁱ-⇒-monotonic B′₁⊑B₁ c₁ A′₁⊑A₁ d₁ A′₂⊑A₂ c₂ B′₂⊑B₂ d₂)

  coerceⁱ-⇒-monotonic C′⊑C c A′⊑A c′ B′⊑B d D′⊑D d′ =
    g-⊑-h (coerceᵍ-monotonic C′⊑C c A′⊑A c′ B′⊑B d D′⊑D d′)

  coerceⁱ-★-monotonic A′⊑A c B′⊑B d c′ d′ =
    g-!-⊑-h-! (coerceᵍ-monotonic ⊑-★ c A′⊑A c′ B′⊑B d ⊑-★ d′)

  coerceᵍ-monotonic C′⊑C c A′⊑A c′ B′⊑B d D′⊑D d′ =
    ↣-⊑-↣
      (coerceⁿ-monotonic C′⊑C c A′⊑A c′)
      (coerceⁿ-monotonic B′⊑B d D′⊑D d′)

normalize-seq-monotonic
  : ∀ {A B C A′ B′ C′}
  → (s : A ⇨ⁿ B)
  → (s′ : A′ ⇨ⁿ B′)
  → (t : B ⇨ⁿ C)
  → (t′ : B′ ⇨ⁿ C′)
  → s ⊑ⁿ s′
  → t ⊑ⁿ t′
  → proj₁ (normalize-seq s t) ⊑ⁿ proj₁ (normalize-seq s′ t′)

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ with s⊑s′
-- case id-⊑-id
... | id-⊑-id A⊑A′ = t⊑t′

-- case id-⊑-?
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | (id-⊑-?{G}{g})
    with t⊑t′
... | id-⊑-id x = s⊑s′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | (id-⊑-? {G} {g}) | id-⊑-! {g = g′}
  rewrite ground-irrelevant g g′ = id-⊑-?-!
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | (id-⊑-? {G = ★ ⇒ ★} {g = G-⇒}) | id-⊑-↣ t⊑t′₁ t⊑t′₂ =
  id-⊑-?-↣ t⊑t′₁ t⊑t′₂
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | (id-⊑-? {G = ★ ⇒ ★} {g = G-⇒}) | id-⊑-↣-! t⊑t′₁ t⊑t′₂ =
  id-⊑-?-↣-! t⊑t′₁ t⊑t′₂
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | (id-⊑-? {G = ★ ⇒ ★} {g = G-⇒}) | ?-⊑-↣ =
  ?-⊑-?-i (⊑-⇒ ⊑-★ ⊑-★)
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | (id-⊑-? {G} {g}) | ?-⊑-id = ?-⊑-?
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ℕ} {g = g})
  | ?-i-⊑-j {G = ℕ} {g = g′} x
  rewrite ground-irrelevant g′ g
  = ?-i-⊑-?-j x
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ℕ} {g = g})
  | ?-i-⊑-j {G = ★ ⇒ ★} {i = i} {j = j} x
  with ⊑ⁱ→⊑ i j x
... | (() , _)
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ★ ⇒ ★} {g = g})
  | ?-i-⊑-j {G = ℕ} {i = i} {j = j} x
  with ⊑ⁱ→⊑ i j x
... | (() , _)
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ★ ⇒ ★} {g = g})
  | ?-i-⊑-j {G = ★ ⇒ ★} {g = g′} x
  rewrite ground-irrelevant g′ g
  = ?-i-⊑-?-j x
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G} {g})
  | ?-i-⊑-id {G = G₁} {g = g₁} G₁⊑G x₁ t⊑t′₁
  with ground-⊑-equal g₁ g G₁⊑G
... | refl = ?-i-⊑-? x₁ t⊑t′₁
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ★ ⇒ ★} {g = G-⇒})
  | ?-↣-!-⊑-! t⊑t′₁ t⊑t′₂ =
  ?-↣-!-⊑-?-! t⊑t′₁ t⊑t′₂
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ★ ⇒ ★} {g = G-⇒})
  | ?-↣-!-⊑-↣ t⊑t′₁ t⊑t′₂ =
  ?-↣-!-⊑-?-↣ t⊑t′₁ t⊑t′₂
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ★ ⇒ ★} {g = G-⇒})
  | ?-↣-!-⊑-↣-! t⊑t′₁ t⊑t′₂ =
  ?-↣-!-⊑-?-↣-! t⊑t′₁ t⊑t′₂
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G = ★ ⇒ ★} {g = G-⇒})
  | ?-↣-!-⊑-id t⊑t′₁ t⊑t′₂ =
  ?-↣-!-⊑-? t⊑t′₁ t⊑t′₂
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G} {g})
  | ?-!-⊑-id {G = G₁} {g = g₁} x
  with ground-⊑-equal g₁ g x
... | refl = ?-i-⊑-? ⊑-★ (!-⊑-id x)
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | (id-⊑-? {G} {g})
  | s-⊑-⊥ x x₁ = s-⊑-?-⊥ ⊑-★ x₁
normalize-seq-monotonic .(idⁿ ★) .(_ ?ⁿ _) (′ i) t′ s⊑s′ t⊑t′
  | id-⊑-? {_} {_}
  | i-⊑-j (i-⊑-⊥ⁱ x x₁)
  with ★⇨ⁱ-is-⊥ i
... | refl = s-⊑-?-⊥ ⊑-refl x₁

-- case id-⊑-!
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | id-⊑-!
  with t⊑t′
... | id-⊑-id x = id-⊑-!
... | ?-i-⊑-id {g = G-ℕ} () x₁ w
... | ?-i-⊑-id {g = G-⇒} () x₁ w
... | ?-!-⊑-id {g = G-ℕ} ()
... | ?-!-⊑-id {g = G-⇒} ()
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | id-⊑-? {g = G-ℕ} = id-⊑-id ⊑-★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | id-⊑-? {g = G-⇒} = id-⊑-id ⊑-★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | id-⊑-?-! {g = G-ℕ} = id-⊑-!
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | id-⊑-?-! {g = G-⇒} = id-⊑-!
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-⊑-? {g = G-ℕ} {g′ = G-ℕ} = ?-⊑-id
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-⊑-? {g = G-⇒} {g′ = G-⇒} = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-⊑-? {g = G-⇒} {g′ = G-⇒} = ?-⊑-id
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-⊑-? {g = G-ℕ} {g′ = G-ℕ} = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-i-⊑-? {g = G-ℕ} {g′ = G-ℕ} x w = ?-i-⊑-id ⊑-refl x w
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-i-⊑-? {g = G-⇒} {g′ = G-⇒} x w = s-⊑-⊥ ⊑-★ x
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-i-⊑-? {g = G-⇒} {g′ = G-⇒} x w = ?-i-⊑-id ⊑-refl x w
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-i-⊑-? {g = G-ℕ} {g′ = G-ℕ} x w = s-⊑-⊥ ⊑-★ x
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-i-⊑-?-j {g = G-ℕ} {g′ = G-ℕ} x = ?-i-⊑-j x
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-i-⊑-?-j {g = G-⇒} {g′ = G-⇒} x
  with ⊑ⁱ→⊑ _ _ x
... | _ , B⊑B′ = s-⊑-⊥ ⊑-★ B⊑B′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-i-⊑-?-j {g = G-⇒} {g′ = G-⇒} x = ?-i-⊑-j x
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-i-⊑-?-j {g = G-ℕ} {g′ = G-ℕ} x
  with ⊑ⁱ→⊑ _ _ x
... | _ , B⊑B′ = s-⊑-⊥ ⊑-★ B⊑B′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-!-⊑-?-! {g = G-ℕ} {g′ = G-ℕ} = ?-i-⊑-j !-⊑-!
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-!-⊑-?-! {g = G-⇒} {g′ = G-⇒} = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-!-⊑-?-! {g = G-⇒} {g′ = G-⇒} = ?-i-⊑-j !-⊑-!
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-!-⊑-?-! {g = G-ℕ} {g′ = G-ℕ} = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-!
  | ?-i-⊑-j {g = g} x
  with ⊑ⁱ→⊑ _ _ x
... | G⊑★ , _ with ground-not-⊑★ g G⊑★
... | ()
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-!
  | i-⊑-j {i = i} {j = j} x
  with ★⇨ⁱ-is-⊥ j | ⊑ⁱ→⊑ i j x
... | refl | A⊑★ , B⊑C′ =
  i-⊑-j (i-⊑-⊥ⁱ (⊑-trans A⊑★ ⊑-★) B⊑C′)
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | s-⊑-?-⊥ {g = G-ℕ} A⊑★ C⊑C′
  = s-⊑-⊥ (⊑-trans A⊑★ ⊑-★) C⊑C′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | s-⊑-?-⊥ {g = G-⇒} A⊑★ C⊑C′
  = s-⊑-⊥ (⊑-trans A⊑★ ⊑-★) C⊑C′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | s-⊑-?-⊥ {g = G-ℕ} A⊑★ C⊑C′
  = s-⊑-⊥ (⊑-trans A⊑★ ⊑-★) C⊑C′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | s-⊑-?-⊥ {g = G-⇒} A⊑★ C⊑C′
  = s-⊑-⊥ (⊑-trans A⊑★ ⊑-★) C⊑C′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | id-⊑-? {g = G-⇒} = s-⊑-⊥ ⊑-★ ⊑-★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | id-⊑-? {g = G-ℕ} = s-⊑-⊥ ⊑-★ ⊑-★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | id-⊑-?-! {g = G-⇒} = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | id-⊑-?-! {g = G-ℕ} = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | id-⊑-?-↣ c⊑ d⊑ = s-⊑-⊥ ⊑-★ ⊑-★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | id-⊑-?-↣ c⊑ d⊑ = id-⊑-↣ c⊑ d⊑
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | id-⊑-?-↣-! c⊑ d⊑ = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | id-⊑-?-↣-! c⊑ d⊑ = id-⊑-↣-! c⊑ d⊑
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-!
  | ?-⊑-?-i G⊑B = {!!}
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-↣-!-⊑-? c⊑id★ d⊑id★ = s-⊑-⊥ ⊑-★ ⊑-★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-↣-!-⊑-? c⊑id★ d⊑id★ = ?-↣-!-⊑-id c⊑id★ d⊑id★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-↣-!-⊑-?-↣ c⊑c′ d⊑d′ = s-⊑-⊥ ⊑-★ ⊑-★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-↣-!-⊑-?-↣ c⊑c′ d⊑d′ = ?-↣-!-⊑-↣ c⊑c′ d⊑d′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-↣-!-⊑-?-! c⊑id★ d⊑id★ = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-↣-!-⊑-?-! c⊑id★ d⊑id★ = ?-↣-!-⊑-! c⊑id★ d⊑id★
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-ℕ}
  | ?-↣-!-⊑-?-↣-! c⊑c′ d⊑d′ = s-⊑-⊥ ⊑-★ ⊑-refl
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-! {g = G-⇒}
  | ?-↣-!-⊑-?-↣-! c⊑c′ d⊑d′ = ?-↣-!-⊑-↣-! c⊑c′ d⊑d′
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′
  | id-⊑-!
  | s-⊑-⊥ A⊑★ B⊑C′ = s-⊑-⊥ ⊑-★ B⊑C′

-- case id-⊑-↣
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | id-⊑-↣ c⊑ d⊑
  with t⊑t′
... | id-⊑-id x = id-⊑-↣ c⊑ d⊑
... | x = {!!}

-- case id-⊑-↣-!
normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | id-⊑-↣-! c⊑ d⊑
  with t⊑t′
... | id-⊑-id x = id-⊑-↣-! c⊑ d⊑
... | x = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | id-⊑-?-!
  with t⊑t′
... | id-⊑-id x = id-⊑-?-!
... | x = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | id-⊑-?-↣ c⊑ d⊑
  with t⊑t′
... | id-⊑-id x = id-⊑-?-↣ c⊑ d⊑
... | x = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | id-⊑-?-↣-! c⊑ d⊑
  with t⊑t′
... | id-⊑-id x = id-⊑-?-↣-! c⊑ d⊑
... | x = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-⊑-? = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-⊑-?-i G⊑B = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-⊑-↣ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-⊑-id = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-i-⊑-? B⊑G i⊑idG = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-i-⊑-?-j i⊑j = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-i-⊑-j i⊑j = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-i-⊑-id G⊑A B⊑A i⊑idA = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-? c⊑id★ d⊑id★ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-! c⊑id★ d⊑id★ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-↣ c⊑c′ d⊑d′ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-?-↣ c⊑c′ d⊑d′ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-↣-! c⊑c′ d⊑d′ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-?-! c⊑id★ d⊑id★ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-?-↣-! c⊑c′ d⊑d′ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-↣-!-⊑-id c⊑idA d⊑idB = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-!-⊑-?-! = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ?-!-⊑-id G⊑A = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | !-⊑-id G⊑A = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | !-⊑-↣ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | !-⊑-↣-! = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ↣-!-⊑-id A⊑C B⊑D c⊑idC d⊑idD = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ↣-!-⊑-! c⊑id★ d⊑id★ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | i-⊑-j i⊑j = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | s-⊑-?-⊥ A⊑★ C⊑C′ = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | ↣-⊑-id c⊑idA d⊑idB = {!!}

normalize-seq-monotonic s s′ t t′ s⊑s′ t⊑t′ | s-⊑-⊥ A⊑A′ B⊑B′ = {!!}
