module CoercionNormalForm where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
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
infix 6 _?ⁿ_⨾_ _?ⁿ_⨾! _?ⁿ_⨾_⨾! ‹_›_⨾_!ⁿ

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
    _?ⁿ_⨾! : ∀ (G : Ty)
      → Ground G
      → ★ ⇨ⁿ ★
    _?ⁿ_⨾_⨾! : ∀ (G : Ty)
      → Ground G
      → G ⇨ᵍ G
      → ★ ⇨ⁿ ★
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
  ⌊ G ?ⁿ _ ⨾! ⌋ˢ = G `? ⨟ G !
  ⌊ G ?ⁿ _ ⨾ g ⨾! ⌋ˢ = (G `? ⨟ ⌊ g ⌋ᵍ) ⨟ G !
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
  wtS (G ?ⁿ g ⨾!) = ⊢⨟ (⊢? g) (⊢! g)
  wtS (G ?ⁿ g ⨾ h ⨾!) = ⊢⨟ (⊢⨟ (⊢? g) (wtG h)) (⊢! g)
  wtS (′ i) = wtI i

  wtI (G !ⁿ g) = ⊢! g
  wtI (‹ G › g ⨾ gnd !ⁿ) = ⊢⨟ (wtG g) (⊢! gnd)
  wtI (＇ g) = wtG g
  wtI (⊥ⁿ A ⇨ B) = ⊢⊥

  wtG (c ↣ d) = ⊢↦ (wtS c) (wtS d)

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

  normalize-seq (G ?ⁿ g ⨾ h ⨾!) t
    with (‹ G › h ⨾ g !ⁿ) i⨟s t
  ... | inj₁ (j , h!⨟t↠j) =
    G ?ⁿ g ⨾ j
    , (((((G `?) ⨟ ⌊ h ⌋ᵍ) ⨟ (G !)) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-assocRᶜ ⟩
      ((G `?) ⨟ (⌊ h ⌋ᵍ ⨟ (G !))) ⨟ ⌊ t ⌋ˢ
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      (G `?) ⨟ ((⌊ h ⌋ᵍ ⨟ (G !)) ⨟ ⌊ t ⌋ˢ)
      —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ h!⨟t↠j ⟩
      (G `?) ⨟ ⌊ j ⌋ⁱ
      ∎ᶜᶜ)
  ... | inj₂ (refl , h!⨟t↠id) =
    G ?ⁿ g
    , (((((G `?) ⨟ ⌊ h ⌋ᵍ) ⨟ (G !)) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-assocRᶜ ⟩
      ((G `?) ⨟ (⌊ h ⌋ᵍ ⨟ (G !))) ⨟ ⌊ t ⌋ˢ
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      (G `?) ⨟ ((⌊ h ⌋ᵍ ⨟ (G !)) ⨟ ⌊ t ⌋ˢ)
      —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ h!⨟t↠id ⟩
      ((G `?) ⨟ idᶜ G)
      —→ᶜᶜ⟨ β-idRᶜ ⟩
      (G `?)
      ∎ᶜᶜ)

  normalize-seq (G ?ⁿ g ⨾!) t
    with (G !ⁿ g) i⨟s t
  ... | inj₁ (j , !⨟t↠j) =
    G ?ⁿ g ⨾ j
    , ((((G `?) ⨟ (G !)) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((G `?) ⨟ ((G !) ⨟ ⌊ t ⌋ˢ))
      —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ !⨟t↠j ⟩
      ((G `?) ⨟ ⌊ j ⌋ⁱ)
      ∎ᶜᶜ)
  ... | inj₂ (refl , !⨟t↠id) =
    G ?ⁿ g
    , ((((G `?) ⨟ (G !)) ⨟ ⌊ t ⌋ˢ)
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      ((G `?) ⨟ ((G !) ⨟ ⌊ t ⌋ˢ))
      —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ !⨟t↠id ⟩
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

  _i⨟s_ (ℕ !ⁿ G-ℕ) (ℕ ?ⁿ G-ℕ ⨾!) =
    inj₁ (ℕ !ⁿ G-ℕ
    , (((ℕ !) ⨟ ((ℕ `?) ⨟ (ℕ !))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      (((ℕ !) ⨟ (ℕ `?)) ⨟ (ℕ !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-proj-inj-okᶜ ⟩
      ((idᶜ ℕ) ⨟ (ℕ !))
      —→ᶜᶜ⟨ β-idLᶜ ⟩
      (ℕ !)
      ∎ᶜᶜ)))

  _i⨟s_ ((★ ⇒ ★) !ⁿ G-⇒) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾!) =
    inj₁ ((★ ⇒ ★) !ⁿ G-⇒
    , ((((★ ⇒ ★) !) ⨟ (((★ ⇒ ★) `?) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      ((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-proj-inj-okᶜ ⟩
      ((idᶜ (★ ⇒ ★)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ β-idLᶜ ⟩
      ((★ ⇒ ★) !)
      ∎ᶜᶜ)))

  _i⨟s_ {A = A} (ℕ !ⁿ G-ℕ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾!) =
    inj₁ (⊥ⁿ A ⇨ ★
    , ((((ℕ !) ⨟ (((★ ⇒ ★) `?) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      (((ℕ !) ⨟ ((★ ⇒ ★) `?)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ())) ⟩
      ((⊥ᶜ ℕ ⇨ (★ ⇒ ★)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ β-⊥Lᶜ (⊢! G-⇒) ⟩
      (⊥ᶜ ℕ ⇨ ★)
      ∎ᶜᶜ)))

  _i⨟s_ {A = A} ((★ ⇒ ★) !ⁿ G-⇒) (ℕ ?ⁿ G-ℕ ⨾!) =
    inj₁ (⊥ⁿ A ⇨ ★
    , (((((★ ⇒ ★) !) ⨟ ((ℕ `?) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      ((((★ ⇒ ★) !) ⨟ (ℕ `?)) ⨟ (ℕ !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ())) ⟩
      ((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ (ℕ !))
      —→ᶜᶜ⟨ β-⊥Lᶜ (⊢! G-ℕ) ⟩
      (⊥ᶜ (★ ⇒ ★) ⇨ ★)
      ∎ᶜᶜ)))

  _i⨟s_ (ℕ !ⁿ G-ℕ) (ℕ ?ⁿ G-ℕ ⨾ () ⨾!)

  _i⨟s_ ((★ ⇒ ★) !ⁿ G-⇒) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ k ⨾!) =
    inj₁ (‹ (★ ⇒ ★) › k ⨾ G-⇒ !ⁿ
    , (((((★ ⇒ ★) !) ⨟ ((((★ ⇒ ★) `?) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      ((((★ ⇒ ★) !) ⨟ (((★ ⇒ ★) `?) ⨟ ⌊ k ⌋ᵍ)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-assocLᶜ ⟩
      (((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (ξ-⨟₁ᶜ β-proj-inj-okᶜ) ⟩
      (((idᶜ (★ ⇒ ★)) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-idLᶜ ⟩
      (⌊ k ⌋ᵍ ⨟ ((★ ⇒ ★) !))
      ∎ᶜᶜ)))

  _i⨟s_ {A = A} (ℕ !ⁿ G-ℕ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ k ⨾!) =
    inj₁ (⊥ⁿ A ⇨ ★
    , ((((ℕ !) ⨟ ((((★ ⇒ ★) `?) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      (((ℕ !) ⨟ (((★ ⇒ ★) `?) ⨟ ⌊ k ⌋ᵍ)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-assocLᶜ ⟩
      ((((ℕ !) ⨟ ((★ ⇒ ★) `?)) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ()))) ⟩
      (((⊥ᶜ ℕ ⇨ (★ ⇒ ★)) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (β-⊥Lᶜ (wtG k)) ⟩
      ((⊥ᶜ ℕ ⇨ (★ ⇒ ★)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ β-⊥Lᶜ (⊢! G-⇒) ⟩
      (⊥ᶜ ℕ ⇨ ★)
      ∎ᶜᶜ)))

  _i⨟s_ {A = A} ((★ ⇒ ★) !ⁿ G-⇒) (ℕ ?ⁿ G-ℕ ⨾ k ⨾!) =
    inj₁ (⊥ⁿ A ⇨ ★
    , (((((★ ⇒ ★) !) ⨟ (((ℕ `?) ⨟ ⌊ k ⌋ᵍ) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      ((((★ ⇒ ★) !) ⨟ ((ℕ `?) ⨟ ⌊ k ⌋ᵍ)) ⨟ (ℕ !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-assocLᶜ ⟩
      (((((★ ⇒ ★) !) ⨟ (ℕ `?)) ⨟ ⌊ k ⌋ᵍ) ⨟ (ℕ !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ()))) ⟩
      (((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ ⌊ k ⌋ᵍ) ⨟ (ℕ !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (β-⊥Lᶜ (wtG k)) ⟩
      ((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ (ℕ !))
      —→ᶜᶜ⟨ β-⊥Lᶜ (⊢! G-ℕ) ⟩
      (⊥ᶜ (★ ⇒ ★) ⇨ ★)
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

  _i⨟s_ (‹ (★ ⇒ ★) › g ⨾ G-⇒ !ⁿ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾!) =
    inj₁ (‹ (★ ⇒ ★) › g ⨾ G-⇒ !ⁿ
    , ((((⌊ g ⌋ᵍ ⨟ ((★ ⇒ ★) !)) ⨟ (((★ ⇒ ★) `?) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ (((★ ⇒ ★) !) ⨟ (((★ ⇒ ★) `?) ⨟ ((★ ⇒ ★) !))))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-assocLᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ ((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ β-proj-inj-okᶜ) ⟩
      (⌊ g ⌋ᵍ ⨟ ((idᶜ (★ ⇒ ★)) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-idLᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ ((★ ⇒ ★) !))
      ∎ᶜᶜ)))

  _i⨟s_ (‹ (★ ⇒ ★) › g ⨾ G-⇒ !ⁿ) (ℕ ?ⁿ G-ℕ ⨾!)
    with g g⨟i (⊥ⁿ (★ ⇒ ★) ⇨ ★)
  ... | j , g⨟⊥↠j =
    inj₁ (j
    , ((((⌊ g ⌋ᵍ ⨟ ((★ ⇒ ★) !)) ⨟ ((ℕ `?) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ (((★ ⇒ ★) !) ⨟ ((ℕ `?) ⨟ (ℕ !))))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-assocLᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ ((((★ ⇒ ★) !) ⨟ (ℕ `?)) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ()))) ⟩
      (⌊ g ⌋ᵍ ⨟ ((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (β-⊥Lᶜ (⊢! G-ℕ)) ⟩
      (⌊ g ⌋ᵍ ⨟ (⊥ᶜ (★ ⇒ ★) ⇨ ★))
      —↠ᶜᶜ⟨ g⨟⊥↠j ⟩
      ⌊ j ⌋ⁱ
      ∎ᶜᶜ)))

  _i⨟s_ (‹ ℕ › () ⨾ G-ℕ !ⁿ) (ℕ ?ⁿ G-ℕ ⨾ k ⨾!)

  _i⨟s_ (‹ (★ ⇒ ★) › g ⨾ G-⇒ !ⁿ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ k ⨾!)
    with g g⨟g k
  ... | m , g⨟k↠m =
    inj₁ (‹ (★ ⇒ ★) › m ⨾ G-⇒ !ⁿ
    , ((((⌊ g ⌋ᵍ ⨟ ((★ ⇒ ★) !)) ⨟ ((((★ ⇒ ★) `?) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ (((★ ⇒ ★) !) ⨟ ((((★ ⇒ ★) `?) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !))))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-assocLᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ ((((★ ⇒ ★) !) ⨟ (((★ ⇒ ★) `?) ⨟ ⌊ k ⌋ᵍ)) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ β-assocLᶜ) ⟩
      (⌊ g ⌋ᵍ ⨟ (((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?)) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ (ξ-⨟₁ᶜ β-proj-inj-okᶜ)) ⟩
      (⌊ g ⌋ᵍ ⨟ (((idᶜ (★ ⇒ ★)) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !)))
      —→ᶜᶜ⟨ β-assocLᶜ ⟩
      ((⌊ g ⌋ᵍ ⨟ ((idᶜ (★ ⇒ ★)) ⨟ ⌊ k ⌋ᵍ)) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ β-assocLᶜ ⟩
      (((⌊ g ⌋ᵍ ⨟ idᶜ (★ ⇒ ★)) ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !))
      —→ᶜᶜ⟨ ξ-⨟₁ᶜ (ξ-⨟₁ᶜ β-idRᶜ) ⟩
      ((⌊ g ⌋ᵍ ⨟ ⌊ k ⌋ᵍ) ⨟ ((★ ⇒ ★) !))
      —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ g⨟k↠m ⟩
      (⌊ m ⌋ᵍ ⨟ ((★ ⇒ ★) !))
      ∎ᶜᶜ)))

  _i⨟s_ (‹ ℕ › () ⨾ G-ℕ !ⁿ) ((★ ⇒ ★) ?ⁿ G-⇒ ⨾ k ⨾!)

  _i⨟s_ (‹ (★ ⇒ ★) › g ⨾ G-⇒ !ⁿ) (ℕ ?ⁿ G-ℕ ⨾ k ⨾!)
    with g g⨟i (⊥ⁿ (★ ⇒ ★) ⇨ ★)
  ... | j , g⨟⊥↠j =
    inj₁ (j
    , ((((⌊ g ⌋ᵍ ⨟ ((★ ⇒ ★) !)) ⨟ (((ℕ `?) ⨟ ⌊ k ⌋ᵍ) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ β-assocRᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ (((★ ⇒ ★) !) ⨟ (((ℕ `?) ⨟ ⌊ k ⌋ᵍ) ⨟ (ℕ !))))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ β-assocLᶜ ⟩
      (⌊ g ⌋ᵍ ⨟ ((((★ ⇒ ★) !) ⨟ ((ℕ `?) ⨟ ⌊ k ⌋ᵍ)) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ β-assocLᶜ) ⟩
      (⌊ g ⌋ᵍ ⨟ (((((★ ⇒ ★) !) ⨟ (ℕ `?)) ⨟ ⌊ k ⌋ᵍ) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ (ξ-⨟₁ᶜ (β-proj-inj-badᶜ (λ ())))) ⟩
      (⌊ g ⌋ᵍ ⨟ (((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ ⌊ k ⌋ᵍ) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (ξ-⨟₁ᶜ (β-⊥Lᶜ (wtG k))) ⟩
      (⌊ g ⌋ᵍ ⨟ ((⊥ᶜ (★ ⇒ ★) ⇨ ℕ) ⨟ (ℕ !)))
      —→ᶜᶜ⟨ ξ-⨟₂ᶜ (β-⊥Lᶜ (⊢! G-ℕ)) ⟩
      (⌊ g ⌋ᵍ ⨟ (⊥ᶜ (★ ⇒ ★) ⇨ ★))
      —↠ᶜᶜ⟨ g⨟⊥↠j ⟩
      ⌊ j ⌋ⁱ
      ∎ᶜᶜ)))

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

inverse-erase
  : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Normalᶜ c
  → ∃[ s ] (⌊ s ⌋ˢ ≡ c)

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

inverse-erase {c = ((★ ⇒ ★) `? ⨟ (c₁ ↦ c₂)) ⨟ ((★ ⇒ ★) !)}
  (⊢⨟ (⊢⨟ (⊢? G-⇒) (⊢↦ cwt dwt)) (⊢! G-⇒))
  (nf-?↦!ˡ G-⇒ n₁ n₂)
  with inverse-erase cwt n₁ | inverse-erase dwt n₂
... | s₁ , eq₁ | s₂ , eq₂ =
  (★ ⇒ ★) ?ⁿ G-⇒ ⨾ (s₁ ↣ s₂) ⨾!
  , cong (λ x → ((★ ⇒ ★) `? ⨟ x) ⨟ ((★ ⇒ ★) !)) (cong₂ _↦_ eq₁ eq₂)

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
  erase-normal (G ?ⁿ g ⨾!) = nf-?! g
  erase-normal (ℕ ?ⁿ g ⨾ () ⨾!)
  erase-normal ((★ ⇒ ★) ?ⁿ g ⨾ (c ↣ d) ⨾!) =
    nf-?↦!ˡ g (erase-normal c) (erase-normal d)
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
