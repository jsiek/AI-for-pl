module CoercionGradualGuarantee where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Contexts
open import CoercionReduction

------------------------------------------------------------------------
-- Coercion simulation
------------------------------------------------------------------------

?-from-ℕ-impossible : ∀ {A Y}
  → ⊢ A `? ⦂ ℕ ⇨ Y
  → ⊥
?-from-ℕ-impossible ()

↦-from-ℕ-impossible : ∀ {c d Y}
  → ⊢ (c ↦ d) ⦂ ℕ ⇨ Y
  → ⊥
↦-from-ℕ-impossible ()

id★-from-ℕ-impossible : ∀ {Y}
  → ⊢ idᶜ ★ ⦂ ℕ ⇨ Y
  → ⊥
id★-from-ℕ-impossible ()

id↦-from-ℕ-impossible : ∀ {A B Y}
  → ⊢ idᶜ (A ⇒ B) ⦂ ℕ ⇨ Y
  → ⊥
id↦-from-ℕ-impossible ()

drop?-from-ℕ-impossible : ∀ {c Y}
  → ⊢ ((★ ⇒ ★) `? ⨟ c) ⦂ ℕ ⇨ Y
  → ⊥
drop?-from-ℕ-impossible (⊢⨟ cwt dwt) with cwt
... | ()

!-from-★-impossible : ∀ {A Y}
  → ⊢ A ! ⦂ ★ ⇨ Y
  → ⊥
!-from-★-impossible (⊢! g) with g
... | ()

↦-from-★-impossible : ∀ {c d Y}
  → ⊢ (c ↦ d) ⦂ ★ ⇨ Y
  → ⊥
↦-from-★-impossible ()

id↦-from-★-impossible : ∀ {A B Y}
  → ⊢ idᶜ (A ⇒ B) ⦂ ★ ⇨ Y
  → ⊥
id↦-from-★-impossible ()

?-target-from-idR!-impossible : ∀ {G A B H}
  → Ground G
  → G ⊑ A
  → ⊢ H `? ⦂ A ⇨ B
  → ⊥
?-target-from-idR!-impossible g G⊑A (⊢? h) = ground-not-⊑★ g G⊑A

postulate
  -- TODO: prove principal β-idRᶜ simulation case.
  simᶜ-β-idR : ∀ {c A B X Y d}
    → c ⊑ᶜ (d ⨟ idᶜ B)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ d ⦂ A ⇨ B
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d))

  -- TODO: prove principal β-assocLᶜ simulation case.
  simᶜ-β-assocL : ∀ {c c₁ c₂ c₃ A B C D X Y}
    → c ⊑ᶜ (c₁ ⨟ (c₂ ⨟ c₃))
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ c₂ ⦂ B ⇨ C
    → ⊢ c₃ ⦂ C ⇨ D
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ ((c₁ ⨟ c₂) ⨟ c₃)))

  -- TODO: prove principal β-assocRᶜ simulation case.
  simᶜ-β-assocR : ∀ {c c₁ c₂ c₃ A B C D X Y}
    → c ⊑ᶜ ((c₁ ⨟ c₂) ⨟ c₃)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ c₂ ⦂ B ⇨ C
    → ⊢ c₃ ⦂ C ⇨ D
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁ ⨟ (c₂ ⨟ c₃))))

  -- TODO: prove principal β-↦ᶜ simulation case.
  simᶜ-β-↦ : ∀ {c c₁ d₁ c₂ d₂ A B C D E F X Y}
    → c ⊑ᶜ ((c₁ ↦ d₁) ⨟ (c₂ ↦ d₂))
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ C ⇨ A
    → ⊢ d₁ ⦂ B ⇨ D
    → ⊢ c₂ ⦂ E ⇨ C
    → ⊢ d₂ ⦂ D ⇨ F
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ ((c₂ ⨟ c₁) ↦ (d₁ ⨟ d₂))))

  -- TODO: prove congruence ξ-⨟₁ᶜ simulation case.
  simᶜ-ξ-⨟₁ : ∀ {c c₁ c₁′ d A B C X Y}
    → c ⊑ᶜ (c₁ ⨟ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ d ⦂ B ⇨ C
    → c₁ —→ᶜᶜ c₁′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁′ ⨟ d)))

  -- TODO: prove congruence ξ-⨟₂ᶜ simulation case.
  simᶜ-ξ-⨟₂ : ∀ {c c₁ d d′ A B C X Y}
    → c ⊑ᶜ (c₁ ⨟ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ d ⦂ B ⇨ C
    → d —→ᶜᶜ d′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁ ⨟ d′)))

  -- TODO: prove congruence ξ-↦₁ᶜ simulation case.
  simᶜ-ξ-↦₁ : ∀ {c c₁ c₁′ d A B C D X Y}
    → c ⊑ᶜ (c₁ ↦ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → c₁ —→ᶜᶜ c₁′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁′ ↦ d)))

  -- TODO: prove congruence ξ-↦₂ᶜ simulation case.
  simᶜ-ξ-↦₂ : ∀ {c c₁ d d′ A B C D X Y}
    → c ⊑ᶜ (c₁ ↦ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → d —→ᶜᶜ d′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁ ↦ d′)))

simᶜ-β-idL-⨟ : ∀ {c₁ c₂ d A B X Y Z}
  → c₁ ⊑ᶜ idᶜ A
  → c₂ ⊑ᶜ d
  → ⊢ c₁ ⦂ X ⇨ Z
  → ⊢ c₂ ⦂ Z ⇨ Y
  → ⊢ d ⦂ A ⇨ B
  → ∃[ c′ ] (((c₁ ⨟ c₂) —↠ᶜᶜ c′) × (c′ ⊑ᶜ d))
simᶜ-β-idL-⨟ {c₂ = c₂} (⊑idᶜ A′⊑A) c₂≤d ⊢idᶜ c₂wt dwt =
  c₂
  , (((idᶜ _ ⨟ c₂)
    —→ᶜᶜ⟨ β-idLᶜ ⟩
    c₂
    ∎ᶜᶜ)
    , c₂≤d)
simᶜ-β-idL-⨟ {c₂ = c₂} (⊑idL nseq cwt A⊑B A⊑C) c₂≤d ⊢idᶜ c₂wt dwt =
  c₂
  , (((idᶜ _ ⨟ c₂)
    —→ᶜᶜ⟨ β-idLᶜ ⟩
    c₂
    ∎ᶜᶜ)
    , c₂≤d)
simᶜ-β-idL-⨟ {c₂ = c₂} (⊑idR atom-id ⊢idᶜ B⊑A C⊑A) c₂≤d ⊢idᶜ c₂wt dwt =
  c₂
  , (((idᶜ _ ⨟ c₂)
    —→ᶜᶜ⟨ β-idLᶜ ⟩
    c₂
    ∎ᶜᶜ)
    , c₂≤d)
simᶜ-β-idL-⨟ {c₂ = c₂}
  (⊑idR atom-? (⊢? G-⇒) B⊑A C⊑A) c₂≤d (⊢? G-⇒) c₂wt dwt =
  (((★ ⇒ ★) `? ⨟ c₂))
  , ((((★ ⇒ ★) `? ⨟ c₂) ∎ᶜᶜ)
    , (⊑drop? c₂≤d))
simᶜ-β-idL-⨟ {c₂ = c₂}
  (⊑idR atom-? (⊢? G-ℕ) B⊑A C⊑A) c₂≤d (⊢? G-ℕ) c₂wt dwt
  with c₂≤d
... | c₂≤id@(⊑idᶜ A′⊑A)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((ℕ `?) ⨟ c₂)
  , ((((ℕ `?) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-? (⊢? G-ℕ) B⊑A C⊑A) c₂≤id))
... | c₂≤id@(⊑idR atom cwt′ B⊑A′ C⊑A′)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((ℕ `?) ⨟ c₂)
  , ((((ℕ `?) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-? (⊢? G-ℕ) B⊑A C⊑A) c₂≤id))
... | c₂≤id@(⊑idR↦ c≤id d≤id)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((ℕ `?) ⨟ c₂)
  , ((((ℕ `?) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-? (⊢? G-ℕ) B⊑A C⊑A) c₂≤id))
... | c₂≤id@(⊑idR⨟ c≤id d≤id)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((ℕ `?) ⨟ c₂)
  , ((((ℕ `?) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-? (⊢? G-ℕ) B⊑A C⊑A) c₂≤id))
... | (⊑! A′⊑A) = {!!}
... | (⊑? A′⊑A) = ⊥-elim (?-from-ℕ-impossible c₂wt)
... | (⊑↦ c≤c′ d≤d′) = ⊥-elim (↦-from-ℕ-impossible c₂wt)
... | (⊑⨟ c≤c′ d≤d′) = {!!}
... | (⊑idL atomic cwt′ A⊑B′ A⊑C′) = {!!}
... | (⊑idL↦★ c≤id d≤id) = ⊥-elim (id★-from-ℕ-impossible c₂wt)
... | (⊑idL↦ c≤id d≤id) = ⊥-elim (id↦-from-ℕ-impossible c₂wt)
... | (⊑idL⨟ c≤id d≤id) = {!!}
... | (⊑drop? c′≤c) = ⊥-elim (drop?-from-ℕ-impossible c₂wt)
... | (⊑drop! c′≤c) = {!!}
... | (⊑⊥ cwt′ A′⊑A B′⊑B)
  with coercion-type-unique c₂wt cwt′
... | refl , refl =
  ((ℕ `?) ⨟ c₂)
  , ((((ℕ `?) ⨟ c₂) ∎ᶜᶜ)
    , (⊑⊥ (⊢⨟ (⊢? G-ℕ) c₂wt) ⊑-★ B′⊑B))
simᶜ-β-idL-⨟ {c₂ = c₂}
  (⊑idR {c = G !} atom-! (⊢! g) B⊑A C⊑A) c₂≤d (⊢! g′) c₂wt dwt
  with c₂≤d
... | c₂≤id@(⊑idᶜ A′⊑A)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((G !) ⨟ c₂)
  , ((((G !) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-! (⊢! g) B⊑A C⊑A) c₂≤id))
... | c₂≤id@(⊑idR atomic cwt′ B⊑A′ C⊑A′)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((G !) ⨟ c₂)
  , ((((G !) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-! (⊢! g) B⊑A C⊑A) c₂≤id))
... | c₂≤id@(⊑idR↦ c≤id d≤id)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((G !) ⨟ c₂)
  , ((((G !) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-! (⊢! g) B⊑A C⊑A) c₂≤id))
... | c₂≤id@(⊑idR⨟ c≤id d≤id)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  ((G !) ⨟ c₂)
  , ((((G !) ⨟ c₂) ∎ᶜᶜ)
    , (⊑idR⨟ (⊑idR atom-! (⊢! g) B⊑A C⊑A) c₂≤id))
... | (⊑! A′⊑A) = ⊥-elim (!-from-★-impossible c₂wt)
... | (⊑? A′⊑A) = ⊥-elim (?-target-from-idR!-impossible g B⊑A dwt)
... | (⊑↦ c≤c′ d≤d′) = ⊥-elim (↦-from-★-impossible c₂wt)
... | (⊑⨟ c≤c′ d≤d′) = {!!}
... | (⊑idL atom-idᶜ cwt′ A⊑B′ A⊑C′)
  rewrite proj₁ (coercion-type-unique dwt ⊢idᶜ)
        | proj₂ (coercion-type-unique dwt ⊢idᶜ) =
  (G !)
  , (((((G !) ⨟ c₂)
    —→ᶜᶜ⟨ β-idRᶜ ⟩
    (G !)
    ∎ᶜᶜ)
    , (⊑idR atom-! (⊢! g) B⊑A C⊑A)))
... | (⊑idL atom-! (⊢! h) A⊑B′ A⊑C′)
  rewrite proj₁ (coercion-type-unique dwt (⊢! h))
        | proj₂ (coercion-type-unique dwt (⊢! h)) =
  (G !)
  , (((((G !) ⨟ c₂)
    —→ᶜᶜ⟨ β-idRᶜ ⟩
    (G !)
    ∎ᶜᶜ)
    , (⊑! B⊑A)))
... | (⊑idL atom-? (⊢? h) A⊑B′ A⊑C′) =
  ⊥-elim (?-target-from-idR!-impossible g B⊑A dwt)
... | (⊑idL↦★ c≤id d≤id) = {!!}
... | (⊑idL↦ c≤id d≤id) = ⊥-elim (id↦-from-★-impossible c₂wt)
... | (⊑idL⨟ c≤id d≤id) = {!!}
... | (⊑drop? c′≤c) = {!!}
... | (⊑drop! c′≤c) = {!!}
... | (⊑⊥ {A = A₀} {B = B₀} cwt′ A′⊑A₀ B′⊑B₀)
  with coercion-type-unique c₂wt cwt′ | coercion-type-unique dwt ⊢⊥
... | refl , refl | refl , refl =
  ((G !) ⨟ c₂)
  , ((((G !) ⨟ c₂) ∎ᶜᶜ)
    , (⊑⊥ (⊢⨟ (⊢! g′) c₂wt) B⊑A B′⊑B₀))
simᶜ-β-idL-⨟ {c₂ = c₂}
  (⊑idR↦ {c = c} {d = d₁} c≤id d≤id) c₂≤d (⊢↦ cwt dwt) c₂wt dwt′ =
  -- TODO case: idR for arrow coercions.
  {!!}
simᶜ-β-idL-⨟ {c₂ = c₃} (⊑idR⨟ {c = c₁} {d = c₂} c₁≤id c₂≤id) c₃≤d
  (⊢⨟ c₁wt c₂wt) c₃wt dwt
  with simᶜ-β-idL-⨟ c₂≤id c₃≤d c₂wt c₃wt dwt
... | c′ , c₂⨟c₃↠c′ , c′≤d
  with simᶜ-β-idL-⨟ c₁≤id c′≤d c₁wt (preserve-—↠ᶜᶜ (⊢⨟ c₂wt c₃wt) c₂⨟c₃↠c′) dwt
... | c″ , c₁⨟c′↠c″ , c″≤d =
  c″
  , (((((c₁ ⨟ c₂) ⨟ c₃)
    —→ᶜᶜ⟨ β-assocRᶜ ⟩
    (c₁ ⨟ (c₂ ⨟ c₃))
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ c₂⨟c₃↠c′ ⟩
    (c₁ ⨟ c′)
    —↠ᶜᶜ⟨ c₁⨟c′↠c″ ⟩
    c″
    ∎ᶜᶜ)
    , c″≤d))
simᶜ-β-idL-⨟ {c₂ = c₂}
  (⊑drop? {c′ = c₁} c₁≤id) c₂≤d (⊢⨟ (⊢? G-⇒) c₁wt) c₂wt dwt
  with simᶜ-β-idL-⨟ c₁≤id c₂≤d c₁wt c₂wt dwt
... | c′ , c₁⨟c₂↠c′ , c′≤d =
  ((★ ⇒ ★) `? ⨟ c′)
  , (((((((★ ⇒ ★) `? ⨟ c₁) ⨟ c₂)
    —→ᶜᶜ⟨ β-assocRᶜ ⟩
    ((★ ⇒ ★) `? ⨟ (c₁ ⨟ c₂))
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ c₁⨟c₂↠c′ ⟩
    ((★ ⇒ ★) `? ⨟ c′)
    ∎ᶜᶜ))
    , (⊑drop? c′≤d)))
simᶜ-β-idL-⨟ {c₂ = c₂}
  (⊑drop! {c′ = c₁} c₁≤id) c₂≤d (⊢⨟ c₁wt (⊢! G-⇒)) c₂wt dwt
  -- TODO case: drop! on the left of composition.
  = {!!}

simᶜ-β-idL : ∀ {c A B X Y d}
  → c ⊑ᶜ (idᶜ A ⨟ d)
  → ⊢ c ⦂ X ⇨ Y
  → ⊢ d ⦂ A ⇨ B
  → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d))
simᶜ-β-idL (⊑idL⨟ c≤id c≤d) ⊢idᶜ dwt =
  idᶜ _ , ((idᶜ _ ∎ᶜᶜ) , c≤d)
simᶜ-β-idL (⊑⨟ c₁≤id c₂≤d) (⊢⨟ c₁wt c₂wt) dwt =
  simᶜ-β-idL-⨟ c₁≤id c₂≤d c₁wt c₂wt dwt
simᶜ-β-idL (⊑drop? c≤id⨟d) (⊢⨟ (⊢? G-⇒) cwt) dwt
  with simᶜ-β-idL c≤id⨟d cwt dwt
... | c′ , c↠c′ , c′≤d =
  ((★ ⇒ ★) `? ⨟ c′)
  , ((multi-ξ-⨟₂ᶜᶜ c↠c′) , (⊑drop? c′≤d))
simᶜ-β-idL (⊑drop! c≤id⨟d) (⊢⨟ cwt (⊢! G-⇒)) dwt
  with simᶜ-β-idL c≤id⨟d cwt dwt
... | c′ , c↠c′ , c′≤d =
  (c′ ⨟ ((★ ⇒ ★) !))
  , ((multi-ξ-⨟₁ᶜᶜ c↠c′) , (⊑drop! c′≤d))

mutual
  ⊑!→⊑id : ∀ {c G A B}
    → Ground G
    → c ⊑ᶜ G !
    → ⊢ c ⦂ A ⇨ B
    → c ⊑ᶜ idᶜ G
  ⊑!→⊑id g (⊑! A⊑G) (⊢! g′) =
    ⊑idR atom-! (⊢! g′) A⊑G ⊑-★
  ⊑!→⊑id g (⊑idL atom-! (⊢! g′) A⊑G A⊑★) ⊢idᶜ =
    ⊑idᶜ A⊑G
  ⊑!→⊑id g (⊑drop? c≤!) (⊢⨟ (⊢? G-⇒) cwt)
    with ⊑ᶜ→⊑ (⊢! g) cwt c≤!
  ... | A⊑G , B⊑★ =
    ⊑idR⨟
      (⊑idR atom-? (⊢? G-⇒) ⊑-★ A⊑G)
      (⊑!→⊑id g c≤! cwt)
  ⊑!→⊑id g (⊑drop! c≤!) (⊢⨟ cwt (⊢! G-⇒))
    with ⊑ᶜ→⊑ (⊢! g) cwt c≤!
  ... | A⊑G , ()

  ⊑?→⊑id : ∀ {c G A B}
    → Ground G
    → c ⊑ᶜ G `?
    → ⊢ c ⦂ A ⇨ B
    → c ⊑ᶜ idᶜ G
  ⊑?→⊑id g (⊑? A⊑G) (⊢? g′) =
    ⊑idR atom-? (⊢? g′) ⊑-★ A⊑G
  ⊑?→⊑id g (⊑idL atom-? (⊢? g′) A⊑★ A⊑G) ⊢idᶜ =
    ⊑idᶜ A⊑G
  ⊑?→⊑id g (⊑drop? c≤?) (⊢⨟ (⊢? G-⇒) cwt)
    with ⊑ᶜ→⊑ (⊢? g) cwt c≤?
  ... | () , B⊑G
  ⊑?→⊑id g (⊑drop! c≤?) (⊢⨟ cwt (⊢! G-⇒))
    with ⊑ᶜ→⊑ (⊢? g) cwt c≤?
  ... | A⊑★ , B⊑G =
    ⊑idR⨟
      (⊑?→⊑id g c≤? cwt)
      (⊑idR atom-! (⊢! G-⇒) B⊑G ⊑-★)

  ⊑!⨟?→⊑id : ∀ {c G A B}
    → Ground G
    → c ⊑ᶜ (G ! ⨟ G `?)
    → ⊢ c ⦂ A ⇨ B
    → c ⊑ᶜ idᶜ G
  ⊑!⨟?→⊑id g (⊑⨟ c≤! c≤?) (⊢⨟ cwt dwt) =
    ⊑idR⨟ (⊑!→⊑id g c≤! cwt) (⊑?→⊑id g c≤? dwt)
  ⊑!⨟?→⊑id g (⊑idL⨟ c≤! c≤?) ⊢idᶜ =
    ⊑!→⊑id g c≤! ⊢idᶜ
  ⊑!⨟?→⊑id g (⊑drop? c≤!⨟?) (⊢⨟ (⊢? G-⇒) cwt)
    with ⊑ᶜ→⊑ (⊢⨟ (⊢! g) (⊢? g)) cwt c≤!⨟?
  ... | A⊑G , B⊑G =
    ⊑idR⨟
      (⊑idR atom-? (⊢? G-⇒) ⊑-★ A⊑G)
      (⊑!⨟?→⊑id g c≤!⨟? cwt)
  ⊑!⨟?→⊑id g (⊑drop! c≤!⨟?) (⊢⨟ cwt (⊢! G-⇒))
    with ⊑ᶜ→⊑ (⊢⨟ (⊢! g) (⊢? g)) cwt c≤!⨟?
  ... | A⊑G , B⊑G =
    ⊑idR⨟
      (⊑!⨟?→⊑id g c≤!⨟? cwt)
      (⊑idR atom-! (⊢! G-⇒) B⊑G ⊑-★)

simᶜ : ∀ {c d d′ A B A′ B′}
  → c ⊑ᶜ d
  → ⊢ c ⦂ A′ ⇨ B′
  → ⊢ d ⦂ A ⇨ B
  → d —→ᶜᶜ d′
  → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d′))
simᶜ {c = c} c≤d cwt (⊢⨟ (⊢! g) (⊢? h)) β-proj-inj-okᶜ =
  c , ((c ∎ᶜᶜ) , (⊑!⨟?→⊑id g c≤d cwt))
simᶜ {c = c} c≤d cwt (⊢⨟ (⊢! g) (⊢? h)) (β-proj-inj-badᶜ {G = G} {H = H} G≢H)
  with ⊑ᶜ→⊑ (⊢⨟ (⊢! g) (⊢? h)) cwt c≤d
... | A′⊑G , B′⊑H =
  c , ((c ∎ᶜᶜ) , (⊑⊥ cwt A′⊑G B′⊑H))
simᶜ c≤d cwt (⊢⨟ ⊢idᶜ dwt) β-idLᶜ =
  simᶜ-β-idL c≤d cwt dwt
simᶜ c≤d cwt (⊢⨟ cwt₁ ⊢idᶜ) β-idRᶜ =
  simᶜ-β-idR c≤d cwt cwt₁
simᶜ c≤d cwt (⊢⨟ cwt₁ (⊢⨟ dwt ewt)) β-assocLᶜ =
  simᶜ-β-assocL c≤d cwt cwt₁ dwt ewt
simᶜ c≤d cwt (⊢⨟ (⊢⨟ cwt₁ dwt) ewt) β-assocRᶜ =
  simᶜ-β-assocR c≤d cwt cwt₁ dwt ewt
simᶜ c≤d cwt (⊢⨟ (⊢↦ cwt₁ dwt) (⊢↦ c′wt d′wt)) β-↦ᶜ =
  simᶜ-β-↦ c≤d cwt cwt₁ dwt c′wt d′wt
simᶜ {c = c} c≤d cwt (⊢⨟ ⊢⊥ dwt) (β-⊥Lᶜ dwt′)
  with ⊑ᶜ→⊑ (⊢⨟ ⊢⊥ dwt′) cwt c≤d
... | A′⊑A , B′⊑C =
  c , ((c ∎ᶜᶜ) , (⊑⊥ cwt A′⊑A B′⊑C))
simᶜ {c = c} c≤d cwt (⊢⨟ (⊢! g) ⊢⊥) β-!⊥ᶜ
  with ⊑ᶜ→⊑ (⊢⨟ (⊢! g) ⊢⊥) cwt c≤d
... | A′⊑G , B′⊑B =
  c , ((c ∎ᶜᶜ) , (⊑⊥ cwt A′⊑G B′⊑B))
simᶜ {c = c} c≤d cwt (⊢⨟ (⊢↦ cwt₁ dwt₁) ⊢⊥) (β-↦⊥ᶜ cwt₂ dwt₂)
  with ⊑ᶜ→⊑ (⊢⨟ (⊢↦ cwt₂ dwt₂) ⊢⊥) cwt c≤d
... | A′⊑A⇒B , B′⊑E =
  c , ((c ∎ᶜᶜ) , (⊑⊥ cwt A′⊑A⇒B B′⊑E))
simᶜ c≤d cwt (⊢⨟ cwt₁ dwt) (ξ-⨟₁ᶜ c→c′) =
  simᶜ-ξ-⨟₁ c≤d cwt cwt₁ dwt c→c′
simᶜ c≤d cwt (⊢⨟ cwt₁ dwt) (ξ-⨟₂ᶜ d→d′) =
  simᶜ-ξ-⨟₂ c≤d cwt cwt₁ dwt d→d′
simᶜ c≤d cwt (⊢↦ cwt₁ dwt) (ξ-↦₁ᶜ c→c′) =
  simᶜ-ξ-↦₁ c≤d cwt cwt₁ dwt c→c′
simᶜ c≤d cwt (⊢↦ cwt₁ dwt) (ξ-↦₂ᶜ d→d′) =
  simᶜ-ξ-↦₂ c≤d cwt cwt₁ dwt d→d′

sim*ᶜ : ∀ {c d d′ A B A′ B′}
  → c ⊑ᶜ d
  → ⊢ c ⦂ A′ ⇨ B′
  → ⊢ d ⦂ A ⇨ B
  → d —↠ᶜᶜ d′
  → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d′))
sim*ᶜ {c = c} c≤d cwt dwt (d ∎ᶜᶜ) =
  c , ((c ∎ᶜᶜ) , c≤d)
sim*ᶜ c≤d cwt dwt (d —→ᶜᶜ⟨ d→d₁ ⟩ d₁↠d′)
  with simᶜ c≤d cwt dwt d→d₁
... | c₁ , c↠c₁ , c₁≤d₁
  with sim*ᶜ c₁≤d₁ (preserve-—↠ᶜᶜ cwt c↠c₁) (preserve-—→ᶜᶜ dwt d→d₁) d₁↠d′
... | c′ , c₁↠c′ , c′≤d′ =
  c′ , ((multi-transᶜᶜ c↠c₁ c₁↠c′) , c′≤d′)
