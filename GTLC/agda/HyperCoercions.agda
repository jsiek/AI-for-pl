module HyperCoercions where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Types
open import CoercionReduction

--------------------------------------------------------------------------------
--- Hypercoercions
--------------------------------------------------------------------------------

infix 4 _；_；_
infix 8 _!ᵗ_

mutual
  data _⇨ᶜ_ : Ty → Ty → Set
  data _⇨ʰ_ : Ty → Ty → Set
  data _⇨ᵐ_ : Ty → Ty → Set
  data _⇨ᵗ_ : Ty → Ty → Set

  data _⇨ᶜ_ where
    _；_；_ : ∀{A B C D}
      → A ⇨ʰ B
      → B ⇨ᵐ C
      → C ⇨ᵗ D
      → A ⇨ᶜ D
  
  data _⇨ʰ_ where
    idʰ : (A : Ty)
      → A ⇨ʰ A
    _?ʰ_ : ∀ (G : Ty)
      → Ground G
      → ★ ⇨ʰ G
    
  data _⇨ᵐ_ where
    idᵐ : (A : Ty)
      → A ⇨ᵐ A
    _↣_ : ∀ {A B C D}
      → C ⇨ᶜ A
      → B ⇨ᶜ D
      → (A ⇒ B) ⇨ᵐ (C ⇒ D)
    ⊥ᵐ_⇨_ : ∀ (A B : Ty)
      → A ⇨ᵐ B

  data _⇨ᵗ_ where
    idᵗ : (A : Ty)
      → A ⇨ᵗ A
    _!ᵗ_ : ∀ (G : Ty)
      → Ground G
      → G ⇨ᵗ ★

data _⇨ʳ_ : Ty → Ty → Set where
    idʳ : (A : Ty)
      → A ⇨ʳ A
      
    _!ʳ_ : ∀ (G : Ty)
      → Ground G
      → G ⇨ʳ ★

    _?ʳ_ : ∀ (G : Ty)
      → Ground G
      → ★ ⇨ʳ G

    ⊥ʳ_⇨_ : ∀ (A B : Ty)
      → A ⇨ʳ B

--------------------------------------------------------------------------------
--- Composition of hypercoercions
--------------------------------------------------------------------------------

mutual
  _⨟ᶜ_ : ∀{A B C} → A ⇨ᶜ B → B ⇨ᶜ C → A ⇨ᶜ C
--  _⨟ᵗʰ_ : ∀{A B C} → A ⇨ᵗ B → B ⇨ʰ C → A ⇨ʳ C
  _⨟ᵐ_ : ∀{A B C} → A ⇨ᵐ B → B ⇨ᵐ C → A ⇨ᵐ C

  (h ； m ； idᵗ _) ⨟ᶜ (idʰ _ ； m′ ； t′) = h ； (m ⨟ᵐ m′) ； t′
  (h ； idᵐ .★ ； idᵗ _) ⨟ᶜ ((_ ?ʰ x) ； m′ ； t′)
      with h
  ... | idʰ .★ = ((_ ?ʰ x) ； m′ ； t′)
  (h ； ⊥ᵐ _ ⇨ .★ ； idᵗ _) ⨟ᶜ ((_ ?ʰ x) ； m′ ； t′) = h ； (⊥ᵐ _ ⇨ _) ； t′
  (h ； m ； G !ᵗ g) ⨟ᶜ (idʰ .★ ； idᵐ .★ ； idᵗ .★) = (h ； m ； G !ᵗ g)
  (h ； m ； G !ᵗ g) ⨟ᶜ (idʰ .★ ； ⊥ᵐ .★ ⇨ _ ； t′) = h ； (⊥ᵐ _ ⇨ _) ； t′
  (h ； m ； G !ᵗ g) ⨟ᶜ ((H ?ʰ x) ； m′ ； t′)
      with G ≟Ty H
  ... | yes refl = h ； (m ⨟ᵐ m′) ； t′
  ... | no neq = h ； (⊥ᵐ _ ⇨ _) ； t′
  

{-
  (h ； m ； idᵗ _) ⨟ᶜ (idʰ _ ； m′ ； t′) = h ； (m ⨟ᵐ m′) ； t′
  (idʰ .★ ； idᵐ .★ ； idᵗ _) ⨟ᶜ ((H ?ʰ h) ； m′ ； t′) = ((H ?ʰ h) ； m′ ； t′)
  (h ； ⊥ᵐ _ ⇨ .★ ； idᵗ _) ⨟ᶜ ((_ ?ʰ x) ； m′ ； t′) = h ； (⊥ᵐ _ ⇨ _) ； t′
  (h ； m ； G !ᵗ g) ⨟ᶜ (idʰ .★ ； idᵐ .★ ； idᵗ .★) = (h ； m ； G !ᵗ g)
  (h ； m ； _ !ᵗ x) ⨟ᶜ (idʰ .★ ； ⊥ᵐ .★ ⇨ _ ； t′) = h ； (⊥ᵐ _ ⇨ _) ； t′
  (h ； m ； G !ᵗ x) ⨟ᶜ ((H ?ʰ x₁) ； m′ ； t′)
      with G ≟Ty H
  ... | yes refl = h ； (m ⨟ᵐ m′) ； t′
  ... | no neq = h ； (⊥ᵐ _ ⇨ _) ； t′
  -}
  
{-
  (h ； m ； t) ⨟ᶜ (h′ ； m′ ； t′)
      with t ⨟ᵗʰ h′
  ((h ； m ； t) ⨟ᶜ (h′ ； m′ ； t′)) | idʳ _                 = h ； (m ⨟ᵐ m′) ； t′
  ((h ； m ； t) ⨟ᶜ (idʰ .★ ； idᵐ .★ ； idᵗ .★)) | _ !ʳ g   = h ； m ； t
  ((h ； m ； t) ⨟ᶜ (h′ ； ⊥ᵐ .★ ⇨ _ ； t′)) | _ !ʳ g         = h ； (⊥ᵐ _ ⇨ _) ； t′
  ((idʰ .★ ； idᵐ .★ ； idᵗ .★) ⨟ᶜ (h′ ； m′ ； t′)) | _ ?ʳ g = (h′ ； m′ ； t′)
  ((h ； ⊥ᵐ _ ⇨ .★ ； idᵗ .★) ⨟ᶜ (h′ ； m′ ； t′)) | _ ?ʳ g   = h ； (⊥ᵐ _ ⇨ _) ； t′
  ((h ； m ； t) ⨟ᶜ (h′ ； m′ ； t′)) | ⊥ʳ _ ⇨ _               = h ； (⊥ᵐ _ ⇨ _) ； t′
-}
{-
  idᵗ _ ⨟ᵗʰ idʰ _ = idʳ _
  idᵗ _ ⨟ᵗʰ (_ ?ʰ g) = _ ?ʳ g
  (_ !ᵗ g) ⨟ᵗʰ idʰ .★ = _ !ʳ g
  (G !ᵗ g) ⨟ᵗʰ (H ?ʰ h)
      with G ≟Ty H
  ... | yes refl = idʳ _
  ... | no neq = ⊥ʳ _ ⇨ _
-}

  idᵐ _ ⨟ᵐ idᵐ _ = idᵐ _
  idᵐ _ ⨟ᵐ (c ↣ d) = c ↣ d
  idᵐ _ ⨟ᵐ (⊥ᵐ _ ⇨ _) = ⊥ᵐ _ ⇨ _
  (c ↣ d) ⨟ᵐ idᵐ .(_ ⇒ _) = c ↣ d
  (c ↣ d) ⨟ᵐ (c′ ↣ d′) = (c′ ⨟ᶜ c) ↣ (d ⨟ᶜ d′)
  (c ↣ d) ⨟ᵐ (⊥ᵐ .(_ ⇒ _) ⇨ _) = ⊥ᵐ _ ⇨ _
  (⊥ᵐ _ ⇨ _) ⨟ᵐ m′ = ⊥ᵐ _ ⇨ _

mutual
  ⌊_⌋ᶜ : ∀ {A B}
    → A ⇨ᶜ B
    → Coercion
  ⌊_；_；_⌋ʰ : ∀ {A B C D}
    → A ⇨ʰ B
    → B ⇨ᵐ C
    → C ⇨ᵗ D
    → Coercion
  ⌊_；_⌋ᵐ : ∀ {A B C}
    → A ⇨ᵐ B
    → B ⇨ᵗ C
    → Coercion
  ⌊_⌋ᵗ : ∀ {A B}
    → A ⇨ᵗ B
    → Coercion

  tgt : ∀{A}{B} → A ⇨ᵗ B → Ty
  tgt {A}{B} t = B

  ⌊ h ； m ； t ⌋ᶜ = ⌊ h ； m ； t ⌋ʰ
  ⌊ idʰ _ ； m ； t ⌋ʰ = ⌊ m ； t ⌋ᵐ
  ⌊ G ?ʰ g ； m ； t ⌋ʰ = G `? ⨟ ⌊ m ； t ⌋ᵐ
  ⌊ idᵐ _ ； t ⌋ᵐ = ⌊ t ⌋ᵗ
  ⌊ c ↣ d ； t ⌋ᵐ = ⌊ c ⌋ᶜ ↦ ⌊ d ⌋ᶜ ⨟ ⌊ t ⌋ᵗ
  ⌊ ⊥ᵐ A ⇨ B ； t ⌋ᵐ = ⊥ᶜ A ⇨ tgt t
  ⌊ idᵗ A ⌋ᵗ = idᶜ A
  ⌊ G !ᵗ g ⌋ᵗ = G !

    
--------------------------------------------------------------------------------
--- Precision on hypercoercions
--------------------------------------------------------------------------------

infix 3 _⊑ʰ_

mutual
  data _⊑ᶜ_ : ∀ {A B A′ B′} → (A ⇨ᶜ B) → (A′ ⇨ᶜ B′) → Set
  data _⊑ʰ_ : ∀ {A B A′ B′} → (A ⇨ʰ B) → (A′ ⇨ʰ B′) → Set
  data _⊑ᵐ_ : ∀ {A B A′ B′} → (A ⇨ᵐ B) → (A′ ⇨ᵐ B′) → Set
  data _⊑ᵗ_ : ∀ {A B A′ B′} → (A ⇨ᵗ B) → (A′ ⇨ᵗ B′) → Set
  
  data _⊑ᶜ_ where
    s-⊑-t : ∀{A B C D A′ B′ C′ D′}
             {h : A ⇨ʰ B}{m : B ⇨ᵐ C}{t : C ⇨ᵗ D}
             {h′ : A′ ⇨ʰ B′}{m′ : B′ ⇨ᵐ C′}{t′ : C′ ⇨ᵗ D′}
      → h ⊑ʰ h′
      → m ⊑ᵐ m′
      → t ⊑ᵗ t′
      → (h ； m ； t) ⊑ᶜ (h′ ； m′ ； t′)

  data _⊑ʰ_ where
    id-⊑ʰ-id : ∀{A A′}
      → A ⊑ A′
      → idʰ A ⊑ʰ idʰ A′
      
    id-⊑ʰ-? : ∀{G}{g : Ground G}
      → idʰ ★ ⊑ʰ G ?ʰ g

    ?-⊑ʰ-id : ∀{G}{g : Ground G}
      → G ?ʰ g ⊑ʰ idʰ G

    ?-⊑ʰ-? : ∀{G}{g : Ground G}
      → G ?ʰ g ⊑ʰ G ?ʰ g

  data _⊑ᵐ_ where
    id-⊑ᵐ-id : ∀{A A′}
      → A ⊑ A′
      → idᵐ A ⊑ᵐ idᵐ A′
      
    id⇒-⊑ᵐ-↣ : ∀{A B A′ B′ C′ D′} {c′ : C′ ⇨ᶜ A′}{d′ : B′ ⇨ᶜ D′}
      → (idʰ A ； idᵐ A ； idᵗ A) ⊑ᶜ c′
      → (idʰ B ； idᵐ B ； idᵗ B) ⊑ᶜ d′
      → idᵐ (A ⇒ B) ⊑ᵐ (c′ ↣ d′)

    id★-⊑ᵐ-↣ : ∀{A′ B′ C′ D′} {c′ : C′ ⇨ᶜ A′}{d′ : B′ ⇨ᶜ D′}
      → (idʰ ★ ； idᵐ ★ ； idᵗ ★) ⊑ᶜ c′
      → (idʰ ★ ； idᵐ ★ ； idᵗ ★) ⊑ᶜ d′
      → idᵐ ★ ⊑ᵐ (c′ ↣ d′)

    ↣-⊑ᵐ-id : ∀{A B C D A′ B′} {c : C ⇨ᶜ A}{d : B ⇨ᶜ D}
      → c ⊑ᶜ (idʰ A′ ； idᵐ A′ ； idᵗ A′)
      → d ⊑ᶜ (idʰ B′ ； idᵐ B′ ； idᵗ B′)
      → (c ↣ d) ⊑ᵐ idᵐ (A′ ⇒ B′)

    ↣-⊑ᵐ-↣ : ∀{A B C D A′ B′  C′ D′}
               {c : C ⇨ᶜ A}{d : B ⇨ᶜ D}
               {c′ : C′ ⇨ᶜ A′}{d′ : B′ ⇨ᶜ D′}
      → c ⊑ᶜ c′
      → d ⊑ᶜ d′
      → (c ↣ d) ⊑ᵐ (c′ ↣ d′)

    m-⊑ᵐ-⊥ : ∀{A B A′ B′}{m : A ⇨ᵐ B}
      → A ⊑ A′ 
      → B ⊑ B′ 
      → m ⊑ᵐ (⊥ᵐ A′ ⇨ B′)

  data _⊑ᵗ_ where
    id-⊑ᵗ-id : ∀{A A′}
      → A ⊑ A′
      → idᵗ A ⊑ᵗ idᵗ A′

    id-⊑ᵗ-! : ∀{G}{g : Ground G}
      → idᵗ ★ ⊑ᵗ (G !ᵗ g)

    !-⊑ᵗ-id : ∀{G}{g : Ground G}
      → (G !ᵗ g) ⊑ᵗ idᵗ G

    !-⊑ᵗ-! : ∀{G}{g : Ground G}
      → (G !ᵗ g) ⊑ᵗ (G !ᵗ g)


mutual
  ⊑ᶜ→⊑ : ∀ {A B A′ B′}
      → (s : A ⇨ᶜ B) → (t : A′ ⇨ᶜ B′)
      → s ⊑ᶜ t
        ---------------
      → A ⊑ A′ × B ⊑ B′

  ⊑ʰ→⊑ : ∀ {A B A′ B′}
      → (i : A ⇨ʰ B) → (j : A′ ⇨ʰ B′)
      → i ⊑ʰ j
        ---------------
      → A ⊑ A′ × B ⊑ B′

  ⊑ᵐ→⊑ : ∀ {A B A′ B′}
      → (i : A ⇨ᵐ B) → (j : A′ ⇨ᵐ B′)
      → i ⊑ᵐ j
        ---------------
      → A ⊑ A′ × B ⊑ B′

  ⊑ᵗ→⊑ : ∀ {A B A′ B′}
      → (g : A ⇨ᵗ B) → (h : A′ ⇨ᵗ B′)
      → g ⊑ᵗ h
        ---------------
      → A ⊑ A′ × B ⊑ B′

  ⊑ᶜ→⊑ (h ； m ； t) (h' ； m' ； t') (s-⊑-t x x₁ x₂) =
     let hh = ⊑ʰ→⊑ h h' x in
     let tt = ⊑ᵗ→⊑ t t' x₂ in
     (hh .proj₁) , (tt .proj₂)
     
  ⊑ʰ→⊑ s t (id-⊑ʰ-id x) = x , x
  ⊑ʰ→⊑ s t id-⊑ʰ-? = ⊑-★ , ⊑-★
  ⊑ʰ→⊑ s t ?-⊑ʰ-id = ⊑-★ , ⊑-refl
  ⊑ʰ→⊑ s t ?-⊑ʰ-? = ⊑-★ , ⊑-refl
  
  ⊑ᵐ→⊑ s t (id-⊑ᵐ-id x) = x , x
  ⊑ᵐ→⊑ s t (id⇒-⊑ᵐ-↣ x x₁) =
    let xx = ⊑ᶜ→⊑ _ _ x in
    let yy = ⊑ᶜ→⊑ _ _ x₁ in
    (⊑-⇒ (xx .proj₂) (yy .proj₁)) , (⊑-⇒ (xx .proj₁) (yy .proj₂))
  ⊑ᵐ→⊑ s t (id★-⊑ᵐ-↣ x x₁) = ⊑-★ , ⊑-★
  ⊑ᵐ→⊑ s t (↣-⊑ᵐ-id x x₁) =
    let xx = ⊑ᶜ→⊑ _ _ x in
    let yy = ⊑ᶜ→⊑ _ _ x₁ in
    (⊑-⇒ (xx .proj₂) (yy .proj₁)) , (⊑-⇒ (xx .proj₁) (yy .proj₂))
  ⊑ᵐ→⊑ s t (↣-⊑ᵐ-↣ x x₁) =
    let xx = ⊑ᶜ→⊑ _ _ x in
    let yy = ⊑ᶜ→⊑ _ _ x₁ in
    (⊑-⇒ (xx .proj₂) (yy .proj₁)) , (⊑-⇒ (xx .proj₁) (yy .proj₂))
  ⊑ᵐ→⊑ s t (m-⊑ᵐ-⊥ x x₁) = x , x₁
  
  ⊑ᵗ→⊑ s t (id-⊑ᵗ-id x) = x , x
  ⊑ᵗ→⊑ s t id-⊑ᵗ-! = ⊑-★ , ⊑-★
  ⊑ᵗ→⊑ s t !-⊑ᵗ-id = ⊑-refl , ⊑-★
  ⊑ᵗ→⊑ s t !-⊑ᵗ-! = ⊑-refl , ⊑-★

--------------------------------------------------------------------------------
--- id ⊑ c ⨟ᶜ d when id ⊑ c and id ⊑ d
--------------------------------------------------------------------------------

idʳ-compose : ∀{A B C D E}
  → (h : A ⇨ʰ B)
  → (m : B ⇨ᵐ C)
  → (m′ : C ⇨ᵐ D)
  → (t′ : D ⇨ᵗ E)
  → ((h ； m ； idᵗ C) ⨟ᶜ (idʰ C ； m′ ； t′)) ≡
      (h ； (m ⨟ᵐ m′) ； t′)
idʳ-compose h m m′ t′ = refl

⊥?-compose : ∀{A B D E G}
  → {g : Ground G}
  → (h : A ⇨ʰ B)
  → (m′ : G ⇨ᵐ D)
  → (t′ : D ⇨ᵗ E)
  → ((h ； ⊥ᵐ B ⇨ ★ ； idᵗ ★) ⨟ᶜ (G ?ʰ g ； m′ ； t′)) ≡
      (h ； ⊥ᵐ B ⇨ D ； t′)
⊥?-compose (idʰ _) m′ t′ = refl
⊥?-compose (_ ?ʰ x) m′ t′ = refl

id-⊑-⨟ᶜ : ∀{A A′ B′ C′}
   → (c′ : A′ ⇨ᶜ B′)
   → (d′ : B′ ⇨ᶜ C′)
   → (idʰ A ； idᵐ A ； idᵗ A) ⊑ᶜ c′
   → (idʰ A ； idᵐ A ； idᵗ A) ⊑ᶜ d′
   → (idʰ A ； idᵐ A ； idᵗ A) ⊑ᶜ (c′ ⨟ᶜ d′)
id-⊑-⨟ᵐ : ∀{A A′ B′ C′}
   → (c′ : A′ ⇨ᵐ B′)
   → (d′ : B′ ⇨ᵐ C′)
   → idᵐ A ⊑ᵐ c′
   → idᵐ A ⊑ᵐ d′
   → idᵐ A ⊑ᵐ (c′ ⨟ᵐ d′)

   
id-⊑-⨟ᶜ (h ； m ； idᵗ _) (idʰ _ ； m′ ； t′) (s-⊑-t x x₁ x₂) (s-⊑-t x₃ x₄ x₅) =
    s-⊑-t x (id-⊑-⨟ᵐ m m′ x₁ x₄) x₅
id-⊑-⨟ᶜ (h ； idᵐ .★ ； idᵗ _) ((_ ?ʰ x₆) ； m′ ； t′) (s-⊑-t x x₁ x₂) (s-⊑-t x₃ x₄ x₅)
    with h
... | idʰ .★ = s-⊑-t x₃ x₄ x₅
id-⊑-⨟ᶜ (h ； ⊥ᵐ _ ⇨ .★ ； idᵗ _) ((_ ?ʰ x₆) ； m′ ； t′) (s-⊑-t x x₁ x₂) (s-⊑-t x₃ x₄ x₅)
    with ⊑ᵐ→⊑ (idᵐ _) (⊥ᵐ _ ⇨ ★) x₁ | ⊑ᵗ→⊑ _ _ x₅
... | aa , bb | cc , dd = s-⊑-t x (m-⊑ᵐ-⊥ aa cc) x₅
id-⊑-⨟ᶜ (h ； m ； _ !ᵗ x₆) (idʰ .★ ； idᵐ .★ ； idᵗ .★) (s-⊑-t x x₁ x₂) (s-⊑-t x₃ x₄ x₅) = s-⊑-t x x₁ x₂
id-⊑-⨟ᶜ (h ； m ； _ !ᵗ x₆) (idʰ .★ ； ⊥ᵐ .★ ⇨ _ ； t′) (s-⊑-t x x₁ x₂) (s-⊑-t x₃ x₄ x₅)
    with ⊑ᵐ→⊑ _ m x₁ | ⊑ᵗ→⊑ _ _ x₅
... | aa , bb | cc , dd = s-⊑-t x (m-⊑ᵐ-⊥ aa cc) x₅
id-⊑-⨟ᶜ (h ； m ； G !ᵗ x₆) ((H ?ʰ x₇) ； m′ ； t′) (s-⊑-t x x₁ x₂) (s-⊑-t x₃ x₄ x₅)
    with G ≟Ty H
... | yes refl = s-⊑-t x (id-⊑-⨟ᵐ m m′ x₁ x₄) x₅
... | no neq
    with ⊑ᵐ→⊑ _ m x₁ | ⊑ᵗ→⊑ _ _ x₅
... | aa , bb | cc , dd = s-⊑-t x (m-⊑ᵐ-⊥ aa cc) x₅

id-⊑-⨟ᵐ (idᵐ _) (idᵐ _) id≤c′ id≤d′ = id≤c′
id-⊑-⨟ᵐ (idᵐ _) (c′ ↣ d′) id≤c′ id≤d′ = id≤d′
id-⊑-⨟ᵐ (idᵐ _) (⊥ᵐ _ ⇨ _) id≤c′ id≤d′ = id≤d′
id-⊑-⨟ᵐ (c ↣ d) (idᵐ .(_ ⇒ _)) id≤c′ id≤d′ = id≤c′
id-⊑-⨟ᵐ {A = ★} (c ↣ d) (c′ ↣ d′) (id★-⊑ᵐ-↣ x x₁) (id★-⊑ᵐ-↣ x₂ x₃) =
    id★-⊑ᵐ-↣ (id-⊑-⨟ᶜ c′ c x₂ x) (id-⊑-⨟ᶜ d d′ x₁ x₃)
id-⊑-⨟ᵐ {A = A ⇒ A₁} (c ↣ d) (c′ ↣ d′) (id⇒-⊑ᵐ-↣ x x₁) (id⇒-⊑ᵐ-↣ x₂ x₃) =
    id⇒-⊑ᵐ-↣ (id-⊑-⨟ᶜ c′ c x₂ x) (id-⊑-⨟ᶜ d d′ x₁ x₃)
id-⊑-⨟ᵐ (c ↣ d) (⊥ᵐ .(_ ⇒ _) ⇨ _) id≤c′ id≤d′
    with ⊑ᵐ→⊑ _ _ id≤d′ | ⊑ᵐ→⊑ _ _ id≤c′
... | aa , bb | cc , dd = m-⊑ᵐ-⊥ cc bb
id-⊑-⨟ᵐ (⊥ᵐ _ ⇨ _) d′ id≤c′ id≤d′
    with ⊑ᵐ→⊑ _ _ id≤d′ | ⊑ᵐ→⊑ _ _ id≤c′
... | aa , bb | cc , dd = m-⊑ᵐ-⊥ cc bb

--------------------------------------------------------------------------------
--- Composition is monotonic
--------------------------------------------------------------------------------

postulate
  trans-id : ∀ {A B A′ B′ C D}{c : A ⇨ᶜ B}{c′ : A′ ⇨ᶜ B′}
   → c ⊑ᶜ (idʰ C ； idᵐ C ； idᵗ C)
   → (idʰ D ； idᵐ D ； idᵗ D) ⊑ᶜ c′
   → c ⊑ᶜ c′

  compose-id1 : ∀{A B A′ B′ C′}{c : A ⇨ᶜ B}{c′ : A′ ⇨ᶜ B′}{d′ : B′ ⇨ᶜ C′}
    → c ⊑ᶜ c′
    → (idʰ B ； idᵐ B ； idᵗ B) ⊑ᶜ d′
    → c ⊑ᶜ (c′ ⨟ᶜ d′)
    
  compose-id2 : ∀{A B A′ B′ C′}{c : A ⇨ᶜ B}{c′ : A′ ⇨ᶜ B′}{d′ : B′ ⇨ᶜ C′}
    → (idʰ A ； idᵐ A ； idᵗ A) ⊑ᶜ c′
    → c ⊑ᶜ d′
    → c ⊑ᶜ (c′ ⨟ᶜ d′)


⨟ᵐ-monotonic : ∀ {A B C A′ B′ C′}
  → (s : A ⇨ᵐ B)
  → (t : B ⇨ᵐ C)
  → (s′ : A′ ⇨ᵐ B′)
  → (t′ : B′ ⇨ᵐ C′)
  → s ⊑ᵐ s′
  → t ⊑ᵐ t′
  → (s ⨟ᵐ t) ⊑ᵐ (s′ ⨟ᵐ t′)

⨟ᶜ-monotonic : ∀ {A B C A′ B′ C′}
  → (s : A ⇨ᶜ B)
  → (t : B ⇨ᶜ C)
  → (s′ : A′ ⇨ᶜ B′)
  → (t′ : B′ ⇨ᶜ C′)
  → s ⊑ᶜ s′
  → t ⊑ᶜ t′
  → (s ⨟ᶜ t) ⊑ᶜ (s′ ⨟ᶜ t′)
⨟ᶜ-monotonic (sh ； sm ； st) (th ； tm ； tt) (sh′ ； sm′ ； st′) (th′ ； tm′ ； tt′) (s-⊑-t sh⊑ sm⊑ st⊑) (s-⊑-t th⊑ tm⊑ tt⊑) = {!!}

⨟ᵐ-monotonic s t s′ t′ (id-⊑ᵐ-id x) (id-⊑ᵐ-id x₁) = id-⊑ᵐ-id x
⨟ᵐ-monotonic s t s′ t′ (id-⊑ᵐ-id x) (id⇒-⊑ᵐ-↣ x₁ x₂) = id⇒-⊑ᵐ-↣ x₁ x₂
⨟ᵐ-monotonic s t s′ t′ (id-⊑ᵐ-id x) (id★-⊑ᵐ-↣ x₁ x₂) = id★-⊑ᵐ-↣ x₁ x₂
⨟ᵐ-monotonic s t s′ t′ (id-⊑ᵐ-id x) (↣-⊑ᵐ-id x₁ x₂) = ↣-⊑ᵐ-id x₁ x₂
⨟ᵐ-monotonic s t s′ t′ (id-⊑ᵐ-id x) (↣-⊑ᵐ-↣ x₁ x₂) = ↣-⊑ᵐ-↣ x₁ x₂
⨟ᵐ-monotonic s t s′ t′ (id-⊑ᵐ-id x) (m-⊑ᵐ-⊥ x₁ x₂) = m-⊑ᵐ-⊥ x x₂
⨟ᵐ-monotonic s t s′ t′ (id⇒-⊑ᵐ-↣ x x₁) (id-⊑ᵐ-id x₂) = id⇒-⊑ᵐ-↣ x x₁
⨟ᵐ-monotonic s t s′ t′ (id⇒-⊑ᵐ-↣ x x₁) (id⇒-⊑ᵐ-↣ x₂ x₃) =
    let xx = id-⊑-⨟ᶜ _ _ x₂ x in
    let yy = id-⊑-⨟ᶜ _ _ x₁ x₃ in
    id⇒-⊑ᵐ-↣ xx yy
⨟ᵐ-monotonic s t s′ t′ (id⇒-⊑ᵐ-↣ x x₁) (↣-⊑ᵐ-id x₂ x₃) =
    ↣-⊑ᵐ-↣ (trans-id x₂ x) (trans-id x₃ x₁)
⨟ᵐ-monotonic s t s′ t′ (id⇒-⊑ᵐ-↣{c′ = c′}{d′} id≤c′ id≤d′)
                       (↣-⊑ᵐ-↣{c = c}{d}{c′₂}{d′₂} c≤c′₂ d≤d′₂) =
  let xx = (compose-id1 c≤c′₂ id≤c′) in
  let yy = (compose-id2 id≤d′ d≤d′₂) in
  ↣-⊑ᵐ-↣ xx yy
⨟ᵐ-monotonic s t s′ t′ (id⇒-⊑ᵐ-↣ x x₁) (m-⊑ᵐ-⊥ x₂ x₃)
    with ⊑ᶜ→⊑ _ _ x | ⊑ᶜ→⊑ _ _ x₁
... | aa , bb | cc , dd = m-⊑ᵐ-⊥ (⊑-⇒ bb cc) x₃    
⨟ᵐ-monotonic s t s′ t′ (id★-⊑ᵐ-↣ x x₁) (id-⊑ᵐ-id x₂) = id★-⊑ᵐ-↣ x x₁
⨟ᵐ-monotonic s t s′ t′ (id★-⊑ᵐ-↣ x x₁) (id★-⊑ᵐ-↣ x₂ x₃) =
   id★-⊑ᵐ-↣ (compose-id1 x₂ x) (compose-id1 x₁ x₃)
⨟ᵐ-monotonic s t s′ t′ (id★-⊑ᵐ-↣ x x₁) (m-⊑ᵐ-⊥ x₂ x₃) = m-⊑ᵐ-⊥ ⊑-★ x₃
⨟ᵐ-monotonic s t s′ t′ (↣-⊑ᵐ-id x x₁) (id-⊑ᵐ-id x₂) = ↣-⊑ᵐ-id x x₁
⨟ᵐ-monotonic s t s′ t′ (↣-⊑ᵐ-id x x₁) (id⇒-⊑ᵐ-↣ x₂ x₃) = {!!}
⨟ᵐ-monotonic s t s′ t′ (↣-⊑ᵐ-id x x₁) (↣-⊑ᵐ-id x₂ x₃) = {!!}
⨟ᵐ-monotonic s t s′ t′ (↣-⊑ᵐ-id x x₁) (↣-⊑ᵐ-↣ x₂ x₃) = {!!}
⨟ᵐ-monotonic s t s′ t′ (↣-⊑ᵐ-id x x₁) (m-⊑ᵐ-⊥ x₂ x₃) = {!!}
⨟ᵐ-monotonic s t s′ t′ (↣-⊑ᵐ-↣ x x₁) t≤t′ = {!!}
⨟ᵐ-monotonic s t s′ t′ (m-⊑ᵐ-⊥ x x₁) t≤t′ = {!!}
