module GTLC where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst)
open import Types
open import Contexts

data Term : Set where
  `_    : Var → Term
  $_    : Nat → Term
  ƛ_⇒_  : Ty → Term → Term
  _·_   : {ℓ : Nat} → Term → Term → Term

infix 4 _⊢_⦂_

data _⊢_⦂_ : Ctx → Term → Ty → Set where
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      ----------------
    → Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Γ n}
      ---------
    → Γ ⊢ $ n ⦂ ℕ

  ⊢ƛ : ∀ {Γ A N B}
    → (A ∷ Γ) ⊢ N ⦂ B
      -----------------------
    → Γ ⊢ ƛ A ⇒ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ L M A A′ B ℓ}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A′ 
    → A′ ~ A
      ----------------
    → Γ ⊢ (_·_ {ℓ = ℓ} L M) ⦂ B

  ⊢·★ : ∀ {Γ L M A ℓ}
    → Γ ⊢ L ⦂ ★
    → Γ ⊢ M ⦂ A
      ----------------
    → Γ ⊢ (_·_ {ℓ = ℓ} L M) ⦂ ★

infix 4 _⊑ᵀ_

data _⊑ᵀ_ : Term → Term → Set where
  ⊑` : ∀ {x}
    → ` x  ⊑ᵀ ` x

  ⊑$ : ∀ {n}
    → $ n ⊑ᵀ $ n

  ⊑ƛ : ∀ {N M A A′}
    → A ⊑ A′
    → N ⊑ᵀ M
    → ƛ A ⇒ N ⊑ᵀ ƛ A′ ⇒ M

  ⊑· : ∀ {ℓ L L′ M M′}
    → L ⊑ᵀ L′
    → M ⊑ᵀ M′
    → (_·_ {ℓ = ℓ} L M) ⊑ᵀ (_·_ {ℓ = ℓ} L′ M′)

infix 4 _⊢_⦂_⊑ᵀ_⦂_
data _⊢_⦂_⊑ᵀ_⦂_ {Γ Γ′ : Ctx} (ρ : Γ ⊑ᵉ Γ′) : Term → Ty → Term → Ty → Set where
  ⊑` : ∀ {A A′ x}
    → Γ ∋ x ⦂ A
    → Γ′ ∋ x ⦂ A′
    → ρ ⊢ ` x ⦂ A ⊑ᵀ ` x ⦂ A′

  ⊑$ : ∀ {n}
    → ρ ⊢ $ n ⦂ ℕ ⊑ᵀ $ n ⦂ ℕ

  ⊑ƛ : ∀ {A A′ B B′ N M}
    → (A⊑A′ : A ⊑ A′)
    → (extend-⊑ᵉ A⊑A′ ρ) ⊢ N ⦂ B ⊑ᵀ M ⦂ B′
    → ρ ⊢ ƛ A ⇒ N ⦂ (A ⇒ B) ⊑ᵀ ƛ A′ ⇒ M ⦂ (A′ ⇒ B′)

  ⊑· : ∀ {A A′ Aarg A′arg B B′ L L′ M M′ ℓ}
    → ρ ⊢ L ⦂ (A ⇒ B) ⊑ᵀ L′ ⦂ (A′ ⇒ B′)
    → ρ ⊢ M ⦂ Aarg ⊑ᵀ M′ ⦂ A′arg
    → Aarg ~ A
    → A′arg ~ A′
    → ρ ⊢ (_·_ {ℓ = ℓ} L M) ⦂ B ⊑ᵀ (_·_ {ℓ = ℓ} L′ M′) ⦂ B′

  ⊑·★ : ∀ {A A′ L L′ M M′ ℓ}
    → ρ ⊢ L ⦂ ★ ⊑ᵀ L′ ⦂ ★
    → ρ ⊢ M ⦂ A ⊑ᵀ M′ ⦂ A′
    → ρ ⊢ (_·_ {ℓ = ℓ} L M) ⦂ ★ ⊑ᵀ (_·_ {ℓ = ℓ} L′ M′) ⦂ ★

  ⊑·★L : ∀ {A A′ A′arg B′ L L′ M M′ ℓ}
    → ρ ⊢ L ⦂ ★ ⊑ᵀ L′ ⦂ (A′ ⇒ B′)
    → ρ ⊢ M ⦂ A ⊑ᵀ M′ ⦂ A′arg
    → A′arg ~ A′
    → ρ ⊢ (_·_ {ℓ = ℓ} L M) ⦂ ★ ⊑ᵀ (_·_ {ℓ = ℓ} L′ M′) ⦂ B′

mutual
  ⊑-to-~ : ∀ {A B} → A ⊑ B → A ~ B
  ⊑-to-~ ⊑-ℕ = ~-ℕ
  ⊑-to-~ {B = ℕ} ⊑-★ = ★~ℕ
  ⊑-to-~ {B = ★} ⊑-★ = ~-★
  ⊑-to-~ {B = A ⇒ B} ⊑-★ = ★~⇒ (~-from-⊑ (⊑-★ {A = A})) (⊑-to-~ (⊑-★ {A = B}))
  ⊑-to-~ (⊑-⇒ A⊑C B⊑D) = ~-⇒ (~-from-⊑ A⊑C) (⊑-to-~ B⊑D)

  ~-from-⊑ : ∀ {A B} → A ⊑ B → B ~ A
  ~-from-⊑ ⊑-ℕ = ~-ℕ
  ~-from-⊑ {B = ℕ} ⊑-★ = ℕ~★
  ~-from-⊑ {B = ★} ⊑-★ = ~-★
  ~-from-⊑ {B = A ⇒ B} ⊑-★ = ⇒~★ (⊑-to-~ (⊑-★ {A = A})) (~-from-⊑ (⊑-★ {A = B}))
  ~-from-⊑ (⊑-⇒ A⊑C B⊑D) = ~-⇒ (⊑-to-~ A⊑C) (~-from-⊑ B⊑D)

⊑ᵀ-type-precision
  : ∀ {Γ Γ′} {ρ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → ρ ⊢ M ⦂ A ⊑ᵀ M′ ⦂ A′
  → A ⊑ A′
⊑ᵀ-type-precision {ρ = ρ} (⊑` {x = x} ∋x ∋x′) = ρ x _ _ ∋x ∋x′
⊑ᵀ-type-precision ⊑$ = ⊑-ℕ
⊑ᵀ-type-precision {ρ = ρ} {A = A ⇒ B} {A′ = A′ ⇒ B′} (⊑ƛ A⊑A′ N⊑M) =
  ⊑-⇒ A⊑A′ (⊑ᵀ-type-precision {ρ = extend-⊑ᵉ A⊑A′ ρ} N⊑M)
⊑ᵀ-type-precision (⊑· L⊑L′ M⊑M′ _ _) with ⊑ᵀ-type-precision L⊑L′
... | ⊑-⇒ _ B⊑B′ = B⊑B′
⊑ᵀ-type-precision (⊑·★ L⊑L′ M⊑M′) = ⊑-★
⊑ᵀ-type-precision (⊑·★L L⊑L′ M⊑M′ _) = ⊑-★

⊑ᵀ-left-typed
  : ∀ {Γ Γ′} {ρ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → ρ ⊢ M ⦂ A ⊑ᵀ M′ ⦂ A′
  → Γ ⊢ M ⦂ A
⊑ᵀ-left-typed (⊑` ∋x _) = ⊢` ∋x
⊑ᵀ-left-typed ⊑$ = ⊢$
⊑ᵀ-left-typed {ρ = ρ} {A = A ⇒ B} {A′ = A′ ⇒ B′} (⊑ƛ A⊑A′ N⊑M) =
  ⊢ƛ (⊑ᵀ-left-typed {ρ = extend-⊑ᵉ A⊑A′ ρ} N⊑M)
⊑ᵀ-left-typed (⊑· L⊑L′ M⊑M′ Aarg~A _) = ⊢· (⊑ᵀ-left-typed L⊑L′) (⊑ᵀ-left-typed M⊑M′) Aarg~A
⊑ᵀ-left-typed (⊑·★ L⊑L′ M⊑M′) = ⊢·★ (⊑ᵀ-left-typed L⊑L′) (⊑ᵀ-left-typed M⊑M′)
⊑ᵀ-left-typed (⊑·★L L⊑L′ M⊑M′ _) = ⊢·★ (⊑ᵀ-left-typed L⊑L′) (⊑ᵀ-left-typed M⊑M′)

⊑ᵀ-right-typed
  : ∀ {Γ Γ′} {ρ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → ρ ⊢ M ⦂ A ⊑ᵀ M′ ⦂ A′
  → Γ′ ⊢ M′ ⦂ A′
⊑ᵀ-right-typed (⊑` _ ∋x′) = ⊢` ∋x′
⊑ᵀ-right-typed ⊑$ = ⊢$
⊑ᵀ-right-typed {ρ = ρ} {A = A ⇒ B} {A′ = A′ ⇒ B′} (⊑ƛ A⊑A′ N⊑M) =
  ⊢ƛ (⊑ᵀ-right-typed {ρ = extend-⊑ᵉ A⊑A′ ρ} N⊑M)
⊑ᵀ-right-typed (⊑· L⊑L′ M⊑M′ _ A′arg~A′) = ⊢· (⊑ᵀ-right-typed L⊑L′) (⊑ᵀ-right-typed M⊑M′) A′arg~A′
⊑ᵀ-right-typed (⊑·★ L⊑L′ M⊑M′) = ⊢·★ (⊑ᵀ-right-typed L⊑L′) (⊑ᵀ-right-typed M⊑M′)
⊑ᵀ-right-typed (⊑·★L L⊑L′ M⊑M′ A′arg~A′) = ⊢· (⊑ᵀ-right-typed L⊑L′) (⊑ᵀ-right-typed M⊑M′) A′arg~A′

term-precision-⊑ᵀ : ∀ {Γ Γ′} {ρ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → Γ ⊢ M ⦂ A
  → Γ′ ⊢ M′ ⦂ A′
  → M ⊑ᵀ M′
  → ρ ⊢ M ⦂ A ⊑ᵀ M′ ⦂ A′
term-precision-⊑ᵀ (⊢` ∋x) (⊢` ∋x′) ⊑` = ⊑` ∋x ∋x′
term-precision-⊑ᵀ ⊢$ ⊢$ ⊑$ = ⊑$
term-precision-⊑ᵀ
  (⊢ƛ {A = A} {N = N} {B = B} N⦂B)
  (⊢ƛ {A = A′} {N = M} {B = B′} M⦂B′)
  (⊑ƛ A⊑A′ N⊑M) =
  ⊑ƛ A⊑A′ (term-precision-⊑ᵀ N⦂B M⦂B′ N⊑M)
term-precision-⊑ᵀ
  (⊢· {A = A} {A′ = Aarg} {B = B} L⦂A⇒B M⦂Aarg Aarg~A)
  (⊢· {A = A′} {A′ = A′arg} {B = B′} L′⦂A′⇒B′ M′⦂A′arg A′arg~A′)
  (⊑· L⊑L′ M⊑M′) =
  ⊑· (term-precision-⊑ᵀ L⦂A⇒B L′⦂A′⇒B′ L⊑L′)
     (term-precision-⊑ᵀ M⦂Aarg M′⦂A′arg M⊑M′)
     Aarg~A
     A′arg~A′
term-precision-⊑ᵀ
  (⊢·★ {A = A} L⦂★ M⦂A)
  (⊢· {A = A′} {A′ = A′arg} {B = B′} L′⦂A′⇒B′ M′⦂A′arg A′arg~A′)
  (⊑· L⊑L′ M⊑M′) =
  ⊑·★L (term-precision-⊑ᵀ L⦂★ L′⦂A′⇒B′ L⊑L′)
       (term-precision-⊑ᵀ M⦂A M′⦂A′arg M⊑M′)
       A′arg~A′
term-precision-⊑ᵀ {ρ = ρ}
  (⊢· {A = A} {A′ = Aarg} {B = B} L⦂A⇒B M⦂Aarg Aarg~A)
  (⊢·★ {A = A′} L′⦂★ M′⦂A′)
  (⊑· L⊑L′ M⊑M′)
  with ⊑ᵀ-type-precision (term-precision-⊑ᵀ {ρ = ρ} L⦂A⇒B L′⦂★ L⊑L′)
... | ()
term-precision-⊑ᵀ
  (⊢·★ {A = A} L⦂★ M⦂A)
  (⊢·★ {A = A′} L′⦂★ M′⦂A′)
  (⊑· L⊑L′ M⊑M′) =
  ⊑·★ (term-precision-⊑ᵀ L⦂★ L′⦂★ L⊑L′)
      (term-precision-⊑ᵀ M⦂A M′⦂A′ M⊑M′)

typing-unique
  : ∀ {Γ M A B}
  → Γ ⊢ M ⦂ A
  → Γ ⊢ M ⦂ B
  → A ≡ B
typing-unique (⊢` ∋x) (⊢` ∋x′) = ∋-unique ∋x ∋x′
typing-unique ⊢$ ⊢$ = refl
typing-unique (⊢ƛ N⦂A) (⊢ƛ N⦂B)
    with typing-unique N⦂A N⦂B
... | refl = refl
typing-unique (⊢· L⦂A⇒B M⦂A′ A′~A) (⊢· L⦂C⇒D M⦂C′ C′~C)
    with typing-unique L⦂A⇒B L⦂C⇒D
... | refl = refl
typing-unique (⊢· L⦂A⇒B M⦂A′ A′~A) (⊢·★ L⦂★ M⦂A)
    with typing-unique L⦂A⇒B L⦂★
... | ()
typing-unique (⊢·★ L⦂★ M⦂A) (⊢· L⦂A⇒B M⦂A′ A′~A)
    with typing-unique L⦂★ L⦂A⇒B
... | ()
typing-unique (⊢·★ L⦂★ M⦂A) (⊢·★ L⦂★₁ M⦂B) = refl


tp-left-id
  : ∀ {Γ Γ′} {ρ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → (M⦂A : Γ ⊢ M ⦂ A)
  → (M′⦂A′ : Γ′ ⊢ M′ ⦂ A′)
  → (M≤M′ : M ⊑ᵀ M′)
  → ⊑ᵀ-left-typed (term-precision-⊑ᵀ {ρ = ρ} M⦂A M′⦂A′ M≤M′) ≡ M⦂A
tp-left-id (⊢` ∋x) (⊢` ∋x′) ⊑` = refl
tp-left-id ⊢$ ⊢$ ⊑$ = refl
tp-left-id (⊢ƛ N⦂B) (⊢ƛ M⦂B′) (⊑ƛ A⊑A′ N⊑M) =
  cong ⊢ƛ (tp-left-id N⦂B M⦂B′ N⊑M)
tp-left-id
  (⊢· L⦂A⇒B M⦂Aarg Aarg~A)
  (⊢· L′⦂A′⇒B′ M′⦂A′arg A′arg~A′)
  (⊑· L⊑L′ M⊑M′)
  = cong₂ (λ L⦂ M⦂ → ⊢· L⦂ M⦂ Aarg~A)
      (tp-left-id L⦂A⇒B L′⦂A′⇒B′ L⊑L′)
      (tp-left-id M⦂Aarg M′⦂A′arg M⊑M′)
tp-left-id
  (⊢·★ L⦂★ M⦂A)
  (⊢· L′⦂A′⇒B′ M′⦂A′arg A′arg~A′)
  (⊑· L⊑L′ M⊑M′)
  = cong₂ ⊢·★
      (tp-left-id L⦂★ L′⦂A′⇒B′ L⊑L′)
      (tp-left-id M⦂A M′⦂A′arg M⊑M′)
tp-left-id
  (⊢·★ L⦂★ M⦂A)
  (⊢·★ L′⦂★ M′⦂A′)
  (⊑· L⊑L′ M⊑M′)
  = cong₂ ⊢·★
      (tp-left-id L⦂★ L′⦂★ L⊑L′)
      (tp-left-id M⦂A M′⦂A′ M⊑M′)
tp-left-id {ρ = ρ}
  (⊢· L⦂A⇒B M⦂Aarg Aarg~A)
  (⊢·★ L′⦂★ M′⦂A′)
  (⊑· L⊑L′ M⊑M′)
    with ⊑ᵀ-type-precision (term-precision-⊑ᵀ {ρ = ρ} L⦂A⇒B L′⦂★ L⊑L′)
... | ()

tp-right-id
  : ∀ {Γ Γ′} {ρ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → (M⦂A : Γ ⊢ M ⦂ A)
  → (M′⦂A′ : Γ′ ⊢ M′ ⦂ A′)
  → (M≤M′ : M ⊑ᵀ M′)
  → ⊑ᵀ-right-typed (term-precision-⊑ᵀ {ρ = ρ} M⦂A M′⦂A′ M≤M′) ≡ M′⦂A′
tp-right-id (⊢` ∋x) (⊢` ∋x′) ⊑` = refl
tp-right-id ⊢$ ⊢$ ⊑$ = refl
tp-right-id (⊢ƛ N⦂B) (⊢ƛ M⦂B′) (⊑ƛ A⊑A′ N⊑M) =
  cong ⊢ƛ (tp-right-id N⦂B M⦂B′ N⊑M)
tp-right-id
  (⊢· L⦂A⇒B M⦂Aarg Aarg~A)
  (⊢· L′⦂A′⇒B′ M′⦂A′arg A′arg~A′)
  (⊑· L⊑L′ M⊑M′)
  = cong₂ (λ L⦂ M⦂ → ⊢· L⦂ M⦂ A′arg~A′)
      (tp-right-id L⦂A⇒B L′⦂A′⇒B′ L⊑L′)
      (tp-right-id M⦂Aarg M′⦂A′arg M⊑M′)
tp-right-id
  (⊢·★ L⦂★ M⦂A)
  (⊢· L′⦂A′⇒B′ M′⦂A′arg A′arg~A′)
  (⊑· L⊑L′ M⊑M′)
  = cong₂ (λ L⦂ M⦂ → ⊢· L⦂ M⦂ A′arg~A′)
      (tp-right-id L⦂★ L′⦂A′⇒B′ L⊑L′)
      (tp-right-id M⦂A M′⦂A′arg M⊑M′)
tp-right-id
  (⊢·★ L⦂★ M⦂A)
  (⊢·★ L′⦂★ M′⦂A′)
  (⊑· L⊑L′ M⊑M′)
  = cong₂ ⊢·★
      (tp-right-id L⦂★ L′⦂★ L⊑L′)
      (tp-right-id M⦂A M′⦂A′ M⊑M′)
tp-right-id {ρ = ρ}
  (⊢· L⦂A⇒B M⦂Aarg Aarg~A)
  (⊢·★ L′⦂★ M′⦂A′)
  (⊑· L⊑L′ M⊑M′)
    with ⊑ᵀ-type-precision (term-precision-⊑ᵀ {ρ = ρ} L⦂A⇒B L′⦂★ L⊑L′)
... | ()
