module proof.TypingLemmas where

-- File Charter:
--   * Private typing/lookup uniqueness and inversion lemmas.
--   * Support code for the private decidable type-checking proof.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (∃; ∃-syntax; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
  renaming (subst to substEq)

open import STLCMore

∋-unique : {Γ : Ctx} {x : Var} {A B : Ty}
    → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B
    → A ≡ B
∋-unique Z Z = refl
∋-unique (S x:A) (S x:B) = ∋-unique x:A x:B

lookup : (Γ : Ctx) (x : Var) → Dec (∃[ A ] Γ ∋ x ⦂ A)
lookup [] x = no λ { () }
lookup (A ∷ Γ) zero = yes (A , Z)
lookup (A ∷ Γ) (suc x)
    with lookup Γ x
... | yes (B , x:B) = yes (B , (S x:B))
... | no nxx = no λ { (B , S sx:B) → nxx (B , sx:B) }

nat-fun : ∀ {A B} → nat ≡ A ⇒ B → ⊥
nat-fun ()

nat-unit : nat ≡ unit -> ⊥
nat-unit ()

unit-nat : unit ≡ nat -> ⊥
unit-nat ()

unit-fun : ∀ {A B} → unit ≡ A ⇒ B → ⊥
unit-fun ()

nat-prod : ∀ {A B} → nat ≡ A `× B → ⊥
nat-prod ()

nat-sum : ∀ {A B} → nat ≡ A `+ B → ⊥
nat-sum ()

unit-prod : ∀ {A B} → unit ≡ A `× B → ⊥
unit-prod ()

unit-sum : ∀ {A B} → unit ≡ A `+ B → ⊥
unit-sum ()

fun-nat : ∀ {A B} → A ⇒ B ≡ nat → ⊥
fun-nat ()

fun-unit : ∀ {A B} → A ⇒ B ≡ unit → ⊥
fun-unit ()

fun-prod : ∀ {A B C D} → A ⇒ B ≡ C `× D → ⊥
fun-prod ()

fun-sum : ∀ {A B C D} → A ⇒ B ≡ C `+ D → ⊥
fun-sum ()

fun-inv1 : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → A ≡ C
fun-inv1 refl = refl

fun-inv2 : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → B ≡ D
fun-inv2 refl = refl

prod-nat : ∀ {A B} → A `× B ≡ nat → ⊥
prod-nat ()

prod-unit : ∀ {A B} → A `× B ≡ unit → ⊥
prod-unit ()

prod-fun : ∀ {A B C D} → A `× B ≡ C ⇒ D → ⊥
prod-fun ()

prod-inv1 : ∀ {A B C D} → A `× B ≡ C `× D → A ≡ C
prod-inv1 refl = refl

prod-inv2 : ∀ {A B C D} → A `× B ≡ C `× D → B ≡ D
prod-inv2 refl = refl

prod-sum : ∀ {A B C D} → A `× B ≡ C `+ D → ⊥
prod-sum ()

sum-nat : ∀ {A B} → A `+ B ≡ nat → ⊥
sum-nat ()

sum-unit : ∀ {A B} → A `+ B ≡ unit → ⊥
sum-unit ()

sum-fun : ∀ {A B C D} → A `+ B ≡ C ⇒ D → ⊥
sum-fun ()

sum-prod : ∀ {A B C D} → A `+ B ≡ C `× D → ⊥
sum-prod ()

sum-inv1 : ∀ {A B C D} → A `+ B ≡ C `+ D → A ≡ C
sum-inv1 refl = refl

sum-inv2 : ∀ {A B C D} → A `+ B ≡ C `+ D → B ≡ D
sum-inv2 refl = refl

typing-unique : (Γ : Ctx) (M : Term) (A B : Ty)
    → Γ ⊢ M ⦂ A → Γ ⊢ M ⦂ B
    → A ≡ B
typing-unique Γ _ _ _ (⊢` x:A) (⊢` x:B) =
  ∋-unique x:A x:B
typing-unique Γ _ _ _ (⊢ƛ {A = A} {B = B₁} {N = N} N:B₁) (⊢ƛ {B = B₂} N:B₂) =
  cong (A ⇒_) (typing-unique (A ∷ Γ) N B₁ B₂ N:B₁ N:B₂)
typing-unique Γ _ _ _ (⊢· {A = A₁} {B = B₁} {L = L} L:AB M:A)
                      (⊢· {A = A₂} {B = B₂} L:CD M:C) =
  fun-inv2 (typing-unique Γ L (A₁ ⇒ B₁) (A₂ ⇒ B₂) L:AB L:CD)
typing-unique Γ _ _ _ (⊢as M:A) (⊢as M:B) =
  typing-unique Γ _ _ _ M:A M:B
typing-unique Γ _ _ _ (⊢let {A = A₁} {B = B₁} {M = M} {N = N} M:A N:B₁)
                      (⊢let {A = A₂} {B = B₂} M:A′ N:B₂) =
  typing-unique (A₁ ∷ Γ) N B₁ B₂ N:B₁
    (substEq (λ A -> (A ∷ Γ) ⊢ N ⦂ B₂)
      (typing-unique Γ M A₂ A₁ M:A′ M:A)
      N:B₂)
typing-unique Γ _ _ _ ⊢zero ⊢zero = refl
typing-unique Γ _ _ _ ⊢unit ⊢unit = refl
typing-unique Γ _ _ _ (⊢suc M:nat) (⊢suc M:nat′) = refl
typing-unique Γ _ _ _ (⊢case {M = M} L:nat M:A N:A) (⊢case L:nat′ M:B N:B) =
  typing-unique Γ M _ _ M:A M:B
typing-unique Γ _ _ _ (⊢pair M:A N:B) (⊢pair M:C N:D) =
  cong₂ _`×_
    (typing-unique Γ _ _ _ M:A M:C)
    (typing-unique Γ _ _ _ N:B N:D)
typing-unique Γ _ _ _ (⊢fst M:AB) (⊢fst M:CD) =
  prod-inv1 (typing-unique Γ _ _ _ M:AB M:CD)
typing-unique Γ _ _ _ (⊢snd M:AB) (⊢snd M:CD) =
  prod-inv2 (typing-unique Γ _ _ _ M:AB M:CD)
typing-unique Γ _ _ _ (⊢inl M:A) (⊢inl M:C) = refl
typing-unique Γ _ _ _ (⊢inr M:B) (⊢inr M:D) = refl
typing-unique Γ _ _ _
  (⊢case⊎ {A = A₁} {B = B₁} {C = C₁} {L = L} {M = M} L:AB M:C N:C)
  (⊢case⊎ {A = A₂} {B = B₂} {C = C₂} L:CD M:D N:D) =
  typing-unique (A₁ ∷ Γ) M C₁ C₂ M:C
    (substEq (λ A -> (A ∷ Γ) ⊢ M ⦂ C₂)
      (sym (sum-inv1 (typing-unique Γ L (A₁ `+ B₁) (A₂ `+ B₂) L:AB L:CD)))
      M:D)
