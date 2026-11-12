module proof.TypingLemmas where

-- File Charter:
--   * Private typing/lookup uniqueness and inversion lemmas.
--   * Support code for the private decidable type-checking proof.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (∃; ∃-syntax; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import STLC

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

fun-inv1 : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → A ≡ C
fun-inv1 refl = refl

fun-inv2 : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → B ≡ D
fun-inv2 refl = refl

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
typing-unique Γ _ _ _ ⊢zero ⊢zero = refl
typing-unique Γ _ _ _ (⊢suc M:nat) (⊢suc M:nat′) = refl
typing-unique Γ _ _ _ (⊢case {M = M} L:nat M:A N:A) (⊢case L:nat′ M:B N:B) =
  typing-unique Γ M _ _ M:A M:B
