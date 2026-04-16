module CastFactorization where

-- File Charter:
--   * Indexed Conversion/Cast relations for factorization work.
--   * Judgments are indexed by store and permissions, mirroring Up/Down typing.
--   * Rule shapes follow the corresponding `wt-*` Up/Down typing rules.
--   * The previous factorization theorem attempt is intentionally removed.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s<s; s≤s)
open import Data.Product using (_,_; _×_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; subst; sym; trans)
open import Data.Nat.Properties using (n<1+n; +-assoc; +-comm; +-suc; <⇒≤; ≤-refl; m≤m+n; m≤n+m; m+n≤o⇒m≤o; m+n≤o⇒n≤o; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; ≤-<-trans; ≤-trans)

open import Types
open import TypeProperties
open import Store
open import UpDown
open import TypeCheckDec using (raiseVarFrom; closeνSrc; open-closeνSrc-id)
open import Conversion
open import Cast

------------------------------------------------------------------------
-- Size machinery for metric-based recursion
------------------------------------------------------------------------

mutual
  size↑ˢ : ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty} → Σ ∣ Φ ⊢ A ↑ˢ B → ℕ
  size↑ˢ (↑ˢ-unseal _ _) = suc zero
  size↑ˢ (↑ˢ-⇒ h↓ h↑) = suc (size↓ˢ h↓ + size↑ˢ h↑)
  size↑ˢ (↑ˢ-∀ h↑) = suc (size↑ˢ h↑)
  size↑ˢ (↑ˢ-id _) = suc zero
  size↑ˢ (h↑₁ ；↑ˢ h↑₂) = suc (size↑ˢ h↑₁ + size↑ˢ h↑₂)

  size↓ˢ : ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty} → Σ ∣ Φ ⊢ A ↓ˢ B → ℕ
  size↓ˢ (↓ˢ-seal _ _) = suc zero
  size↓ˢ (↓ˢ-⇒ h↑ h↓) = suc (size↑ˢ h↑ + size↓ˢ h↓)
  size↓ˢ (↓ˢ-∀ h↓) = suc (size↓ˢ h↓)
  size↓ˢ (↓ˢ-id _) = suc zero
  size↓ˢ (h↓₁ ；↓ˢ h↓₂) = suc (size↓ˢ h↓₁ + size↓ˢ h↓₂)

mutual
  size⊑ᶜ : ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty} → Σ ∣ Φ ⊢ A ⊑ᶜ B → ℕ
  size⊑ᶜ (⊑ᶜ-tag _ _) = suc zero
  size⊑ᶜ (⊑ᶜ-unseal★ _ _) = suc zero
  size⊑ᶜ (⊑ᶜ-⇒ h⊒ h⊑) = suc (size⊒ᶜ h⊒ + size⊑ᶜ h⊑)
  size⊑ᶜ (⊑ᶜ-∀ h⊑) = suc (size⊑ᶜ h⊑)
  size⊑ᶜ (⊑ᶜ-ν h⊑) = suc (size⊑ᶜ h⊑)
  size⊑ᶜ (⊑ᶜ-id _) = suc zero
  size⊑ᶜ (h⊑₁ ；⊑ᶜ h⊑₂) = suc (size⊑ᶜ h⊑₁ + size⊑ᶜ h⊑₂)

  size⊒ᶜ : ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty} → Σ ∣ Φ ⊢ A ⊒ᶜ B → ℕ
  size⊒ᶜ (⊒ᶜ-untag _ _ _) = suc zero
  size⊒ᶜ (⊒ᶜ-seal★ _ _) = suc zero
  size⊒ᶜ (⊒ᶜ-⇒ h⊑ h⊒) = suc (size⊑ᶜ h⊑ + size⊒ᶜ h⊒)
  size⊒ᶜ (⊒ᶜ-∀ h⊒) = suc (size⊒ᶜ h⊒)
  size⊒ᶜ (⊒ᶜ-ν h⊒) = suc (size⊒ᶜ h⊒)
  size⊒ᶜ (⊒ᶜ-id _) = suc zero
  size⊒ᶜ (h⊒₁ ；⊒ᶜ h⊒₂) = suc (size⊒ᶜ h⊒₁ + size⊒ᶜ h⊒₂)

cutSize⊑↑ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
  → Σ ∣ Φ ⊢ A ⊑ᶜ B
  → Σ ∣ Φ ⊢ B ↑ˢ C
  → ℕ
cutSize⊑↑ h⊑ h↑ = size⊑ᶜ h⊑ + size↑ˢ h↑

cutSize↓⊒ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
  → Σ ∣ Φ ⊢ A ↓ˢ B
  → Σ ∣ Φ ⊢ B ⊒ᶜ C
  → ℕ
cutSize↓⊒ h↓ h⊒ = size↓ˢ h↓ + size⊒ᶜ h⊒

<-suc-cancel :
  ∀ {m n : ℕ}
  → suc m < suc n
  → m < n
<-suc-cancel (s<s h) = h

size⊑ᶜ-id :
  ∀ {Σ : Store}{Φ : List CastPerm}{A : Ty}
  (wfA : WfTySome A)
  → size⊑ᶜ (⊑ᶜ-id {Σ = Σ} {Φ = Φ} {A = A} wfA) ≡ suc zero
size⊑ᶜ-id wfA = refl

size⊒ᶜ-id :
  ∀ {Σ : Store}{Φ : List CastPerm}{A : Ty}
  (wfA : WfTySome A)
  → size⊒ᶜ (⊒ᶜ-id {Σ = Σ} {Φ = Φ} {A = A} wfA) ≡ suc zero
size⊒ᶜ-id wfA = refl

size↑ˢ-subst-store :
  ∀ {Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}
  → (eqΣ : Σ ≡ Σ′)
  → (p : Σ ∣ Φ ⊢ A ↑ˢ B)
  → size↑ˢ (subst (λ S → S ∣ Φ ⊢ A ↑ˢ B) eqΣ p) ≡ size↑ˢ p
size↑ˢ-subst-store refl p = refl

size↓ˢ-subst-store :
  ∀ {Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}
  → (eqΣ : Σ ≡ Σ′)
  → (p : Σ ∣ Φ ⊢ A ↓ˢ B)
  → size↓ˢ (subst (λ S → S ∣ Φ ⊢ A ↓ˢ B) eqΣ p) ≡ size↓ˢ p
size↓ˢ-subst-store refl p = refl

size↑ˢ-subst-left :
  ∀ {Σ : Store}{Φ : List CastPerm}{A A′ B : Ty}
  → (eqA : A ≡ A′)
  → (p : Σ ∣ Φ ⊢ A ↑ˢ B)
  → size↑ˢ (subst (λ T → Σ ∣ Φ ⊢ T ↑ˢ B) eqA p) ≡ size↑ˢ p
size↑ˢ-subst-left refl p = refl

size↑ˢ-subst-right :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B B′ : Ty}
  → (eqB : B ≡ B′)
  → (p : Σ ∣ Φ ⊢ A ↑ˢ B)
  → size↑ˢ (subst (λ T → Σ ∣ Φ ⊢ A ↑ˢ T) eqB p) ≡ size↑ˢ p
size↑ˢ-subst-right refl p = refl

size↓ˢ-subst-left :
  ∀ {Σ : Store}{Φ : List CastPerm}{A A′ B : Ty}
  → (eqA : A ≡ A′)
  → (p : Σ ∣ Φ ⊢ A ↓ˢ B)
  → size↓ˢ (subst (λ T → Σ ∣ Φ ⊢ T ↓ˢ B) eqA p) ≡ size↓ˢ p
size↓ˢ-subst-left refl p = refl

size↓ˢ-subst-right :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B B′ : Ty}
  → (eqB : B ≡ B′)
  → (p : Σ ∣ Φ ⊢ A ↓ˢ B)
  → size↓ˢ (subst (λ T → Σ ∣ Φ ⊢ A ↓ˢ T) eqB p) ≡ size↓ˢ p
size↓ˢ-subst-right refl p = refl

size⊑ᶜ-subst-left :
  ∀ {Σ : Store}{Φ : List CastPerm}{A A′ B : Ty}
  → (eqA : A ≡ A′)
  → (p : Σ ∣ Φ ⊢ A ⊑ᶜ B)
  → size⊑ᶜ (subst (λ T → Σ ∣ Φ ⊢ T ⊑ᶜ B) eqA p) ≡ size⊑ᶜ p
size⊑ᶜ-subst-left refl p = refl

size⊑ᶜ-subst-right :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B B′ : Ty}
  → (eqB : B ≡ B′)
  → (p : Σ ∣ Φ ⊢ A ⊑ᶜ B)
  → size⊑ᶜ (subst (λ T → Σ ∣ Φ ⊢ A ⊑ᶜ T) eqB p) ≡ size⊑ᶜ p
size⊑ᶜ-subst-right refl p = refl

size⊒ᶜ-subst-left :
  ∀ {Σ : Store}{Φ : List CastPerm}{A A′ B : Ty}
  → (eqA : A ≡ A′)
  → (p : Σ ∣ Φ ⊢ A ⊒ᶜ B)
  → size⊒ᶜ (subst (λ T → Σ ∣ Φ ⊢ T ⊒ᶜ B) eqA p) ≡ size⊒ᶜ p
size⊒ᶜ-subst-left refl p = refl

size⊒ᶜ-subst-right :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B B′ : Ty}
  → (eqB : B ≡ B′)
  → (p : Σ ∣ Φ ⊢ A ⊒ᶜ B)
  → size⊒ᶜ (subst (λ T → Σ ∣ Φ ⊢ A ⊒ᶜ T) eqB p) ≡ size⊒ᶜ p
size⊒ᶜ-subst-right refl p = refl

------------------------------------------------------------------------
-- Termination measure lemmas
------------------------------------------------------------------------

drop-left-+-< :
  ∀ (a b c n : ℕ)
  → (a + b + c < n)
  → (b + c < n)
drop-left-+-< a b c n h =
  ≤-<-trans
    (subst (λ t → b + c ≤ t) (sym (+-assoc a b c)) (m≤n+m (b + c) a))
    h

drop-left-+< :
  ∀ (a b n : ℕ)
  → (a + b < n)
  → (b < n)
drop-left-+< a b n h = ≤-<-trans (m≤n+m b a) h

drop-right-+< :
  ∀ (a b n : ℕ)
  → (a + b < n)
  → (a < n)
drop-right-+< a b n h = ≤-<-trans (m≤m+n a b) h

drop-suc-right-< :
  ∀ (a b n : ℕ)
  → (a + suc b < n)
  → (a + b < n)
drop-suc-right-< a b n h =
  ≤-<-trans (+-monoʳ-≤ a (<⇒≤ (n<1+n b))) h

swap-suc-sides-+< :
  ∀ (a b n : ℕ)
  → (a + suc b < n)
  → (suc a + b < n)
swap-suc-sides-+< a b n h = subst (λ t → t < n) (+-suc a b) h

cancel-+-suc-< :
  ∀ (a b n : ℕ)
  → (a + suc b < suc n)
  → (a + b < n)
cancel-+-suc-< a b n h =
  <-suc-cancel (subst (λ t → t < suc n) (+-suc a b) h)

+-shuffle :
  ∀ (a b c d : ℕ)
  → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-shuffle a b c d =
  trans
    (+-assoc a b (c + d))
    (trans
      (cong (a +_) (trans (sym (+-assoc b c d)) (cong (_+ d) (+-comm b c))))
      (trans
        (cong (λ t → a + t) (+-assoc c b d))
        (sym (+-assoc a c (b + d)))))

swap-+-≤ :
  ∀ (a b : ℕ)
  → a + b ≤ b + a
swap-+-≤ a b =
  subst
    (a + b ≤_)
    (sym (+-comm b a))
    ≤-refl

two-suc-+-mono :
  ∀ (a b c d : ℕ)
  → a + b ≤ c + d
  → suc a + suc b ≤ suc c + suc d
two-suc-+-mono a b c d h =
  subst
    (λ t → t ≤ suc c + suc d)
    (sym (+-suc (suc a) b))
    (subst
      (λ t → suc (suc a + b) ≤ t)
      (sym (+-suc (suc c) d))
      (s≤s (s≤s h)))

compose-budget-left :
  ∀ (x y z u a b c : ℕ)
  → x + y ≤ a + u
  → u + z ≤ b + c
  → x + suc (y + z) ≤ suc (a + b) + c
compose-budget-left x y z u a b c hxy huz =
  subst
    (λ t → x + suc (y + z) ≤ t)
    (cong suc (sym (+-assoc a b c)))
    (subst
      (λ t → t ≤ suc (a + (b + c)))
      (sym (+-suc x (y + z)))
      (s≤s base))
  where
    step₁ : x + (y + z) ≤ (a + u) + z
    step₁ =
      subst
        (λ t → t ≤ (a + u) + z)
        (+-assoc x y z)
        (+-monoˡ-≤ z hxy)

    step₂ : x + (y + z) ≤ a + (u + z)
    step₂ =
      subst
        (λ t → x + (y + z) ≤ t)
        (+-assoc a u z)
        step₁

    base : x + (y + z) ≤ a + (b + c)
    base = ≤-trans step₂ (+-monoʳ-≤ a huz)

compose-budget-right :
  ∀ (a b c d p h₁ h₂ : ℕ)
  → a + b ≤ p + h₁
  → c + d ≤ b + h₂
  → suc (a + c) + d ≤ p + suc (h₁ + h₂)
compose-budget-right a b c d p h₁ h₂ hab hcd =
  subst
    (λ t → suc (a + c) + d ≤ t)
    (sym (+-suc p (h₁ + h₂)))
    (s≤s base)
  where
    step₁ : (a + c) + d ≤ a + (b + h₂)
    step₁ =
      subst
        (λ t → t ≤ a + (b + h₂))
        (sym (+-assoc a c d))
        (+-monoʳ-≤ a hcd)

    step₂ : (a + c) + d ≤ (a + b) + h₂
    step₂ =
      subst
        (λ t → (a + c) + d ≤ t)
        (sym (+-assoc a b h₂))
        step₁

    step₃ : (a + b) + h₂ ≤ p + (h₁ + h₂)
    step₃ =
      subst
        (λ t → (a + b) + h₂ ≤ t)
        (+-assoc p h₁ h₂)
        (+-monoˡ-≤ h₂ hab)

    base : (a + c) + d ≤ p + (h₁ + h₂)
    base = ≤-trans step₂ step₃

arrow-budget-⊑↑ :
  ∀ (a b c d p q r s : ℕ)
  → a + b ≤ p + q
  → c + d ≤ r + s
  → suc (b + c) + suc (a + d) ≤ suc (q + r) + suc (p + s)
arrow-budget-⊑↑ a b c d p q r s hab hcd =
  two-suc-+-mono (b + c) (a + d) (q + r) (p + s) base₂
  where
    base₀ : (a + b) + (c + d) ≤ (p + q) + (r + s)
    base₀ = +-mono-≤ hab hcd

    base₁ : (b + c) + (a + d) ≤ (p + q) + (r + s)
    base₁ =
      subst
        (λ t → t ≤ (p + q) + (r + s))
        (sym
          (trans
            (+-shuffle b c a d)
            (cong (_+ (c + d)) (+-comm b a))))
        base₀

    base₂ : (b + c) + (a + d) ≤ (q + r) + (p + s)
    base₂ =
      subst
        (λ t → (b + c) + (a + d) ≤ t)
        (sym
          (trans
            (+-shuffle q r p s)
            (cong (_+ (r + s)) (+-comm q p))))
        base₁

arrow-budget-↓⊒ :
  ∀ (a b c d p q r s : ℕ)
  → c + a ≤ r + p
  → b + d ≤ q + s
  → suc (a + b) + suc (c + d) ≤ suc (p + q) + suc (r + s)
arrow-budget-↓⊒ a b c d p q r s hca hbd =
  two-suc-+-mono (a + b) (c + d) (p + q) (r + s) base₂
  where
    hca′ : a + c ≤ p + r
    hca′ =
      subst
        (λ t → a + c ≤ t)
        (sym (+-comm p r))
        (subst
          (λ t → t ≤ r + p)
          (+-comm c a)
          hca)

    base₀ : (a + c) + (b + d) ≤ (p + r) + (q + s)
    base₀ = +-mono-≤ hca′ hbd

    base₁ : (a + b) + (c + d) ≤ (p + r) + (q + s)
    base₁ =
      subst
        (λ t → t ≤ (p + r) + (q + s))
        (sym (+-shuffle a b c d))
        base₀

    base₂ : (a + b) + (c + d) ≤ (p + q) + (r + s)
    base₂ =
      subst
        (λ t → (a + b) + (c + d) ≤ t)
        (+-shuffle p r q s)
        base₁

id-budget⊑↑ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A C : Ty}
  (wfA : WfTySome A)
  (h↑ : Σ ∣ Φ ⊢ A ↑ˢ C)
  → size↑ˢ h↑ + size⊑ᶜ (⊑ᶜ-id {Σ = Σ} {Φ = Φ} {A = C} (wfTySome C))
    ≤ cutSize⊑↑ (⊑ᶜ-id wfA) h↑
id-budget⊑↑ {Σ = Σ} {Φ = Φ} {A = A} {C = C} wfA h↑ =
  subst
    (λ t → t ≤ cutSize⊑↑ (⊑ᶜ-id wfA) h↑)
    eqL
    (subst
      (λ t → size↑ˢ h↑ + suc zero ≤ t)
      eqR
      (subst (_≤ suc zero + size↑ˢ h↑) (sym (+-comm (size↑ˢ h↑) (suc zero))) ≤-refl))
  where
    eqL : size↑ˢ h↑ + size⊑ᶜ (⊑ᶜ-id {Σ = Σ} {Φ = Φ} {A = C} (wfTySome C)) ≡ size↑ˢ h↑ + suc zero
    eqL = cong (size↑ˢ h↑ +_) (size⊑ᶜ-id {Σ = Σ} {Φ = Φ} {A = C} (wfTySome C))

    eqR : suc zero + size↑ˢ h↑ ≡ cutSize⊑↑ (⊑ᶜ-id {Σ = Σ} {Φ = Φ} {A = A} wfA) h↑
    eqR = sym (cong (_+ size↑ˢ h↑) (size⊑ᶜ-id {Σ = Σ} {Φ = Φ} {A = A} wfA))

------------------------------------------------------------------------
-- Factorization theorem statements
------------------------------------------------------------------------

ν-store-⟰ᵗ :
  (Σ : Store) →
  ⟰ᵗ ((zero , ★) ∷ ⟰ˢ Σ) ≡ ((zero , ★) ∷ ⟰ˢ (⟰ᵗ Σ))
ν-store-⟰ᵗ Σ =
  cong₂ _∷_
    (cong₂ _,_ refl refl)
    (renameStoreᵗ-ext-⟰ˢ suc Σ)


renameStoreᵗ-cong :
  ∀ {ρ ρ′ : Renameᵗ}
  → ((X : TyVar) → ρ X ≡ ρ′ X)
  → (Σ : Store)
  → renameStoreᵗ ρ Σ ≡ renameStoreᵗ ρ′ Σ
renameStoreᵗ-cong h [] = refl
renameStoreᵗ-cong h ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (rename-cong h A))
    (renameStoreᵗ-cong h Σ)

closeVarAt-zero :
  (X : TyVar) →
  closeVarAt zero X ≡ suc X
closeVarAt-zero X = refl

renameStoreᵗ-closeVarAt-zero :
  (Σ : Store) →
  renameStoreᵗ (closeVarAt zero) Σ ≡ ⟰ᵗ Σ
renameStoreᵗ-closeVarAt-zero Σ = renameStoreᵗ-cong closeVarAt-zero Σ

closeInlineAt-⇑ˢ :
  (d : TyVar) (A : Ty) →
  closeInlineAt d (⇑ˢ A) ≡ renameᵗ (closeVarAt d) A
closeInlineAt-⇑ˢ d (＇ X) = refl
closeInlineAt-⇑ˢ d (｀ α) = refl
closeInlineAt-⇑ˢ d (‵ ι) = refl
closeInlineAt-⇑ˢ d ★ = refl
closeInlineAt-⇑ˢ d (A ⇒ B) =
  cong₂ _⇒_ (closeInlineAt-⇑ˢ d A) (closeInlineAt-⇑ˢ d B)
closeInlineAt-⇑ˢ d (`∀ A) =
  cong `∀
    (trans
      (substˢᵗ-cong
        (singleSealTyEnv-ext d)
        (renameᵗ (extᵗ (closeVarAt d)) (⇑ˢ A)))
      (trans
        (cong
          (substˢᵗ (singleSealTyEnv (＇ (suc d))))
          (sym (rename-cong (closeVarAt-ext d) (⇑ˢ A))))
        (trans
          (closeInlineAt-⇑ˢ (suc d) A)
          (rename-cong (closeVarAt-ext d) A))))

lookup-close-⟰ˢ :
  ∀ {Σ : Store}{α : Seal}{A : Ty}{d : TyVar}
  → ⟰ˢ Σ ∋ˢ suc α ⦂ A
  → renameStoreᵗ (closeVarAt d) Σ ∋ˢ α ⦂ closeInlineAt d A
lookup-close-⟰ˢ {Σ = []} ()
lookup-close-⟰ˢ {Σ = (β , B) ∷ Σ} {α = α} {A = A} {d = d} (Z∋ˢ α≡β A≡B′) =
  Z∋ˢ
    (suc-injective α≡β)
    (trans
      (cong (closeInlineAt d) A≡B′)
      (closeInlineAt-⇑ˢ d B))
lookup-close-⟰ˢ {Σ = (β , B) ∷ Σ} {d = d} (S∋ˢ h) =
  S∋ˢ (lookup-close-⟰ˢ {Σ = Σ} {d = d} h)

lookup-close-ν :
  ∀ {Σ : Store}{α : Seal}{A : Ty}{d : TyVar}
  → ((zero , ★) ∷ ⟰ˢ Σ) ∋ˢ suc α ⦂ A
  → renameStoreᵗ (closeVarAt d) Σ ∋ˢ α ⦂ closeInlineAt d A
lookup-close-ν (Z∋ˢ () _)
lookup-close-ν (S∋ˢ h) = lookup-close-⟰ˢ h

lookup-close-ν-cons :
  ∀ {Σ : Store}{α : Seal}{A T : Ty}{d : TyVar}
  → ((zero , T) ∷ ⟰ˢ Σ) ∋ˢ suc α ⦂ A
  → renameStoreᵗ (closeVarAt d) Σ ∋ˢ α ⦂ closeInlineAt d A
lookup-close-ν-cons (Z∋ˢ () _)
lookup-close-ν-cons (S∋ˢ h) = lookup-close-⟰ˢ h

renameStoreᵗ-closeVarAt-suc :
  (d : TyVar) (Σ : Store) →
  renameStoreᵗ (closeVarAt (suc d)) (⟰ᵗ Σ) ≡
  ⟰ᵗ (renameStoreᵗ (closeVarAt d) Σ)
renameStoreᵗ-closeVarAt-suc d Σ =
  trans
    (renameStoreᵗ-cong (closeVarAt-ext d) (⟰ᵗ Σ))
    (renameStoreᵗ-ext-⟰ᵗ (closeVarAt d) Σ)

ν★-store-⟰ᵗ :
  (Σ : Store) →
  ⟰ᵗ ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ≡ ((zero , ⇑ˢ ★) ∷ ⟰ˢ (⟰ᵗ Σ))
ν★-store-⟰ᵗ Σ = renameStoreᵗ-cons-⟰ˢ suc ★ Σ

raiseVarFrom-closeVarAt :
  (d X : TyVar) →
  raiseVarFrom d X ≡ closeVarAt d X
raiseVarFrom-closeVarAt zero X = refl
raiseVarFrom-closeVarAt (suc d) zero = refl
raiseVarFrom-closeVarAt (suc d) (suc X) = cong suc (raiseVarFrom-closeVarAt d X)

closeνSrc-inline-k :
  (d : TyVar) (C : Ty) →
  closeνSrc d C ≡ closeInlineAt d C
closeνSrc-inline-k d (＇ X) = cong ＇_ (raiseVarFrom-closeVarAt d X)
closeνSrc-inline-k d (｀ 0) = refl
closeνSrc-inline-k d (｀ (suc α)) = refl
closeνSrc-inline-k d (‵ ι) = refl
closeνSrc-inline-k d ★ = refl
closeνSrc-inline-k d (A ⇒ B) =
  cong₂ _⇒_ (closeνSrc-inline-k d A) (closeνSrc-inline-k d B)
closeνSrc-inline-k d (`∀ A) =
  cong `∀ (trans (closeνSrc-inline-k (suc d) A) (closeInlineAt-suc d A))

closeνSrc-inline :
  (C : Ty) →
  closeνSrc zero C ≡ (⇑ᵗ C) [ ＇ zero ]ˢᵗ
closeνSrc-inline C = trans (closeνSrc-inline-k zero C) (closeν-inline C)

mutual
  ↑ˢ-seal⇒var-helper :
    ∀ {Σ : Store}{Φ : List CastPerm}{B C : Ty}{d : TyVar}
    → ((zero , ★) ∷ ⟰ˢ Σ) ∣ cast-seal ∷ Φ ⊢ B ↑ˢ C
    → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d B ↑ˢ closeInlineAt d C
  ↑ˢ-seal⇒var-helper (↑ˢ-unseal {α = zero} h ())
  ↑ˢ-seal⇒var-helper {d = d} (↑ˢ-unseal {α = suc α} h (there-conv α∈Φ)) =
    ↑ˢ-unseal (lookup-close-ν {d = d} h) α∈Φ
  ↑ˢ-seal⇒var-helper (↑ˢ-⇒ p q) =
    ↑ˢ-⇒ (↓ˢ-seal⇒var-helper p) (↑ˢ-seal⇒var-helper q)
  ↑ˢ-seal⇒var-helper {Σ = Σ} {Φ = Φ} {d = d} (↑ˢ-∀ {A = B} {B = C} p)
    rewrite ν-store-⟰ᵗ Σ =
    subst
      (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d (`∀ B) ↑ˢ T)
      eqC
      (subst
        (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ T ↑ˢ `∀ (closeInlineAt (suc d) C))
        (sym eqB)
        (↑ˢ-∀
          (subst
            (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↑ˢ closeInlineAt (suc d) C)
            (renameStoreᵗ-closeVarAt-suc d Σ)
            (↑ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
    where
    eqB :
      closeInlineAt d (`∀ B) ≡ `∀ (closeInlineAt (suc d) B)
    eqB = cong `∀ (sym (closeInlineAt-suc d B))

    eqC :
      `∀ (closeInlineAt (suc d) C) ≡ closeInlineAt d (`∀ C)
    eqC = sym (cong `∀ (sym (closeInlineAt-suc d C)))
  ↑ˢ-seal⇒var-helper {d = d} (↑ˢ-id {A = A} wfA) =
    ↑ˢ-id (wfTySome (closeInlineAt d A))
  ↑ˢ-seal⇒var-helper (p ；↑ˢ q) =
    ↑ˢ-seal⇒var-helper p ；↑ˢ ↑ˢ-seal⇒var-helper q

  ↓ˢ-seal⇒var-helper :
    ∀ {Σ : Store}{Φ : List CastPerm}{B C : Ty}{d : TyVar}
    → ((zero , ★) ∷ ⟰ˢ Σ) ∣ cast-seal ∷ Φ ⊢ B ↓ˢ C
    → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d B ↓ˢ closeInlineAt d C
  ↓ˢ-seal⇒var-helper (↓ˢ-seal {α = zero} h ())
  ↓ˢ-seal⇒var-helper {d = d} (↓ˢ-seal {α = suc α} h (there-conv α∈Φ)) =
    ↓ˢ-seal (lookup-close-ν {d = d} h) α∈Φ
  ↓ˢ-seal⇒var-helper (↓ˢ-⇒ p q) =
    ↓ˢ-⇒ (↑ˢ-seal⇒var-helper p) (↓ˢ-seal⇒var-helper q)
  ↓ˢ-seal⇒var-helper {Σ = Σ} {Φ = Φ} {d = d} (↓ˢ-∀ {A = B} {B = C} p)
    rewrite ν-store-⟰ᵗ Σ =
    subst
      (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d (`∀ B) ↓ˢ T)
      eqC
      (subst
        (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ T ↓ˢ `∀ (closeInlineAt (suc d) C))
        (sym eqB)
        (↓ˢ-∀
          (subst
            (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↓ˢ closeInlineAt (suc d) C)
            (renameStoreᵗ-closeVarAt-suc d Σ)
            (↓ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
    where
    eqB :
      closeInlineAt d (`∀ B) ≡ `∀ (closeInlineAt (suc d) B)
    eqB = cong `∀ (sym (closeInlineAt-suc d B))

    eqC :
      `∀ (closeInlineAt (suc d) C) ≡ closeInlineAt d (`∀ C)
    eqC = sym (cong `∀ (sym (closeInlineAt-suc d C)))
  ↓ˢ-seal⇒var-helper {d = d} (↓ˢ-id {A = A} wfA) =
    ↓ˢ-id (wfTySome (closeInlineAt d A))
  ↓ˢ-seal⇒var-helper (p ；↓ˢ q) =
    ↓ˢ-seal⇒var-helper p ；↓ˢ ↓ˢ-seal⇒var-helper q

mutual
  ↑ˢ-tag⇒var-helper :
    ∀ {Σ : Store}{Φ : List CastPerm}{B C : Ty}{d : TyVar}
    → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ cast-tag ∷ Φ ⊢ B ↑ˢ C
    → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d B ↑ˢ closeInlineAt d C
  ↑ˢ-tag⇒var-helper (↑ˢ-unseal {α = zero} h ())
  ↑ˢ-tag⇒var-helper {d = d} (↑ˢ-unseal {α = suc α} h (there-conv α∈Φ)) =
    ↑ˢ-unseal (lookup-close-ν-cons {d = d} h) α∈Φ
  ↑ˢ-tag⇒var-helper (↑ˢ-⇒ p q) =
    ↑ˢ-⇒ (↓ˢ-tag⇒var-helper p) (↑ˢ-tag⇒var-helper q)
  ↑ˢ-tag⇒var-helper {Σ = Σ} {Φ = Φ} {d = d} (↑ˢ-∀ {A = B} {B = C} p)
    rewrite ν★-store-⟰ᵗ Σ =
    subst
      (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d (`∀ B) ↑ˢ T)
      eqC
      (subst
        (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ T ↑ˢ `∀ (closeInlineAt (suc d) C))
        (sym eqB)
        (↑ˢ-∀
          (subst
            (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↑ˢ closeInlineAt (suc d) C)
            (renameStoreᵗ-closeVarAt-suc d Σ)
            (↑ˢ-tag⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
    where
    eqB :
      closeInlineAt d (`∀ B) ≡ `∀ (closeInlineAt (suc d) B)
    eqB = cong `∀ (sym (closeInlineAt-suc d B))

    eqC :
      `∀ (closeInlineAt (suc d) C) ≡ closeInlineAt d (`∀ C)
    eqC = sym (cong `∀ (sym (closeInlineAt-suc d C)))
  ↑ˢ-tag⇒var-helper {d = d} (↑ˢ-id {A = A} wfA) =
    ↑ˢ-id (wfTySome (closeInlineAt d A))
  ↑ˢ-tag⇒var-helper (p ；↑ˢ q) =
    ↑ˢ-tag⇒var-helper p ；↑ˢ ↑ˢ-tag⇒var-helper q

  ↓ˢ-tag⇒var-helper :
    ∀ {Σ : Store}{Φ : List CastPerm}{B C : Ty}{d : TyVar}
    → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ cast-tag ∷ Φ ⊢ B ↓ˢ C
    → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d B ↓ˢ closeInlineAt d C
  ↓ˢ-tag⇒var-helper (↓ˢ-seal {α = zero} h ())
  ↓ˢ-tag⇒var-helper {d = d} (↓ˢ-seal {α = suc α} h (there-conv α∈Φ)) =
    ↓ˢ-seal (lookup-close-ν-cons {d = d} h) α∈Φ
  ↓ˢ-tag⇒var-helper (↓ˢ-⇒ p q) =
    ↓ˢ-⇒ (↑ˢ-tag⇒var-helper p) (↓ˢ-tag⇒var-helper q)
  ↓ˢ-tag⇒var-helper {Σ = Σ} {Φ = Φ} {d = d} (↓ˢ-∀ {A = B} {B = C} p)
    rewrite ν★-store-⟰ᵗ Σ =
    subst
      (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ closeInlineAt d (`∀ B) ↓ˢ T)
      eqC
      (subst
        (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ T ↓ˢ `∀ (closeInlineAt (suc d) C))
        (sym eqB)
        (↓ˢ-∀
          (subst
            (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↓ˢ closeInlineAt (suc d) C)
            (renameStoreᵗ-closeVarAt-suc d Σ)
            (↓ˢ-tag⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
    where
    eqB :
      closeInlineAt d (`∀ B) ≡ `∀ (closeInlineAt (suc d) B)
    eqB = cong `∀ (sym (closeInlineAt-suc d B))

    eqC :
      `∀ (closeInlineAt (suc d) C) ≡ closeInlineAt d (`∀ C)
    eqC = sym (cong `∀ (sym (closeInlineAt-suc d C)))
  ↓ˢ-tag⇒var-helper {d = d} (↓ˢ-id {A = A} wfA) =
    ↓ˢ-id (wfTySome (closeInlineAt d A))
  ↓ˢ-tag⇒var-helper (p ；↓ˢ q) =
    ↓ˢ-tag⇒var-helper p ；↓ˢ ↓ˢ-tag⇒var-helper q

{-
    Σ, α:=★ ∣ Φ, cs ⊢ A[α] ↑ˢ C[α]
    ------------------------------
    Σ       ∣ Φ     ⊢ A[X] ↑ˢ C[X]
-}
↑ˢ-seal⇒var :
  ∀ {Σ : Store}{Φ : List CastPerm}{A C : Ty}
  → ((zero , ★) ∷ ⟰ˢ Σ) ∣ cast-seal ∷ Φ ⊢ ((⇑ˢ A) [ α₀ ]ᵗ) ↑ˢ C
  → ⟰ᵗ Σ ∣ Φ ⊢ A ↑ˢ ((⇑ᵗ C) [ ＇ zero ]ˢᵗ)
↑ˢ-seal⇒var {Σ = Σ} {Φ = Φ} {A = A} {C = C} p =
  subst
    (λ T → ⟰ᵗ Σ ∣ Φ ⊢ A ↑ˢ T)
    (closeν-inline C)
    (subst
      (λ S → S ∣ Φ ⊢ A ↑ˢ closeInlineAt zero C)
      (renameStoreᵗ-closeVarAt-zero Σ)
      (subst
        (λ T → renameStoreᵗ (closeVarAt zero) Σ ∣ Φ ⊢ T ↑ˢ closeInlineAt zero C)
        (closeInline-open-at zero A)
        (↑ˢ-seal⇒var-helper
          (subst
            (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ↑ˢ C)
            (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A)))
            p))))

↓ˢ-tag⇒var :
  ∀ {Σ : Store}{Φ : List CastPerm}{A C : Ty}
  → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ cast-tag ∷ Φ ⊢ C ↓ˢ ((⇑ˢ A) [ α₀ ]ᵗ)
  → ⟰ᵗ Σ ∣ Φ ⊢ ((⇑ᵗ C) [ ＇ zero ]ˢᵗ) ↓ˢ A
↓ˢ-tag⇒var {Σ = Σ} {Φ = Φ} {A = A} {C = C} p =
  subst
    (λ T → ⟰ᵗ Σ ∣ Φ ⊢ T ↓ˢ A)
    (closeν-inline C)
    (subst
      (λ T → ⟰ᵗ Σ ∣ Φ ⊢ closeInlineAt zero C ↓ˢ T)
      (closeInlineAt-zero-open A)
      (subst
        (λ S → S ∣ Φ ⊢ closeInlineAt zero C ↓ˢ closeInlineAt zero ((⇑ˢ A) [ α₀ ]ᵗ))
        (renameStoreᵗ-closeVarAt-zero Σ)
        (↓ˢ-tag⇒var-helper p)))

mutual
  ↑ˢ-weaken-seal :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    → Σ ∣ Φ ⊢ A ↑ˢ B
    → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ ⇑ˢ A ↑ˢ ⇑ˢ B
  ↑ˢ-weaken-seal (↑ˢ-unseal {α = α} h α∈Φ) =
    ↑ˢ-unseal (S∋ˢ (renameLookupˢ suc h)) (there-conv α∈Φ)
  ↑ˢ-weaken-seal (↑ˢ-⇒ p q) = ↑ˢ-⇒ (↓ˢ-weaken-seal p) (↑ˢ-weaken-seal q)
  ↑ˢ-weaken-seal {Σ = Σ} {Φ = Φ} (↑ˢ-∀ {A = A} {B = B} p) =
    ↑ˢ-∀
      (subst
        (λ S → S ∣ (cast-seal ∷ Φ) ⊢ ⇑ˢ A ↑ˢ ⇑ˢ B)
        (sym (ν-store-⟰ᵗ Σ))
        (↑ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  ↑ˢ-weaken-seal (↑ˢ-id {A = A} wfA) = ↑ˢ-id (wfTySome (⇑ˢ A))
  ↑ˢ-weaken-seal (p ；↑ˢ q) = ↑ˢ-weaken-seal p ；↑ˢ ↑ˢ-weaken-seal q

  ↓ˢ-weaken-seal :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    → Σ ∣ Φ ⊢ A ↓ˢ B
    → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ ⇑ˢ A ↓ˢ ⇑ˢ B
  ↓ˢ-weaken-seal (↓ˢ-seal {α = α} h α∈Φ) =
    ↓ˢ-seal (S∋ˢ (renameLookupˢ suc h)) (there-conv α∈Φ)
  ↓ˢ-weaken-seal (↓ˢ-⇒ p q) = ↓ˢ-⇒ (↑ˢ-weaken-seal p) (↓ˢ-weaken-seal q)
  ↓ˢ-weaken-seal {Σ = Σ} {Φ = Φ} (↓ˢ-∀ {A = A} {B = B} p) =
    ↓ˢ-∀
      (subst
        (λ S → S ∣ (cast-seal ∷ Φ) ⊢ ⇑ˢ A ↓ˢ ⇑ˢ B)
        (sym (ν-store-⟰ᵗ Σ))
        (↓ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  ↓ˢ-weaken-seal (↓ˢ-id {A = A} wfA) = ↓ˢ-id (wfTySome (⇑ˢ A))
  ↓ˢ-weaken-seal (p ；↓ˢ q) = ↓ˢ-weaken-seal p ；↓ˢ ↓ˢ-weaken-seal q

mutual
  ↑ˢ-weaken-tag :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    → Σ ∣ Φ ⊢ A ↑ˢ B
    → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ↑ˢ ⇑ˢ B
  ↑ˢ-weaken-tag (↑ˢ-unseal {α = α} h α∈Φ) =
    ↑ˢ-unseal (S∋ˢ (renameLookupˢ suc h)) (there-conv α∈Φ)
  ↑ˢ-weaken-tag (↑ˢ-⇒ p q) = ↑ˢ-⇒ (↓ˢ-weaken-tag p) (↑ˢ-weaken-tag q)
  ↑ˢ-weaken-tag {Σ = Σ} {Φ = Φ} (↑ˢ-∀ {A = A} {B = B} p) =
    ↑ˢ-∀
      (subst
        (λ S → S ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ↑ˢ ⇑ˢ B)
        (sym (ν★-store-⟰ᵗ Σ))
        (↑ˢ-weaken-tag {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  ↑ˢ-weaken-tag (↑ˢ-id {A = A} wfA) = ↑ˢ-id (wfTySome (⇑ˢ A))
  ↑ˢ-weaken-tag (p ；↑ˢ q) = ↑ˢ-weaken-tag p ；↑ˢ ↑ˢ-weaken-tag q

  ↓ˢ-weaken-tag :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    → Σ ∣ Φ ⊢ A ↓ˢ B
    → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ↓ˢ ⇑ˢ B
  ↓ˢ-weaken-tag (↓ˢ-seal {α = α} h α∈Φ) =
    ↓ˢ-seal (S∋ˢ (renameLookupˢ suc h)) (there-conv α∈Φ)
  ↓ˢ-weaken-tag (↓ˢ-⇒ p q) = ↓ˢ-⇒ (↑ˢ-weaken-tag p) (↓ˢ-weaken-tag q)
  ↓ˢ-weaken-tag {Σ = Σ} {Φ = Φ} (↓ˢ-∀ {A = A} {B = B} p) =
    ↓ˢ-∀
      (subst
        (λ S → S ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ↓ˢ ⇑ˢ B)
        (sym (ν★-store-⟰ᵗ Σ))
        (↓ˢ-weaken-tag {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  ↓ˢ-weaken-tag (↓ˢ-id {A = A} wfA) = ↓ˢ-id (wfTySome (⇑ˢ A))
  ↓ˢ-weaken-tag (p ；↓ˢ q) = ↓ˢ-weaken-tag p ；↓ˢ ↓ˢ-weaken-tag q

mutual
  size↑ˢ-weaken-seal :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    (h↑ : Σ ∣ Φ ⊢ A ↑ˢ B)
    → size↑ˢ (↑ˢ-weaken-seal h↑) ≡ size↑ˢ h↑
  size↑ˢ-weaken-seal (↑ˢ-unseal h α∈Φ) = refl
  size↑ˢ-weaken-seal (↑ˢ-⇒ p q) =
    cong suc (cong₂ _+_ (size↓ˢ-weaken-seal p) (size↑ˢ-weaken-seal q))
  size↑ˢ-weaken-seal {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = `∀ B} (↑ˢ-∀ p) =
    cong
      suc
      (trans
        (size↑ˢ-subst-store
          (sym (ν-store-⟰ᵗ Σ))
          (↑ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
        (size↑ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  size↑ˢ-weaken-seal (↑ˢ-id wfA) = refl
  size↑ˢ-weaken-seal (p ；↑ˢ q) =
    cong suc (cong₂ _+_ (size↑ˢ-weaken-seal p) (size↑ˢ-weaken-seal q))

  size↓ˢ-weaken-seal :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B)
    → size↓ˢ (↓ˢ-weaken-seal h↓) ≡ size↓ˢ h↓
  size↓ˢ-weaken-seal (↓ˢ-seal h α∈Φ) = refl
  size↓ˢ-weaken-seal (↓ˢ-⇒ p q) =
    cong suc (cong₂ _+_ (size↑ˢ-weaken-seal p) (size↓ˢ-weaken-seal q))
  size↓ˢ-weaken-seal {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = `∀ B} (↓ˢ-∀ p) =
    cong
      suc
      (trans
        (size↓ˢ-subst-store
          (sym (ν-store-⟰ᵗ Σ))
          (↓ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
        (size↓ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  size↓ˢ-weaken-seal (↓ˢ-id wfA) = refl
  size↓ˢ-weaken-seal (p ；↓ˢ q) =
    cong suc (cong₂ _+_ (size↓ˢ-weaken-seal p) (size↓ˢ-weaken-seal q))

mutual
  size↑ˢ-weaken-tag :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    (h↑ : Σ ∣ Φ ⊢ A ↑ˢ B)
    → size↑ˢ (↑ˢ-weaken-tag h↑) ≡ size↑ˢ h↑
  size↑ˢ-weaken-tag (↑ˢ-unseal h α∈Φ) = refl
  size↑ˢ-weaken-tag (↑ˢ-⇒ p q) =
    cong suc (cong₂ _+_ (size↓ˢ-weaken-tag p) (size↑ˢ-weaken-tag q))
  size↑ˢ-weaken-tag {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = `∀ B} (↑ˢ-∀ p) =
    cong
      suc
      (trans
        (size↑ˢ-subst-store
          (sym (ν★-store-⟰ᵗ Σ))
          (↑ˢ-weaken-tag {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
        (size↑ˢ-weaken-tag {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  size↑ˢ-weaken-tag (↑ˢ-id wfA) = refl
  size↑ˢ-weaken-tag (p ；↑ˢ q) =
    cong suc (cong₂ _+_ (size↑ˢ-weaken-tag p) (size↑ˢ-weaken-tag q))

  size↓ˢ-weaken-tag :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B)
    → size↓ˢ (↓ˢ-weaken-tag h↓) ≡ size↓ˢ h↓
  size↓ˢ-weaken-tag (↓ˢ-seal h α∈Φ) = refl
  size↓ˢ-weaken-tag (↓ˢ-⇒ p q) =
    cong suc (cong₂ _+_ (size↑ˢ-weaken-tag p) (size↓ˢ-weaken-tag q))
  size↓ˢ-weaken-tag {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = `∀ B} (↓ˢ-∀ p) =
    cong
      suc
      (trans
        (size↓ˢ-subst-store
          (sym (ν★-store-⟰ᵗ Σ))
          (↓ˢ-weaken-tag {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
        (size↓ˢ-weaken-tag {Σ = ⟰ᵗ Σ} {Φ = Φ} p))
  size↓ˢ-weaken-tag (↓ˢ-id wfA) = refl
  size↓ˢ-weaken-tag (p ；↓ˢ q) =
    cong suc (cong₂ _+_ (size↓ˢ-weaken-tag p) (size↓ˢ-weaken-tag q))

mutual
  size↑ˢ-seal⇒var-helper :
    ∀ {Σ : Store}{Φ : List CastPerm}{B C : Ty}{d : TyVar}
    (p : ((zero , ★) ∷ ⟰ˢ Σ) ∣ cast-seal ∷ Φ ⊢ B ↑ˢ C)
    → size↑ˢ (↑ˢ-seal⇒var-helper {Σ = Σ} {Φ = Φ} {B = B} {C = C} {d = d} p) ≡ size↑ˢ p
  size↑ˢ-seal⇒var-helper (↑ˢ-unseal {α = zero} h ())
  size↑ˢ-seal⇒var-helper (↑ˢ-unseal {α = suc α} h (there-conv α∈Φ)) = refl
  size↑ˢ-seal⇒var-helper (↑ˢ-⇒ p q) =
    cong suc (cong₂ _+_ (size↓ˢ-seal⇒var-helper p) (size↑ˢ-seal⇒var-helper q))
  size↑ˢ-seal⇒var-helper {Σ = Σ} {Φ = Φ} {d = d} (↑ˢ-∀ {A = B} {B = C} p)
    rewrite ν-store-⟰ᵗ Σ =
    trans
      (size↑ˢ-subst-right
        (sym (cong `∀ (sym (closeInlineAt-suc d C))))
        (subst
          (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ T ↑ˢ `∀ (closeInlineAt (suc d) C))
          (sym (cong `∀ (sym (closeInlineAt-suc d B))))
          (↑ˢ-∀
            (subst
              (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↑ˢ closeInlineAt (suc d) C)
              (renameStoreᵗ-closeVarAt-suc d Σ)
              (↑ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p)))))
      (trans
        (size↑ˢ-subst-left
          (sym (cong `∀ (sym (closeInlineAt-suc d B))))
          (↑ˢ-∀
            (subst
              (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↑ˢ closeInlineAt (suc d) C)
              (renameStoreᵗ-closeVarAt-suc d Σ)
              (↑ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
        (cong
          suc
          (trans
            (size↑ˢ-subst-store
              (renameStoreᵗ-closeVarAt-suc d Σ)
              (↑ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))
            (size↑ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
  size↑ˢ-seal⇒var-helper (↑ˢ-id wfA) = refl
  size↑ˢ-seal⇒var-helper (p ；↑ˢ q) =
    cong suc (cong₂ _+_ (size↑ˢ-seal⇒var-helper p) (size↑ˢ-seal⇒var-helper q))

  size↓ˢ-seal⇒var-helper :
    ∀ {Σ : Store}{Φ : List CastPerm}{B C : Ty}{d : TyVar}
    (p : ((zero , ★) ∷ ⟰ˢ Σ) ∣ cast-seal ∷ Φ ⊢ B ↓ˢ C)
    → size↓ˢ (↓ˢ-seal⇒var-helper {Σ = Σ} {Φ = Φ} {B = B} {C = C} {d = d} p) ≡ size↓ˢ p
  size↓ˢ-seal⇒var-helper (↓ˢ-seal {α = zero} h ())
  size↓ˢ-seal⇒var-helper (↓ˢ-seal {α = suc α} h (there-conv α∈Φ)) = refl
  size↓ˢ-seal⇒var-helper (↓ˢ-⇒ p q) =
    cong suc (cong₂ _+_ (size↑ˢ-seal⇒var-helper p) (size↓ˢ-seal⇒var-helper q))
  size↓ˢ-seal⇒var-helper {Σ = Σ} {Φ = Φ} {d = d} (↓ˢ-∀ {A = B} {B = C} p)
    rewrite ν-store-⟰ᵗ Σ =
    trans
      (size↓ˢ-subst-right
        (sym (cong `∀ (sym (closeInlineAt-suc d C))))
        (subst
          (λ T → renameStoreᵗ (closeVarAt d) Σ ∣ Φ ⊢ T ↓ˢ `∀ (closeInlineAt (suc d) C))
          (sym (cong `∀ (sym (closeInlineAt-suc d B))))
          (↓ˢ-∀
            (subst
              (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↓ˢ closeInlineAt (suc d) C)
              (renameStoreᵗ-closeVarAt-suc d Σ)
              (↓ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p)))))
      (trans
        (size↓ˢ-subst-left
          (sym (cong `∀ (sym (closeInlineAt-suc d B))))
          (↓ˢ-∀
            (subst
              (λ S → S ∣ Φ ⊢ closeInlineAt (suc d) B ↓ˢ closeInlineAt (suc d) C)
              (renameStoreᵗ-closeVarAt-suc d Σ)
              (↓ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
        (cong
          suc
          (trans
            (size↓ˢ-subst-store
              (renameStoreᵗ-closeVarAt-suc d Σ)
              (↓ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))
            (size↓ˢ-seal⇒var-helper {Σ = ⟰ᵗ Σ} {Φ = Φ} {B = B} {C = C} {d = suc d} p))))
  size↓ˢ-seal⇒var-helper (↓ˢ-id wfA) = refl
  size↓ˢ-seal⇒var-helper (p ；↓ˢ q) =
    cong suc (cong₂ _+_ (size↓ˢ-seal⇒var-helper p) (size↓ˢ-seal⇒var-helper q))

size↑ˢ-seal⇒var :
  ∀ {Σ : Store}{Φ : List CastPerm}{A C : Ty}
  (p : ((zero , ★) ∷ ⟰ˢ Σ) ∣ cast-seal ∷ Φ ⊢ ((⇑ˢ A) [ α₀ ]ᵗ) ↑ˢ C)
  → size↑ˢ (↑ˢ-seal⇒var {Σ = Σ} {Φ = Φ} {A = A} {C = C} p) ≡ size↑ˢ p
size↑ˢ-seal⇒var {Σ = Σ} {Φ = Φ} {A = A} {C = C} p =
  trans
    (size↑ˢ-subst-right
      (closeν-inline C)
      (subst
        (λ S → S ∣ Φ ⊢ A ↑ˢ closeInlineAt zero C)
        (renameStoreᵗ-closeVarAt-zero Σ)
        (subst
          (λ T → renameStoreᵗ (closeVarAt zero) Σ ∣ Φ ⊢ T ↑ˢ closeInlineAt zero C)
          (closeInline-open-at zero A)
          (↑ˢ-seal⇒var-helper
            (subst
              (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ↑ˢ C)
              (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A)))
              p)))))
    (trans
      (size↑ˢ-subst-store
        (renameStoreᵗ-closeVarAt-zero Σ)
        (subst
          (λ T → renameStoreᵗ (closeVarAt zero) Σ ∣ Φ ⊢ T ↑ˢ closeInlineAt zero C)
          (closeInline-open-at zero A)
          (↑ˢ-seal⇒var-helper
            (subst
              (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ↑ˢ C)
              (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A)))
              p))))
      (trans
        (size↑ˢ-subst-left
          (closeInline-open-at zero A)
          (↑ˢ-seal⇒var-helper
            (subst
              (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ↑ˢ C)
              (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A)))
              p)))
        (trans
          (size↑ˢ-seal⇒var-helper
            (subst
              (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ↑ˢ C)
              (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A)))
              p))
          (size↑ˢ-subst-left
            (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A)))
            p))))

mutual
  -- Left-oriented cut: recurse on cast derivation (`⊑ᶜ`)
  record Cut⊑↑Result {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    (h⊑ : Σ ∣ Φ ⊢ A ⊑ᶜ B)
    (h↑ : Σ ∣ Φ ⊢ B ↑ˢ C) : Set where
    constructor mkCut⊑↑
    field
      D : Ty
      h↑′ : Σ ∣ Φ ⊢ A ↑ˢ D
      h⊑′ : Σ ∣ Φ ⊢ D ⊑ᶜ C
      budget↑≤ : size↑ˢ h↑′ ≤ cutSize⊑↑ h⊑ h↑
      budget⊑≤ : size⊑ᶜ h⊑′ ≤ cutSize⊑↑ h⊑ h↑
      budget≤ : size↑ˢ h↑′ + size⊑ᶜ h⊑′ ≤ cutSize⊑↑ h⊑ h↑

  record Cut↓⊒Result {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B)
    (h⊒ : Σ ∣ Φ ⊢ B ⊒ᶜ C) : Set where
    constructor mkCut↓⊒
    field
      D : Ty
      h⊒′ : Σ ∣ Φ ⊢ A ⊒ᶜ D
      h↓′ : Σ ∣ Φ ⊢ D ↓ˢ C
      budget⊒≤ : size⊒ᶜ h⊒′ ≤ cutSize↓⊒ h↓ h⊒
      budget↓≤ : size↓ˢ h↓′ ≤ cutSize↓⊒ h↓ h⊒
      budget≤ : size⊒ᶜ h⊒′ + size↓ˢ h↓′ ≤ cutSize↓⊒ h↓ h⊒

  mkCut⊑↑-sum :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C D : Ty}
    {h⊑ : Σ ∣ Φ ⊢ A ⊑ᶜ B}
    {h↑ : Σ ∣ Φ ⊢ B ↑ˢ C}
    → (h↑′ : Σ ∣ Φ ⊢ A ↑ˢ D)
    → (h⊑′ : Σ ∣ Φ ⊢ D ⊑ᶜ C)
    → size↑ˢ h↑′ + size⊑ᶜ h⊑′ ≤ cutSize⊑↑ h⊑ h↑
    → Cut⊑↑Result h⊑ h↑
  mkCut⊑↑-sum h↑′ h⊑′ hsum =
    mkCut⊑↑ _ h↑′ h⊑′ (m+n≤o⇒m≤o (size↑ˢ h↑′) hsum) (m+n≤o⇒n≤o (size↑ˢ h↑′) hsum) hsum

  mkCut↓⊒-sum :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C D : Ty}
    {h↓ : Σ ∣ Φ ⊢ A ↓ˢ B}
    {h⊒ : Σ ∣ Φ ⊢ B ⊒ᶜ C}
    → (h⊒′ : Σ ∣ Φ ⊢ A ⊒ᶜ D)
    → (h↓′ : Σ ∣ Φ ⊢ D ↓ˢ C)
    → size⊒ᶜ h⊒′ + size↓ˢ h↓′ ≤ cutSize↓⊒ h↓ h⊒
    → Cut↓⊒Result h↓ h⊒
  mkCut↓⊒-sum h⊒′ h↓′ hsum =
    mkCut↓⊒ _ h⊒′ h↓′ (m+n≤o⇒m≤o (size⊒ᶜ h⊒′) hsum) (m+n≤o⇒n≤o (size⊒ᶜ h⊒′) hsum) hsum

  -- One-axis cut proof by induction on explicit fuel.
  ⊑ᶜ⨾↑ˢ-fuel :
    (n : ℕ)
    → ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → (h⊑ : Σ ∣ Φ ⊢ A ⊑ᶜ B)
    → (h↑ : Σ ∣ Φ ⊢ B ↑ˢ C)
    → cutSize⊑↑ h⊑ h↑ < n
    → Cut⊑↑Result h⊑ h↑
  ⊑ᶜ⨾↑ˢ-fuel zero h⊑ h↑ ()
  ⊑ᶜ⨾↑ˢ-fuel (suc n) {C = C} (⊑ᶜ-id {A = A} wfA) h↑ hlt =
    mkCut⊑↑-sum
      h↑
      (⊑ᶜ-id (wfTySome C))
      (id-budget⊑↑ wfA h↑)
  ⊑ᶜ⨾↑ˢ-fuel (suc n) (p ；⊑ᶜ q) h↑ hlt with ⊑ᶜ⨾↑ˢ-fuel n q h↑ (drop-left-+-< (size⊑ᶜ p) (size⊑ᶜ q) (size↑ˢ h↑) n (<-suc-cancel hlt))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) (p ；⊑ᶜ q) h↑ hlt | r₁
    with ⊑ᶜ⨾↑ˢ-fuel n p (Cut⊑↑Result.h↑′ r₁)
           (≤-<-trans
             (+-monoʳ-≤
               (size⊑ᶜ p)
               (Cut⊑↑Result.budget↑≤ r₁))
             (subst
               (λ t → t < n)
               (+-assoc (size⊑ᶜ p) (size⊑ᶜ q) (size↑ˢ h↑))
               (<-suc-cancel hlt)))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) (p ；⊑ᶜ q) h↑ hlt | r₁ | r₂ =
    mkCut⊑↑-sum
      (Cut⊑↑Result.h↑′ r₂)
      ((Cut⊑↑Result.h⊑′ r₂) ；⊑ᶜ (Cut⊑↑Result.h⊑′ r₁))
      (compose-budget-left
        (size↑ˢ (Cut⊑↑Result.h↑′ r₂))
        (size⊑ᶜ (Cut⊑↑Result.h⊑′ r₂))
        (size⊑ᶜ (Cut⊑↑Result.h⊑′ r₁))
        (size↑ˢ (Cut⊑↑Result.h↑′ r₁))
        (size⊑ᶜ p)
        (size⊑ᶜ q)
        (size↑ˢ h↑)
        (Cut⊑↑Result.budget≤ r₂)
        (Cut⊑↑Result.budget≤ r₁))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) (⊑ᶜ-⇒ p q) (↑ˢ-⇒ q↓ q↑) hlt
    with ↓ˢ⨾⊒ᶜ-fuel n q↓ p
           (let
              hsum =
                drop-suc-right-<
                  (size⊒ᶜ p + size⊑ᶜ q)
                  (size↓ˢ q↓ + size↑ˢ q↑)
                  n
                  (<-suc-cancel hlt)
              hshuf =
                subst
                  (λ t → t < n)
                  (+-shuffle (size⊒ᶜ p) (size⊑ᶜ q) (size↓ˢ q↓) (size↑ˢ q↑))
                  hsum
              hshuf′ =
                subst
                  (λ t → t < n)
                  (cong (λ t → t + (size⊑ᶜ q + size↑ˢ q↑)) (+-comm (size⊒ᶜ p) (size↓ˢ q↓)))
                  hshuf
            in
              drop-right-+<
                (size↓ˢ q↓ + size⊒ᶜ p)
                (size⊑ᶜ q + size↑ˢ q↑)
                n
                hshuf′)
         | ⊑ᶜ⨾↑ˢ-fuel n q q↑
             (let
                hsum =
                  drop-suc-right-<
                    (size⊒ᶜ p + size⊑ᶜ q)
                    (size↓ˢ q↓ + size↑ˢ q↑)
                    n
                    (<-suc-cancel hlt)
                hshuf =
                  subst
                    (λ t → t < n)
                    (+-shuffle (size⊒ᶜ p) (size⊑ᶜ q) (size↓ˢ q↓) (size↑ˢ q↑))
                    hsum
                hshuf′ =
                  subst
                    (λ t → t < n)
                    (cong (λ t → t + (size⊑ᶜ q + size↑ˢ q↑)) (+-comm (size⊒ᶜ p) (size↓ˢ q↓)))
                    hshuf
              in
                drop-left-+<
                  (size↓ˢ q↓ + size⊒ᶜ p)
                  (size⊑ᶜ q + size↑ˢ q↑)
                  n
                  hshuf′)
  ⊑ᶜ⨾↑ˢ-fuel (suc n) (⊑ᶜ-⇒ p q) (↑ˢ-⇒ q↓ q↑) hlt | r↓ | r↑ =
    mkCut⊑↑-sum
      (↑ˢ-⇒ (Cut↓⊒Result.h↓′ r↓) (Cut⊑↑Result.h↑′ r↑))
      (⊑ᶜ-⇒ (Cut↓⊒Result.h⊒′ r↓) (Cut⊑↑Result.h⊑′ r↑))
      (arrow-budget-⊑↑
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r↓))
        (size↓ˢ (Cut↓⊒Result.h↓′ r↓))
        (size↑ˢ (Cut⊑↑Result.h↑′ r↑))
        (size⊑ᶜ (Cut⊑↑Result.h⊑′ r↑))
        (size↓ˢ q↓)
        (size⊒ᶜ p)
        (size⊑ᶜ q)
        (size↑ˢ q↑)
        (Cut↓⊒Result.budget≤ r↓)
        (Cut⊑↑Result.budget≤ r↑))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) (⊑ᶜ-∀ p) (↑ˢ-∀ q) hlt with ⊑ᶜ⨾↑ˢ-fuel n p q (drop-suc-right-< (size⊑ᶜ p) (size↑ˢ q) n (<-suc-cancel hlt))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) (⊑ᶜ-∀ p) (↑ˢ-∀ q) hlt | r =
    mkCut⊑↑-sum
      (↑ˢ-∀ (Cut⊑↑Result.h↑′ r))
      (⊑ᶜ-∀ (Cut⊑↑Result.h⊑′ r))
      (two-suc-+-mono
        (size↑ˢ (Cut⊑↑Result.h↑′ r))
        (size⊑ᶜ (Cut⊑↑Result.h⊑′ r))
        (size⊑ᶜ p)
        (size↑ˢ q)
        (Cut⊑↑Result.budget≤ r))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) {A = A} h⊑ (↑ˢ-id wfB) hlt =
    mkCut⊑↑-sum (↑ˢ-id (wfTySome A)) h⊑ (swap-+-≤ (suc zero) (size⊑ᶜ h⊑))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) h⊑ (h↑₁ ；↑ˢ h↑₂) hlt with ⊑ᶜ⨾↑ˢ-fuel n h⊑ h↑₁
    (let
       hsum =
         cancel-+-suc-<
           (size⊑ᶜ h⊑)
           (size↑ˢ h↑₁ + size↑ˢ h↑₂)
           n
           hlt
       hsum′ =
         subst
           (λ t → t < n)
           (sym (+-assoc (size⊑ᶜ h⊑) (size↑ˢ h↑₁) (size↑ˢ h↑₂)))
           hsum
     in
       drop-right-+<
         (size⊑ᶜ h⊑ + size↑ˢ h↑₁)
         (size↑ˢ h↑₂)
         n
         hsum′)
  ⊑ᶜ⨾↑ˢ-fuel (suc n) h⊑ (h↑₁ ；↑ˢ h↑₂) hlt | r₁
    with ⊑ᶜ⨾↑ˢ-fuel n (Cut⊑↑Result.h⊑′ r₁) h↑₂
           (≤-<-trans
             (+-monoˡ-≤
               (size↑ˢ h↑₂)
               (Cut⊑↑Result.budget⊑≤ r₁))
             (subst
               (λ t → t < n)
               (sym (+-assoc (size⊑ᶜ h⊑) (size↑ˢ h↑₁) (size↑ˢ h↑₂)))
               (cancel-+-suc-< (size⊑ᶜ h⊑) (size↑ˢ h↑₁ + size↑ˢ h↑₂) n hlt)))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) h⊑ (h↑₁ ；↑ˢ h↑₂) hlt | r₁ | r₂ =
    mkCut⊑↑-sum
      ((Cut⊑↑Result.h↑′ r₁) ；↑ˢ (Cut⊑↑Result.h↑′ r₂))
      (Cut⊑↑Result.h⊑′ r₂)
      (compose-budget-right
        (size↑ˢ (Cut⊑↑Result.h↑′ r₁))
        (size⊑ᶜ (Cut⊑↑Result.h⊑′ r₁))
        (size↑ˢ (Cut⊑↑Result.h↑′ r₂))
        (size⊑ᶜ (Cut⊑↑Result.h⊑′ r₂))
        (size⊑ᶜ h⊑)
        (size↑ˢ h↑₁)
        (size↑ˢ h↑₂)
        (Cut⊑↑Result.budget≤ r₁)
        (Cut⊑↑Result.budget≤ r₂))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = ｀ α} {C = C}
    (h⊑₀@(⊑ᶜ-ν h⊑)) (h↑₀@(↑ˢ-unseal h α∈Φ)) hlt
    with ⊑ᶜ⨾↑ˢ-fuel n h⊑
         (↑ˢ-unseal (S∋ˢ (renameLookupˢ suc h)) (there-conv α∈Φ))
         (<-suc-cancel hlt)
  ⊑ᶜ⨾↑ˢ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = ｀ α} {C = C}
    (h⊑₀@(⊑ᶜ-ν h⊑)) (h↑₀@(↑ˢ-unseal h α∈Φ)) hlt | r =
    mkCut⊑↑-sum
      (↑ˢ-∀ h↑ν)
      h⊑ν
      ν-budget
    where
    D : Ty
    D = Cut⊑↑Result.D r

    h↑′ : ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ ((⇑ˢ A) [ α₀ ]ᵗ) ↑ˢ D
    h↑′ = Cut⊑↑Result.h↑′ r

    h⊑′ : ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ D ⊑ᶜ ⇑ˢ C
    h⊑′ = Cut⊑↑Result.h⊑′ r

    h↑ν : ⟰ᵗ Σ ∣ Φ ⊢ A ↑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)
    h↑ν = ↑ˢ-seal⇒var {Σ = Σ} {Φ = Φ} {A = A} {C = D} h↑′

    eq-open :
      (⇑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ D
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline D)))
        (open-closeνSrc-id D)

    h⊑ν : Σ ∣ Φ ⊢ `∀ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ) ⊑ᶜ C
    h⊑ν =
      ⊑ᶜ-ν
        (subst
          (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ⊑ᶜ ⇑ˢ C)
          (sym eq-open)
          h⊑′)

    postulate
      ν-budget :
        size↑ˢ (↑ˢ-∀ h↑ν) + size⊑ᶜ h⊑ν ≤ cutSize⊑↑ h⊑₀ h↑₀


  ⊑ᶜ⨾↑ˢ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = B} {C = C}
    (h⊑₀@(⊑ᶜ-ν h⊑)) (h↑₀@(↑ˢ-⇒ q↓ q↑)) hlt
    with ⊑ᶜ⨾↑ˢ-fuel n h⊑
           (↑ˢ-⇒ (↓ˢ-weaken-seal q↓) (↑ˢ-weaken-seal q↑))
           (subst
             (λ m → m < n)
             (sym (cong (size⊑ᶜ h⊑ +_) (size↑ˢ-weaken-seal (↑ˢ-⇒ q↓ q↑))))
             (<-suc-cancel hlt))
  ⊑ᶜ⨾↑ˢ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = B} {C = C}
    (h⊑₀@(⊑ᶜ-ν h⊑)) (h↑₀@(↑ˢ-⇒ q↓ q↑)) hlt | r =
    mkCut⊑↑-sum
      (↑ˢ-∀ h↑ν)
      h⊑ν
      ν-budget
    where
    D : Ty
    D = Cut⊑↑Result.D r

    h↑′ : ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ ((⇑ˢ A) [ α₀ ]ᵗ) ↑ˢ D
    h↑′ = Cut⊑↑Result.h↑′ r

    h⊑′ : ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ D ⊑ᶜ ⇑ˢ C
    h⊑′ = Cut⊑↑Result.h⊑′ r

    h↑ν : ⟰ᵗ Σ ∣ Φ ⊢ A ↑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)
    h↑ν = ↑ˢ-seal⇒var {Σ = Σ} {Φ = Φ} {A = A} {C = D} h↑′

    eq-open :
      (⇑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ D
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline D)))
        (open-closeνSrc-id D)

    h⊑ν : Σ ∣ Φ ⊢ `∀ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ) ⊑ᶜ C
    h⊑ν =
      ⊑ᶜ-ν
        (subst
          (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ⊑ᶜ ⇑ˢ C)
          (sym eq-open)
          h⊑′)

    postulate
      ν-budget :
        size↑ˢ (↑ˢ-∀ h↑ν) + size⊑ᶜ h⊑ν ≤ cutSize⊑↑ h⊑₀ h↑₀

  ⊑ᶜ⨾↑ˢ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = `∀ B} {C = `∀ C}
    (h⊑₀@(⊑ᶜ-ν h⊑)) (h↑₀@(↑ˢ-∀ ↑q)) hlt
    with (let
           p↑ν =
             subst
               (λ S → S ∣ (cast-seal ∷ Φ) ⊢ ⇑ˢ B ↑ˢ ⇑ˢ C)
               (sym (ν-store-⟰ᵗ Σ))
               (↑ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} ↑q)
           h↑ν = ↑ˢ-∀ p↑ν
           size-h↑ν =
             cong
               suc
               (trans
                 (size↑ˢ-subst-store (sym (ν-store-⟰ᵗ Σ)) (↑ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} ↑q))
                 (size↑ˢ-weaken-seal {Σ = ⟰ᵗ Σ} {Φ = Φ} ↑q))
           hlt′ =
             subst
               (λ m → m < n)
               (sym (cong (size⊑ᶜ h⊑ +_) size-h↑ν))
               (<-suc-cancel hlt)
         in ⊑ᶜ⨾↑ˢ-fuel n h⊑ h↑ν hlt′)
  ⊑ᶜ⨾↑ˢ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = `∀ B} {C = `∀ C}
    (h⊑₀@(⊑ᶜ-ν h⊑)) (h↑₀@(↑ˢ-∀ ↑q)) hlt | r =
    mkCut⊑↑-sum
      (↑ˢ-∀ h↑ν)
      h⊑ν
      ν-budget
    where
    D : Ty
    D = Cut⊑↑Result.D r

    h↑′ : ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ ((⇑ˢ A) [ α₀ ]ᵗ) ↑ˢ D
    h↑′ = Cut⊑↑Result.h↑′ r

    h⊑′ : ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ D ⊑ᶜ ⇑ˢ (`∀ C)
    h⊑′ = Cut⊑↑Result.h⊑′ r

    h↑ν : ⟰ᵗ Σ ∣ Φ ⊢ A ↑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)
    h↑ν = ↑ˢ-seal⇒var {Σ = Σ} {Φ = Φ} {A = A} {C = D} h↑′

    eq-open :
      (⇑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ D
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline D)))
        (open-closeνSrc-id D)

    h⊑ν : Σ ∣ Φ ⊢ `∀ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ) ⊑ᶜ `∀ C
    h⊑ν =
      ⊑ᶜ-ν
        (subst
          (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ⊑ᶜ ⇑ˢ (`∀ C))
          (sym eq-open)
          h⊑′)

    postulate
      ν-budget :
        size↑ˢ (↑ˢ-∀ h↑ν) + size⊑ᶜ h⊑ν ≤ cutSize⊑↑ h⊑₀ h↑₀


  ↓ˢ⨾⊒ᶜ-fuel :
    (n : ℕ)
    → ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B)
    → (h⊒ : Σ ∣ Φ ⊢ B ⊒ᶜ C)
    → cutSize↓⊒ h↓ h⊒ < n
    → Cut↓⊒Result h↓ h⊒
  ↓ˢ⨾⊒ᶜ-fuel zero h↓ h⊒ ()
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-id {A = A} wfA) h⊒ hlt =
    mkCut↓⊒-sum h⊒ (↓ˢ-id (wfTySome _)) (swap-+-≤ (size⊒ᶜ h⊒) (suc zero))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (h↓₁ ；↓ˢ h↓₂) h⊒ hlt with ↓ˢ⨾⊒ᶜ-fuel n h↓₂ h⊒ (drop-left-+-< (size↓ˢ h↓₁) (size↓ˢ h↓₂) (size⊒ᶜ h⊒) n (<-suc-cancel hlt))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (h↓₁ ；↓ˢ h↓₂) h⊒ hlt | r₁
    with ↓ˢ⨾⊒ᶜ-fuel n h↓₁ (Cut↓⊒Result.h⊒′ r₁)
           (≤-<-trans
             (+-monoʳ-≤
               (size↓ˢ h↓₁)
               (Cut↓⊒Result.budget⊒≤ r₁))
             (subst
               (λ t → t < n)
               (+-assoc (size↓ˢ h↓₁) (size↓ˢ h↓₂) (size⊒ᶜ h⊒))
               (<-suc-cancel hlt)))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (h↓₁ ；↓ˢ h↓₂) h⊒ hlt | r₁ | r₂ =
    mkCut↓⊒-sum
      (Cut↓⊒Result.h⊒′ r₂)
      ((Cut↓⊒Result.h↓′ r₂) ；↓ˢ (Cut↓⊒Result.h↓′ r₁))
      (compose-budget-left
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₂))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₂))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₁))
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₁))
        (size↓ˢ h↓₁)
        (size↓ˢ h↓₂)
        (size⊒ᶜ h⊒)
        (Cut↓⊒Result.budget≤ r₂)
        (Cut↓⊒Result.budget≤ r₁))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-⇒ p q) (⊒ᶜ-⇒ r s) hlt
    with ⊑ᶜ⨾↑ˢ-fuel n r p
           (let
              hsum =
                drop-suc-right-<
                  (size↑ˢ p + size↓ˢ q)
                  (size⊑ᶜ r + size⊒ᶜ s)
                  n
                  (<-suc-cancel hlt)
              hshuf =
                subst
                  (λ t → t < n)
                  (+-shuffle (size↑ˢ p) (size↓ˢ q) (size⊑ᶜ r) (size⊒ᶜ s))
                  hsum
              hshuf′ =
                subst
                  (λ t → t < n)
                  (cong (λ t → t + (size↓ˢ q + size⊒ᶜ s)) (+-comm (size↑ˢ p) (size⊑ᶜ r)))
                  hshuf
            in
              drop-right-+<
                (size⊑ᶜ r + size↑ˢ p)
                (size↓ˢ q + size⊒ᶜ s)
                n
                hshuf′)
         | ↓ˢ⨾⊒ᶜ-fuel n q s
             (let
                hsum =
                  drop-suc-right-<
                    (size↑ˢ p + size↓ˢ q)
                    (size⊑ᶜ r + size⊒ᶜ s)
                    n
                    (<-suc-cancel hlt)
                hshuf =
                  subst
                    (λ t → t < n)
                    (+-shuffle (size↑ˢ p) (size↓ˢ q) (size⊑ᶜ r) (size⊒ᶜ s))
                    hsum
                hshuf′ =
                  subst
                    (λ t → t < n)
                    (cong (λ t → t + (size↓ˢ q + size⊒ᶜ s)) (+-comm (size↑ˢ p) (size⊑ᶜ r)))
                    hshuf
              in
                drop-left-+<
                  (size⊑ᶜ r + size↑ˢ p)
                  (size↓ˢ q + size⊒ᶜ s)
                  n
                  hshuf′)
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-⇒ p q) (⊒ᶜ-⇒ r s) hlt | r↑ | r↓ =
    mkCut↓⊒-sum
      (⊒ᶜ-⇒ (Cut⊑↑Result.h⊑′ r↑) (Cut↓⊒Result.h⊒′ r↓))
      (↓ˢ-⇒ (Cut⊑↑Result.h↑′ r↑) (Cut↓⊒Result.h↓′ r↓))
      (arrow-budget-↓⊒
        (size⊑ᶜ (Cut⊑↑Result.h⊑′ r↑))
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r↓))
        (size↑ˢ (Cut⊑↑Result.h↑′ r↑))
        (size↓ˢ (Cut↓⊒Result.h↓′ r↓))
        (size↑ˢ p)
        (size↓ˢ q)
        (size⊑ᶜ r)
        (size⊒ᶜ s)
        (Cut⊑↑Result.budget≤ r↑)
        (Cut↓⊒Result.budget≤ r↓))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-∀ p) (⊒ᶜ-∀ q) hlt with ↓ˢ⨾⊒ᶜ-fuel n p q (drop-suc-right-< (size↓ˢ p) (size⊒ᶜ q) n (<-suc-cancel hlt))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-∀ p) (⊒ᶜ-∀ q) hlt | r =
    mkCut↓⊒-sum
      (⊒ᶜ-∀ (Cut↓⊒Result.h⊒′ r))
      (↓ˢ-∀ (Cut↓⊒Result.h↓′ r))
      (two-suc-+-mono
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r))
        (size↓ˢ (Cut↓⊒Result.h↓′ r))
        (size↓ˢ p)
        (size⊒ᶜ q)
        (Cut↓⊒Result.budget≤ r))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = A} {B = ｀ α} {C = `∀ C}
    (h↓₀@(↓ˢ-seal h α∈Φ)) (h⊒₀@(⊒ᶜ-ν h⊒)) hlt
    with (let
           h↓ν : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ↓ˢ ⇑ˢ (｀ α)
           h↓ν = ↓ˢ-seal (S∋ˢ (renameLookupˢ suc h)) (there-conv α∈Φ)
         in ↓ˢ⨾⊒ᶜ-fuel n h↓ν h⊒ (<-suc-cancel hlt))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = A} {B = ｀ α} {C = `∀ C}
    (h↓₀@(↓ˢ-seal h α∈Φ)) (h⊒₀@(⊒ᶜ-ν h⊒)) hlt | r =
    mkCut↓⊒-sum
      h⊒ν
      h↓ν
      ν-budget
    where
    D : Ty
    D = Cut↓⊒Result.D r

    h⊒′ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ⊒ᶜ D
    h⊒′ = Cut↓⊒Result.h⊒′ r

    h↓′ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ D ↓ˢ ((⇑ˢ C) [ α₀ ]ᵗ)
    h↓′ = Cut↓⊒Result.h↓′ r

    eq-open :
      (⇑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ D
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline D)))
        (open-closeνSrc-id D)

    h⊒ν =
      ⊒ᶜ-ν
        (subst
          (λ T → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ⊒ᶜ T)
          (sym eq-open)
          h⊒′)

    h↓ν = ↓ˢ-∀ (↓ˢ-tag⇒var h↓′)

    postulate
      ν-budget :
        size⊒ᶜ h⊒ν + size↓ˢ h↓ν ≤ cutSize↓⊒ h↓₀ h⊒₀

  ↓ˢ⨾⊒ᶜ-fuel (suc n) {A = A} (↓ˢ-seal h α∈Φ) (⊒ᶜ-id wfB) hlt =
    mkCut↓⊒-sum (⊒ᶜ-id (wfTySome A)) (↓ˢ-seal h α∈Φ) (swap-+-≤ (suc zero) (size↓ˢ (↓ˢ-seal h α∈Φ)))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-seal h α∈Φ) (p ；⊒ᶜ q) hlt
    with ↓ˢ⨾⊒ᶜ-fuel n (↓ˢ-seal h α∈Φ) p
           (≤-<-trans (s≤s (m≤m+n (size⊒ᶜ p) (size⊒ᶜ q))) (<-suc-cancel hlt))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-seal h α∈Φ) (p ；⊒ᶜ q) hlt | r₁
    with ↓ˢ⨾⊒ᶜ-fuel n (Cut↓⊒Result.h↓′ r₁) q
           (≤-<-trans
             (+-monoˡ-≤
               (size⊒ᶜ q)
               (Cut↓⊒Result.budget↓≤ r₁))
             (subst
               (λ t → t < n)
               (+-assoc (size↓ˢ (↓ˢ-seal h α∈Φ)) (size⊒ᶜ p) (size⊒ᶜ q))
               (<-suc-cancel hlt)))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-seal h α∈Φ) (p ；⊒ᶜ q) hlt | r₁ | r₂ =
    mkCut↓⊒-sum
      ((Cut↓⊒Result.h⊒′ r₁) ；⊒ᶜ (Cut↓⊒Result.h⊒′ r₂))
      (Cut↓⊒Result.h↓′ r₂)
      (compose-budget-right
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₁))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₁))
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₂))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₂))
        (size↓ˢ (↓ˢ-seal h α∈Φ))
        (size⊒ᶜ p)
        (size⊒ᶜ q)
        (Cut↓⊒Result.budget≤ r₁)
        (Cut↓⊒Result.budget≤ r₂))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = A} {B = B} {C = `∀ C}
    (h↓₀@(↓ˢ-⇒ p q)) (h⊒₀@(⊒ᶜ-ν h⊒)) hlt
    with ↓ˢ⨾⊒ᶜ-fuel n (↓ˢ-weaken-tag (↓ˢ-⇒ p q)) h⊒
           (subst
             (λ m → m < n)
             (sym (cong (λ t → t + size⊒ᶜ h⊒) (size↓ˢ-weaken-tag (↓ˢ-⇒ p q))))
             (swap-suc-sides-+< (size↑ˢ p + size↓ˢ q) (size⊒ᶜ h⊒) n (<-suc-cancel hlt)))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = A} {B = B} {C = `∀ C}
    (h↓₀@(↓ˢ-⇒ p q)) (h⊒₀@(⊒ᶜ-ν h⊒)) hlt | r =
    mkCut↓⊒-sum
      h⊒ν
      h↓ν
      ν-budget
    where
    D : Ty
    D = Cut↓⊒Result.D r

    h⊒′ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ⊒ᶜ D
    h⊒′ = Cut↓⊒Result.h⊒′ r

    h↓′ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ D ↓ˢ ((⇑ˢ C) [ α₀ ]ᵗ)
    h↓′ = Cut↓⊒Result.h↓′ r

    eq-open :
      (⇑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ D
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline D)))
        (open-closeνSrc-id D)

    h⊒ν =
      ⊒ᶜ-ν
        (subst
          (λ T → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ⊒ᶜ T)
          (sym eq-open)
          h⊒′)

    h↓ν = ↓ˢ-∀ (↓ˢ-tag⇒var h↓′)

    postulate
      ν-budget :
        size⊒ᶜ h⊒ν + size↓ˢ h↓ν ≤ cutSize↓⊒ h↓₀ h⊒₀

  ↓ˢ⨾⊒ᶜ-fuel (suc n) {A = A} (↓ˢ-⇒ p q) (⊒ᶜ-id wfB) hlt =
    mkCut↓⊒-sum (⊒ᶜ-id (wfTySome A)) (↓ˢ-⇒ p q) (swap-+-≤ (suc zero) (size↓ˢ (↓ˢ-⇒ p q)))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-⇒ p q) (r ；⊒ᶜ s) hlt
    with ↓ˢ⨾⊒ᶜ-fuel n (↓ˢ-⇒ p q) r
           (let
              hsum =
                swap-suc-sides-+<
                  (size↑ˢ p + size↓ˢ q)
                  (size⊒ᶜ r + size⊒ᶜ s)
                  n
                  (<-suc-cancel hlt)
              hsum′ =
                subst
                  (λ t → t < n)
                  (sym (+-assoc (suc (size↑ˢ p + size↓ˢ q)) (size⊒ᶜ r) (size⊒ᶜ s)))
                  hsum
            in
              drop-right-+<
                (suc (size↑ˢ p + size↓ˢ q) + size⊒ᶜ r)
                (size⊒ᶜ s)
                n
                hsum′)
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-⇒ p q) (r ；⊒ᶜ s) hlt | r₁
    with ↓ˢ⨾⊒ᶜ-fuel n (Cut↓⊒Result.h↓′ r₁) s
           (≤-<-trans
             (+-monoˡ-≤
               (size⊒ᶜ s)
               (Cut↓⊒Result.budget↓≤ r₁))
             (let
                hsum =
                  swap-suc-sides-+<
                    (size↑ˢ p + size↓ˢ q)
                    (size⊒ᶜ r + size⊒ᶜ s)
                    n
                    (<-suc-cancel hlt)
              in
                subst
                  (λ t → t < n)
                  (sym (+-assoc (suc (size↑ˢ p + size↓ˢ q)) (size⊒ᶜ r) (size⊒ᶜ s)))
                  hsum))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-⇒ p q) (r ；⊒ᶜ s) hlt | r₁ | r₂ =
    mkCut↓⊒-sum
      ((Cut↓⊒Result.h⊒′ r₁) ；⊒ᶜ (Cut↓⊒Result.h⊒′ r₂))
      (Cut↓⊒Result.h↓′ r₂)
      (compose-budget-right
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₁))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₁))
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₂))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₂))
        (size↓ˢ (↓ˢ-⇒ p q))
        (size⊒ᶜ r)
        (size⊒ᶜ s)
        (Cut↓⊒Result.budget≤ r₁)
        (Cut↓⊒Result.budget≤ r₂))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = A} {B = B} {C = `∀ C}
    (h↓₀@(↓ˢ-∀ p)) (h⊒₀@(⊒ᶜ-ν h⊒)) hlt
    with ↓ˢ⨾⊒ᶜ-fuel n (↓ˢ-weaken-tag (↓ˢ-∀ p)) h⊒
           (subst
             (λ m → m < n)
             (sym (cong (λ t → t + size⊒ᶜ h⊒) (size↓ˢ-weaken-tag (↓ˢ-∀ p))))
             (swap-suc-sides-+< (size↓ˢ p) (size⊒ᶜ h⊒) n (<-suc-cancel hlt)))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) {Σ = Σ} {Φ = Φ} {A = A} {B = B} {C = `∀ C}
    (h↓₀@(↓ˢ-∀ p)) (h⊒₀@(⊒ᶜ-ν h⊒)) hlt | r =
    mkCut↓⊒-sum
      h⊒ν
      h↓ν
      ν-budget
    where
    D : Ty
    D = Cut↓⊒Result.D r

    h⊒′ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ⊒ᶜ D
    h⊒′ = Cut↓⊒Result.h⊒′ r

    h↓′ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ D ↓ˢ ((⇑ˢ C) [ α₀ ]ᵗ)
    h↓′ = Cut↓⊒Result.h↓′ r

    eq-open :
      (⇑ˢ ((⇑ᵗ D) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ D
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline D)))
        (open-closeνSrc-id D)

    h⊒ν =
      ⊒ᶜ-ν
        (subst
          (λ T → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ A ⊒ᶜ T)
          (sym eq-open)
          h⊒′)

    h↓ν = ↓ˢ-∀ (↓ˢ-tag⇒var h↓′)

    postulate
      ν-budget :
        size⊒ᶜ h⊒ν + size↓ˢ h↓ν ≤ cutSize↓⊒ h↓₀ h⊒₀

  ↓ˢ⨾⊒ᶜ-fuel (suc n) {A = A} (↓ˢ-∀ p) (⊒ᶜ-id wfB) hlt =
    mkCut↓⊒-sum (⊒ᶜ-id (wfTySome A)) (↓ˢ-∀ p) (swap-+-≤ (suc zero) (size↓ˢ (↓ˢ-∀ p)))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-∀ p) (r ；⊒ᶜ s) hlt
    with ↓ˢ⨾⊒ᶜ-fuel n (↓ˢ-∀ p) r
           (let
              hsum =
                swap-suc-sides-+<
                  (size↓ˢ p)
                  (size⊒ᶜ r + size⊒ᶜ s)
                  n
                  (<-suc-cancel hlt)
              hsum′ =
                subst
                  (λ t → t < n)
                  (sym (+-assoc (suc (size↓ˢ p)) (size⊒ᶜ r) (size⊒ᶜ s)))
                  hsum
            in
              drop-right-+<
                (suc (size↓ˢ p) + size⊒ᶜ r)
                (size⊒ᶜ s)
                n
                hsum′)
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-∀ p) (r ；⊒ᶜ s) hlt | r₁
    with ↓ˢ⨾⊒ᶜ-fuel n (Cut↓⊒Result.h↓′ r₁) s
           (≤-<-trans
             (+-monoˡ-≤
               (size⊒ᶜ s)
               (Cut↓⊒Result.budget↓≤ r₁))
             (let
                hsum =
                  swap-suc-sides-+<
                    (size↓ˢ p)
                    (size⊒ᶜ r + size⊒ᶜ s)
                    n
                    (<-suc-cancel hlt)
              in
                subst
                  (λ t → t < n)
                  (sym (+-assoc (suc (size↓ˢ p)) (size⊒ᶜ r) (size⊒ᶜ s)))
                  hsum))
  ↓ˢ⨾⊒ᶜ-fuel (suc n) (↓ˢ-∀ p) (r ；⊒ᶜ s) hlt | r₁ | r₂ =
    mkCut↓⊒-sum
      ((Cut↓⊒Result.h⊒′ r₁) ；⊒ᶜ (Cut↓⊒Result.h⊒′ r₂))
      (Cut↓⊒Result.h↓′ r₂)
      (compose-budget-right
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₁))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₁))
        (size⊒ᶜ (Cut↓⊒Result.h⊒′ r₂))
        (size↓ˢ (Cut↓⊒Result.h↓′ r₂))
        (size↓ˢ (↓ˢ-∀ p))
        (size⊒ᶜ r)
        (size⊒ᶜ s)
        (Cut↓⊒Result.budget≤ r₁)
        (Cut↓⊒Result.budget≤ r₂))

⊑ᶜ⨾↑ˢ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
  → Σ ∣ Φ ⊢ A ⊑ᶜ B
  → Σ ∣ Φ ⊢ B ↑ˢ C
  → ∃[ D ] (Σ ∣ Φ ⊢ A ↑ˢ D) × (Σ ∣ Φ ⊢ D ⊑ᶜ C)
⊑ᶜ⨾↑ˢ p h↑ with ⊑ᶜ⨾↑ˢ-fuel (suc (cutSize⊑↑ p h↑)) p h↑ (n<1+n (cutSize⊑↑ p h↑))
⊑ᶜ⨾↑ˢ p h↑ | r = Cut⊑↑Result.D r , (Cut⊑↑Result.h↑′ r , Cut⊑↑Result.h⊑′ r)

↓ˢ⨾⊒ᶜ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
  → Σ ∣ Φ ⊢ A ↓ˢ B
  → Σ ∣ Φ ⊢ B ⊒ᶜ C
  → ∃[ D ] (Σ ∣ Φ ⊢ A ⊒ᶜ D) × (Σ ∣ Φ ⊢ D ↓ˢ C)
↓ˢ⨾⊒ᶜ h↓ h⊒ with ↓ˢ⨾⊒ᶜ-fuel (suc (cutSize↓⊒ h↓ h⊒)) h↓ h⊒ (n<1+n (cutSize↓⊒ h↓ h⊒))
↓ˢ⨾⊒ᶜ h↓ h⊒ | r = Cut↓⊒Result.D r , (Cut↓⊒Result.h⊒′ r , Cut↓⊒Result.h↓′ r)

mutual
  wt⊑-factor :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up}
    → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
    → ∃[ C ] (Σ ∣ Φ ⊢ A ↑ˢ C) × (Σ ∣ Φ ⊢ C ⊑ᶜ B)
  wt⊑-factor {A = G} (wt-tag g ok) =
    G , (↑ˢ-id (wfTySome G) , ⊑ᶜ-tag g ok)
  wt⊑-factor (wt-unseal {A = A} hα α∈Φ) =
    A , (↑ˢ-unseal hα α∈Φ , ⊑ᶜ-id (wfTySome A))
  wt⊑-factor (wt-unseal★ {α = α} hα α∈Φ) =
    ｀ α , (↑ˢ-id (wfTySome (｀ α)) , ⊑ᶜ-unseal★ hα α∈Φ)
  wt⊑-factor (wt-↦ p q) with wt⊒-factor p | wt⊑-factor q
  wt⊑-factor (wt-↦ p q) | C , (h↓ , h⊒) | D , (h↑ , h⊑) = C ⇒ D , ↑ˢ-⇒ h⊒ h↑ , ⊑ᶜ-⇒ h↓ h⊑
  wt⊑-factor (wt-∀ p) with wt⊑-factor p
  wt⊑-factor (wt-∀ p) | C , (h↑ , h⊑) =
    `∀ C , (↑ˢ-∀ h↑ , ⊑ᶜ-∀ h⊑)
    
  {- Case
     wt-p: Σ, α:=★ ∣ Φ, cs ⊢  p[α]  : A[α] ⊑ B
           -----------------------------------
           Σ ∣ Φ ⊢  να.p[α]  : ∀X.A[X] ⊑ B
  -}
  wt⊑-factor {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = B} (wt-ν wt-p) with wt⊑-factor wt-p
  wt⊑-factor {Σ = Σ} {Φ = Φ} {A = `∀ A} {B = B} (wt-ν wt-p) | C , (IH↑ , IH⊑) =
    {-
    IH↑   : Σ, α:=★ ∣ Φ, cs ⊢ A[α] ↑ˢ C[α]   (alpha can only shows up in id)
       (convert cast-seal α to X)
    nts     Σ ∣ Φ ⊢ A[X] ↑ˢ C[X]    by ↑ˢ-seal⇒var

    IH⊑   : Σ, α:=★ ∣ Φ, cs ⊢ C[X] ⊑ᶜ B
       (convert X to α)
    nts     Σ, α:=★ ∣ Φ, cs ⊢ C[α] ⊑ᶜ B

     C = C[α], A = A[X]
    -}
    `∀ ((⇑ᵗ C) [ ＇ zero ]ˢᵗ) ,
    ↑ˢ-∀ (↑ˢ-seal⇒var IH↑) ,
    ⊑ᶜ-ν
      (subst
        (λ T → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ T ⊑ᶜ ⇑ˢ B)
        (sym eq-open)
        IH⊑)
    where
    eq-open :
      (⇑ˢ ((⇑ᵗ C) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ C
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline C)))
        (open-closeνSrc-id C)
  wt⊑-factor {A = A} (wt-id wfA) =
    A , (↑ˢ-id wfA , ⊑ᶜ-id wfA)
  wt⊑-factor (wt-； p q) with wt⊑-factor p | wt⊑-factor q
  wt⊑-factor (wt-； p q) | C₁ , (h↑₁ , h⊑₁) | C₂ , (h↑₂ , h⊑₂)
    with ⊑ᶜ⨾↑ˢ h⊑₁ h↑₂
  wt⊑-factor (wt-； p q) | C₁ , (h↑₁ , h⊑₁) | C₂ , (h↑₂ , h⊑₂) | C₃ , (h↑₁₂ , h⊑₁₂) =
    C₃ , (h↑₁ ；↑ˢ h↑₁₂ , h⊑₁₂ ；⊑ᶜ h⊑₂)

  wt⊒-factor :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down}
    → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
    → ∃[ C ] (Σ ∣ Φ ⊢ A ⊒ᶜ C) × (Σ ∣ Φ ⊢ C ↓ˢ B)
  wt⊒-factor (wt-untag {G = G} g ok ℓ) =
    G , (⊒ᶜ-untag g ok ℓ , ↓ˢ-id (wfTySome G))
  wt⊒-factor (wt-seal {α = α} {A = A} hα α∈Φ) =
    A , (⊒ᶜ-id (wfTySome A) , ↓ˢ-seal hα α∈Φ)
  wt⊒-factor (wt-seal★ {α = α} hα α∈Φ) =
    ｀ α , (⊒ᶜ-seal★ hα α∈Φ , ↓ˢ-id (wfTySome (｀ α)))
  wt⊒-factor (wt-↦ p q) with wt⊑-factor p | wt⊒-factor q
  wt⊒-factor (wt-↦ p q) | C₁ , (h↑ , h⊑) | C₂ , (h↓ , h⊒) = C₁ ⇒ C₂ , ⊒ᶜ-⇒ h⊑ h↓ , ↓ˢ-⇒ h↑ h⊒
  wt⊒-factor (wt-∀ p) with wt⊒-factor p
  wt⊒-factor (wt-∀ p) | C , (h⊒ , h↓) =
    `∀ C , (⊒ᶜ-∀ h⊒ , ↓ˢ-∀ h↓)
  wt⊒-factor {Σ = Σ} {Φ = Φ} {A = B} {B = `∀ A} (wt-ν p) with wt⊒-factor p
  wt⊒-factor {Σ = Σ} {Φ = Φ} {A = B} {B = `∀ A} (wt-ν p) | C , (h⊒ , h↓) =
    `∀ ((⇑ᵗ C) [ ＇ zero ]ˢᵗ) ,
    ⊒ᶜ-ν
      (subst
        (λ T → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ B ⊒ᶜ T)
        (sym eq-open)
        h⊒) ,
    ↓ˢ-∀ (↓ˢ-tag⇒var h↓)
    where
    eq-open :
      (⇑ˢ ((⇑ᵗ C) [ ＇ zero ]ˢᵗ)) [ α₀ ]ᵗ ≡ C
    eq-open =
      trans
        (cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) (sym (closeνSrc-inline C)))
        (open-closeνSrc-id C)
  wt⊒-factor {A = A} (wt-id wfA) =
    A , (⊒ᶜ-id wfA , ↓ˢ-id wfA)
  wt⊒-factor (wt-； p q) with wt⊒-factor p | wt⊒-factor q
  wt⊒-factor (wt-； p q) | C₁ , (h⊒₁ , h↓₁) | C₂ , (h⊒₂ , h↓₂)
    with ↓ˢ⨾⊒ᶜ h↓₁ h⊒₂
  wt⊒-factor (wt-； p q) | C₁ , (h⊒₁ , h↓₁) | C₂ , (h⊒₂ , h↓₂) | C₃ , (h⊒₁₂ , h↓₁₂) =
    C₃ , (h⊒₁ ；⊒ᶜ h⊒₁₂ , h↓₁₂ ；↓ˢ h↓₂)
