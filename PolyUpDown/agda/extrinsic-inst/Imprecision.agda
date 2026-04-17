module Imprecision where

-- File Charter:
--   * Store-free type imprecision for extrinsic-inst PolyUpDown.
--   * Defines unindexed imprecision evidence over `Ty` (and dual direction).
--   * This relation is intended to align with `Cast` (not full `UpDown`
--   * cast typing).

open import Types
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; s≤s⁻¹)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-suc; +-mono-≤; m≤m+n; m≤n+m; n≤1+n)
open import TypeProperties
  using (renameˢ-ground ; substᵗ-ground ; renameˢ-ext-⇑ˢ;
         renameˢ-ν-src ; substᵗ-⇑ˢ ; substᵗ-ν-src ; liftSubstˢ)

------------------------------------------------------------------------
-- Type imprecision
------------------------------------------------------------------------

infix 4 _⊑_ _⊒_

data _⊑_ : Ty → Ty → Set where
  ⊑-★★ : ★ ⊑ ★
  ⊑-★ : ∀ {A G} → Ground G → A ⊑ G → A ⊑ ★
  ⊑-＇ : ∀ {X} → ＇ X ⊑ ＇ X
  ⊑-｀ : ∀ {α} → ｀ α ⊑ ｀ α
  ⊑-‵ : ∀ {ι} → ‵ ι ⊑ ‵ ι
  ⊑-⇒ : ∀ {A A′ B B′}
    → A ⊑ A′
    → B ⊑ B′
    → (A ⇒ B) ⊑ (A′ ⇒ B′)
  ⊑-∀ : ∀ {A B}
    → A ⊑ B
    → (`∀ A) ⊑ (`∀ B)
  ⊑-ν : ∀ {A B}
    → ((⇑ˢ A) [ α₀ ]ᵗ) ⊑ ⇑ˢ B
    → (`∀ A) ⊑ B

_⊒_ : Ty → Ty → Set
B ⊒ A = A ⊑ B

⊑-refl : ∀ {A} → A ⊑ A
⊑-refl {＇ X} = ⊑-＇
⊑-refl {｀ α} = ⊑-｀
⊑-refl {‵ ι} = ⊑-‵
⊑-refl {★} = ⊑-★★
⊑-refl {A ⇒ B} = ⊑-⇒ ⊑-refl ⊑-refl
⊑-refl {`∀ A} = ⊑-∀ ⊑-refl

⊒-refl : ∀ {A} → A ⊒ A
⊒-refl = ⊑-refl 

cast-⊑ :
  ∀ {A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  A ⊑ B →
  A′ ⊑ B′
cast-⊑ refl refl p = p

------------------------------------------------------------------------
-- Seal substitution for imprecision
------------------------------------------------------------------------

mutual
  renameˢ-⊑ :
    (ρ : Renameˢ) →
    ∀ {A B} →
    A ⊑ B →
    renameˢ ρ A ⊑ renameˢ ρ B
  renameˢ-⊑ ρ ⊑-★★ = ⊑-★★
  renameˢ-⊑ ρ (⊑-★ g p) =
    ⊑-★ (renameˢ-ground ρ g) (renameˢ-⊑ ρ p)
  renameˢ-⊑ ρ ⊑-＇ = ⊑-＇
  renameˢ-⊑ ρ ⊑-｀ = ⊑-｀
  renameˢ-⊑ ρ ⊑-‵ = ⊑-‵
  renameˢ-⊑ ρ (⊑-⇒ p q) =
    ⊑-⇒ (renameˢ-⊑ ρ p) (renameˢ-⊑ ρ q)
  renameˢ-⊑ ρ (⊑-∀ p) = ⊑-∀ (renameˢ-⊑ ρ p)
  renameˢ-⊑ ρ (⊑-ν {A = A} {B = B} p) =
    ⊑-ν
      (cast-⊑
        (renameˢ-ν-src ρ A)
        (renameˢ-ext-⇑ˢ ρ B)
        (renameˢ-⊑ (extˢ ρ) p))

  substᵗ-⊑ :
    (σ : Substᵗ) →
    ∀ {A B} →
    A ⊑ B →
    substᵗ σ A ⊑ substᵗ σ B
  substᵗ-⊑ σ ⊑-★★ = ⊑-★★
  substᵗ-⊑ σ (⊑-★ g p) =
    ⊑-★ (substᵗ-ground σ g) (substᵗ-⊑ σ p)
  substᵗ-⊑ σ ⊑-＇ = ⊑-refl
  substᵗ-⊑ σ ⊑-｀ = ⊑-｀
  substᵗ-⊑ σ ⊑-‵ = ⊑-‵
  substᵗ-⊑ σ (⊑-⇒ p q) =
    ⊑-⇒ (substᵗ-⊑ σ p) (substᵗ-⊑ σ q)
  substᵗ-⊑ σ (⊑-∀ p) = ⊑-∀ (substᵗ-⊑ (extsᵗ σ) p)
  substᵗ-⊑ σ (⊑-ν {A = A} {B = B} p) =
    ⊑-ν
      (cast-⊑
        (substᵗ-ν-src σ A)
        (substᵗ-⇑ˢ σ B)
        (substᵗ-⊑ (liftSubstˢ σ) p))

------------------------------------------------------------------------
-- Proof of transitivity
------------------------------------------------------------------------

size⊑ : ∀ {A B} → A ⊑ B → ℕ
size⊑ ⊑-★★ = zero
size⊑ (⊑-★ g p) = suc (size⊑ p)
size⊑ ⊑-＇ = zero
size⊑ ⊑-｀ = zero
size⊑ ⊑-‵ = zero
size⊑ (⊑-⇒ p q) = suc (size⊑ p + size⊑ q)
size⊑ (⊑-∀ p) = suc (size⊑ p)
size⊑ (⊑-ν p) = suc (size⊑ p)

size-cast-⊑ :
  ∀ {A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (p : A ⊑ B) →
  size⊑ (cast-⊑ eqA eqB p) ≡ size⊑ p
size-cast-⊑ refl refl p = refl

size-renameˢ-⊑ :
  (ρ : Renameˢ) →
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (renameˢ-⊑ ρ p) ≡ size⊑ p
size-renameˢ-⊑ ρ ⊑-★★ = refl
size-renameˢ-⊑ ρ (⊑-★ g p) = cong suc (size-renameˢ-⊑ ρ p)
size-renameˢ-⊑ ρ ⊑-＇ = refl
size-renameˢ-⊑ ρ ⊑-｀ = refl
size-renameˢ-⊑ ρ ⊑-‵ = refl
size-renameˢ-⊑ ρ (⊑-⇒ p q) =
  cong suc (cong₂ _+_ (size-renameˢ-⊑ ρ p) (size-renameˢ-⊑ ρ q))
size-renameˢ-⊑ ρ (⊑-∀ p) = cong suc (size-renameˢ-⊑ ρ p)
size-renameˢ-⊑ ρ (⊑-ν {A = A} {B = B} p) =
  cong
    suc
    (trans
      (size-cast-⊑
        (renameˢ-ν-src ρ A)
        (renameˢ-ext-⇑ˢ ρ B)
        (renameˢ-⊑ (extˢ ρ) p))
      (size-renameˢ-⊑ (extˢ ρ) p))

data LeafTy : Ty → Set where
  leaf-＇ : ∀ {X} → LeafTy (＇ X)
  leaf-｀ : ∀ {α} → LeafTy (｀ α)
  leaf-‵ : ∀ {ι} → LeafTy (‵ ι)
  leaf-★ : LeafTy ★

LeafSubst : Substᵗ → Set
LeafSubst σ = ∀ X → LeafTy (σ X)

leaf-renameᵗ :
  (ρ : Renameᵗ) →
  ∀ {A} →
  LeafTy A →
  LeafTy (renameᵗ ρ A)
leaf-renameᵗ ρ leaf-＇ = leaf-＇
leaf-renameᵗ ρ leaf-｀ = leaf-｀
leaf-renameᵗ ρ leaf-‵ = leaf-‵
leaf-renameᵗ ρ leaf-★ = leaf-★

leaf-renameˢ :
  (ρ : Renameˢ) →
  ∀ {A} →
  LeafTy A →
  LeafTy (renameˢ ρ A)
leaf-renameˢ ρ leaf-＇ = leaf-＇
leaf-renameˢ ρ leaf-｀ = leaf-｀
leaf-renameˢ ρ leaf-‵ = leaf-‵
leaf-renameˢ ρ leaf-★ = leaf-★

extsᵗ-leaf :
  ∀ {σ} →
  LeafSubst σ →
  LeafSubst (extsᵗ σ)
extsᵗ-leaf leafσ zero = leaf-＇
extsᵗ-leaf leafσ (suc X) = leaf-renameᵗ suc (leafσ X)

liftSubstˢ-leaf :
  ∀ {σ} →
  LeafSubst σ →
  LeafSubst (liftSubstˢ σ)
liftSubstˢ-leaf leafσ X = leaf-renameˢ suc (leafσ X)

size-⊑-refl-leaf :
  ∀ {A} →
  LeafTy A →
  size⊑ (⊑-refl {A = A}) ≡ zero
size-⊑-refl-leaf leaf-＇ = refl
size-⊑-refl-leaf leaf-｀ = refl
size-⊑-refl-leaf leaf-‵ = refl
size-⊑-refl-leaf leaf-★ = refl

size-substᵗ-⊑-leaf :
  (σ : Substᵗ) →
  LeafSubst σ →
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (substᵗ-⊑ σ p) ≡ size⊑ p
size-substᵗ-⊑-leaf σ leafσ ⊑-★★ = refl
size-substᵗ-⊑-leaf σ leafσ (⊑-★ g p) =
  cong suc (size-substᵗ-⊑-leaf σ leafσ p)
size-substᵗ-⊑-leaf σ leafσ {A = ＇ X} ⊑-＇ =
  size-⊑-refl-leaf (leafσ X)
size-substᵗ-⊑-leaf σ leafσ ⊑-｀ = refl
size-substᵗ-⊑-leaf σ leafσ ⊑-‵ = refl
size-substᵗ-⊑-leaf σ leafσ (⊑-⇒ p q) =
  cong suc
    (cong₂
      _+_
      (size-substᵗ-⊑-leaf σ leafσ p)
      (size-substᵗ-⊑-leaf σ leafσ q))
size-substᵗ-⊑-leaf σ leafσ (⊑-∀ p) =
  cong suc (size-substᵗ-⊑-leaf (extsᵗ σ) (extsᵗ-leaf leafσ) p)
size-substᵗ-⊑-leaf σ leafσ (⊑-ν {A = A} {B = B} p) =
  cong
    suc
    (trans
      (size-cast-⊑
        (substᵗ-ν-src σ A)
        (substᵗ-⇑ˢ σ B)
        (substᵗ-⊑ (liftSubstˢ σ) p))
      (size-substᵗ-⊑-leaf (liftSubstˢ σ) (liftSubstˢ-leaf leafσ) p))

leaf-singleTyEnv-α₀ : LeafSubst (singleTyEnv α₀)
leaf-singleTyEnv-α₀ zero = leaf-｀
leaf-singleTyEnv-α₀ (suc X) = leaf-＇

shift-⊑ :
  ∀ {A B} →
  A ⊑ B →
  ⇑ˢ A ⊑ ⇑ˢ B
shift-⊑ = renameˢ-⊑ suc

size-shift-⊑ :
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (shift-⊑ p) ≡ size⊑ p
size-shift-⊑ p = size-renameˢ-⊑ suc p

open-shift-⊑ :
  ∀ {A B} →
  A ⊑ B →
  ((⇑ˢ A) [ α₀ ]ᵗ) ⊑ ((⇑ˢ B) [ α₀ ]ᵗ)
open-shift-⊑ p = substᵗ-⊑ (singleTyEnv α₀) (shift-⊑ p)

size-open-shift-⊑ :
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (open-shift-⊑ p) ≡ size⊑ p
size-open-shift-⊑ p =
  trans
    (size-substᵗ-⊑-leaf
      (singleTyEnv α₀)
      leaf-singleTyEnv-α₀
      (shift-⊑ p))
    (size-shift-⊑ p)

step-≤ :
  ∀ {m n} →
  m ≤ n →
  suc m ≤ suc n
step-≤ = s≤s

pred-★-bound :
  ∀ {a b n} →
  a + suc b ≤ suc n →
  a + b ≤ n
pred-★-bound {a} {b} {n} h =
  s≤s⁻¹
    (subst
      (λ x → x ≤ suc n)
      (+-suc a b)
      h)

left-rec-⇒-bound :
  ∀ {a b c d n} →
  suc (a + b) + suc (c + d) ≤ suc n →
  a + c ≤ n
left-rec-⇒-bound {a} {b} {c} {d} h =
  ≤-trans
    (≤-trans
      (+-mono-≤ (m≤m+n a b) (m≤m+n c d))
      (subst
        (λ x → a + b + (c + d) ≤ x)
        (sym (+-suc (a + b) (c + d)))
        (n≤1+n (a + b + (c + d)))))
    (s≤s⁻¹ h)

right-rec-⇒-bound :
  ∀ {a b c d n} →
  suc (a + b) + suc (c + d) ≤ suc n →
  b + d ≤ n
right-rec-⇒-bound {a} {b} {c} {d} h =
  ≤-trans
    (≤-trans
      (+-mono-≤ (m≤n+m b a) (m≤n+m d c))
      (subst
        (λ x → (a + b) + (c + d) ≤ x)
        (sym (+-suc (a + b) (c + d)))
        (n≤1+n ((a + b) + (c + d)))))
    (s≤s⁻¹ h)

ν-rec-bound :
  ∀ {a b n} →
  suc a + b ≤ suc n →
  a + b ≤ n
ν-rec-bound h = s≤s⁻¹ h

∀ν-rec-bound :
  ∀ {a b n} →
  suc a + suc b ≤ suc n →
  a + b ≤ n
∀ν-rec-bound {a} {b} {n} h =
  ≤-trans
    (≤-trans
      (n≤1+n (a + b))
      (subst
        (λ x → suc (a + b) ≤ x)
        (sym (+-suc a b))
        ≤-refl))
    (s≤s⁻¹ h)

⊑-trans-fuel :
  ∀ {n A B C} →
  (p : A ⊑ B) →
  (q : B ⊑ C) →
  size⊑ p + size⊑ q ≤ n →
  A ⊑ C
⊑-trans-fuel {n = zero} p ⊑-★★ h = p
⊑-trans-fuel {n = zero} ⊑-★★ (⊑-★ g q) ()
⊑-trans-fuel {n = zero} (⊑-★ g p) (⊑-★ g₁ q) ()
⊑-trans-fuel {n = zero} ⊑-＇ (⊑-★ g q) ()
⊑-trans-fuel {n = zero} ⊑-｀ (⊑-★ g q) ()
⊑-trans-fuel {n = zero} ⊑-‵ (⊑-★ g q) ()
⊑-trans-fuel {n = zero} (⊑-⇒ p₁ p₂) (⊑-★ g q) ()
⊑-trans-fuel {n = zero} (⊑-∀ p) (⊑-★ g q) ()
⊑-trans-fuel {n = zero} (⊑-ν p) (⊑-★ g q) ()
⊑-trans-fuel {n = zero} p ⊑-＇ h = p
⊑-trans-fuel {n = zero} p ⊑-｀ h = p
⊑-trans-fuel {n = zero} p ⊑-‵ h = p
⊑-trans-fuel {n = zero} (⊑-⇒ p₁ p₂) (⊑-⇒ q₁ q₂) ()
⊑-trans-fuel {n = zero} (⊑-∀ p) (⊑-∀ q) ()
⊑-trans-fuel {n = zero} (⊑-∀ p) (⊑-ν q) ()
⊑-trans-fuel {n = zero} (⊑-ν p) q ()
⊑-trans-fuel {n = suc n} p ⊑-★★ h = p
⊑-trans-fuel {n = suc n} p (⊑-★ g q) h =
  ⊑-★ g (⊑-trans-fuel p q (pred-★-bound h))
⊑-trans-fuel {n = suc n} p ⊑-＇ h = p
⊑-trans-fuel {n = suc n} p ⊑-｀ h = p
⊑-trans-fuel {n = suc n} p ⊑-‵ h = p
⊑-trans-fuel {n = suc n} (⊑-⇒ p₁ p₂) (⊑-⇒ q₁ q₂) h =
  ⊑-⇒
    (⊑-trans-fuel
      p₁
      q₁
      (left-rec-⇒-bound
        {a = size⊑ p₁} {b = size⊑ p₂}
        {c = size⊑ q₁} {d = size⊑ q₂}
        h))
    (⊑-trans-fuel
      p₂
      q₂
      (right-rec-⇒-bound
        {a = size⊑ p₁} {b = size⊑ p₂}
        {c = size⊑ q₁} {d = size⊑ q₂}
        h))
⊑-trans-fuel {n = suc n} (⊑-ν p) q h =
  ⊑-ν
    (⊑-trans-fuel
      p
      (shift-⊑ q)
      (subst
        (λ x → size⊑ p + x ≤ n)
        (sym (size-shift-⊑ q))
        (ν-rec-bound {a = size⊑ p} {b = size⊑ q} h)))
⊑-trans-fuel {n = suc n} (⊑-∀ p) (⊑-∀ q) h =
  ⊑-∀
    (⊑-trans-fuel
      p
      q
      (∀ν-rec-bound {a = size⊑ p} {b = size⊑ q} h))
⊑-trans-fuel {n = suc n} (⊑-∀ p) (⊑-ν q) h =
  ⊑-ν
    (⊑-trans-fuel
      (open-shift-⊑ p)
      q
      (subst
        (λ x → x + size⊑ q ≤ n)
        (sym (size-open-shift-⊑ p))
        (∀ν-rec-bound {a = size⊑ p} {b = size⊑ q} h)))

⊑-trans : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
⊑-trans p q = ⊑-trans-fuel p q ≤-refl

⊒-trans : ∀ {A B C} → A ⊒ B → B ⊒ C → A ⊒ C
⊒-trans p q = ⊑-trans q p

------------------------------------------------------------------------
-- Dynamic-right inversion (Peter-style, flipped orientation)
------------------------------------------------------------------------

data DynRightInv (A : Ty) : Set where
  inv-★★ : A ≡ ★ → DynRightInv A
  inv-★ : ∀ {G} → Ground G → A ⊑ G → DynRightInv A
  inv-ν★ :
    ∀ {B} →
    A ⊑ `∀ B →
    ((⇑ˢ B) [ α₀ ]ᵗ) ⊑ ★ →
    DynRightInv A

dyn-right-inv : ∀ {A} → A ⊑ ★ → DynRightInv A
dyn-right-inv ⊑-★★ = inv-★★ refl
dyn-right-inv (⊑-★ g p) = inv-★ g p
dyn-right-inv (⊑-ν {A = A} p) = inv-ν★ (⊑-∀ (⊑-refl {A = A})) p
