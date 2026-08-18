module proof.LR-narrow.TypeRenamingComposition where

-- File Charter:
--   * Composition laws for type-variable renaming of GTSFImp terms.
--   * Handles the dependent consistency and conversion evidence carried by
--     casts, then exposes the renaming square needed under type binders.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.HeterogeneousEquality as HE
open import proof.LR-narrow.FunExt using (funext)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Relation.Binary.PropositionalEquality.WithK
  using (≡-irrelevant)

open import Types
open import Consistency
open import Conversion
open import CastTerms
open import proof.TypeInTermSubst using (toRename-wk-eq)
open import proof.Imprecision using (∈ᵗ-unique)

------------------------------------------------------------------------
-- Heterogeneous congruence for intrinsically indexed evidence
------------------------------------------------------------------------

data Packed↑ (Δ : TyCtx) : Set where
  pack↑ : ∀ {A B} → Conv↑ Δ A B → Packed↑ Δ

data Packed↓ (Δ : TyCtx) : Set where
  pack↓ : ∀ {A B} → Conv↓ Δ A B → Packed↓ Δ

pack-↦↑ : ∀ {Δ} → Packed↓ Δ → Packed↑ Δ → Packed↑ Δ
pack-↦↑ (pack↓ c) (pack↑ d) = pack↑ (c ↦↑ d)

pack-↦↓ : ∀ {Δ} → Packed↑ Δ → Packed↓ Δ → Packed↓ Δ
pack-↦↓ (pack↑ c) (pack↓ d) = pack↓ (c ↦↓ d)

pack-∀↑ : ∀ {Δ} → Packed↑ (Nat.suc Δ) → Packed↑ Δ
pack-∀↑ (pack↑ c) = pack↑ (`∀↑ c)

pack-∀↓ : ∀ {Δ} → Packed↓ (Nat.suc Δ) → Packed↓ Δ
pack-∀↓ (pack↓ c) = pack↓ (`∀↓ c)

Hcong₁ : ∀ {a b} {A : Set a} {B : A → Set b} {x y}
  → (f : (z : A) → B z)
  → HE._≅_ x y
  → HE._≅_ (f x) (f y)
Hcong₁ f HE.refl = HE.refl

Hcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
    {C : ∀ x → B x → Set c} {x y u v}
  → (f : (z : A) (w : B z) → C z w)
  → HE._≅_ x y
  → HE._≅_ u v
  → HE._≅_ (f x u) (f y v)
Hcong₂ f HE.refl HE.refl = HE.refl

Hcong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b}
    {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
    {x y u v i j}
  → (f : (z : A) (w : B z) (k : C z w) → D z w k)
  → HE._≅_ x y → HE._≅_ u v → HE._≅_ i j
  → HE._≅_ (f x u i) (f y v j)
Hcong₃ f HE.refl HE.refl HE.refl = HE.refl

Hcong₄ : ∀ {a b c d e} {A : Set a} {B : A → Set b}
    {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
    {E : ∀ x y z → D x y z → Set e} {x y u v i j p q}
  → (f : (z : A) (w : B z) (k : C z w) (l : D z w k)
      → E z w k l)
  → HE._≅_ x y → HE._≅_ u v → HE._≅_ i j → HE._≅_ p q
  → HE._≅_ (f x u i p) (f y v j q)
Hcong₄ f HE.refl HE.refl HE.refl HE.refl = HE.refl

Hcong₅ : ∀ {a b c d e f} {A : Set a} {B : A → Set b}
    {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
    {E : ∀ x y z → D x y z → Set e}
    {F : ∀ x y z w → E x y z w → Set f}
    {x y u v i j p q r s}
  → (g : (z : A) (w : B z) (k : C z w) (l : D z w k)
      (m : E z w k l) → F z w k l m)
  → HE._≅_ x y → HE._≅_ u v → HE._≅_ i j → HE._≅_ p q
  → HE._≅_ r s → HE._≅_ (g x u i p r) (g y v j q s)
Hcong₅ g HE.refl HE.refl HE.refl HE.refl HE.refl = HE.refl

Hcong₇ : ∀ {a b c d e f g h} {A : Set a} {B : A → Set b}
    {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
    {E : ∀ x y z → D x y z → Set e}
    {F : ∀ x y z w → E x y z w → Set f}
    {G : ∀ x y z w t → F x y z w t → Set g}
    {H : ∀ x y z w t u → G x y z w t u → Set h}
    {x y u v i j p q r s o n aa bb}
  → (k : (z : A) (w : B z) (l : C z w) (m : D z w l)
      (t : E z w l m) (z′ : F z w l m t)
      (q′ : G z w l m t z′) → H z w l m t z′ q′)
  → HE._≅_ x y → HE._≅_ u v → HE._≅_ i j → HE._≅_ p q
  → HE._≅_ r s → HE._≅_ o n → HE._≅_ aa bb
  → HE._≅_ (k x u i p r o aa) (k y v j q s n bb)
Hcong₇ k HE.refl HE.refl HE.refl HE.refl HE.refl HE.refl HE.refl =
  HE.refl

------------------------------------------------------------------------
-- Renaming squares stable under type binders
------------------------------------------------------------------------

renameᵗ-square : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₃)
    (tau₁ : Δ₀ ⇒ʳ Δ₂) (tau₂ : Δ₂ ⇒ʳ Δ₃)
  → (∀ X → rho₂ (rho₁ X) ≡ tau₂ (tau₁ X))
  → (A : Ty Δ₀)
  → renameᵗ rho₂ (renameᵗ rho₁ A)
    ≡ renameᵗ tau₂ (renameᵗ tau₁ A)
renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq A =
  trans (renameᵗ-comp rho₁ rho₂ A)
    (trans (renameᵗ-cong A eq) (sym (renameᵗ-comp tau₁ tau₂ A)))

ext-square : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    {rho₁ : Δ₀ ⇒ʳ Δ₁} {rho₂ : Δ₁ ⇒ʳ Δ₃}
    {tau₁ : Δ₀ ⇒ʳ Δ₂} {tau₂ : Δ₂ ⇒ʳ Δ₃}
  → (∀ X → rho₂ (rho₁ X) ≡ tau₂ (tau₁ X))
  → ∀ X → extᵗ rho₂ (extᵗ rho₁ X)
    ≡ extᵗ tau₂ (extᵗ tau₁ X)
ext-square eq Fin.zero = refl
ext-square eq (Fin.suc X) = cong Fin.suc (eq X)

renameEnv-id : ∀ {Δ} (mu : Env∼ Δ) → renameEnv∼ id↪ᵗ mu ≡ mu
renameEnv-id {Nat.zero} mu = funext λ ()
renameEnv-id {Nat.suc Δ} mu = funext eq
  where
  eq : ∀ X → renameEnv∼ id↪ᵗ mu X ≡ mu X
  eq Fin.zero = refl
  eq (Fin.suc X) =
    cong (λ nu → nu X) (renameEnv-id (λ Y → mu (Fin.suc Y)))

renameEnv-wk : ∀ {Δ} (mu : Env∼ Δ)
  → renameEnv∼ wk↪ᵗ mu ≡ extᵐ mu
renameEnv-wk mu = funext eq
  where
  eq : ∀ X → renameEnv∼ wk↪ᵗ mu X ≡ extᵐ mu X
  eq Fin.zero = refl
  eq (Fin.suc X) = cong (λ nu → nu X) (renameEnv-id mu)

renameEnv-keep-ext : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′) (mu : Env∼ Δ)
  → renameEnv∼ (keep rho) (extᵐ mu) ≡ extᵐ (renameEnv∼ rho mu)
renameEnv-keep-ext rho mu = funext λ where
  Fin.zero → refl
  (Fin.suc X) → refl

renameEnv-shift : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′) (mu : Env∼ Δ)
  → renameEnv∼ (keep rho) (renameEnv∼ wk↪ᵗ mu)
    ≡ renameEnv∼ wk↪ᵗ (renameEnv∼ rho mu)
renameEnv-shift rho mu =
  trans (cong (renameEnv∼ (keep rho)) (renameEnv-wk mu))
    (trans (renameEnv-keep-ext rho mu)
      (sym (renameEnv-wk (renameEnv∼ rho mu))))

toRename-shift : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′) (X : TyVar Δ)
  → toRenameᵗ (keep rho) (toRenameᵗ wk↪ᵗ X)
    ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ rho X)
toRename-shift rho X =
  trans (cong (toRenameᵗ (keep rho)) (toRename-wk-eq X))
    (sym (toRename-wk-eq (toRenameᵗ rho X)))

data RenamingSquare : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    → Δ₀ ↪ᵗ Δ₁ → Δ₁ ↪ᵗ Δ₃
    → Δ₀ ↪ᵗ Δ₂ → Δ₂ ↪ᵗ Δ₃ → Set where
  shift-square : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′)
    → RenamingSquare wk↪ᵗ (keep rho) rho wk↪ᵗ
  keep-square : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
      {rho₁ : Δ₀ ↪ᵗ Δ₁} {rho₂ : Δ₁ ↪ᵗ Δ₃}
      {tau₁ : Δ₀ ↪ᵗ Δ₂} {tau₂ : Δ₂ ↪ᵗ Δ₃}
    → RenamingSquare rho₁ rho₂ tau₁ tau₂
    → RenamingSquare (keep rho₁) (keep rho₂)
        (keep tau₁) (keep tau₂)

square-toRename : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    {rho₁ : Δ₀ ↪ᵗ Δ₁} {rho₂ : Δ₁ ↪ᵗ Δ₃}
    {tau₁ : Δ₀ ↪ᵗ Δ₂} {tau₂ : Δ₂ ↪ᵗ Δ₃}
  → RenamingSquare rho₁ rho₂ tau₁ tau₂
  → ∀ X → toRenameᵗ rho₂ (toRenameᵗ rho₁ X)
    ≡ toRenameᵗ tau₂ (toRenameᵗ tau₁ X)
square-toRename (shift-square rho) X = toRename-shift rho X
square-toRename (keep-square square) Fin.zero = refl
square-toRename (keep-square square) (Fin.suc X) =
  cong Fin.suc (square-toRename square X)

square-env : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    {rho₁ : Δ₀ ↪ᵗ Δ₁} {rho₂ : Δ₁ ↪ᵗ Δ₃}
    {tau₁ : Δ₀ ↪ᵗ Δ₂} {tau₂ : Δ₂ ↪ᵗ Δ₃}
  → (square : RenamingSquare rho₁ rho₂ tau₁ tau₂)
  → (mu : Env∼ Δ₀)
  → renameEnv∼ rho₂ (renameEnv∼ rho₁ mu)
    ≡ renameEnv∼ tau₂ (renameEnv∼ tau₁ mu)
square-env (shift-square rho) mu = renameEnv-shift rho mu
square-env {rho₁ = keep rho₁} {rho₂ = keep rho₂}
    {tau₁ = keep tau₁} {tau₂ = keep tau₂}
    (keep-square square) mu = funext eq
  where
  eq : ∀ X
    → renameEnv∼ (keep rho₂) (renameEnv∼ (keep rho₁) mu) X
      ≡ renameEnv∼ (keep tau₂) (renameEnv∼ (keep tau₁) mu) X
  eq Fin.zero = refl
  eq (Fin.suc X) = cong (λ nu → nu X)
    (square-env square (λ Y → mu (Fin.suc Y)))

square-type : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    {rho₁ : Δ₀ ↪ᵗ Δ₁} {rho₂ : Δ₁ ↪ᵗ Δ₃}
    {tau₁ : Δ₀ ↪ᵗ Δ₂} {tau₂ : Δ₂ ↪ᵗ Δ₃}
  → RenamingSquare rho₁ rho₂ tau₁ tau₂
  → (A : Ty Δ₀)
  → renameᵗ (toRenameᵗ rho₂) (renameᵗ (toRenameᵗ rho₁) A)
    ≡ renameᵗ (toRenameᵗ tau₂) (renameᵗ (toRenameᵗ tau₁) A)
square-type {rho₁ = rho₁} {rho₂} {tau₁} {tau₂} square A =
  renameᵗ-square (toRenameᵗ rho₁) (toRenameᵗ rho₂)
    (toRenameᵗ tau₁) (toRenameᵗ tau₂) (square-toRename square) A

------------------------------------------------------------------------
-- Consistency evidence respects renaming squares
------------------------------------------------------------------------

transport-unique≅ : ∀ {P Q : Set}
  → P ≡ Q
  → (p : P) (q : Q)
  → ((x y : Q) → x ≡ y)
  → HE._≅_ p q
transport-unique≅ refl p q unique = HE.≡-to-≅ (unique p q)

¬-unique : ∀ {A : Set} (p q : A → ⊥) → p ≡ q
¬-unique p q = funext (λ x → ⊥-elim (p x))

atom-unique : ∀ {Δ} {A : Ty Δ} (a b : Atom A) → a ≡ b
atom-unique (＇ X) (＇ .X) = refl
atom-unique (‵ ι) (‵ .ι) = refl
atom-unique ★ ★ = refl

∼★-unique : ∀ {Δ} {mu : Env∼ Δ} {G : Ty Δ}
  → (p q : mu ⊢ G ∼★)
  → p ≡ q
∼★-unique ⇒∼★ ⇒∼★ = refl
∼★-unique ι∼★ ι∼★ = refl
∼★-unique (X∼★ᵍ eq) (X∼★ᵍ eq′)
    rewrite ≡-irrelevant eq eq′ = refl
∼★-unique (X∼★ᵍ eq) (X∼★ᶜ eq′)
    with trans (sym eq) eq′
∼★-unique (X∼★ᵍ eq) (X∼★ᶜ eq′) | ()
∼★-unique (X∼★ᶜ eq) (X∼★ᵍ eq′)
    with trans (sym eq) eq′
∼★-unique (X∼★ᶜ eq) (X∼★ᵍ eq′) | ()
∼★-unique (X∼★ᶜ eq) (X∼★ᶜ eq′)
    rewrite ≡-irrelevant eq eq′ = refl
∼★-unique ∀∼★ ∀∼★ = refl

★∼-unique : ∀ {Δ} {mu : Env∼ Δ} {G : Ty Δ}
  → (p q : mu ⊢★∼ G)
  → p ≡ q
★∼-unique ★∼⇒ ★∼⇒ = refl
★∼-unique ★∼ι ★∼ι = refl
★∼-unique (★∼Xᵍ eq) (★∼Xᵍ eq′)
    rewrite ≡-irrelevant eq eq′ = refl
★∼-unique (★∼Xᵍ eq) (★∼Xᶜ eq′)
    with trans (sym eq) eq′
★∼-unique (★∼Xᵍ eq) (★∼Xᶜ eq′) | ()
★∼-unique (★∼Xᶜ eq) (★∼Xᵍ eq′)
    with trans (sym eq) eq′
★∼-unique (★∼Xᶜ eq) (★∼Xᵍ eq′) | ()
★∼-unique (★∼Xᶜ eq) (★∼Xᶜ eq′)
    rewrite ≡-irrelevant eq eq′ = refl
★∼-unique ★∼∀ ★∼∀ = refl

subst-left≅ : ∀ {Δ} {mu : Env∼ Δ} {A A′ B : Ty Δ}
    (eq : A ≡ A′) (c : mu ⊢ A ∼ B)
  → HE._≅_ (subst-left-∼ eq c) c
subst-left≅ refl c = HE.refl

subst-right≅ : ∀ {Δ} {mu : Env∼ Δ} {A B B′ : Ty Δ}
    (eq : B ≡ B′) (c : mu ⊢ A ∼ B)
  → HE._≅_ (subst-right-∼ eq c) c
subst-right≅ refl c = HE.refl

rename∼-cong≅ : ∀ {Δ Δ′} {mu : Env∼ Δ} {nu : Env∼ Δ′}
    (rho : Δ ⇒ʳ Δ′) (eq : ∀ X → nu (rho X) ≡ mu X)
    {A B C D : Ty Δ} {c : mu ⊢ A ∼ B} {d : mu ⊢ C ∼ D}
  → HE._≅_ A C
  → HE._≅_ B D
  → HE._≅_ c d
  → HE._≅_ (rename∼ rho eq c) (rename∼ rho eq d)
rename∼-cong≅ {mu = mu} {nu = nu} rho eq A≅C B≅D c≅d =
  Hcong₃ (λ A B c → rename∼ {μ = mu} {μ′ = nu} rho eq c)
    A≅C B≅D c≅d

mk-id-star : ∀ {Δ} (mu : Env∼ Δ) → mu ⊢ ★ ∼ ★
mk-id-star mu = id ★

mk-id-base : ∀ {Δ} (mu : Env∼ Δ) (ι : Base)
  → mu ⊢ ‵ ι ∼ ‵ ι
mk-id-base mu ι = id (‵ ι)

mk-id-var : ∀ {Δ} (mu : Env∼ Δ) (X : TyVar Δ)
  → mu ⊢ ＇ X ∼ ＇ X
mk-id-var mu X = id (＇ X)

mk-arrow : ∀ {Δ} (mu : Env∼ Δ) (A A′ B B′ : Ty Δ)
  → flipᵐ mu ⊢ A′ ∼ A
  → mu ⊢ B ∼ B′
  → mu ⊢ (A ⇒ B) ∼ (A′ ⇒ B′)
mk-arrow mu A A′ B B′ c d = c ↦ d

mk-all : ∀ {Δ} (mu : Env∼ Δ) (A B : Ty (Nat.suc Δ))
  → extᵐ mu ⊢ A ∼ B
  → mu ⊢ `∀ A ∼ `∀ B
mk-all mu A B c = ∀ᶜ c

mk-bang : ∀ {Δ} (mu : Env∼ Δ) (A G : Ty Δ)
  → Ground G
  → mu ⊢ G ∼★
  → mu ⊢ A ∼ G
  → NonStar A
  → mu ⊢ A ∼ ★
mk-bang mu A G Gᵍ G∼★ c Ans =
  _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄

mk-query : ∀ {Δ} (mu : Env∼ Δ) (G B : Ty Δ)
  → Ground G
  → mu ⊢★∼ G
  → mu ⊢ G ∼ B
  → NonStar B
  → mu ⊢ ★ ∼ B
mk-query mu G B Gᵍ ★∼G c Bns =
  ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄

mk-inst : ∀ {Δ} (mu : Env∼ Δ) (A : Ty (Nat.suc Δ)) (B : Ty Δ)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → instᵐ mu ⊢ A ∼ ⇑ᵗ B
  → B ≢ ★
  → mu ⊢ `∀ A ∼ B
mk-inst mu A B Anv z∈A c B≢★ =
  inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★

mk-gen : ∀ {Δ} (mu : Env∼ Δ) (A : Ty Δ) (B : Ty (Nat.suc Δ))
  → NonVar B
  → Fin.zero ∈ᵗ B
  → genᵐ mu ⊢ ⇑ᵗ A ∼ B
  → A ≢ ★
  → mu ⊢ A ∼ `∀ B
mk-gen mu A B Bnv z∈B c A≢★ =
  gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★

mk-bot-elim : ∀ {Δ} (mu : Env∼ Δ)
  → mu ⊢ (`∀ (＇ Fin.zero)) ∼ (`∀ ★)
mk-bot-elim mu = bot-elim

mk-bot-intro : ∀ {Δ} (mu : Env∼ Δ)
  → mu ⊢ (`∀ ★) ∼ (`∀ (＇ Fin.zero))
mk-bot-intro mu = bot-intro

ext-pointwise : ∀ {Δ Δ′} {rho tau : Δ ⇒ʳ Δ′}
  → (∀ X → rho X ≡ tau X)
  → ∀ X → extᵗ rho X ≡ extᵗ tau X
ext-pointwise eq Fin.zero = refl
ext-pointwise eq (Fin.suc X) = cong Fin.suc (eq X)

rename∼-parallel≅ : ∀ {Δ Δ′}
    {mu₀ : Env∼ Δ} {mu₁ mu₂ : Env∼ Δ′}
    (rho tau : Δ ⇒ʳ Δ′)
    (eq₁ : ∀ X → mu₁ (rho X) ≡ mu₀ X)
    (eq₂ : ∀ X → mu₂ (tau X) ≡ mu₀ X)
  → mu₁ ≡ mu₂
  → (eq-rho : ∀ X → rho X ≡ tau X)
  → ∀ {A B} (c : mu₀ ⊢ A ∼ B)
  → HE._≅_ (rename∼ rho eq₁ c) (rename∼ tau eq₂ c)
rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho (id ★) =
  Hcong₁ mk-id-star (HE.≡-to-≅ eq-mu)
rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho (id (‵ ι)) =
  Hcong₂ mk-id-base (HE.≡-to-≅ eq-mu) HE.refl
rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho (id (＇ X)) =
  Hcong₂ mk-id-var (HE.≡-to-≅ eq-mu) (HE.≡-to-≅ (eq-rho X))
rename∼-parallel≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    rho tau eq₁ eq₂ eq-mu eq-rho
    (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} c d) =
  Hcong₇ mk-arrow (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ (renameᵗ-cong A eq-rho))
    (HE.≡-to-≅ (renameᵗ-cong A′ eq-rho))
    (HE.≡-to-≅ (renameᵗ-cong B eq-rho))
    (HE.≡-to-≅ (renameᵗ-cong B′ eq-rho))
    (rename∼-parallel≅ {mu₀ = flipᵐ mu₀} {mu₁ = flipᵐ mu₁}
      {mu₂ = flipᵐ mu₂} rho tau
      (flip-rename-env {μ = mu₀} {μ′ = mu₁} rho eq₁)
      (flip-rename-env {μ = mu₀} {μ′ = mu₂} tau eq₂)
      (cong flipᵐ eq-mu) eq-rho c)
    (rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho d)
rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho
    (∀ᶜ_ {A = A} {B = B} c) =
  Hcong₄ mk-all (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ (renameᵗ-cong A (ext-pointwise eq-rho)))
    (HE.≡-to-≅ (renameᵗ-cong B (ext-pointwise eq-rho)))
    (rename∼-parallel≅ (extᵗ rho) (extᵗ tau)
      (extᵐ-rename rho eq₁) (extᵐ-rename tau eq₂)
      (cong extᵐ eq-mu) (ext-pointwise eq-rho) c)
rename∼-parallel≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    rho tau eq₁ eq₂ eq-mu eq-rho
    (_! {A = A} {G = G} ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
  Hcong₇ mk-bang (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ G-eq)
    (transport-unique≅ (cong Ground G-eq) _ _ ground-unique)
    (transport-unique≅
      (cong₂ (λ nu T → nu ⊢ T ∼★) eq-mu G-eq)
      (rename∼★ rho eq₁ G∼★) (rename∼★ tau eq₂ G∼★) ∼★-unique)
    (rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho c)
    (transport-unique≅ (cong NonStar A-eq) _ _ nonStar-unique)
  where
  A-eq = renameᵗ-cong A eq-rho
  G-eq = renameᵗ-cong G eq-rho
rename∼-parallel≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    rho tau eq₁ eq₂ eq-mu eq-rho
    (？_ {G = G} {B = B} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
  Hcong₇ mk-query (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ G-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong Ground G-eq) _ _ ground-unique)
    (transport-unique≅
      (cong₂ (λ nu T → nu ⊢★∼ T) eq-mu G-eq)
      (rename★∼ rho eq₁ ★∼G) (rename★∼ tau eq₂ ★∼G) ★∼-unique)
    (rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho c)
    (transport-unique≅ (cong NonStar B-eq) _ _ nonStar-unique)
  where
  G-eq = renameᵗ-cong G eq-rho
  B-eq = renameᵗ-cong B eq-rho
rename∼-parallel≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    rho tau eq₁ eq₂ eq-mu eq-rho
    (inst_ {A = A} {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  Hcong₇ mk-inst (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong NonVar A-eq) _ _ nonVar-unique)
    (transport-unique≅ (cong (Fin.zero ∈ᵗ_) A-eq) _ _ ∈ᵗ-unique)
    premise-heq
    (transport-unique≅ (cong (_≢ ★) B-eq) _ _ ¬-unique)
  where
  A-eq = renameᵗ-cong A (ext-pointwise eq-rho)
  B-eq = renameᵗ-cong B eq-rho
  left-inner = rename∼ (extᵗ rho) (instᵐ-rename rho eq₁) c
  right-inner = rename∼ (extᵗ tau) (instᵐ-rename tau eq₂) c
  left-to-raw = subst-right≅ (renameᵗ-shift rho B) left-inner
  right-to-raw = subst-right≅ (renameᵗ-shift tau B) right-inner
  raw-heq = rename∼-parallel≅ (extᵗ rho) (extᵗ tau)
    (instᵐ-rename rho eq₁) (instᵐ-rename tau eq₂)
    (cong instᵐ eq-mu) (ext-pointwise eq-rho) c
  premise-heq = HE.trans left-to-raw
    (HE.trans raw-heq (HE.sym right-to-raw))
rename∼-parallel≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    rho tau eq₁ eq₂ eq-mu eq-rho
    (gen_ {A = A} {B = B} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  Hcong₇ mk-gen (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong NonVar B-eq) _ _ nonVar-unique)
    (transport-unique≅ (cong (Fin.zero ∈ᵗ_) B-eq) _ _ ∈ᵗ-unique)
    premise-heq
    (transport-unique≅ (cong (_≢ ★) A-eq) _ _ ¬-unique)
  where
  A-eq = renameᵗ-cong A eq-rho
  B-eq = renameᵗ-cong B (ext-pointwise eq-rho)
  left-inner = rename∼ (extᵗ rho) (genᵐ-rename rho eq₁) c
  right-inner = rename∼ (extᵗ tau) (genᵐ-rename tau eq₂) c
  left-to-raw = subst-left≅ (renameᵗ-shift rho A) left-inner
  right-to-raw = subst-left≅ (renameᵗ-shift tau A) right-inner
  raw-heq = rename∼-parallel≅ (extᵗ rho) (extᵗ tau)
    (genᵐ-rename rho eq₁) (genᵐ-rename tau eq₂)
    (cong genᵐ eq-mu) (ext-pointwise eq-rho) c
  premise-heq = HE.trans left-to-raw
    (HE.trans raw-heq (HE.sym right-to-raw))
rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho bot-elim =
  Hcong₁ mk-bot-elim (HE.≡-to-≅ eq-mu)
rename∼-parallel≅ rho tau eq₁ eq₂ eq-mu eq-rho bot-intro =
  Hcong₁ mk-bot-intro (HE.≡-to-≅ eq-mu)

rename∼-square≅ : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    {mu₀ : Env∼ Δ₀} {mu₁ : Env∼ Δ₁} {mu₂ : Env∼ Δ₂}
    {mu₃ mu₄ : Env∼ Δ₃}
    (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₃)
    (tau₁ : Δ₀ ⇒ʳ Δ₂) (tau₂ : Δ₂ ⇒ʳ Δ₃)
    (eq₁ : ∀ X → mu₁ (rho₁ X) ≡ mu₀ X)
    (eq₂ : ∀ X → mu₃ (rho₂ X) ≡ mu₁ X)
    (eq₃ : ∀ X → mu₂ (tau₁ X) ≡ mu₀ X)
    (eq₄ : ∀ X → mu₄ (tau₂ X) ≡ mu₂ X)
  → mu₃ ≡ mu₄
  → (eq-rho : ∀ X → rho₂ (rho₁ X) ≡ tau₂ (tau₁ X))
  → ∀ {A B} (c : mu₀ ⊢ A ∼ B)
  → HE._≅_ (rename∼ rho₂ eq₂ (rename∼ rho₁ eq₁ c))
      (rename∼ tau₂ eq₄ (rename∼ tau₁ eq₃ c))
rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
    eq-mu eq-rho (id ★) =
  Hcong₁ mk-id-star (HE.≡-to-≅ eq-mu)
rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
    eq-mu eq-rho (id (‵ ι)) =
  Hcong₂ mk-id-base (HE.≡-to-≅ eq-mu) HE.refl
rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
    eq-mu eq-rho (id (＇ X)) =
  Hcong₂ mk-id-var (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ (eq-rho X))
rename∼-square≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    {mu₃ = mu₃} {mu₄ = mu₄} rho₁ rho₂ tau₁ tau₂
    eq₁ eq₂ eq₃ eq₄ eq-mu eq-rho
    (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} c d) =
  Hcong₇ mk-arrow (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ (renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho A))
    (HE.≡-to-≅ (renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho A′))
    (HE.≡-to-≅ (renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho B))
    (HE.≡-to-≅ (renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho B′))
    (rename∼-square≅ {mu₀ = flipᵐ mu₀} {mu₁ = flipᵐ mu₁}
      {mu₂ = flipᵐ mu₂} {mu₃ = flipᵐ mu₃} {mu₄ = flipᵐ mu₄}
      rho₁ rho₂ tau₁ tau₂
      (flip-rename-env {μ = mu₀} {μ′ = mu₁} rho₁ eq₁)
      (flip-rename-env {μ = mu₁} {μ′ = mu₃} rho₂ eq₂)
      (flip-rename-env {μ = mu₀} {μ′ = mu₂} tau₁ eq₃)
      (flip-rename-env {μ = mu₂} {μ′ = mu₄} tau₂ eq₄)
      (cong flipᵐ eq-mu) eq-rho c)
    (rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
      eq-mu eq-rho d)
rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
    eq-mu eq-rho (∀ᶜ_ {A = A} {B = B} c) =
  Hcong₄ mk-all (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ (renameᵗ-square (extᵗ rho₁) (extᵗ rho₂)
      (extᵗ tau₁) (extᵗ tau₂) (ext-square eq-rho) A))
    (HE.≡-to-≅ (renameᵗ-square (extᵗ rho₁) (extᵗ rho₂)
      (extᵗ tau₁) (extᵗ tau₂) (ext-square eq-rho) B))
    (rename∼-square≅ (extᵗ rho₁) (extᵗ rho₂)
      (extᵗ tau₁) (extᵗ tau₂)
      (extᵐ-rename rho₁ eq₁) (extᵐ-rename rho₂ eq₂)
      (extᵐ-rename tau₁ eq₃) (extᵐ-rename tau₂ eq₄)
      (cong extᵐ eq-mu) (ext-square eq-rho) c)
rename∼-square≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    {mu₃ = mu₃} {mu₄ = mu₄}
    rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄ eq-mu eq-rho
    (_! {A = A} {G = G} ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
  Hcong₇ mk-bang (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ G-eq)
    (transport-unique≅ (cong Ground G-eq) _ _ ground-unique)
    (transport-unique≅
      (cong₂ (λ nu T → nu ⊢ T ∼★) eq-mu G-eq)
      left-G∼★ right-G∼★ ∼★-unique)
    (rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
      eq-mu eq-rho c)
    (transport-unique≅ (cong NonStar A-eq) _ _ nonStar-unique)
  where
  A-eq = renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho A
  G-eq = renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho G
  left-G∼★ = rename∼★ {μ = mu₁} {μ′ = mu₃} rho₂ eq₂
    (rename∼★ {μ = mu₀} {μ′ = mu₁} rho₁ eq₁ G∼★)
  right-G∼★ = rename∼★ {μ = mu₂} {μ′ = mu₄} tau₂ eq₄
    (rename∼★ {μ = mu₀} {μ′ = mu₂} tau₁ eq₃ G∼★)
rename∼-square≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    {mu₃ = mu₃} {mu₄ = mu₄}
    rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄ eq-mu eq-rho
    (？_ {G = G} {B = B} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
  Hcong₇ mk-query (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ G-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong Ground G-eq) _ _ ground-unique)
    (transport-unique≅
      (cong₂ (λ nu T → nu ⊢★∼ T) eq-mu G-eq)
      left-★∼G right-★∼G ★∼-unique)
    (rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
      eq-mu eq-rho c)
    (transport-unique≅ (cong NonStar B-eq) _ _ nonStar-unique)
  where
  G-eq = renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho G
  B-eq = renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho B
  left-★∼G = rename★∼ {μ = mu₁} {μ′ = mu₃} rho₂ eq₂
    (rename★∼ {μ = mu₀} {μ′ = mu₁} rho₁ eq₁ ★∼G)
  right-★∼G = rename★∼ {μ = mu₂} {μ′ = mu₄} tau₂ eq₄
    (rename★∼ {μ = mu₀} {μ′ = mu₂} tau₁ eq₃ ★∼G)
rename∼-square≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    {mu₃ = mu₃} {mu₄ = mu₄}
    rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄ eq-mu eq-rho
    (inst_ {A = A} {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  Hcong₇ mk-inst (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong NonVar A-eq) _ _ nonVar-unique)
    (transport-unique≅ (cong (Fin.zero ∈ᵗ_) A-eq) _ _ ∈ᵗ-unique)
    premise-heq
    (transport-unique≅ (cong (_≢ ★) B-eq) _ _ ¬-unique)
  where
  A-eq = renameᵗ-square (extᵗ rho₁) (extᵗ rho₂)
    (extᵗ tau₁) (extᵗ tau₂) (ext-square eq-rho) A
  B-eq = renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho B

  left-inner =
    rename∼ (extᵗ rho₂) (instᵐ-rename rho₂ eq₂)
      (subst-right-∼ (renameᵗ-shift rho₁ B)
        (rename∼ (extᵗ rho₁) (instᵐ-rename rho₁ eq₁) c))

  left-to-raw =
    HE.trans
      (subst-right≅ (renameᵗ-shift rho₂ (renameᵗ rho₁ B)) left-inner)
      (rename∼-cong≅ (extᵗ rho₂) (instᵐ-rename rho₂ eq₂)
        HE.refl (HE.≡-to-≅ (sym (renameᵗ-shift rho₁ B)))
        (subst-right≅ (renameᵗ-shift rho₁ B)
          (rename∼ (extᵗ rho₁) (instᵐ-rename rho₁ eq₁) c)))

  right-inner =
    rename∼ (extᵗ tau₂) (instᵐ-rename tau₂ eq₄)
      (subst-right-∼ (renameᵗ-shift tau₁ B)
        (rename∼ (extᵗ tau₁) (instᵐ-rename tau₁ eq₃) c))

  right-to-raw =
    HE.trans
      (subst-right≅ (renameᵗ-shift tau₂ (renameᵗ tau₁ B)) right-inner)
      (rename∼-cong≅ (extᵗ tau₂) (instᵐ-rename tau₂ eq₄)
        HE.refl (HE.≡-to-≅ (sym (renameᵗ-shift tau₁ B)))
        (subst-right≅ (renameᵗ-shift tau₁ B)
          (rename∼ (extᵗ tau₁) (instᵐ-rename tau₁ eq₃) c)))

  raw-heq = rename∼-square≅ (extᵗ rho₁) (extᵗ rho₂)
    (extᵗ tau₁) (extᵗ tau₂)
    (instᵐ-rename rho₁ eq₁) (instᵐ-rename rho₂ eq₂)
    (instᵐ-rename tau₁ eq₃) (instᵐ-rename tau₂ eq₄)
    (cong instᵐ eq-mu) (ext-square eq-rho) c

  premise-heq = HE.trans left-to-raw
    (HE.trans raw-heq (HE.sym right-to-raw))
rename∼-square≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂}
    {mu₃ = mu₃} {mu₄ = mu₄}
    rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄ eq-mu eq-rho
    (gen_ {A = A} {B = B} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  Hcong₇ mk-gen (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong NonVar B-eq) _ _ nonVar-unique)
    (transport-unique≅ (cong (Fin.zero ∈ᵗ_) B-eq) _ _ ∈ᵗ-unique)
    premise-heq
    (transport-unique≅ (cong (_≢ ★) A-eq) _ _ ¬-unique)
  where
  A-eq = renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq-rho A
  B-eq = renameᵗ-square (extᵗ rho₁) (extᵗ rho₂)
    (extᵗ tau₁) (extᵗ tau₂) (ext-square eq-rho) B

  left-inner =
    rename∼ (extᵗ rho₂) (genᵐ-rename rho₂ eq₂)
      (subst-left-∼ (renameᵗ-shift rho₁ A)
        (rename∼ (extᵗ rho₁) (genᵐ-rename rho₁ eq₁) c))

  left-to-raw =
    HE.trans
      (subst-left≅ (renameᵗ-shift rho₂ (renameᵗ rho₁ A)) left-inner)
      (rename∼-cong≅ (extᵗ rho₂) (genᵐ-rename rho₂ eq₂)
        (HE.≡-to-≅ (sym (renameᵗ-shift rho₁ A))) HE.refl
        (subst-left≅ (renameᵗ-shift rho₁ A)
          (rename∼ (extᵗ rho₁) (genᵐ-rename rho₁ eq₁) c)))

  right-inner =
    rename∼ (extᵗ tau₂) (genᵐ-rename tau₂ eq₄)
      (subst-left-∼ (renameᵗ-shift tau₁ A)
        (rename∼ (extᵗ tau₁) (genᵐ-rename tau₁ eq₃) c))

  right-to-raw =
    HE.trans
      (subst-left≅ (renameᵗ-shift tau₂ (renameᵗ tau₁ A)) right-inner)
      (rename∼-cong≅ (extᵗ tau₂) (genᵐ-rename tau₂ eq₄)
        (HE.≡-to-≅ (sym (renameᵗ-shift tau₁ A))) HE.refl
        (subst-left≅ (renameᵗ-shift tau₁ A)
          (rename∼ (extᵗ tau₁) (genᵐ-rename tau₁ eq₃) c)))

  raw-heq = rename∼-square≅ (extᵗ rho₁) (extᵗ rho₂)
    (extᵗ tau₁) (extᵗ tau₂)
    (genᵐ-rename rho₁ eq₁) (genᵐ-rename rho₂ eq₂)
    (genᵐ-rename tau₁ eq₃) (genᵐ-rename tau₂ eq₄)
    (cong genᵐ eq-mu) (ext-square eq-rho) c

  premise-heq = HE.trans left-to-raw
    (HE.trans raw-heq (HE.sym right-to-raw))
rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
    eq-mu eq-rho bot-elim =
  Hcong₁ mk-bot-elim (HE.≡-to-≅ eq-mu)
rename∼-square≅ rho₁ rho₂ tau₁ tau₂ eq₁ eq₂ eq₃ eq₄
    eq-mu eq-rho bot-intro =
  Hcong₁ mk-bot-intro (HE.≡-to-≅ eq-mu)

cast-square≅ : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    {rho₁ : Δ₀ ↪ᵗ Δ₁} {rho₂ : Δ₁ ↪ᵗ Δ₃}
    {tau₁ : Δ₀ ↪ᵗ Δ₂} {tau₂ : Δ₂ ↪ᵗ Δ₃}
    {mu : Env∼ Δ₀} {A B : Ty Δ₀}
  → (square : RenamingSquare rho₁ rho₂ tau₁ tau₂)
  → (c : mu ⊢ A ∼ B)
  → HE._≅_ (renameᵐᶜ rho₂ (renameᵐᶜ rho₁ c))
      (renameᵐᶜ tau₂ (renameᵐᶜ tau₁ c))
cast-square≅ {rho₁ = rho₁} {rho₂} {tau₁} {tau₂} {mu}
    square c =
  rename∼-square≅ (toRenameᵗ rho₁) (toRenameᵗ rho₂)
    (toRenameᵗ tau₁) (toRenameᵗ tau₂)
    (renameEnv∼-preserves rho₁ mu)
    (renameEnv∼-preserves rho₂ (renameEnv∼ rho₁ mu))
    (renameEnv∼-preserves tau₁ mu)
    (renameEnv∼-preserves tau₂ (renameEnv∼ tau₁ mu))
    (square-env square mu) (square-toRename square) c

------------------------------------------------------------------------
-- Conversion evidence respects renaming squares
------------------------------------------------------------------------

mutual
  reveal-square : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
      (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₃)
      (tau₁ : Δ₀ ⇒ʳ Δ₂) (tau₂ : Δ₂ ⇒ʳ Δ₃)
      (eq : ∀ X → rho₂ (rho₁ X) ≡ tau₂ (tau₁ X))
      {A B : Ty Δ₀} (c : Conv↑ Δ₀ A B)
    → pack↑ (rename↑ rho₂ (rename↑ rho₁ c))
      ≡ pack↑ (rename↑ tau₂ (rename↑ tau₁ c))
  reveal-square rho₁ rho₂ tau₁ tau₂ eq (unseal X R)
      rewrite eq X | renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq R = refl
  reveal-square rho₁ rho₂ tau₁ tau₂ eq (c ↦↑ d) =
    cong₂ pack-↦↑ (conceal-square rho₁ rho₂ tau₁ tau₂ eq c)
      (reveal-square rho₁ rho₂ tau₁ tau₂ eq d)
  reveal-square rho₁ rho₂ tau₁ tau₂ eq (`∀↑ c)
      = cong pack-∀↑
        (reveal-square (extᵗ rho₁) (extᵗ rho₂)
          (extᵗ tau₁) (extᵗ tau₂) (ext-square eq) c)
  reveal-square rho₁ rho₂ tau₁ tau₂ eq (id↑ A)
      rewrite renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq A = refl

  conceal-square : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
      (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₃)
      (tau₁ : Δ₀ ⇒ʳ Δ₂) (tau₂ : Δ₂ ⇒ʳ Δ₃)
      (eq : ∀ X → rho₂ (rho₁ X) ≡ tau₂ (tau₁ X))
      {A B : Ty Δ₀} (c : Conv↓ Δ₀ A B)
    → pack↓ (rename↓ rho₂ (rename↓ rho₁ c))
      ≡ pack↓ (rename↓ tau₂ (rename↓ tau₁ c))
  conceal-square rho₁ rho₂ tau₁ tau₂ eq (seal X R)
      rewrite eq X | renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq R = refl
  conceal-square rho₁ rho₂ tau₁ tau₂ eq (c ↦↓ d) =
    cong₂ pack-↦↓ (reveal-square rho₁ rho₂ tau₁ tau₂ eq c)
      (conceal-square rho₁ rho₂ tau₁ tau₂ eq d)
  conceal-square rho₁ rho₂ tau₁ tau₂ eq (`∀↓ c)
      = cong pack-∀↓
        (conceal-square (extᵗ rho₁) (extᵗ rho₂)
          (extᵗ tau₁) (extᵗ tau₂) (ext-square eq) c)
  conceal-square rho₁ rho₂ tau₁ tau₂ eq (id↓ A)
      rewrite renameᵗ-square rho₁ rho₂ tau₁ tau₂ eq A = refl

mk-cast-term : ∀ {Δ} (mu : Env∼ Δ) (A B : Ty Δ)
  → Term Δ
  → mu ⊢ A ∼ B
  → Term Δ
mk-cast-term mu A B M c = M ⟨ c ⟩

apply↑ : ∀ {Δ} → Term Δ → Packed↑ Δ → Term Δ
apply↑ M (pack↑ c) = M ↑ c

apply↓ : ∀ {Δ} → Term Δ → Packed↓ Δ → Term Δ
apply↓ M (pack↓ c) = M ↓ c

------------------------------------------------------------------------
-- Term renaming respects squares
------------------------------------------------------------------------

renameᵗᵐ-square : ∀ {Δ₀ Δ₁ Δ₂ Δ₃}
    {rho₁ : Δ₀ ↪ᵗ Δ₁} {rho₂ : Δ₁ ↪ᵗ Δ₃}
    {tau₁ : Δ₀ ↪ᵗ Δ₂} {tau₂ : Δ₂ ↪ᵗ Δ₃}
  → (square : RenamingSquare rho₁ rho₂ tau₁ tau₂)
  → (M : Term Δ₀)
  → renameᵗᵐ rho₂ (renameᵗᵐ rho₁ M)
    ≡ renameᵗᵐ tau₂ (renameᵗᵐ tau₁ M)
renameᵗᵐ-square square (` x) = refl
renameᵗᵐ-square square (ƛ M) =
  cong ƛ_ (renameᵗᵐ-square square M)
renameᵗᵐ-square square (L · M) =
  cong₂ _·_ (renameᵗᵐ-square square L)
    (renameᵗᵐ-square square M)
renameᵗᵐ-square square (Λ M) =
  cong Λ_ (renameᵗᵐ-square (keep-square square) M)
renameᵗᵐ-square square (M ⦂∀ C [ A ])
    rewrite square-type (keep-square square) C
      | square-type square A =
  cong (λ N → N ⦂∀ _ [ _ ]) (renameᵗᵐ-square square M)
renameᵗᵐ-square square ($ κ) = refl
renameᵗᵐ-square square (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (renameᵗᵐ-square square L) (renameᵗᵐ-square square M)
renameᵗᵐ-square {rho₁ = rho₁} {rho₂} {tau₁} {tau₂} square
    (M ⟨ c ⟩) =
  HE.≅-to-≡
    (Hcong₅ mk-cast-term
      (HE.≡-to-≅ (square-env square _))
      (HE.≡-to-≅ (square-type square _))
      (HE.≡-to-≅ (square-type square _))
      (HE.≡-to-≅ (renameᵗᵐ-square square M))
      (cast-square≅ square c))
renameᵗᵐ-square {rho₁ = rho₁} {rho₂} {tau₁} {tau₂} square
    (M ↑ c) =
  cong₂ apply↑ (renameᵗᵐ-square square M)
    (reveal-square (toRenameᵗ rho₁) (toRenameᵗ rho₂)
      (toRenameᵗ tau₁) (toRenameᵗ tau₂)
      (square-toRename square) c)
renameᵗᵐ-square {rho₁ = rho₁} {rho₂} {tau₁} {tau₂} square
    (M ↓ c) =
  cong₂ apply↓ (renameᵗᵐ-square square M)
    (conceal-square (toRenameᵗ rho₁) (toRenameᵗ rho₂)
      (toRenameᵗ tau₁) (toRenameᵗ tau₂)
      (square-toRename square) c)
renameᵗᵐ-square square blame = refl
