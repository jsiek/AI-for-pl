module TermProperties where

-- File Charter:
--   * Term-variable metatheory for extrinsic-inst terms.
--   * Renaming/substitution environments for term variables, with lifting through
--   * type binders and typing-preservation theorems.
--   * Single-variable and single-type substitution APIs used by reduction.
-- Note to self:
--   * Keep raw term syntax and type/seal structural actions in `Terms.agda`;
--   * this file owns term-variable substitution infrastructure.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; map; length; []; _∷_)
open import Data.Nat using (_<_; suc; zero; z<s; s<s)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Store
open import Ctx using (⤊ᵗ)
open import UpDown
open import Terms hiding (_[_]ᵀ)

cong₃ : ∀ {A B C D : Set}
  (f : A → B → C → D)
  {x x′ : A} {y y′ : B} {z z′ : C} →
  x ≡ x′ →
  y ≡ y′ →
  z ≡ z′ →
  f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- Term-variable renaming and substitution environments
------------------------------------------------------------------------

Renameˣ : Set
Renameˣ = Var → Var

Renameˣ-wt : (Γ Γ′ : Ctx) (ρ : Renameˣ) → Set
Renameˣ-wt Γ Γ′ ρ = ∀ {A : Ty}{x : Var} → (h : Γ ∋ x ⦂ A) → Γ′ ∋ ρ x ⦂ A

Substˣ : Set
Substˣ = Var → Term

Substˣ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} → (σ : Substˣ) → Set
Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ =
  ∀ {A : Ty}{x : Var} → (h : Γ ∋ x ⦂ A) → Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ σ x ⦂ A

extʳ : Renameˣ → Renameˣ
extʳ ρ zero = zero
extʳ ρ (suc x) = suc (ρ x)

extʳ-wt : ∀ {Γ Γ′ : Ctx}{A : Ty} → (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (A ∷ Γ) (A ∷ Γ′) (extʳ ρ)
extʳ-wt ρ hρ Z = Z
extʳ-wt ρ hρ (S h) = S (hρ h)

wkʳ : Renameˣ
wkʳ x = suc x

wkʳ-wt : ∀ {Γ : Ctx}{A B : Ty}{x : Var} →
  (h : Γ ∋ x ⦂ A) →
  (B ∷ Γ) ∋ wkʳ x ⦂ A
wkʳ-wt h = S h

map∋ : ∀ {Γ : Ctx}{x : Var}{A : Ty} → (f : Ty → Ty) →
  Γ ∋ x ⦂ A →
  map f Γ ∋ x ⦂ f A
map∋ f Z = Z
map∋ f (S h) = S (map∋ f h)

unmap∋-⤊ᵗ : ∀ {Γ : Ctx}{x : Var}{A : Ty} →
  ⤊ᵗ Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] Σ[ _ ∈ (A ≡ renameᵗ suc B) ] (Γ ∋ x ⦂ B)
unmap∋-⤊ᵗ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ᵗ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ᵗ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftᵗʳ : Renameˣ → Renameˣ
liftᵗʳ ρ x = ρ x

liftᵗʳ-wt : ∀ {Γ Γ′ : Ctx} → (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (⤊ᵗ Γ) (⤊ᵗ Γ′) (liftᵗʳ ρ)
liftᵗʳ-wt {Γ′ = Γ′} ρ hρ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  subst
    (λ T → ⤊ᵗ Γ′ ∋ ρ x ⦂ T)
    (sym eq)
    (map∋ (renameᵗ suc) (hρ h₀))

------------------------------------------------------------------------
-- Renaming and substitution actions on terms (term variables)
------------------------------------------------------------------------

renameˣᵐ : Renameˣ → Term → Term
renameˣᵐ ρ (` x) = ` (ρ x)
renameˣᵐ ρ (ƛ A ⇒ M) = ƛ A ⇒ renameˣᵐ (extʳ ρ) M
renameˣᵐ ρ (L · M) = renameˣᵐ ρ L · renameˣᵐ ρ M
renameˣᵐ ρ (Λ M) = Λ (renameˣᵐ (liftᵗʳ ρ) M)
renameˣᵐ ρ (M ⦂∀ B [ T ]) = renameˣᵐ ρ M ⦂∀ B [ T ]
renameˣᵐ ρ ($ κ) = $ κ
renameˣᵐ ρ (L ⊕[ op ] M) = renameˣᵐ ρ L ⊕[ op ] renameˣᵐ ρ M
renameˣᵐ ρ (M up p) = renameˣᵐ ρ M up p
renameˣᵐ ρ (M down p) = renameˣᵐ ρ M down p
renameˣᵐ ρ (blame ℓ) = blame ℓ

renameˣᵐ-value : ∀ {V} (ρ : Renameˣ) →
  Value V →
  Value (renameˣᵐ ρ V)
renameˣᵐ-value ρ (ƛ A ⇒ N) = ƛ A ⇒ renameˣᵐ (extʳ ρ) N
renameˣᵐ-value ρ ($ κ) = $ κ
renameˣᵐ-value ρ (Λ N) = Λ renameˣᵐ (liftᵗʳ ρ) N
renameˣᵐ-value ρ (vV up p) = renameˣᵐ-value ρ vV up p
renameˣᵐ-value ρ (vV down p) = renameˣᵐ-value ρ vV down p

renameˣ-term-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ renameˣᵐ ρ M ⦂ A
renameˣ-term-wt ρ hρ (⊢` h) = ⊢` (hρ h)
renameˣ-term-wt ρ hρ (⊢ƛ {A = A} wfA M) =
  ⊢ƛ wfA (renameˣ-term-wt (extʳ ρ) (extʳ-wt ρ hρ) M)
renameˣ-term-wt ρ hρ (⊢· L M) =
  ⊢· (renameˣ-term-wt ρ hρ L) (renameˣ-term-wt ρ hρ M)
renameˣ-term-wt ρ hρ (⊢Λ vM M) =
  ⊢Λ (renameˣᵐ-value (liftᵗʳ ρ) vM)
    (renameˣ-term-wt (liftᵗʳ ρ) (liftᵗʳ-wt ρ hρ) M)
renameˣ-term-wt ρ hρ (⊢• {B = B} M wfB wfT) =
  ⊢• {B = B} (renameˣ-term-wt ρ hρ M) wfB wfT
renameˣ-term-wt ρ hρ (⊢$ κ) = ⊢$ κ
renameˣ-term-wt ρ hρ (⊢⊕ L op M) =
  ⊢⊕ (renameˣ-term-wt ρ hρ L) op (renameˣ-term-wt ρ hρ M)
renameˣ-term-wt ρ hρ (⊢up {p = p} Φ lenΦ M hp) =
  ⊢up {p = p} Φ lenΦ (renameˣ-term-wt ρ hρ M) hp
renameˣ-term-wt ρ hρ (⊢down {p = p} Φ lenΦ M hp) =
  ⊢down {p = p} Φ lenΦ (renameˣ-term-wt ρ hρ M) hp
renameˣ-term-wt ρ hρ (⊢blame ℓ) = ⊢blame ℓ

↑ᵗᵐ : Substˣ → Substˣ
↑ᵗᵐ σ x = renameᵗᵐ suc (σ x)

↑ᵗᵐ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} →
  (σ : Substˣ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ →
  Substˣ-wt {suc Δ} {Ψ} {⟰ᵗ Σ} {⤊ᵗ Γ} {⤊ᵗ Γ′} (↑ᵗᵐ σ)
↑ᵗᵐ-wt σ hσ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  cong-⊢⦂
    refl
    refl
    refl
    (sym eq)
    (renameᵗ-term suc TyRenameWf-suc (hσ {x = x} h₀))

extˣ : Substˣ → Substˣ
extˣ σ zero = ` zero
extˣ σ (suc x) = renameˣᵐ wkʳ (σ x)

extˣ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{A : Ty} →
  (σ : Substˣ) →
  (hσ : Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {A ∷ Γ′} (extˣ σ)
extˣ-wt σ hσ Z = ⊢` Z
extˣ-wt σ hσ (S h) = renameˣ-term-wt wkʳ wkʳ-wt (hσ h)

substˣ-term : Substˣ → Term → Term
substˣ-term σ (` x) = σ x
substˣ-term σ (ƛ A ⇒ M) = ƛ A ⇒ substˣ-term (extˣ σ) M
substˣ-term σ (L · M) = substˣ-term σ L · substˣ-term σ M
substˣ-term σ (Λ M) = Λ (substˣ-term (↑ᵗᵐ σ) M)
substˣ-term σ (M ⦂∀ B [ T ]) = substˣ-term σ M ⦂∀ B [ T ]
substˣ-term σ ($ κ) = $ κ
substˣ-term σ (L ⊕[ op ] M) = substˣ-term σ L ⊕[ op ] substˣ-term σ M
substˣ-term σ (M up p) = substˣ-term σ M up p
substˣ-term σ (M down p) = substˣ-term σ M down p
substˣ-term σ (blame ℓ) = blame ℓ

substˣ-term-value : ∀ {V} (σ : Substˣ) →
  Value V →
  Value (substˣ-term σ V)
substˣ-term-value σ (ƛ A ⇒ N) = ƛ A ⇒ substˣ-term (extˣ σ) N
substˣ-term-value σ ($ κ) = $ κ
substˣ-term-value σ (Λ N) = Λ substˣ-term (↑ᵗᵐ σ) N
substˣ-term-value σ (vV up p) = substˣ-term-value σ vV up p
substˣ-term-value σ (vV down p) = substˣ-term-value σ vV down p

substˣ-term-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (σ : Substˣ) →
  (hσ : Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ) →
  (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ substˣ-term σ M ⦂ A
substˣ-term-wt σ hσ (⊢` {x = x} h) = hσ h
substˣ-term-wt σ hσ (⊢ƛ {A = A} wfA M) =
  ⊢ƛ wfA (substˣ-term-wt (extˣ σ) (extˣ-wt {A = A} σ hσ) M)
substˣ-term-wt σ hσ (⊢· L M) =
  ⊢· (substˣ-term-wt σ hσ L) (substˣ-term-wt σ hσ M)
substˣ-term-wt σ hσ (⊢Λ vM M) =
  ⊢Λ (substˣ-term-value (↑ᵗᵐ σ) vM)
    (substˣ-term-wt (↑ᵗᵐ σ) (↑ᵗᵐ-wt σ hσ) M)
substˣ-term-wt σ hσ (⊢• {B = B} M wfB wfT) =
  ⊢• {B = B} (substˣ-term-wt σ hσ M) wfB wfT
substˣ-term-wt σ hσ (⊢$ κ) = ⊢$ κ
substˣ-term-wt σ hσ (⊢⊕ L op M) =
  ⊢⊕ (substˣ-term-wt σ hσ L) op (substˣ-term-wt σ hσ M)
substˣ-term-wt σ hσ (⊢up {p = p} Φ lenΦ M hp) =
  ⊢up {p = p} Φ lenΦ (substˣ-term-wt σ hσ M) hp
substˣ-term-wt σ hσ (⊢down {p = p} Φ lenΦ M hp) =
  ⊢down {p = p} Φ lenΦ (substˣ-term-wt σ hσ M) hp
substˣ-term-wt σ hσ (⊢blame ℓ) = ⊢blame ℓ

------------------------------------------------------------------------
-- Congruence for raw term actions
------------------------------------------------------------------------

extʳ-cong : ∀ {ρ ρ′ : Renameˣ} →
  ((x : Var) → ρ x ≡ ρ′ x) →
  (x : Var) →
  extʳ ρ x ≡ extʳ ρ′ x
extʳ-cong h zero = refl
extʳ-cong h (suc x) = cong suc (h x)

renameˣᵐ-cong : ∀ {ρ ρ′ : Renameˣ} →
  ((x : Var) → ρ x ≡ ρ′ x) →
  (M : Term) →
  renameˣᵐ ρ M ≡ renameˣᵐ ρ′ M
renameˣᵐ-cong h (` x) = cong `_ (h x)
renameˣᵐ-cong h (ƛ A ⇒ M) =
  cong (ƛ A ⇒_) (renameˣᵐ-cong (extʳ-cong h) M)
renameˣᵐ-cong h (L · M) =
  cong₂ _·_ (renameˣᵐ-cong h L) (renameˣᵐ-cong h M)
renameˣᵐ-cong h (Λ M) = cong Λ_ (renameˣᵐ-cong h M)
renameˣᵐ-cong h (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_] (renameˣᵐ-cong h M) refl refl
renameˣᵐ-cong h ($ κ) = refl
renameˣᵐ-cong h (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (renameˣᵐ-cong h L) refl (renameˣᵐ-cong h M)
renameˣᵐ-cong h (M up p) = cong₂ _up_ (renameˣᵐ-cong h M) refl
renameˣᵐ-cong h (M down p) =
  cong₂ _down_ (renameˣᵐ-cong h M) refl
renameˣᵐ-cong h (blame ℓ) = refl

extˣ-cong : ∀ {σ τ : Substˣ} →
  ((x : Var) → σ x ≡ τ x) →
  (x : Var) →
  extˣ σ x ≡ extˣ τ x
extˣ-cong h zero = refl
extˣ-cong h (suc x) = cong (renameˣᵐ wkʳ) (h x)

↑ᵗᵐ-cong : ∀ {σ τ : Substˣ} →
  ((x : Var) → σ x ≡ τ x) →
  (x : Var) →
  ↑ᵗᵐ σ x ≡ ↑ᵗᵐ τ x
↑ᵗᵐ-cong h x = cong (renameᵗᵐ suc) (h x)

substˣ-term-cong : ∀ {σ τ : Substˣ} →
  ((x : Var) → σ x ≡ τ x) →
  (M : Term) →
  substˣ-term σ M ≡ substˣ-term τ M
substˣ-term-cong h (` x) = h x
substˣ-term-cong h (ƛ A ⇒ M) =
  cong (ƛ A ⇒_) (substˣ-term-cong (extˣ-cong h) M)
substˣ-term-cong h (L · M) =
  cong₂ _·_ (substˣ-term-cong h L) (substˣ-term-cong h M)
substˣ-term-cong h (Λ M) =
  cong Λ_ (substˣ-term-cong (↑ᵗᵐ-cong h) M)
substˣ-term-cong h (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_] (substˣ-term-cong h M) refl refl
substˣ-term-cong h ($ κ) = refl
substˣ-term-cong h (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (substˣ-term-cong h L) refl (substˣ-term-cong h M)
substˣ-term-cong h (M up p) =
  cong₂ _up_ (substˣ-term-cong h M) refl
substˣ-term-cong h (M down p) =
  cong₂ _down_ (substˣ-term-cong h M) refl
substˣ-term-cong h (blame ℓ) = refl

renameᵗᵐ-cong : ∀ {ρ ρ′ : Renameᵗ} →
  ((X : TyVar) → ρ X ≡ ρ′ X) →
  (M : Term) →
  renameᵗᵐ ρ M ≡ renameᵗᵐ ρ′ M
renameᵗᵐ-cong h (` x) = refl
renameᵗᵐ-cong h (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_ (rename-cong h A) (renameᵗᵐ-cong h M)
renameᵗᵐ-cong h (L · M) =
  cong₂ _·_ (renameᵗᵐ-cong h L) (renameᵗᵐ-cong h M)
renameᵗᵐ-cong h (Λ M) = cong Λ_ (renameᵗᵐ-cong h-ext M)
  where
  h-ext : (X : TyVar) → extᵗ _ X ≡ extᵗ _ X
  h-ext zero = refl
  h-ext (suc X) = cong suc (h X)
renameᵗᵐ-cong h (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (renameᵗᵐ-cong h M)
    (rename-cong h-ext B)
    (rename-cong h T)
  where
  h-ext : (X : TyVar) → extᵗ _ X ≡ extᵗ _ X
  h-ext zero = refl
  h-ext (suc X) = cong suc (h X)
renameᵗᵐ-cong h ($ κ) = refl
renameᵗᵐ-cong h (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (renameᵗᵐ-cong h L) refl (renameᵗᵐ-cong h M)
renameᵗᵐ-cong h (M up p) =
  cong₂ _up_ (renameᵗᵐ-cong h M) (rename⊑ᵗ-cong h p)
renameᵗᵐ-cong h (M down p) =
  cong₂ _down_ (renameᵗᵐ-cong h M) (rename⊒ᵗ-cong h p)
renameᵗᵐ-cong h (blame ℓ) = refl

substᵗᵐ-cong : ∀ {σ τ : Substᵗ} →
  ((X : TyVar) → σ X ≡ τ X) →
  (M : Term) →
  substᵗᵐ σ M ≡ substᵗᵐ τ M
substᵗᵐ-cong h (` x) = refl
substᵗᵐ-cong h (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_ (substᵗ-cong h A) (substᵗᵐ-cong h M)
substᵗᵐ-cong h (L · M) =
  cong₂ _·_ (substᵗᵐ-cong h L) (substᵗᵐ-cong h M)
substᵗᵐ-cong h (Λ M) = cong Λ_ (substᵗᵐ-cong h-ext M)
  where
  h-ext : (X : TyVar) → extsᵗ _ X ≡ extsᵗ _ X
  h-ext zero = refl
  h-ext (suc X) = cong (renameᵗ suc) (h X)
substᵗᵐ-cong h (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (substᵗᵐ-cong h M)
    (substᵗ-cong h-ext B)
    (substᵗ-cong h T)
  where
  h-ext : (X : TyVar) → extsᵗ _ X ≡ extsᵗ _ X
  h-ext zero = refl
  h-ext (suc X) = cong (renameᵗ suc) (h X)
substᵗᵐ-cong h ($ κ) = refl
substᵗᵐ-cong h (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (substᵗᵐ-cong h L) refl (substᵗᵐ-cong h M)
substᵗᵐ-cong h (M up p) =
  cong₂ _up_ (substᵗᵐ-cong h M) (subst⊑ᵗ-cong h p)
substᵗᵐ-cong h (M down p) =
  cong₂ _down_ (substᵗᵐ-cong h M) (subst⊒ᵗ-cong h p)
substᵗᵐ-cong h (blame ℓ) = refl

------------------------------------------------------------------------
-- Type substitution identity on terms
------------------------------------------------------------------------

extsᵗ-id : (X : TyVar) → extsᵗ (λ Y → ＇ Y) X ≡ ＇ X
extsᵗ-id zero = refl
extsᵗ-id (suc X) = refl

liftSubstˢ-id : (X : TyVar) → liftSubstˢ (λ Y → ＇ Y) X ≡ ＇ X
liftSubstˢ-id X = refl

mutual
  subst⊑ᵗ-id :
    (p : Up) →
    subst⊑ᵗ (λ X → ＇ X) p ≡ p
  subst⊑ᵗ-id (tag G) = cong tag (substᵗ-id G)
  subst⊑ᵗ-id (unseal α) = refl
  subst⊑ᵗ-id (p ↦ q) =
    cong₂ _↦_ (subst⊒ᵗ-id p) (subst⊑ᵗ-id q)
  subst⊑ᵗ-id (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (subst⊑ᵗ-cong extsᵗ-id p)
        (subst⊑ᵗ-id p))
  subst⊑ᵗ-id (ν p) =
    cong ν_
      (trans
        (subst⊑ᵗ-cong liftSubstˢ-id p)
        (subst⊑ᵗ-id p))
  subst⊑ᵗ-id (id A) = cong id (substᵗ-id A)
  subst⊑ᵗ-id (p ； q) =
    cong₂ _；_ (subst⊑ᵗ-id p) (subst⊑ᵗ-id q)

  subst⊒ᵗ-id :
    (p : Down) →
    subst⊒ᵗ (λ X → ＇ X) p ≡ p
  subst⊒ᵗ-id (untag G ℓ) =
    cong (λ T → untag T ℓ) (substᵗ-id G)
  subst⊒ᵗ-id (seal α) = refl
  subst⊒ᵗ-id (p ↦ q) =
    cong₂ _↦_ (subst⊑ᵗ-id p) (subst⊒ᵗ-id q)
  subst⊒ᵗ-id (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (subst⊒ᵗ-cong extsᵗ-id p)
        (subst⊒ᵗ-id p))
  subst⊒ᵗ-id (ν p) =
    cong ν_
      (trans
        (subst⊒ᵗ-cong liftSubstˢ-id p)
        (subst⊒ᵗ-id p))
  subst⊒ᵗ-id (id A) = cong id (substᵗ-id A)
  subst⊒ᵗ-id (p ； q) =
    cong₂ _；_ (subst⊒ᵗ-id p) (subst⊒ᵗ-id q)

substᵗᵐ-id : (M : Term) → substᵗᵐ (λ X → ＇ X) M ≡ M
substᵗᵐ-id (` x) = refl
substᵗᵐ-id (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_ (substᵗ-id A) (substᵗᵐ-id M)
substᵗᵐ-id (L · M) =
  cong₂ _·_ (substᵗᵐ-id L) (substᵗᵐ-id M)
substᵗᵐ-id (Λ M) =
  cong Λ_
    (trans
      (substᵗᵐ-cong extsᵗ-id M)
      (substᵗᵐ-id M))
substᵗᵐ-id (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (substᵗᵐ-id M)
    (trans (substᵗ-cong extsᵗ-id B) (substᵗ-id B))
    (substᵗ-id T)
substᵗᵐ-id ($ κ) = refl
substᵗᵐ-id (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (substᵗᵐ-id L) refl (substᵗᵐ-id M)
substᵗᵐ-id (M up p) =
  cong₂ _up_ (substᵗᵐ-id M) (subst⊑ᵗ-id p)
substᵗᵐ-id (M down p) =
  cong₂ _down_ (substᵗᵐ-id M) (subst⊒ᵗ-id p)
substᵗᵐ-id (blame ℓ) = refl

IdOnΔ : TyCtx → Substᵗ → Set
IdOnΔ Δ σ = ∀ {X} → X < Δ → σ X ≡ ＇ X

IdOnΔ-exts :
  ∀ {Δ σ} →
  IdOnΔ Δ σ →
  IdOnΔ (suc Δ) (extsᵗ σ)
IdOnΔ-exts hσ {zero} z<s = refl
IdOnΔ-exts hσ {suc X} (s<s X<Δ) =
  cong (renameᵗ suc) (hσ X<Δ)

IdOnΔ-liftSubstˢ :
  ∀ {Δ σ} →
  IdOnΔ Δ σ →
  IdOnΔ Δ (liftSubstˢ σ)
IdOnΔ-liftSubstˢ hσ X<Δ = cong ⇑ˢ (hσ X<Δ)

substᵗ-id-typed :
  ∀ {Δ Ψ A σ} →
  IdOnΔ Δ σ →
  WfTy Δ Ψ A →
  substᵗ σ A ≡ A
substᵗ-id-typed hσ (wfVar X<Δ) = hσ X<Δ
substᵗ-id-typed hσ (wfSeal α<Ψ) = refl
substᵗ-id-typed hσ wfBase = refl
substᵗ-id-typed hσ wf★ = refl
substᵗ-id-typed hσ (wf⇒ hA hB) =
  cong₂ _⇒_ (substᵗ-id-typed hσ hA) (substᵗ-id-typed hσ hB)
substᵗ-id-typed hσ (wf∀ hA) =
  cong `∀ (substᵗ-id-typed (IdOnΔ-exts hσ) hA)

mutual
  subst⊑ᵗ-id-typed :
    ∀ {Δ Ψ Σ Φ A B p σ} →
    IdOnΔ Δ σ →
    length Φ ≡ Ψ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    subst⊑ᵗ σ p ≡ p
  subst⊑ᵗ-id-typed hσ lenΦ (wt-tag g ok) =
    cong tag (substᵗ-id-typed hσ (ground-wf lenΦ g ok))
  subst⊑ᵗ-id-typed hσ lenΦ (wt-unseal h α∈Φ) = refl
  subst⊑ᵗ-id-typed hσ lenΦ (wt-unseal★ h α∈Φ) = refl
  subst⊑ᵗ-id-typed hσ lenΦ (wt-↦ p q) =
    cong₂ _↦_
      (subst⊒ᵗ-id-typed hσ lenΦ p)
      (subst⊑ᵗ-id-typed hσ lenΦ q)
  subst⊑ᵗ-id-typed hσ lenΦ (wt-∀ p) =
    cong ∀ᵖ
      (subst⊑ᵗ-id-typed
        (IdOnΔ-exts hσ)
        lenΦ
        p)
  subst⊑ᵗ-id-typed hσ lenΦ (wt-ν p) =
    cong ν_
      (subst⊑ᵗ-id-typed
        (IdOnΔ-liftSubstˢ hσ)
        (cong suc lenΦ)
        p)
  subst⊑ᵗ-id-typed hσ lenΦ (wt-id wfA) =
    cong id (substᵗ-id-typed hσ wfA)
  subst⊑ᵗ-id-typed hσ lenΦ (wt-； p q) =
    cong₂ _；_
      (subst⊑ᵗ-id-typed hσ lenΦ p)
      (subst⊑ᵗ-id-typed hσ lenΦ q)

  subst⊒ᵗ-id-typed :
    ∀ {Δ Ψ Σ Φ A B p σ} →
    IdOnΔ Δ σ →
    length Φ ≡ Ψ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    subst⊒ᵗ σ p ≡ p
  subst⊒ᵗ-id-typed hσ lenΦ (wt-untag g ok ℓ) =
    cong (λ T → untag T ℓ) (substᵗ-id-typed hσ (ground-wf lenΦ g ok))
  subst⊒ᵗ-id-typed hσ lenΦ (wt-seal h α∈Φ) = refl
  subst⊒ᵗ-id-typed hσ lenΦ (wt-seal★ h α∈Φ) = refl
  subst⊒ᵗ-id-typed hσ lenΦ (wt-↦ p q) =
    cong₂ _↦_
      (subst⊑ᵗ-id-typed hσ lenΦ p)
      (subst⊒ᵗ-id-typed hσ lenΦ q)
  subst⊒ᵗ-id-typed hσ lenΦ (wt-∀ p) =
    cong ∀ᵖ
      (subst⊒ᵗ-id-typed
        (IdOnΔ-exts hσ)
        lenΦ
        p)
  subst⊒ᵗ-id-typed hσ lenΦ (wt-ν p) =
    cong ν_
      (subst⊒ᵗ-id-typed
        (IdOnΔ-liftSubstˢ hσ)
        (cong suc lenΦ)
        p)
  subst⊒ᵗ-id-typed hσ lenΦ (wt-id wfA) =
    cong id (substᵗ-id-typed hσ wfA)
  subst⊒ᵗ-id-typed hσ lenΦ (wt-； p q) =
    cong₂ _；_
      (subst⊒ᵗ-id-typed hσ lenΦ p)
      (subst⊒ᵗ-id-typed hσ lenΦ q)

substᵗᵐ-id-typed :
  ∀ {Δ Ψ Σ Γ M A σ} →
  IdOnΔ Δ σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  substᵗᵐ σ M ≡ M
substᵗᵐ-id-typed hσ (⊢` h) = refl
substᵗᵐ-id-typed hσ (⊢ƛ wfA M⊢) =
  cong₂ ƛ_⇒_
    (substᵗ-id-typed hσ wfA)
    (substᵗᵐ-id-typed hσ M⊢)
substᵗᵐ-id-typed hσ (⊢· L⊢ M⊢) =
  cong₂ _·_
    (substᵗᵐ-id-typed hσ L⊢)
    (substᵗᵐ-id-typed hσ M⊢)
substᵗᵐ-id-typed hσ (⊢Λ vM M⊢) =
  cong Λ_
    (substᵗᵐ-id-typed
      (IdOnΔ-exts hσ)
      M⊢)
substᵗᵐ-id-typed hσ (⊢• M⊢ wfB wfT) =
  cong₃ _⦂∀_[_]
    (substᵗᵐ-id-typed hσ M⊢)
    (substᵗ-id-typed (IdOnΔ-exts hσ) wfB)
    (substᵗ-id-typed hσ wfT)
substᵗᵐ-id-typed hσ (⊢$ κ) = refl
substᵗᵐ-id-typed hσ (⊢⊕ L⊢ op M⊢) =
  cong₃ _⊕[_]_
    (substᵗᵐ-id-typed hσ L⊢)
    refl
    (substᵗᵐ-id-typed hσ M⊢)
substᵗᵐ-id-typed hσ (⊢up Φ lenΦ M⊢ hp) =
  cong₂ _up_
    (substᵗᵐ-id-typed hσ M⊢)
    (subst⊑ᵗ-id-typed hσ lenΦ hp)
substᵗᵐ-id-typed hσ (⊢down Φ lenΦ M⊢ hp) =
  cong₂ _down_
    (substᵗᵐ-id-typed hσ M⊢)
    (subst⊒ᵗ-id-typed hσ lenΦ hp)
substᵗᵐ-id-typed hσ (⊢blame ℓ) = refl

substᵗᵐ-id-emptyΔ :
  ∀ {Ψ Σ Γ M A σ} →
  0 ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  substᵗᵐ σ M ≡ M
substᵗᵐ-id-emptyΔ M⊢ = substᵗᵐ-id-typed (λ ()) M⊢

------------------------------------------------------------------------
-- Type-variable renamings/substitutions commute on terms
------------------------------------------------------------------------

renameᵗᵐ-renameᵗᵐ :
  (ρ₁ ρ₂ : Renameᵗ) (M : Term) →
  renameᵗᵐ ρ₂ (renameᵗᵐ ρ₁ M) ≡
  renameᵗᵐ (λ X → ρ₂ (ρ₁ X)) M
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (` x) = refl
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_
    (renameᵗ-compose ρ₁ ρ₂ A)
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ M)
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (L · M) =
  cong₂ _·_
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ L)
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ M)
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (Λ M) =
  cong Λ_
    (trans
      (renameᵗᵐ-renameᵗᵐ (extᵗ ρ₁) (extᵗ ρ₂) M)
      (renameᵗᵐ-cong env M))
  where
  env : (X : TyVar) →
    extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ Y → ρ₂ (ρ₁ Y)) X
  env zero = refl
  env (suc X) = refl
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ M)
    (trans
      (renameᵗ-compose (extᵗ ρ₁) (extᵗ ρ₂) B)
      (rename-cong env B))
    (renameᵗ-compose ρ₁ ρ₂ T)
  where
  env : (X : TyVar) →
    extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ Y → ρ₂ (ρ₁ Y)) X
  env zero = refl
  env (suc X) = refl
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ ($ κ) = refl
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ L)
    refl
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ M)
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (M up p) =
  cong₂ _up_
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ M)
    (rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ p)
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (M down p) =
  cong₂ _down_
    (renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ M)
    (rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ p)
renameᵗᵐ-renameᵗᵐ ρ₁ ρ₂ (blame ℓ) = refl

renameᵗᵐ-suc-extᵗ :
  (ρ : Renameᵗ) (M : Term) →
  renameᵗᵐ suc (renameᵗᵐ ρ M) ≡
  renameᵗᵐ (extᵗ ρ) (renameᵗᵐ suc M)
renameᵗᵐ-suc-extᵗ ρ M =
  trans
    (renameᵗᵐ-renameᵗᵐ ρ suc M)
    (sym (renameᵗᵐ-renameᵗᵐ suc (extᵗ ρ) M))

substᵗᵐ-renameᵗᵐ :
  (ρ : Renameᵗ) (σ : Substᵗ) (M : Term) →
  substᵗᵐ σ (renameᵗᵐ ρ M) ≡
  substᵗᵐ (λ X → σ (ρ X)) M
substᵗᵐ-renameᵗᵐ ρ σ (` x) = refl
substᵗᵐ-renameᵗᵐ ρ σ (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_
    (substᵗ-renameᵗ ρ σ A)
    (substᵗᵐ-renameᵗᵐ ρ σ M)
substᵗᵐ-renameᵗᵐ ρ σ (L · M) =
  cong₂ _·_
    (substᵗᵐ-renameᵗᵐ ρ σ L)
    (substᵗᵐ-renameᵗᵐ ρ σ M)
substᵗᵐ-renameᵗᵐ ρ σ (Λ M) =
  cong Λ_
    (trans
      (substᵗᵐ-renameᵗᵐ (extᵗ ρ) (extsᵗ σ) M)
      (substᵗᵐ-cong env M))
  where
  env : (X : TyVar) →
    extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
  env zero = refl
  env (suc X) = refl
substᵗᵐ-renameᵗᵐ ρ σ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (substᵗᵐ-renameᵗᵐ ρ σ M)
    (trans
      (substᵗ-renameᵗ (extᵗ ρ) (extsᵗ σ) B)
      (substᵗ-cong env B))
    (substᵗ-renameᵗ ρ σ T)
  where
  env : (X : TyVar) →
    extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
  env zero = refl
  env (suc X) = refl
substᵗᵐ-renameᵗᵐ ρ σ ($ κ) = refl
substᵗᵐ-renameᵗᵐ ρ σ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (substᵗᵐ-renameᵗᵐ ρ σ L)
    refl
    (substᵗᵐ-renameᵗᵐ ρ σ M)
substᵗᵐ-renameᵗᵐ ρ σ (M up p) =
  cong₂ _up_
    (substᵗᵐ-renameᵗᵐ ρ σ M)
    (subst⊑ᵗ-rename⊑ᵗ ρ σ p)
substᵗᵐ-renameᵗᵐ ρ σ (M down p) =
  cong₂ _down_
    (substᵗᵐ-renameᵗᵐ ρ σ M)
    (subst⊒ᵗ-rename⊒ᵗ ρ σ p)
substᵗᵐ-renameᵗᵐ ρ σ (blame ℓ) = refl

renameᵗᵐ-substᵗᵐ :
  (ρ : Renameᵗ) (σ : Substᵗ) (M : Term) →
  renameᵗᵐ ρ (substᵗᵐ σ M) ≡
  substᵗᵐ (λ X → renameᵗ ρ (σ X)) M
renameᵗᵐ-substᵗᵐ ρ σ (` x) = refl
renameᵗᵐ-substᵗᵐ ρ σ (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_
    (renameᵗ-substᵗ ρ σ A)
    (renameᵗᵐ-substᵗᵐ ρ σ M)
renameᵗᵐ-substᵗᵐ ρ σ (L · M) =
  cong₂ _·_
    (renameᵗᵐ-substᵗᵐ ρ σ L)
    (renameᵗᵐ-substᵗᵐ ρ σ M)
renameᵗᵐ-substᵗᵐ ρ σ (Λ M) =
  cong Λ_
    (trans
      (renameᵗᵐ-substᵗᵐ (extᵗ ρ) (extsᵗ σ) M)
      (substᵗᵐ-cong env M))
  where
  env : (X : TyVar) →
    renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡
    extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
  env zero = refl
  env (suc X) = sym (renameᵗ-suc-comm ρ (σ X))
renameᵗᵐ-substᵗᵐ ρ σ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (renameᵗᵐ-substᵗᵐ ρ σ M)
    (trans
      (renameᵗ-substᵗ (extᵗ ρ) (extsᵗ σ) B)
      (substᵗ-cong env B))
    (renameᵗ-substᵗ ρ σ T)
  where
  env : (X : TyVar) →
    renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡
    extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
  env zero = refl
  env (suc X) = sym (renameᵗ-suc-comm ρ (σ X))
renameᵗᵐ-substᵗᵐ ρ σ ($ κ) = refl
renameᵗᵐ-substᵗᵐ ρ σ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (renameᵗᵐ-substᵗᵐ ρ σ L)
    refl
    (renameᵗᵐ-substᵗᵐ ρ σ M)
renameᵗᵐ-substᵗᵐ ρ σ (M up p) =
  cong₂ _up_
    (renameᵗᵐ-substᵗᵐ ρ σ M)
    (rename⊑ᵗ-subst⊑ᵗ ρ σ p)
renameᵗᵐ-substᵗᵐ ρ σ (M down p) =
  cong₂ _down_
    (renameᵗᵐ-substᵗᵐ ρ σ M)
    (rename⊒ᵗ-subst⊒ᵗ ρ σ p)
renameᵗᵐ-substᵗᵐ ρ σ (blame ℓ) = refl

renameᵗᵐ-suc-extsᵗ :
  (σ : Substᵗ) (M : Term) →
  renameᵗᵐ suc (substᵗᵐ σ M) ≡
  substᵗᵐ (extsᵗ σ) (renameᵗᵐ suc M)
renameᵗᵐ-suc-extsᵗ σ M =
  trans
    (renameᵗᵐ-substᵗᵐ suc σ M)
    (sym (substᵗᵐ-renameᵗᵐ suc (extsᵗ σ) M))

substᵗᵐ-substᵗᵐ :
  (τ σ : Substᵗ) (M : Term) →
  substᵗᵐ τ (substᵗᵐ σ M) ≡
  substᵗᵐ (λ X → substᵗ τ (σ X)) M
substᵗᵐ-substᵗᵐ τ σ (` x) = refl
substᵗᵐ-substᵗᵐ τ σ (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_
    (substᵗ-substᵗ τ σ A)
    (substᵗᵐ-substᵗᵐ τ σ M)
substᵗᵐ-substᵗᵐ τ σ (L · M) =
  cong₂ _·_
    (substᵗᵐ-substᵗᵐ τ σ L)
    (substᵗᵐ-substᵗᵐ τ σ M)
substᵗᵐ-substᵗᵐ τ σ (Λ M) =
  cong Λ_
    (trans
      (substᵗᵐ-substᵗᵐ (extsᵗ τ) (extsᵗ σ) M)
      (substᵗᵐ-cong env M))
  where
  env : (X : TyVar) →
    substᵗ (extsᵗ τ) (extsᵗ σ X) ≡
    extsᵗ (λ Y → substᵗ τ (σ Y)) X
  env zero = refl
  env (suc X) = substᵗ-suc-renameᵗ-suc τ (σ X)
substᵗᵐ-substᵗᵐ τ σ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (substᵗᵐ-substᵗᵐ τ σ M)
    (trans
      (substᵗ-substᵗ (extsᵗ τ) (extsᵗ σ) B)
      (substᵗ-cong env B))
    (substᵗ-substᵗ τ σ T)
  where
  env : (X : TyVar) →
    substᵗ (extsᵗ τ) (extsᵗ σ X) ≡
    extsᵗ (λ Y → substᵗ τ (σ Y)) X
  env zero = refl
  env (suc X) = substᵗ-suc-renameᵗ-suc τ (σ X)
substᵗᵐ-substᵗᵐ τ σ ($ κ) = refl
substᵗᵐ-substᵗᵐ τ σ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (substᵗᵐ-substᵗᵐ τ σ L)
    refl
    (substᵗᵐ-substᵗᵐ τ σ M)
substᵗᵐ-substᵗᵐ τ σ (M up p) =
  cong₂ _up_
    (substᵗᵐ-substᵗᵐ τ σ M)
    (subst⊑ᵗ-subst⊑ᵗ τ σ p)
substᵗᵐ-substᵗᵐ τ σ (M down p) =
  cong₂ _down_
    (substᵗᵐ-substᵗᵐ τ σ M)
    (subst⊒ᵗ-subst⊒ᵗ τ σ p)
substᵗᵐ-substᵗᵐ τ σ (blame ℓ) = refl

------------------------------------------------------------------------
-- Mixed term-variable and type-variable actions commute
------------------------------------------------------------------------

renameˣᵐ-renameᵗᵐ-commute :
  (ρ : Renameˣ) (ρᵗ : Renameᵗ) (M : Term) →
  renameˣᵐ ρ (renameᵗᵐ ρᵗ M) ≡
  renameᵗᵐ ρᵗ (renameˣᵐ ρ M)
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (` x) = refl
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (ƛ A ⇒ M) =
  cong (ƛ renameᵗ ρᵗ A ⇒_)
    (renameˣᵐ-renameᵗᵐ-commute (extʳ ρ) ρᵗ M)
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (L · M) =
  cong₂ _·_
    (renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ L)
    (renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ M)
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (Λ M) =
  cong Λ_ (renameˣᵐ-renameᵗᵐ-commute ρ (extᵗ ρᵗ) M)
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ M)
    refl
    refl
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ ($ κ) = refl
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ L)
    refl
    (renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ M)
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (M up p) =
  cong₂ _up_ (renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ M) refl
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (M down p) =
  cong₂ _down_ (renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ M) refl
renameˣᵐ-renameᵗᵐ-commute ρ ρᵗ (blame ℓ) = refl

substˣ-term-renameᵗᵐ-commute-gen :
  (σ τ : Substˣ) (ρᵗ : Renameᵗ) →
  ((x : Var) → τ x ≡ renameᵗᵐ ρᵗ (σ x)) →
  (M : Term) →
  substˣ-term τ (renameᵗᵐ ρᵗ M) ≡
  renameᵗᵐ ρᵗ (substˣ-term σ M)
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (` x) = h x
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (ƛ A ⇒ M) =
  cong (ƛ renameᵗ ρᵗ A ⇒_)
    (substˣ-term-renameᵗᵐ-commute-gen
      (extˣ σ)
      (extˣ τ)
      ρᵗ
      h-ext
      M)
  where
  h-ext : (x : Var) → extˣ τ x ≡ renameᵗᵐ ρᵗ (extˣ σ x)
  h-ext zero = refl
  h-ext (suc x) =
    trans
      (cong (renameˣᵐ wkʳ) (h x))
      (renameˣᵐ-renameᵗᵐ-commute wkʳ ρᵗ (σ x))
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (L · M) =
  cong₂ _·_
    (substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h L)
    (substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h M)
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (Λ M) =
  cong Λ_
    (substˣ-term-renameᵗᵐ-commute-gen
      (↑ᵗᵐ σ)
      (↑ᵗᵐ τ)
      (extᵗ ρᵗ)
      h-up
      M)
  where
  h-up : (x : Var) → ↑ᵗᵐ τ x ≡ renameᵗᵐ (extᵗ ρᵗ) (↑ᵗᵐ σ x)
  h-up x =
    trans
      (cong (renameᵗᵐ suc) (h x))
      (renameᵗᵐ-suc-extᵗ ρᵗ (σ x))
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h M)
    refl
    refl
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h ($ κ) = refl
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h L)
    refl
    (substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h M)
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (M up p) =
  cong₂ _up_
    (substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h M)
    refl
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (M down p) =
  cong₂ _down_
    (substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h M)
    refl
substˣ-term-renameᵗᵐ-commute-gen σ τ ρᵗ h (blame ℓ) = refl

substˣ-term-renameᵗᵐ-commute :
  (σ : Substˣ) (ρᵗ : Renameᵗ) (M : Term) →
  substˣ-term (λ x → renameᵗᵐ ρᵗ (σ x)) (renameᵗᵐ ρᵗ M) ≡
  renameᵗᵐ ρᵗ (substˣ-term σ M)
substˣ-term-renameᵗᵐ-commute σ ρᵗ M =
  substˣ-term-renameᵗᵐ-commute-gen
    σ
    (λ x → renameᵗᵐ ρᵗ (σ x))
    ρᵗ
    (λ x → refl)
    M

renameˣᵐ-substᵗᵐ-commute :
  (ρ : Renameˣ) (τ : Substᵗ) (M : Term) →
  renameˣᵐ ρ (substᵗᵐ τ M) ≡
  substᵗᵐ τ (renameˣᵐ ρ M)
renameˣᵐ-substᵗᵐ-commute ρ τ (` x) = refl
renameˣᵐ-substᵗᵐ-commute ρ τ (ƛ A ⇒ M) =
  cong (ƛ substᵗ τ A ⇒_)
    (renameˣᵐ-substᵗᵐ-commute (extʳ ρ) τ M)
renameˣᵐ-substᵗᵐ-commute ρ τ (L · M) =
  cong₂ _·_
    (renameˣᵐ-substᵗᵐ-commute ρ τ L)
    (renameˣᵐ-substᵗᵐ-commute ρ τ M)
renameˣᵐ-substᵗᵐ-commute ρ τ (Λ M) =
  cong Λ_ (renameˣᵐ-substᵗᵐ-commute ρ (extsᵗ τ) M)
renameˣᵐ-substᵗᵐ-commute ρ τ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (renameˣᵐ-substᵗᵐ-commute ρ τ M)
    refl
    refl
renameˣᵐ-substᵗᵐ-commute ρ τ ($ κ) = refl
renameˣᵐ-substᵗᵐ-commute ρ τ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (renameˣᵐ-substᵗᵐ-commute ρ τ L)
    refl
    (renameˣᵐ-substᵗᵐ-commute ρ τ M)
renameˣᵐ-substᵗᵐ-commute ρ τ (M up p) =
  cong₂ _up_ (renameˣᵐ-substᵗᵐ-commute ρ τ M) refl
renameˣᵐ-substᵗᵐ-commute ρ τ (M down p) =
  cong₂ _down_ (renameˣᵐ-substᵗᵐ-commute ρ τ M) refl
renameˣᵐ-substᵗᵐ-commute ρ τ (blame ℓ) = refl

substᵗᵐ-substˣ-term-commute-gen :
  (τ : Substᵗ) (σ σ′ : Substˣ) →
  ((x : Var) → σ′ x ≡ substᵗᵐ τ (σ x)) →
  (M : Term) →
  substᵗᵐ τ (substˣ-term σ M) ≡
  substˣ-term σ′ (substᵗᵐ τ M)
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (` x) = sym (h x)
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (ƛ A ⇒ M) =
  cong (ƛ substᵗ τ A ⇒_)
    (substᵗᵐ-substˣ-term-commute-gen τ (extˣ σ) (extˣ σ′) h-ext M)
  where
  h-ext : (x : Var) → extˣ σ′ x ≡ substᵗᵐ τ (extˣ σ x)
  h-ext zero = refl
  h-ext (suc x) =
    trans
      (cong (renameˣᵐ wkʳ) (h x))
      (renameˣᵐ-substᵗᵐ-commute wkʳ τ (σ x))
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (L · M) =
  cong₂ _·_
    (substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h L)
    (substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h M)
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (Λ M) =
  cong Λ_
    (substᵗᵐ-substˣ-term-commute-gen
      (extsᵗ τ)
      (↑ᵗᵐ σ)
      (↑ᵗᵐ σ′)
      h-up
      M)
  where
  h-up : (x : Var) → ↑ᵗᵐ σ′ x ≡ substᵗᵐ (extsᵗ τ) (↑ᵗᵐ σ x)
  h-up x =
    trans
      (cong (renameᵗᵐ suc) (h x))
      (renameᵗᵐ-suc-extsᵗ τ (σ x))
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h M)
    refl
    refl
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h ($ κ) = refl
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h L)
    refl
    (substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h M)
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (M up p) =
  cong₂ _up_ (substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h M) refl
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (M down p) =
  cong₂ _down_ (substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h M) refl
substᵗᵐ-substˣ-term-commute-gen τ σ σ′ h (blame ℓ) = refl

substᵗᵐ-substˣ-term-commute :
  (τ : Substᵗ) (σ : Substˣ) (M : Term) →
  substᵗᵐ τ (substˣ-term σ M) ≡
  substˣ-term (λ x → substᵗᵐ τ (σ x)) (substᵗᵐ τ M)
substᵗᵐ-substˣ-term-commute τ σ M =
  substᵗᵐ-substˣ-term-commute-gen
    τ
    σ
    (λ x → substᵗᵐ τ (σ x))
    (λ x → refl)
    M

------------------------------------------------------------------------
-- Term-variable renaming/substitution algebra
------------------------------------------------------------------------

renˣ : Renameˣ → Substˣ
renˣ ρ x = ` (ρ x)

idˣ : Substˣ
idˣ x = ` x

infixr 50 _⨟ˣ_
_⨟ˣ_ : Substˣ → Substˣ → Substˣ
(σ ⨟ˣ τ) x = substˣ-term τ (σ x)

extʳ-comp :
  (ρ₁ ρ₂ : Renameˣ) →
  (x : Var) →
  extʳ ρ₂ (extʳ ρ₁ x) ≡ extʳ (λ y → ρ₂ (ρ₁ y)) x
extʳ-comp ρ₁ ρ₂ zero = refl
extʳ-comp ρ₁ ρ₂ (suc x) = refl

renameˣᵐ-renameˣᵐ :
  (ρ₁ ρ₂ : Renameˣ) (M : Term) →
  renameˣᵐ ρ₂ (renameˣᵐ ρ₁ M) ≡
  renameˣᵐ (λ x → ρ₂ (ρ₁ x)) M
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (` x) = refl
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (ƛ A ⇒ M) =
  cong (ƛ A ⇒_)
    (trans
      (renameˣᵐ-renameˣᵐ (extʳ ρ₁) (extʳ ρ₂) M)
      (renameˣᵐ-cong (extʳ-comp ρ₁ ρ₂) M))
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (L · M) =
  cong₂ _·_
    (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ L)
    (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ M)
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (Λ M) =
  cong Λ_
    (trans
      (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ M)
      (renameˣᵐ-cong (λ x → refl) M))
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ M)
    refl
    refl
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ ($ κ) = refl
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_
    (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ L)
    refl
    (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ M)
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (M up p) =
  cong₂ _up_ (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ M) refl
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (M down p) =
  cong₂ _down_ (renameˣᵐ-renameˣᵐ ρ₁ ρ₂ M) refl
renameˣᵐ-renameˣᵐ ρ₁ ρ₂ (blame ℓ) = refl

extˣ-extʳ :
  (ρ : Renameˣ) (σ : Substˣ) →
  (x : Var) →
  extˣ σ (extʳ ρ x) ≡ extˣ (λ y → σ (ρ y)) x
extˣ-extʳ ρ σ zero = refl
extˣ-extʳ ρ σ (suc x) = refl

renˣ-subˣ :
  (ρ : Renameˣ) (σ : Substˣ) (M : Term) →
  substˣ-term σ (renameˣᵐ ρ M) ≡
  substˣ-term (λ x → σ (ρ x)) M
renˣ-subˣ ρ σ (` x) = refl
renˣ-subˣ ρ σ (ƛ A ⇒ M) =
  cong (ƛ A ⇒_)
    (trans
      (renˣ-subˣ (extʳ ρ) (extˣ σ) M)
      (substˣ-term-cong (extˣ-extʳ ρ σ) M))
renˣ-subˣ ρ σ (L · M) =
  cong₂ _·_ (renˣ-subˣ ρ σ L) (renˣ-subˣ ρ σ M)
renˣ-subˣ ρ σ (Λ M) =
  cong Λ_
    (trans
      (renˣ-subˣ ρ (↑ᵗᵐ σ) M)
      (substˣ-term-cong (λ x → refl) M))
renˣ-subˣ ρ σ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_] (renˣ-subˣ ρ σ M) refl refl
renˣ-subˣ ρ σ ($ κ) = refl
renˣ-subˣ ρ σ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (renˣ-subˣ ρ σ L) refl (renˣ-subˣ ρ σ M)
renˣ-subˣ ρ σ (M up p) = cong₂ _up_ (renˣ-subˣ ρ σ M) refl
renˣ-subˣ ρ σ (M down p) = cong₂ _down_ (renˣ-subˣ ρ σ M) refl
renˣ-subˣ ρ σ (blame ℓ) = refl

extʳ-extˣ :
  (ρ : Renameˣ) (σ : Substˣ) →
  (x : Var) →
  renameˣᵐ (extʳ ρ) (extˣ σ x) ≡
  extˣ (λ y → renameˣᵐ ρ (σ y)) x
extʳ-extˣ ρ σ zero = refl
extʳ-extˣ ρ σ (suc x) =
  trans
    (renameˣᵐ-renameˣᵐ wkʳ (extʳ ρ) (σ x))
    (trans
      (renameˣᵐ-cong (λ y → refl) (σ x))
      (sym (renameˣᵐ-renameˣᵐ ρ wkʳ (σ x))))

subˣ-renˣ :
  (ρ : Renameˣ) (σ : Substˣ) (M : Term) →
  renameˣᵐ ρ (substˣ-term σ M) ≡
  substˣ-term (λ x → renameˣᵐ ρ (σ x)) M
subˣ-renˣ ρ σ (` x) = refl
subˣ-renˣ ρ σ (ƛ A ⇒ M) =
  cong (ƛ A ⇒_)
    (trans
      (subˣ-renˣ (extʳ ρ) (extˣ σ) M)
      (substˣ-term-cong (extʳ-extˣ ρ σ) M))
subˣ-renˣ ρ σ (L · M) =
  cong₂ _·_ (subˣ-renˣ ρ σ L) (subˣ-renˣ ρ σ M)
subˣ-renˣ ρ σ (Λ M) =
  cong Λ_
    (trans
      (subˣ-renˣ ρ (↑ᵗᵐ σ) M)
      (substˣ-term-cong h-up M))
  where
  h-up : (x : Var) →
    renameˣᵐ ρ (↑ᵗᵐ σ x) ≡ ↑ᵗᵐ (λ y → renameˣᵐ ρ (σ y)) x
  h-up x = renameˣᵐ-renameᵗᵐ-commute ρ suc (σ x)
subˣ-renˣ ρ σ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_] (subˣ-renˣ ρ σ M) refl refl
subˣ-renˣ ρ σ ($ κ) = refl
subˣ-renˣ ρ σ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (subˣ-renˣ ρ σ L) refl (subˣ-renˣ ρ σ M)
subˣ-renˣ ρ σ (M up p) = cong₂ _up_ (subˣ-renˣ ρ σ M) refl
subˣ-renˣ ρ σ (M down p) = cong₂ _down_ (subˣ-renˣ ρ σ M) refl
subˣ-renˣ ρ σ (blame ℓ) = refl

extˣ-subˣ :
  (σ τ : Substˣ) →
  (x : Var) →
  substˣ-term (extˣ τ) (extˣ σ x) ≡ extˣ (σ ⨟ˣ τ) x
extˣ-subˣ σ τ zero = refl
extˣ-subˣ σ τ (suc x) =
  trans
    (renˣ-subˣ wkʳ (extˣ τ) (σ x))
    (trans
      (substˣ-term-cong (λ y → refl) (σ x))
      (sym (subˣ-renˣ wkʳ τ (σ x))))

subˣ-subˣ :
  (σ τ : Substˣ) (M : Term) →
  substˣ-term τ (substˣ-term σ M) ≡ substˣ-term (σ ⨟ˣ τ) M
subˣ-subˣ σ τ (` x) = refl
subˣ-subˣ σ τ (ƛ A ⇒ M) =
  cong (ƛ A ⇒_)
    (trans
      (subˣ-subˣ (extˣ σ) (extˣ τ) M)
      (substˣ-term-cong (extˣ-subˣ σ τ) M))
subˣ-subˣ σ τ (L · M) =
  cong₂ _·_ (subˣ-subˣ σ τ L) (subˣ-subˣ σ τ M)
subˣ-subˣ σ τ (Λ M) =
  cong Λ_
    (trans
      (subˣ-subˣ (↑ᵗᵐ σ) (↑ᵗᵐ τ) M)
      (substˣ-term-cong h-up M))
  where
  h-up : (x : Var) →
    substˣ-term (↑ᵗᵐ τ) (↑ᵗᵐ σ x) ≡ ↑ᵗᵐ (σ ⨟ˣ τ) x
  h-up x = substˣ-term-renameᵗᵐ-commute τ suc (σ x)
subˣ-subˣ σ τ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_] (subˣ-subˣ σ τ M) refl refl
subˣ-subˣ σ τ ($ κ) = refl
subˣ-subˣ σ τ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (subˣ-subˣ σ τ L) refl (subˣ-subˣ σ τ M)
subˣ-subˣ σ τ (M up p) = cong₂ _up_ (subˣ-subˣ σ τ M) refl
subˣ-subˣ σ τ (M down p) = cong₂ _down_ (subˣ-subˣ σ τ M) refl
subˣ-subˣ σ τ (blame ℓ) = refl

extˣ-id : (x : Var) → extˣ idˣ x ≡ idˣ x
extˣ-id zero = refl
extˣ-id (suc x) = refl

↑ᵗᵐ-id : (x : Var) → ↑ᵗᵐ idˣ x ≡ idˣ x
↑ᵗᵐ-id x = refl

subˣ-id : (M : Term) → substˣ-term idˣ M ≡ M
subˣ-id (` x) = refl
subˣ-id (ƛ A ⇒ M) =
  cong (ƛ A ⇒_)
    (trans
      (substˣ-term-cong extˣ-id M)
      (subˣ-id M))
subˣ-id (L · M) = cong₂ _·_ (subˣ-id L) (subˣ-id M)
subˣ-id (Λ M) =
  cong Λ_
    (trans
      (substˣ-term-cong ↑ᵗᵐ-id M)
      (subˣ-id M))
subˣ-id (M ⦂∀ B [ T ]) = cong₃ _⦂∀_[_] (subˣ-id M) refl refl
subˣ-id ($ κ) = refl
subˣ-id (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (subˣ-id L) refl (subˣ-id M)
subˣ-id (M up p) = cong₂ _up_ (subˣ-id M) refl
subˣ-id (M down p) = cong₂ _down_ (subˣ-id M) refl
subˣ-id (blame ℓ) = refl

extˣ-renˣ :
  (ρ : Renameˣ) →
  (x : Var) →
  extˣ (renˣ ρ) x ≡ renˣ (extʳ ρ) x
extˣ-renˣ ρ zero = refl
extˣ-renˣ ρ (suc x) = refl

↑ᵗᵐ-renˣ :
  (ρ : Renameˣ) →
  (x : Var) →
  ↑ᵗᵐ (renˣ ρ) x ≡ renˣ ρ x
↑ᵗᵐ-renˣ ρ x = refl

substˣ-renˣ :
  (ρ : Renameˣ) (M : Term) →
  substˣ-term (renˣ ρ) M ≡ renameˣᵐ ρ M
substˣ-renˣ ρ (` x) = refl
substˣ-renˣ ρ (ƛ A ⇒ M) =
  cong (ƛ A ⇒_)
    (trans
      (substˣ-term-cong (extˣ-renˣ ρ) M)
      (substˣ-renˣ (extʳ ρ) M))
substˣ-renˣ ρ (L · M) =
  cong₂ _·_ (substˣ-renˣ ρ L) (substˣ-renˣ ρ M)
substˣ-renˣ ρ (Λ M) =
  cong Λ_
    (trans
      (substˣ-term-cong (↑ᵗᵐ-renˣ ρ) M)
      (substˣ-renˣ ρ M))
substˣ-renˣ ρ (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_] (substˣ-renˣ ρ M) refl refl
substˣ-renˣ ρ ($ κ) = refl
substˣ-renˣ ρ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (substˣ-renˣ ρ L) refl (substˣ-renˣ ρ M)
substˣ-renˣ ρ (M up p) = cong₂ _up_ (substˣ-renˣ ρ M) refl
substˣ-renˣ ρ (M down p) = cong₂ _down_ (substˣ-renˣ ρ M) refl
substˣ-renˣ ρ (blame ℓ) = refl

------------------------------------------------------------------------
-- Single-variable and single-type substitution APIs
------------------------------------------------------------------------

infixl 8 _[_]
infixl 8 _[_]ᵀ

singleVarEnv : Term → Substˣ
singleVarEnv V zero = V
singleVarEnv V (suc x) = ` x

infixr 5 _•ˣ_
_•ˣ_ : Term → Substˣ → Substˣ
(V •ˣ σ) zero = V
(V •ˣ σ) (suc x) = σ x

singleVarEnv-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {Γ} (singleVarEnv V)
singleVarEnv-wt {V = V} V⊢ Z = V⊢
singleVarEnv-wt V⊢ (S h) = ⊢` h

_[_] : Term → Term → Term
N [ V ] = substˣ-term (singleVarEnv V) N

[]-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{N V : Term}{A B : Ty} →
  (N⊢ : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ N ⦂ B) →
  (V⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (N [ V ]) ⦂ B
[]-wt {V = V} N⊢ V⊢ =
  substˣ-term-wt (singleVarEnv V) (singleVarEnv-wt V⊢) N⊢

extˣ-sub-cons :
  (σ : Substˣ) (N V : Term) →
  (substˣ-term (extˣ σ) N) [ V ] ≡ substˣ-term (V •ˣ σ) N
extˣ-sub-cons σ N V =
  trans
    (subˣ-subˣ (extˣ σ) (singleVarEnv V) N)
    (substˣ-term-cong eq N)
  where
  eq : (x : Var) → ((extˣ σ) ⨟ˣ (singleVarEnv V)) x ≡ (V •ˣ σ) x
  eq zero = refl
  eq (suc x) =
    trans
      (renˣ-subˣ wkʳ (singleVarEnv V) (σ x))
      (trans
        (substˣ-term-cong (λ y → refl) (σ x))
        (subˣ-id (σ x)))

map-singleTyEnv-⤊ᵗ : (T : Ty) (Γ : Ctx) →
  map (substᵗ (singleTyEnv T)) (⤊ᵗ Γ) ≡ Γ
map-singleTyEnv-⤊ᵗ T [] = refl
map-singleTyEnv-⤊ᵗ T (A ∷ Γ) =
  cong₂ _∷_
    (open-renᵗ-suc A T)
    (map-singleTyEnv-⤊ᵗ T Γ)

_[_]ᵀ : Term → Ty → Term
M [ T ]ᵀ = substᵗᵐ (singleTyEnv T) M

[]ᵀ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (M⊢ : (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ M ⦂ A) →
  (T : Ty) →
  (wfT : WfTy Δ Ψ T) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M [ T ]ᵀ) ⦂ (A [ T ]ᵗ)
[]ᵀ-wt {Σ = Σ} {Γ = Γ} {M = M} {A = A} M⊢ T wfT =
  cong-⊢⦂
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)
    (map-singleTyEnv-⤊ᵗ T Γ)
    refl
    refl
    (substᵗ-wt (singleTyEnv T) (singleTyEnv-Wf T wfT) M⊢)

------------------------------------------------------------------------
-- Permission-list well-formedness and practical renaming shortcut
------------------------------------------------------------------------

PermWf : SealCtx → List CastPerm → Set
PermWf Ψ P = ∀ {α} → α ∈ P → α < Ψ

PermWf-every :
  ∀ {Ψ} →
  PermWf Ψ (every Ψ)
PermWf-every = every-index

PermWf-ext-true :
  ∀ {Ψ}{P : List CastPerm} →
  PermWf Ψ P →
  PermWf (suc Ψ) (conv ∷ P)
PermWf-ext-true wfP {zero} here-conv = z<s
PermWf-ext-true wfP {suc α} (there p) = s<s (wfP p)

PermWf-ext-false :
  ∀ {Ψ}{P : List CastPerm} →
  PermWf Ψ P →
  PermWf (suc Ψ) (cast-tag ∷ P)
PermWf-ext-false wfP {zero} ()
PermWf-ext-false wfP {suc α} (there p) = s<s (wfP p)

RenOk-every-from-PermWf :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} {P : List CastPerm} →
  SealRenameWf Ψ Ψ′ ρ →
  PermWf Ψ P →
  RenOk ρ P (every Ψ′)
RenOk-every-from-PermWf hρ wfP p = every-member _ (hρ (wfP p))

RenOk-ext-true-every :
  ∀ {Ψ′}{ρ : Renameˢ}{P : List CastPerm} →
  RenOk ρ P (every Ψ′) →
  RenOk (extˢ ρ) (conv ∷ P) (every (suc Ψ′))
RenOk-ext-true-every ok {zero} here-conv = here-conv
RenOk-ext-true-every ok {suc α} (there p) = there (ok p)

RenOk-ext-false-every :
  ∀ {Ψ′}{ρ : Renameˢ}{P : List CastPerm} →
  RenOk ρ P (every Ψ′) →
  RenOk (extˢ ρ) (cast-tag ∷ P) (every (suc Ψ′))
RenOk-ext-false-every ok {zero} ()
RenOk-ext-false-every ok {suc α} (there p) = there (ok p)

pred-< :
  ∀ {α Ψ} →
  suc α < suc Ψ →
  α < Ψ
pred-< (s<s α<Ψ) = α<Ψ

tail-PermWf :
  ∀ {Ψ}{b : CastPerm}{P : List CastPerm} →
  PermWf (suc Ψ) (b ∷ P) →
  PermWf Ψ P
tail-PermWf wf {α} p = pred-< (wf (there p))

shift-Renameˢ :
  Renameˢ →
  Renameˢ
shift-Renameˢ ρ α = ρ (suc α)

shift-SealRenameWf :
  ∀ {Ψ Ψ′}{ρ : Renameˢ} →
  SealRenameWf (suc Ψ) Ψ′ ρ →
  SealRenameWf Ψ Ψ′ (shift-Renameˢ ρ)
shift-SealRenameWf hρ α<Ψ = hρ (s<s α<Ψ)

setPerm :
  Seal →
  List CastPerm →
  List CastPerm
setPerm zero [] = conv ∷ []
setPerm zero (b ∷ P) = conv ∷ P
setPerm (suc α) [] = cast-tag ∷ setPerm α []
setPerm (suc α) (b ∷ P) = b ∷ setPerm α P

setPerm-hit :
  (α : Seal) →
  (P : List CastPerm) →
  α ∈ setPerm α P
setPerm-hit zero [] = here-conv
setPerm-hit zero (b ∷ P) = here-conv
setPerm-hit (suc α) [] = there (setPerm-hit α [])
setPerm-hit (suc α) (b ∷ P) = there (setPerm-hit α P)

setPerm-preserve :
  ∀ {α β}{P : List CastPerm} →
  β ∈ P →
  β ∈ setPerm α P
setPerm-preserve {α = zero} {β = zero} here-conv = here-conv
setPerm-preserve {α = zero} {β = zero} here-seal = here-conv
setPerm-preserve {α = zero} {β = suc β} (there p) = there p
setPerm-preserve {α = suc α} {β = zero} here-conv = here-conv
setPerm-preserve {α = suc α} {β = zero} here-seal = here-seal
setPerm-preserve {α = suc α} {β = suc β} (there p) =
  there (setPerm-preserve {α = α} {β = β} p)

renamePerm :
  ∀ {Ψ Ψ′} →
  (ρ : Renameˢ) →
  SealRenameWf Ψ Ψ′ ρ →
  List CastPerm →
  List CastPerm
renamePerm {Ψ = zero} {Ψ′ = Ψ′} ρ hρ P = none Ψ′
renamePerm {Ψ = suc Ψ} ρ hρ [] =
  renamePerm
    {Ψ = Ψ}
    (shift-Renameˢ ρ)
    (shift-SealRenameWf hρ)
    []
renamePerm {Ψ = suc Ψ} ρ hρ (cast-tag ∷ P) =
  renamePerm
    {Ψ = Ψ}
    (shift-Renameˢ ρ)
    (shift-SealRenameWf hρ)
    P
renamePerm {Ψ = suc Ψ} ρ hρ (conv ∷ P) =
  setPerm
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)
renamePerm {Ψ = suc Ψ} ρ hρ (cast-seal ∷ P) =
  setPerm
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)

renamePerm-ok :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} {P : List CastPerm} →
  (hρ : SealRenameWf Ψ Ψ′ ρ) →
  PermWf Ψ P →
  RenOk ρ P (renamePerm ρ hρ P)
renamePerm-ok {Ψ = zero} hρ wfP {α} α∈P with wfP α∈P
renamePerm-ok {Ψ = zero} hρ wfP {α} α∈P | ()
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = []} hρ wfP {α} ()
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-tag ∷ P} hρ wfP {zero} ()
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-tag ∷ P} hρ wfP {suc α} (there α∈P) =
  renamePerm-ok
    (shift-SealRenameWf hρ)
    (tail-PermWf wfP)
    α∈P
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = conv ∷ P} hρ wfP {zero} here-conv =
  setPerm-hit
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = conv ∷ P} hρ wfP {suc α} (there α∈P) =
  setPerm-preserve
    (renamePerm-ok
      (shift-SealRenameWf hρ)
      (tail-PermWf wfP)
      α∈P)
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-seal ∷ P} hρ wfP {zero} here-seal =
  setPerm-hit
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-seal ∷ P} hρ wfP {suc α} (there α∈P) =
  setPerm-preserve
    (renamePerm-ok
      (shift-SealRenameWf hρ)
      (tail-PermWf wfP)
      α∈P)
