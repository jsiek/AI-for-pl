module Terms where

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Relation.Binary.HeterogeneousEquality as H
            using (_≅_) renaming (cong to congʰ)

open import Types
open import Ctx
open import Heq using (Hcong₁; Hcong₂; Hcong₃; Hcong₄; Hcong₅)

infix  4 _;_⊢_
infix  9 `_
infix  5 ƛ_˙_
infixl 7 _·_
infixl 7 _∙_
infix  8 `suc_

data _;_⊢_ (Δ : TyCtx) (Γ : Ctx Δ) : Type Δ → Set where

  `true :
      --------------- (T-True)
    Δ ; Γ ⊢ `Bool

  `false :
      ---------------- (T-False)
    Δ ; Γ ⊢ `Bool

  `zero :
      --------------- (T-Zero)
    Δ ; Γ ⊢ `Nat

  `suc_ :
    Δ ; Γ ⊢ `Nat
      ----------------- (T-Suc)
    → Δ ; Γ ⊢ `Nat

  `case-nat : ∀ {A}
    → Δ ; Γ ⊢ `Nat
    → Δ ; Γ ⊢ A
    → Δ ; Γ , `Nat ⊢ A
      ---------------------- (T-CaseNat)
    → Δ ; Γ ⊢ A

  `if_then_else : ∀ {A}
    → Δ ; Γ ⊢ `Bool
    → Δ ; Γ ⊢ A
    → Δ ; Γ ⊢ A
      ---------------------- (T-If)
    → Δ ; Γ ⊢ A

  `_ : ∀ {A}
    → Γ ∋ A
      --------------- (T-Var)
    → Δ ; Γ ⊢ A

  ƛ_˙_ : ∀ {B}
    → (A : Type Δ)
    → Δ ; Γ , A ⊢ B
      ------------------ (T-Abs)
    → Δ ; Γ ⊢ A ⇒ B

  _·_ : ∀ {A B}
    → Δ ; Γ ⊢ A ⇒ B
    → Δ ; Γ ⊢ A
      ------------------ (T-App)
    → Δ ; Γ ⊢ B

  -- | New rules for System F | --
  Λ_ : ∀ {A}
    → Δ ,α ; ⇑ᶜ Γ ⊢ A
      --------------------- (T-TAbs)
    → Δ ; Γ ⊢ `∀ A

  _∙_    : ∀ {A : Type (Δ ,α)}
    → Δ ; Γ ⊢ (`∀ A)
    → (B : Type Δ)
      --------------------- (T-TApp)
    → Δ ; Γ ⊢ A [ B ]ᵗ


------------------------------------
-- | Substitute types into term | --
------------------------------------

renameCtx-extᵗ-⇑ᶜ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (Γ : Ctx Δ)
  → renameCtx (extᵗ ρ) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx ρ Γ)
renameCtx-extᵗ-⇑ᶜ ρ ∅ = refl
renameCtx-extᵗ-⇑ᶜ ρ (Γ , A)
  rewrite renameCtx-extᵗ-⇑ᶜ ρ Γ
        | renameᵗ-shift ρ A = refl

renameᵀ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ' ; renameCtx ρ Γ ⊢ renameᵗ ρ A
renameᵀ ρ `zero         = `zero
renameᵀ ρ `true         = `true
renameᵀ ρ `false        = `false
renameᵀ ρ (`suc M)      = `suc (renameᵀ ρ M)
renameᵀ ρ (`case-nat L M N) = `case-nat (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (`if_then_else L M N) = `if_then_else (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (` x)         = ` (renameᵗ-∋ ρ x)
renameᵀ ρ (ƛ A ˙ N)     = ƛ renameᵗ ρ A ˙ (renameᵀ ρ N)
renameᵀ ρ (L · M)       = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N)         = Λ (substEq (_ ;_⊢ _) (renameCtx-extᵗ-⇑ᶜ ρ _) (renameᵀ (extᵗ ρ) N))
renameᵀ ρ (_∙_ {A = A₁} M A) =
  substEq (λ T → _ ; _ ⊢ T) (sym (renameᵗ-[]ᵗ ρ A₁ A)) (renameᵀ ρ M ∙ renameᵗ ρ A)

substCtx-extsᵗ-⇑ᶜ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (Γ : Ctx Δ)
  → substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ ⇑ᶜ (substCtx σ Γ)
substCtx-extsᵗ-⇑ᶜ σ ∅ = refl
substCtx-extsᵗ-⇑ᶜ σ (Γ , A)
  rewrite substCtx-extsᵗ-⇑ᶜ σ Γ
        | ren-subᵗ S_ (extsᵗ σ) A
        | sym (sub-renᵗ S_ σ A) = refl

substᵀ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ' ; substCtx σ Γ ⊢ substᵗ σ A
substᵀ σ `zero             = `zero
substᵀ σ `true             = `true
substᵀ σ `false            = `false
substᵀ σ (`suc M)          = `suc (substᵀ σ M)
substᵀ σ (`case-nat L M N) = `case-nat (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (`if_then_else L M N) = `if_then_else (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (` x)             = ` (substᵗ-∋ σ x)
substᵀ σ (ƛ A ˙ N)         = ƛ substᵗ σ A ˙ (substᵀ σ N)
substᵀ σ (L · M)           = substᵀ σ L · substᵀ σ M
substᵀ σ {Γ = Γ} (Λ N) = Λ (substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ σ Γ) (substᵀ (extsᵗ σ) {Γ = ⇑ᶜ Γ} N))
substᵀ {Δ = Δ} {Δ' = Δ'} σ {Γ = Γ} (_∙_ {A = A₁} M B) =
  substEq (λ T → Δ' ; substCtx σ Γ ⊢ T) (sym (substᵗ-[]ᵗ σ A₁ B)) (substᵀ σ M ∙ substᵗ σ B)

substCtx-σ₀-⇑ᶜ-cancel : ∀ {Δ} (Γ : Ctx Δ) (B : Type Δ)
  → substCtx (σ₀ᵗ B) (⇑ᶜ Γ) ≡ Γ
substCtx-σ₀-⇑ᶜ-cancel ∅ B = refl
substCtx-σ₀-⇑ᶜ-cancel (Γ , A) B
  rewrite substCtx-σ₀-⇑ᶜ-cancel Γ B
        | ren-subᵗ S_ (σ₀ᵗ B) A
        | sub-idᵗ A = refl

_[_]ᵀ : ∀ {Δ} {Γ : Ctx Δ} {A : Type (Δ ,α)}
  → Δ ,α ; ⇑ᶜ Γ ⊢ A
  → (B : Type Δ)
    ---------------------------
  → Δ ; Γ ⊢ A [ B ]ᵗ
_[_]ᵀ {Γ = Γ} N B = substEq (_ ;_⊢ _) (substCtx-σ₀-⇑ᶜ-cancel Γ B) (substᵀ (σ₀ᵗ B) {Γ = ⇑ᶜ Γ} N)


------------------------------------
-- | Substitute terms into term | --
------------------------------------

_→ʳ_ : ∀ {Δ} → Ctx Δ → Ctx Δ → Set
_→ʳ_ Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

idʳ : ∀ {Δ} {Γ : Ctx Δ} → Γ →ʳ Γ
idʳ x = x

ext : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ʳ Γ'
  → (Γ , A) →ʳ (Γ' , A)
ext ρ Z      = Z
ext ρ (S x)  = S (ρ x)

⇑ʳ : ∀ {Δ} {Γ Γ' : Ctx Δ}
  → Γ →ʳ Γ'
  → (⇑ᶜ Γ) →ʳ (⇑ᶜ Γ')
⇑ʳ {Γ = ∅}     ρ ()
⇑ʳ {Γ = Γ , A} ρ Z      = renameᵗ-∋ S_ (ρ Z)
⇑ʳ {Γ = Γ , A} ρ (S x)  = ⇑ʳ (λ y → ρ (S y)) x

rename : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ʳ Γ'
  → Δ ; Γ ⊢ A
  → Δ ; Γ' ⊢ A
rename ρ `zero        = `zero
rename ρ `true        = `true
rename ρ `false       = `false
rename ρ (`suc M)     = `suc (rename ρ M)
rename ρ (`case-nat L M N) = `case-nat (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (`if_then_else L M N) = `if_then_else (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (` x)        = ` (ρ x)
rename ρ (ƛ _ ˙ N)    = ƛ _ ˙ (rename (ext ρ) N)
rename ρ (L · M)      = rename ρ L · rename ρ M
rename ρ (Λ N)        = Λ (rename (⇑ʳ ρ) N)
rename ρ (M ∙ B)      = rename ρ M ∙ B

_→ˢ_ : ∀ {Δ} → Ctx Δ → Ctx Δ → Set
_→ˢ_ Γ Γ' = ∀ {A} → Γ ∋ A → _ ; Γ' ⊢ A

ren : ∀ {Δ} {Γ Γ' : Ctx Δ} → Γ →ʳ Γ' → Γ →ˢ Γ'
ren ρ x = ` (ρ x)

infixr 6 _•_

_•_ : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Δ ; Γ' ⊢ A
  → Γ →ˢ Γ'
  → (Γ , A) →ˢ Γ'
(M • σ) Z      = M
(M • σ) (S x)  = σ x

id : ∀ {Δ} {Γ : Ctx Δ} → Γ →ˢ Γ
id x = ` x

↑ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Γ →ˢ (Γ , A)
↑ x = ` (S x)

⇑ : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ ; Γ , B ⊢ A
⇑ M = rename S_ M

exts : ∀ {Δ} {Γ Δ' : Ctx Δ} {A : Type Δ}
  → Γ →ˢ Δ'
  → (Γ , A) →ˢ (Δ' , A)
exts σ Z      = ` Z
exts σ (S x)  = ⇑ (σ x)

exts-id-id : ∀ {Δ Γ A B} → exts {A = A} (id {Δ} {Γ}) {B} ≡ id {Δ} {Γ , A} {B}
exts-id-id = extensionality λ where
  Z      → refl
  (S x)  → refl

⇑ᵀ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Δ ,α ; ⇑ᶜ Γ ⊢ renameᵗ S_ A
⇑ᵀ = renameᵀ S_

⇑ˢ : ∀ {Δ} {Γ Δ' : Ctx Δ}
  → Γ →ˢ Δ'
  → (⇑ᶜ Γ) →ˢ (⇑ᶜ Δ')
⇑ˢ {Γ = ∅} σ ()
⇑ˢ {Γ = Γ , A} σ Z       = ⇑ᵀ (σ Z)
⇑ˢ {Γ = Γ , A} σ (S x)   = ⇑ˢ (λ y → σ (S y)) x

private
  ⇑ʳ-S : ∀ {Δ} {Γ Γ' : Ctx Δ} {C : Type Δ} {B : Type (Δ ,α)}
    → (ρ : Γ →ʳ Γ')
    → (x : ⇑ᶜ Γ ∋ B)
    → ⇑ʳ (λ y → S_ {B = C} (ρ y)) x ≡ S_ {B = renameᵗ S_ C} (⇑ʳ ρ x)
  ⇑ʳ-S {Γ = ∅} ρ ()
  ⇑ʳ-S {Γ = Γ , A} ρ Z = refl
  ⇑ʳ-S {Γ = Γ , A} {Γ' = Γ'} {C = C} ρ (S x)
    rewrite ⇑ʳ-S {Γ = Γ} {Γ' = Γ'} {C = C} (λ y → ρ (S_ {B = A} y)) x = refl

⇑ʳ-id-id : ∀ {Δ Γ A} (x : ⇑ᶜ Γ ∋ A) → ⇑ʳ idʳ x ≡ idʳ {Δ = Δ ,α} {Γ = ⇑ᶜ Γ} x
⇑ʳ-id-id {Γ = ∅} ()
⇑ʳ-id-id {Γ = Γ , B} Z = refl
⇑ʳ-id-id {Δ} {Γ = Γ , B} (S x) rewrite ⇑ʳ-S {C = B} (idʳ {Δ} {Γ}) x
        | ⇑ʳ-id-id {Δ} {Γ} x = refl

private
  ⇑ˢ-ren : ∀ {Δ} {Γ Γ' : Ctx Δ} (ρ : Γ →ʳ Γ') {A}
    → (x : ⇑ᶜ Γ ∋ A)
    → ⇑ˢ (ren ρ) x ≡ ren (⇑ʳ ρ) x
  ⇑ˢ-ren {Γ = ∅} ρ ()
  ⇑ˢ-ren {Γ = Γ , B} ρ Z = refl
  ⇑ˢ-ren {Γ = Γ , B} ρ (S x) rewrite ⇑ˢ-ren (λ y → ρ (S y)) x = refl

⇑ˢ-id-id : ∀ {Δ Γ A} (x : ⇑ᶜ Γ ∋ A) → ⇑ˢ (id {Δ} {Γ}) x ≡ id {Δ = Δ ,α} {Γ = ⇑ᶜ Γ} x
⇑ˢ-id-id x rewrite ⇑ˢ-ren idʳ x | ⇑ʳ-id-id x = refl

subst : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ˢ Γ'
  → Δ ; Γ ⊢ A
  → Δ ; Γ' ⊢ A
subst σ `zero        = `zero
subst σ `true        = `true
subst σ `false       = `false
subst σ (`suc M)     = `suc (subst σ M)
subst σ (`case-nat L M N) = `case-nat (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (`if_then_else L M N) = `if_then_else (subst σ L) (subst σ M) (subst σ N)
subst σ (` x)        = σ x
subst σ (ƛ A ˙ N)    = ƛ A ˙ (subst (exts σ) N)
subst σ (L · M)      = subst σ L · subst σ M
subst σ (Λ N)        = Λ (subst (⇑ˢ σ) N)
subst σ (M ∙ B)      = subst σ M ∙ B

exts-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ} {σ τ : Γ →ˢ Γ'}
  → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
  → ∀ {B} (x : Γ , A ∋ B)
  → exts σ x ≡ exts τ x
exts-cong h Z = refl
exts-cong h (S x) = cong ⇑ (h x)

⇑ˢ-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {σ τ : Γ →ˢ Γ'}
  → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
  → ∀ {B} (x : ⇑ᶜ Γ ∋ B)
  → ⇑ˢ σ x ≡ ⇑ˢ τ x
⇑ˢ-cong {Γ = ∅} h ()
⇑ˢ-cong {Γ = Γ , A} h Z = cong ⇑ᵀ (h Z)
⇑ˢ-cong {Γ = Γ , A} {σ = σ} {τ = τ} h (S x) =
  ⇑ˢ-cong {σ = λ y → σ (S y)} {τ = λ y → τ (S y)} (λ y → h (S y)) x

subst-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ} {σ τ : Γ →ˢ Γ'}
  → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
  → (M : Δ ; Γ ⊢ A)
  → subst σ M ≡ subst τ M
subst-cong h `zero = refl
subst-cong h `true = refl
subst-cong h `false = refl
subst-cong h (`suc M) = cong `suc_ (subst-cong h M)
subst-cong {Γ = Γ} {σ = σ} {τ = τ} h (`case-nat L M N)
  rewrite subst-cong h L
        | subst-cong h M
        | subst-cong (exts-cong {A = `Nat} h) N = refl
subst-cong h (`if_then_else L M N)
  rewrite subst-cong h L
        | subst-cong h M
        | subst-cong h N = refl
subst-cong h (` x) = h x
subst-cong {A = A ⇒ B} h (ƛ A ˙ N) = cong (ƛ A ˙_) (subst-cong (exts-cong {A = A} h) N)
subst-cong h (L · M) = cong₂ _·_ (subst-cong h L) (subst-cong h M)
subst-cong h (Λ N) = cong Λ_ (subst-cong (⇑ˢ-cong h) N)
subst-cong h (M ∙ B) = cong (_∙ B) (subst-cong h M)

sub-id : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A)
    ---------------------------------
  → subst id M ≡ M
sub-id `zero = refl
sub-id `true = refl
sub-id `false = refl
sub-id (`suc M) rewrite sub-id M = refl
sub-id {Δ = Δ} {Γ = Γ} {A = A} (`case-nat L M N) rewrite sub-id L | sub-id M =
  cong (`case-nat L M)
    (trans (subst-cong exts-id N)
           (sub-id N))
  where
  exts-id : ∀ {B} (x : Γ , `Nat ∋ B) → exts (id {Δ} {Γ}) x ≡ id {Δ} {Γ , `Nat} x
  exts-id Z = refl
  exts-id (S x) = refl
sub-id (`if_then_else L M N) rewrite sub-id L | sub-id M | sub-id N = refl
sub-id (` x) = refl
sub-id {Δ = Δ} {Γ = Γ} {A = A ⇒ B} (ƛ A ˙ M) =
  cong (ƛ A ˙_)
    (trans (subst-cong exts-id M)
           (sub-id M))
  where
  exts-id : ∀ {C} (x : Γ , A ∋ C) → exts (id {Δ} {Γ}) x ≡ id {Δ} {Γ , A} x
  exts-id Z = refl
  exts-id (S x) = refl
sub-id (M · M₁) rewrite sub-id M | sub-id M₁ = refl
sub-id (Λ M) = cong Λ_ (trans (subst-cong ⇑ˢ-id-id M) (sub-id M))
sub-id (M ∙ B) rewrite sub-id M = refl

infixr 5 _⨟_

_⨟_ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} → Γ₁ →ˢ Γ₂ → Γ₂ →ˢ Γ₃ → Γ₁ →ˢ Γ₃
(σ ⨟ τ) x = subst τ (σ x)

σ₀ : ∀ {Δ Γ A} → Δ ; Γ ⊢ A → (Γ , A) →ˢ Γ
σ₀ M = M • id

_[_] : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ}
  → Δ ; Γ , A ⊢ B
  → Δ ; Γ ⊢ A
    ------------------
  → Δ ; Γ ⊢ B
_[_] N M = subst (σ₀ M) N

--------------------------------------------------------------------------------
-- Commuting theorems: renaming (term level)
--------------------------------------------------------------------------------

ext-cong : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A : Type Δ}
  {ρ ρ' : Γ₁ →ʳ Γ₂}
  → (∀ {B} (x : Γ₁ ∋ B) → ρ x ≡ ρ' x)
  → ∀ {B} (x : Γ₁ , A ∋ B)
  → ext ρ x ≡ ext ρ' x
ext-cong h Z = refl
ext-cong h (S x) = cong S_ (h x)

⇑ʳ-cong : ∀ {Δ} {Γ Γ' : Ctx Δ}
  {ρ ρ' : Γ →ʳ Γ'}
  → (∀ {B} (x : Γ ∋ B) → ρ x ≡ ρ' x)
  → ∀ {B} (x : ⇑ᶜ Γ ∋ B)
  → ⇑ʳ ρ x ≡ ⇑ʳ ρ' x
⇑ʳ-cong {Γ = ∅} h ()
⇑ʳ-cong {Γ = Γ , A} h Z = cong (renameᵗ-∋ S_) (h Z)
⇑ʳ-cong {Γ = Γ , A} {ρ = ρ} {ρ'} h (S x) =
  ⇑ʳ-cong {ρ = λ y → ρ (S y)} {ρ' = λ y → ρ' (S y)} (λ y → h (S y)) x

rename-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  {ρ ρ' : Γ →ʳ Γ'}
  → (∀ {B} (x : Γ ∋ B) → ρ x ≡ ρ' x)
  → (M : Δ ; Γ ⊢ A)
  → rename ρ M ≡ rename ρ' M
rename-cong h `zero = refl
rename-cong h `true = refl
rename-cong h `false = refl
rename-cong h (`suc M) = cong `suc_ (rename-cong h M)
rename-cong h (`case-nat L M N)
  rewrite rename-cong h L
        | rename-cong h M
        | rename-cong (ext-cong {A = `Nat} h) N = refl
rename-cong h (`if_then_else L M N)
  rewrite rename-cong h L
        | rename-cong h M
        | rename-cong h N = refl
rename-cong h (` x) = cong `_ (h x)
rename-cong {A = A ⇒ B} h (ƛ A ˙ N) = cong (ƛ A ˙_) (rename-cong (ext-cong {A = A} h) N)
rename-cong h (L · M) = cong₂ _·_ (rename-cong h L) (rename-cong h M)
rename-cong h (Λ N) = cong Λ_ (rename-cong (⇑ʳ-cong h) N)
rename-cong h (M ∙ B) = cong (_∙ B) (rename-cong h M)

ext-comp : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (ρ₁ : Γ₁ →ʳ Γ₂)
  (ρ₂ : Γ₂ →ʳ Γ₃)
  → ∀ {B} (x : Γ₁ , A ∋ B)
  → ext ρ₂ (ext ρ₁ x) ≡ ext (λ y → ρ₂ (ρ₁ y)) x
ext-comp ρ₁ ρ₂ Z = refl
ext-comp ρ₁ ρ₂ (S x) = refl

private
  ⇑ʳ-renameᵗ-∋-S : ∀ {Δ} {Γ Γ' : Ctx Δ}
    (ρ : Γ →ʳ Γ')
    → ∀ {A} (x : Γ ∋ A)
    → ⇑ʳ ρ (renameᵗ-∋ S_ x) ≡ renameᵗ-∋ S_ (ρ x)
  ⇑ʳ-renameᵗ-∋-S {Γ = ∅} ρ ()
  ⇑ʳ-renameᵗ-∋-S {Γ = Γ , B} ρ Z = refl
  ⇑ʳ-renameᵗ-∋-S {Γ = Γ , B} ρ (S x) =
    ⇑ʳ-renameᵗ-∋-S (λ y → ρ (S y)) x

⇑ʳ-comp : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ}
  (ρ₁ : Γ₁ →ʳ Γ₂)
  (ρ₂ : Γ₂ →ʳ Γ₃)
  → ∀ {A} (x : ⇑ᶜ Γ₁ ∋ A)
  → ⇑ʳ ρ₂ (⇑ʳ ρ₁ x) ≡ ⇑ʳ (λ y → ρ₂ (ρ₁ y)) x
⇑ʳ-comp {Γ₁ = ∅} ρ₁ ρ₂ ()
⇑ʳ-comp {Γ₁ = Γ₁ , B} ρ₁ ρ₂ Z = ⇑ʳ-renameᵗ-∋-S ρ₂ (ρ₁ Z)
⇑ʳ-comp {Γ₁ = Γ₁ , B} ρ₁ ρ₂ (S x) =
  ⇑ʳ-comp (λ y → ρ₁ (S y)) ρ₂ x

rename-comp : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (ρ₁ : Γ₁ →ʳ Γ₂)
  (ρ₂ : Γ₂ →ʳ Γ₃)
  (M : Δ ; Γ₁ ⊢ A)
  → rename ρ₂ (rename ρ₁ M) ≡ rename (λ x → ρ₂ (ρ₁ x)) M
rename-comp ρ₁ ρ₂ `zero = refl
rename-comp ρ₁ ρ₂ `true = refl
rename-comp ρ₁ ρ₂ `false = refl
rename-comp ρ₁ ρ₂ (`suc M) rewrite rename-comp ρ₁ ρ₂ M = refl
rename-comp ρ₁ ρ₂ (`case-nat L M N)
  rewrite rename-comp ρ₁ ρ₂ L
        | rename-comp ρ₁ ρ₂ M
        | rename-comp (ext ρ₁) (ext ρ₂) N
        | rename-cong (ext-comp ρ₁ ρ₂) N = refl
rename-comp ρ₁ ρ₂ (`if_then_else L M N)
  rewrite rename-comp ρ₁ ρ₂ L
        | rename-comp ρ₁ ρ₂ M
        | rename-comp ρ₁ ρ₂ N = refl
rename-comp ρ₁ ρ₂ (` x) = refl
rename-comp ρ₁ ρ₂ (ƛ A ˙ N)
  rewrite rename-comp (ext ρ₁) (ext ρ₂) N
        | rename-cong (ext-comp ρ₁ ρ₂) N = refl
rename-comp ρ₁ ρ₂ (L · M)
  rewrite rename-comp ρ₁ ρ₂ L
        | rename-comp ρ₁ ρ₂ M = refl
rename-comp ρ₁ ρ₂ (Λ N)
  rewrite rename-comp (⇑ʳ ρ₁) (⇑ʳ ρ₂) N
        | rename-cong (⇑ʳ-comp ρ₁ ρ₂) N = refl
rename-comp ρ₁ ρ₂ (M ∙ B) rewrite rename-comp ρ₁ ρ₂ M = refl

exts-ext : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (ρ : Γ₁ →ʳ Γ₂)
  (σ : Γ₂ →ˢ Γ₃)
  → ∀ {B} (x : Γ₁ , A ∋ B)
  → exts σ (ext ρ x) ≡ exts (λ y → σ (ρ y)) x
exts-ext ρ σ Z = refl
exts-ext ρ σ (S x) = refl

private
  ⇑ˢ-renameᵗ-∋-S : ∀ {Δ} {Γ Γ' : Ctx Δ}
    (σ : Γ →ˢ Γ')
    → ∀ {A} (x : Γ ∋ A)
    → ⇑ˢ σ (renameᵗ-∋ S_ x) ≡ ⇑ᵀ (σ x)
  ⇑ˢ-renameᵗ-∋-S {Γ = ∅} σ ()
  ⇑ˢ-renameᵗ-∋-S {Γ = Γ , B} σ Z = refl
  ⇑ˢ-renameᵗ-∋-S {Γ = Γ , B} σ (S x) =
    ⇑ˢ-renameᵗ-∋-S (λ y → σ (S y)) x

⇑ˢ-⇑ʳ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ}
  (ρ : Γ₁ →ʳ Γ₂)
  (σ : Γ₂ →ˢ Γ₃)
  → ∀ {A} (x : ⇑ᶜ Γ₁ ∋ A)
  → ⇑ˢ σ (⇑ʳ ρ x) ≡ ⇑ˢ (λ y → σ (ρ y)) x
⇑ˢ-⇑ʳ {Γ₁ = ∅} ρ σ ()
⇑ˢ-⇑ʳ {Γ₁ = Γ₁ , B} ρ σ Z = ⇑ˢ-renameᵗ-∋-S σ (ρ Z)
⇑ˢ-⇑ʳ {Γ₁ = Γ₁ , B} ρ σ (S x) =
  ⇑ˢ-⇑ʳ (λ y → ρ (S y)) σ x

ren-sub : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (ρ : Γ₁ →ʳ Γ₂)
  (σ : Γ₂ →ˢ Γ₃)
  (M : Δ ; Γ₁ ⊢ A)
  → subst σ (rename ρ M) ≡ subst (λ x → σ (ρ x)) M
ren-sub ρ σ `zero = refl
ren-sub ρ σ `true = refl
ren-sub ρ σ `false = refl
ren-sub ρ σ (`suc M) rewrite ren-sub ρ σ M = refl
ren-sub ρ σ (`case-nat L M N)
  rewrite ren-sub ρ σ L
        | ren-sub ρ σ M
        | ren-sub (ext ρ) (exts σ) N
        | subst-cong (exts-ext ρ σ) N = refl
ren-sub ρ σ (`if_then_else L M N)
  rewrite ren-sub ρ σ L
        | ren-sub ρ σ M
        | ren-sub ρ σ N = refl
ren-sub ρ σ (` x) = refl
ren-sub ρ σ (ƛ A ˙ N)
  rewrite ren-sub (ext ρ) (exts σ) N
        | subst-cong (exts-ext ρ σ) N = refl
ren-sub ρ σ (L · M)
  rewrite ren-sub ρ σ L
        | ren-sub ρ σ M = refl
ren-sub ρ σ (Λ N)
  rewrite ren-sub (⇑ʳ ρ) (⇑ˢ σ) N
        | subst-cong (⇑ˢ-⇑ʳ ρ σ) N = refl
ren-sub ρ σ (M ∙ B) rewrite ren-sub ρ σ M = refl

rename-shift : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {A B : Type Δ}
  (ρ : Γ₁ →ʳ Γ₂)
  (M : Δ ; Γ₁ ⊢ A)
  → rename (ext {A = B} ρ) (⇑ {A = A} {B = B} M) ≡ ⇑ {A = A} {B = B} (rename ρ M)
rename-shift {B = B} ρ M =
  trans
    (rename-comp (S_ {B = B}) (ext {A = B} ρ) M)
    (trans
      (rename-cong (λ x → refl) M)
      (sym (rename-comp ρ (S_ {B = B}) M)))

ext-exts : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (ρ : Γ₂ →ʳ Γ₃)
  (σ : Γ₁ →ˢ Γ₂)
  → ∀ {B} (x : Γ₁ , A ∋ B)
  → rename (ext ρ) (exts σ x) ≡ exts (λ y → rename ρ (σ y)) x
ext-exts ρ σ Z = refl
ext-exts {A = A} ρ σ (S x) = rename-shift {B = A} ρ (σ x)

postulate
  ⇑ʳ-⇑ˢ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ}
    (ρ : Γ₂ →ʳ Γ₃)
    (σ : Γ₁ →ˢ Γ₂)
    → ∀ {A} (x : ⇑ᶜ Γ₁ ∋ A)
    → rename (⇑ʳ ρ) (⇑ˢ σ x) ≡ ⇑ˢ (λ y → rename ρ (σ y)) x

sub-ren : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (ρ : Γ₂ →ʳ Γ₃)
  (σ : Γ₁ →ˢ Γ₂)
  (M : Δ ; Γ₁ ⊢ A)
  → rename ρ (subst σ M) ≡ subst (λ x → rename ρ (σ x)) M
sub-ren ρ σ `zero = refl
sub-ren ρ σ `true = refl
sub-ren ρ σ `false = refl
sub-ren ρ σ (`suc M) rewrite sub-ren ρ σ M = refl
sub-ren ρ σ (`case-nat L M N)
  rewrite sub-ren ρ σ L
        | sub-ren ρ σ M
        | sub-ren (ext ρ) (exts σ) N
        | subst-cong (ext-exts ρ σ) N = refl
sub-ren ρ σ (`if_then_else L M N)
  rewrite sub-ren ρ σ L
        | sub-ren ρ σ M
        | sub-ren ρ σ N = refl
sub-ren ρ σ (` x) = refl
sub-ren ρ σ (ƛ A ˙ N)
  rewrite sub-ren (ext ρ) (exts σ) N
        | subst-cong (ext-exts ρ σ) N = refl
sub-ren ρ σ (L · M)
  rewrite sub-ren ρ σ L
        | sub-ren ρ σ M = refl
sub-ren ρ σ (Λ N)
  rewrite sub-ren (⇑ʳ ρ) (⇑ˢ σ) N
        | subst-cong (⇑ʳ-⇑ˢ ρ σ) N = refl
sub-ren ρ σ (M ∙ B) rewrite sub-ren ρ σ M = refl

exts-subst : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (σ : Γ₁ →ˢ Γ₂)
  (τ : Γ₂ →ˢ Γ₃)
  → ∀ {B} (x : Γ₁ , A ∋ B)
  → subst (exts τ) (exts σ x) ≡ exts (σ ⨟ τ) x
exts-subst σ τ Z = refl
exts-subst σ τ (S x) =
  trans
    (ren-sub S_ (exts τ) (σ x))
    (trans
      (subst-cong (λ y → refl) (σ x))
      (sym (sub-ren S_ τ (σ x))))

postulate
  ⇑ˢ-subst : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ}
    (σ : Γ₁ →ˢ Γ₂)
    (τ : Γ₂ →ˢ Γ₃)
    → ∀ {A} (x : ⇑ᶜ Γ₁ ∋ A)
    → subst (⇑ˢ τ) (⇑ˢ σ x) ≡ ⇑ˢ (σ ⨟ τ) x

sub-sub : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (σ : Γ₁ →ˢ Γ₂)
  (τ : Γ₂ →ˢ Γ₃)
  (M : Δ ; Γ₁ ⊢ A)
  → subst τ (subst σ M) ≡ subst (σ ⨟ τ) M
sub-sub σ τ `zero = refl
sub-sub σ τ `true = refl
sub-sub σ τ `false = refl
sub-sub σ τ (`suc M) rewrite sub-sub σ τ M = refl
sub-sub σ τ (`case-nat L M N)
  rewrite sub-sub σ τ L
        | sub-sub σ τ M
        | sub-sub (exts σ) (exts τ) N
        | subst-cong (exts-subst σ τ) N = refl
sub-sub σ τ (`if_then_else L M N)
  rewrite sub-sub σ τ L
        | sub-sub σ τ M
        | sub-sub σ τ N = refl
sub-sub σ τ (` x) = refl
sub-sub σ τ (ƛ A ˙ N)
  rewrite sub-sub (exts σ) (exts τ) N
        | subst-cong (exts-subst σ τ) N = refl
sub-sub σ τ (L · M)
  rewrite sub-sub σ τ L
        | sub-sub σ τ M = refl
sub-sub σ τ (Λ N)
  rewrite sub-sub (⇑ˢ σ) (⇑ˢ τ) N
        | subst-cong (⇑ˢ-subst σ τ) N = refl
sub-sub σ τ (M ∙ B) rewrite sub-sub σ τ M = refl

subst-σ₀ : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  (σ : Γ →ˢ Γ')
  (M : Δ ; Γ ⊢ A)
  → ∀ {B} (x : Γ , A ∋ B)
  → subst σ (σ₀ M x) ≡ subst (σ₀ (subst σ M)) (exts σ x)
subst-σ₀ σ M Z = refl
subst-σ₀ σ M (S x) =
  sym
    (trans
      (ren-sub S_ (σ₀ (subst σ M)) (σ x))
      (trans
        (subst-cong (λ y → refl) (σ x))
        (sub-id (σ x))))

extsᵗ-idᵗ-id : ∀ {Δ} → extsᵗ (idᵗ {Δ}) ≡ idᵗ {Δ ,α}
extsᵗ-idᵗ-id = extensionality λ where
  Z      → refl
  (S α)  → refl

substCtx-idᵗ-id : ∀ {Δ} (Γ : Ctx Δ) → substCtx idᵗ Γ ≡ Γ
substCtx-idᵗ-id ∅ = refl
substCtx-idᵗ-id (Γ , A) = cong₂ _,_ (substCtx-idᵗ-id Γ) (sub-idᵗ A)

cidᵀ : ∀ {Δ Γ A}
  → Δ ; Γ ⊢ A
  → Δ ; substCtx idᵗ Γ ⊢ substᵗ idᵗ A
cidᵀ {Δ} {Γ} {A} M =
  substEq
    (λ Ξ → Δ ; Ξ ⊢ substᵗ idᵗ A)
    (sym (substCtx-idᵗ-id Γ))
    (substEq
      (λ T → Δ ; Γ ⊢ T)
      (sym (sub-idᵗ A))
      M)

{-
sub-idᵀ : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A)
    ---------------------------------
  → substᵀ idᵗ M ≡ cidᵀ M
sub-idᵀ M = H.≅-to-≡ (H.trans (sub-idᵀ-raw M) (H.sym (cidᵀ-raw M)))
  where
  sub-idᵀ-raw : ∀ {Δ Γ A} (N : Δ ; Γ ⊢ A)
      -----------------------------------
    → substᵀ idᵗ N ≅ N
  sub-idᵀ-raw {Γ = Γ} {A = A} `zero
    rewrite substCtx-idᵗ-id Γ
          | sub-idᵗ A = H.refl
  sub-idᵀ-raw {Γ = Γ} {A = A} `true
    rewrite substCtx-idᵗ-id Γ
          | sub-idᵗ A = H.refl
  sub-idᵀ-raw {Γ = Γ} {A = A} `false
    rewrite substCtx-idᵗ-id Γ
          | sub-idᵗ A = H.refl
  sub-idᵀ-raw (`suc N) =
    let IH = (sub-idᵀ-raw N) in
    let xx = congʰ{?}{?}{x = substᵀ idᵗ N}{y = N} `suc_ {!IH!} in
    {!!}
  sub-idᵀ-raw (`case-nat L M N) =
    {!!} -- Hcong₃ `case-nat (sub-idᵀ-raw L) (sub-idᵀ-raw M) (sub-idᵀ-raw N)
  sub-idᵀ-raw (`if_then_else L M N) =
    {!!} -- Hcong₃ `if_then_else (sub-idᵀ-raw L) (sub-idᵀ-raw M) (sub-idᵀ-raw N)
  sub-idᵀ-raw {Δ = Δ} {Γ = Γ} {A = A} (` x) = {!!}
--    rewrite substCtx-idᵗ-id Γ
--          | sub-idᵗ A = H.refl
  sub-idᵀ-raw (ƛ A ˙ N) = {!!} -- rewrite sub-idᵗ A = ? -- Hcong₁ (ƛ A ˙_) (sub-idᵀ-raw N)
  sub-idᵀ-raw (N · N₁) = {!!} -- Hcong₂ _·_ (sub-idᵀ-raw N) (sub-idᵀ-raw N₁)
  sub-idᵀ-raw {Δ = Δ} {Γ = Γ} (Λ N) = {!!}
    -- rewrite substCtx-extsᵗ-⇑ᶜ (idᵗ {Δ}) Γ
    --       | extsᵗ-idᵗ-id {Δ} = Hcong₁ Λ_ (sub-idᵀ-raw N)
  sub-idᵀ-raw {Δ = Δ} {Γ = Γ} (_∙_ {A = A} N B) = {!!}
    -- rewrite sub-idᵗ B =
    -- H.trans
    --   (H.≡-subst-removable (λ T → Δ ; Γ ⊢ T) (sym (substᵗ-[]ᵗ idᵗ A B)) (substᵀ idᵗ N ∙ B))
    --   (Hcong₁ (_∙ B) (sub-idᵀ-raw N))

  cidᵀ-raw : ∀ {Δ Γ A} (N : Δ ; Γ ⊢ A) → cidᵀ N ≅ N
  cidᵀ-raw {Γ = Γ} {A = A} N
    rewrite substCtx-idᵗ-id Γ
          | sub-idᵗ A = H.refl
-}

subst-[] : ∀ {Δ} {Γ Γ' : Ctx Δ} {A B : Type Δ}
  (σ : Γ →ˢ Γ')
  (N : Δ ; Γ , A ⊢ B)
  (M : Δ ; Γ ⊢ A)
  → subst σ (N [ M ]) ≡ (subst (exts σ) N) [ subst σ M ]
subst-[] σ N M =
  trans
    (sub-sub (σ₀ M) σ N)
    (trans
      (subst-cong (subst-σ₀ σ M) N)
      (sym (sub-sub (exts σ) (σ₀ (subst σ M)) N)))

exts-sub-cons : ∀ {Δ} {Γ Γ' : Ctx Δ} {A B : Type Δ}
  (σ : Γ →ˢ Γ')
  (N : Δ ; Γ , A ⊢ B)
  (M : Δ ; Γ' ⊢ A)
  → (subst (exts σ) N) [ M ] ≡ subst (M • σ) N
exts-sub-cons {Γ = Γ} {A = A} σ N M =
  trans
    (sub-sub (exts σ) (σ₀ M) N)
    (subst-cong eq N)
  where
  eq : ∀ {C} (x : Γ , A ∋ C)
    → subst (σ₀ M) (exts σ x) ≡ (M • σ) x
  eq Z = refl
  eq (S x) =
    trans
      (ren-sub S_ (σ₀ M) (σ x))
      (trans
        (subst-cong (λ y → refl) (σ x))
        (sub-id (σ x)))
