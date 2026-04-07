module intrinsic.Terms where

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Relation.Binary.HeterogeneousEquality as H
            using (_≅_) renaming (cong to congʰ)
open import Data.Nat using (ℕ; zero; suc)

open import intrinsic.Types
open import intrinsic.Ctx
open import intrinsic.Heq using (Hcong₁; Hcong₂; Hcong₃; Hcong₄; Hcong₅)

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

-- A structural characterization of substitutions that act like renamings.
data SubstWk : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (ξ : Δ ⇒ʳ Δ') → Set where
  swk-↑ : ∀ {Δ}
    → SubstWk (↑ᵗ {Δ}) S_
  swk-ren : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ')
    → SubstWk (λ α → ` (ρ α)) ρ
  swk-ext : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
    → SubstWk σ ξ
    → SubstWk (extsᵗ σ) (extᵗ ξ)

SubstWk-varEq : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  → SubstWk σ ξ
  → (α : TyVar Δ)
  → σ α ≡ ` (ξ α)
SubstWk-varEq swk-↑ α = refl
SubstWk-varEq (swk-ren ρ) α = refl
SubstWk-varEq (swk-ext wk) Z = refl
SubstWk-varEq (swk-ext wk) (S α) = cong ⇑ᵗ (SubstWk-varEq wk α)

SubstWk-typeEq : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  → SubstWk σ ξ
  → (A : Type Δ)
  → substᵗ σ A ≡ renameᵗ ξ A
SubstWk-typeEq wk (` α) = SubstWk-varEq wk α
SubstWk-typeEq wk `Nat = refl
SubstWk-typeEq wk `Bool = refl
SubstWk-typeEq wk (A ⇒ B) =
  cong₂ _⇒_ (SubstWk-typeEq wk A) (SubstWk-typeEq wk B)
SubstWk-typeEq wk (`∀ A) =
  cong `∀_ (SubstWk-typeEq (swk-ext wk) A)

SubstWk-ctxEq : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  → SubstWk σ ξ
  → (Γ : Ctx Δ)
  → substCtx σ Γ ≡ renameCtx ξ Γ
SubstWk-ctxEq wk ∅ = refl
SubstWk-ctxEq wk (Γ , A) =
  cong₂ _,_ (SubstWk-ctxEq wk Γ) (SubstWk-typeEq wk A)

castWk : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  → (wk : SubstWk σ ξ)
  → ∀ {Γ : Ctx Δ} {A : Type Δ}
  → Δ' ; substCtx σ Γ ⊢ substᵗ σ A
  → Δ' ; renameCtx ξ Γ ⊢ renameᵗ ξ A
castWk {Δ' = Δ'} {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} M =
  substEq
    (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ξ A)
    (SubstWk-ctxEq wk Γ)
    (substEq
      (λ T → Δ' ; substCtx σ Γ ⊢ T)
      (SubstWk-typeEq wk A)
      M)

castWk-removable : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type Δ}
  (M : Δ' ; substCtx σ Γ ⊢ substᵗ σ A)
  → castWk wk M ≅ M
castWk-removable {Δ' = Δ'} {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} M =
  H.trans
    (H.≡-subst-removable
      (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ξ A)
      (SubstWk-ctxEq wk Γ)
      (substEq
        (λ T → Δ' ; substCtx σ Γ ⊢ T)
        (SubstWk-typeEq wk A)
        M))
    (H.≡-subst-removable
      (λ T → Δ' ; substCtx σ Γ ⊢ T)
      (SubstWk-typeEq wk A)
      M)

castWk-∋ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type Δ'}
  → substCtx σ Γ ∋ A
  → renameCtx ξ Γ ∋ A
castWk-∋ wk {Γ = Γ} x =
  substEq (λ Ψ → Ψ ∋ _) (SubstWk-ctxEq wk Γ) x

cast-SubstWk-ctxEq-S : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {B : Type Δ} {A : Type Δ'}
  (x : substCtx σ Γ ∋ A)
  → substEq
      (λ Ψ → Ψ ∋ A)
      (SubstWk-ctxEq wk (Γ , B))
      (S x)
    ≡
    S (substEq
        (λ Ψ → Ψ ∋ A)
        (SubstWk-ctxEq wk Γ)
        x)
cast-SubstWk-ctxEq-S wk {Γ = Γ} {B = B} x
  rewrite SubstWk-ctxEq wk Γ
        | SubstWk-typeEq wk B = refl

cast-∋-Sᵗʷ : ∀ {Δ} {Γ : Ctx Δ} {A B C : Type Δ}
  (p : A ≡ B)
  (x : Γ ∋ A)
  → substEq (λ T → Γ , C ∋ T) p (S x)
    ≡
    S (substEq (λ T → Γ ∋ T) p x)
cast-∋-Sᵗʷ refl x = refl

castWk-∋-substᵗ-∋ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type Δ}
  (x : Γ ∋ A)
  → castWk-∋ wk
      (substEq
        (λ T → substCtx σ Γ ∋ T)
        (SubstWk-typeEq wk A)
        (substᵗ-∋ σ x))
    ≡
    renameᵗ-∋ ξ x
castWk-∋-substᵗ-∋ {σ = σ} {ξ = ξ} wk {Γ = ∅} ()
castWk-∋-substᵗ-∋ {σ = σ} {ξ = ξ} wk {Γ = Γ , B} {A = B} Z
  rewrite SubstWk-ctxEq wk Γ
        | SubstWk-typeEq wk B = refl
castWk-∋-substᵗ-∋ {σ = σ} {ξ = ξ} wk {Γ = Γ , B} {A = A} (S x) =
  trans
    (cong (castWk-∋ wk)
      (cast-∋-Sᵗʷ
        {Γ = substCtx σ Γ}
        {C = substᵗ σ B}
        (SubstWk-typeEq wk A)
        (substᵗ-∋ σ x)))
    (trans
      (cast-SubstWk-ctxEq-S wk
        {Γ = Γ}
        {B = B}
        (substEq
          (λ T → substCtx σ Γ ∋ T)
          (SubstWk-typeEq wk A)
          (substᵗ-∋ σ x)))
      (cong S_ (castWk-∋-substᵗ-∋ wk {Γ = Γ} {A = A} x)))

substᵗ-↑ᵗ : ∀ {Δ} (A : Type Δ)
  → substᵗ ↑ᵗ A ≡ renameᵗ S_ A
substᵗ-↑ᵗ A =
  trans
    (sym (ren-subᵗ S_ idᵗ A))
    (sub-idᵗ (renameᵗ S_ A))

substCtx-↑ᵗ : ∀ {Δ} (Γ : Ctx Δ)
  → substCtx ↑ᵗ Γ ≡ renameCtx S_ Γ
substCtx-↑ᵗ ∅ = refl
substCtx-↑ᵗ (Γ , A) rewrite substCtx-↑ᵗ Γ | substᵗ-↑ᵗ A = refl

cast↑-∋ : ∀ {Δ} {Γ : Ctx Δ} {A : Type (Δ ,α)}
  → substCtx ↑ᵗ Γ ∋ A
  → renameCtx S_ Γ ∋ A
cast↑-∋ {Γ = Γ} {A = A} x =
  substEq (λ Ψ → Ψ ∋ A) (substCtx-↑ᵗ Γ) x

cast↑ᶜ : ∀ {Δ} {Γ : Ctx Δ} {A : Type (Δ ,α)}
  → Δ ,α ; substCtx ↑ᵗ Γ ⊢ A
  → Δ ,α ; renameCtx S_ Γ ⊢ A
cast↑ᶜ {Δ = Δ} {Γ = Γ} {A = A} M =
  substEq (λ Ψ → Δ ,α ; Ψ ⊢ A) (substCtx-↑ᵗ Γ) M

cast↑ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  → Δ ,α ; substCtx ↑ᵗ Γ ⊢ substᵗ ↑ᵗ A
  → Δ ,α ; renameCtx S_ Γ ⊢ renameᵗ S_ A
cast↑ {Δ = Δ} {Γ = Γ} {A = A} M =
  cast↑ᶜ
    (substEq
      (λ T → Δ ,α ; substCtx ↑ᵗ Γ ⊢ T)
      (substᵗ-↑ᵗ A)
      M)

cast↑ᶜ-var : ∀ {Δ} {Γ : Ctx Δ} {A : Type (Δ ,α)}
  (x : substCtx ↑ᵗ Γ ∋ A)
  → cast↑ᶜ (` x) ≡ ` (cast↑-∋ x)
cast↑ᶜ-var {Γ = Γ} x
  rewrite substCtx-↑ᵗ Γ = refl

cast↑-suc : ∀ {Δ} {Γ : Ctx Δ}
  (N : Δ ,α ; substCtx ↑ᵗ Γ ⊢ `Nat)
  → cast↑ (`suc N) ≡ `suc (cast↑ N)
cast↑-suc {Δ = Δ} {Γ = Γ} N
  rewrite substCtx-↑ᵗ Γ
        | substᵗ-↑ᵗ (`Nat {Δ = Δ}) = refl

cast↑-if : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  (L : Δ ,α ; substCtx ↑ᵗ Γ ⊢ `Bool)
  (M N : Δ ,α ; substCtx ↑ᵗ Γ ⊢ substᵗ ↑ᵗ A)
  → cast↑ (`if_then_else {A = substᵗ ↑ᵗ A} L M N)
    ≡ `if_then_else {A = renameᵗ S_ A} (cast↑ L) (cast↑ M) (cast↑ N)
cast↑-if {Γ = Γ} {A = A} L M N
  rewrite substCtx-↑ᵗ Γ
        | substᵗ-↑ᵗ A = refl

cast↑-case-nat : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  (L : Δ ,α ; substCtx ↑ᵗ Γ ⊢ `Nat)
  (M : Δ ,α ; substCtx ↑ᵗ Γ ⊢ substᵗ ↑ᵗ A)
  (N : Δ ,α ; substCtx ↑ᵗ Γ , `Nat ⊢ substᵗ ↑ᵗ A)
  → cast↑ (`case-nat {A = substᵗ ↑ᵗ A} L M N)
    ≡ `case-nat {A = renameᵗ S_ A}
        (cast↑ L)
        (cast↑ M)
        (cast↑ {Γ = Γ , `Nat} {A = A} N)
cast↑-case-nat {Γ = Γ} {A = A} L M N
  rewrite substCtx-↑ᵗ Γ
        | substᵗ-↑ᵗ A = refl

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

renᵀ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') → Δ ⇒ˢ Δ'
renᵀ ρ x = ` (ρ x)

renameCtx-renᵀ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (Γ : Ctx Δ)
  → renameCtx ρ Γ ≡ substCtx (renᵀ ρ) Γ
renameCtx-renᵀ ρ Γ = sym (SubstWk-ctxEq (swk-ren ρ) Γ)

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

mapʳᵀ : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ') {Γ Γ' : Ctx Δ}
  → Γ →ʳ Γ'
  → renameCtx ξ Γ →ʳ renameCtx ξ Γ'
mapʳᵀ ξ {Γ = ∅} ρ ()
mapʳᵀ ξ {Γ = Γ , A} ρ Z = renameᵗ-∋ ξ (ρ Z)
mapʳᵀ ξ {Γ = Γ , A} ρ (S x) = mapʳᵀ ξ (λ y → ρ (S y)) x

mapʳᵀ-S : ∀ {Δ} {Γ Γ' : Ctx Δ}
  (ρ : Γ →ʳ Γ')
  → ∀ {A} (x : ⇑ᶜ Γ ∋ A)
  → mapʳᵀ S_ ρ x ≡ ⇑ʳ ρ x
mapʳᵀ-S {Γ = ∅} ρ ()
mapʳᵀ-S {Γ = Γ , B} ρ Z = refl
mapʳᵀ-S {Γ = Γ , B} ρ (S x) =
  mapʳᵀ-S (λ y → ρ (S y)) x

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

mapʳᵀ-liftS : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (ρ : Γ →ʳ Γ')
  → ∀ {B} (x : renameCtx ξ Γ ∋ B)
  → mapʳᵀ ξ (λ y → S_ {B = A} (ρ y)) x
    ≡ S_ {B = renameᵗ ξ A} (mapʳᵀ ξ ρ x)
mapʳᵀ-liftS ξ {Γ = ∅} ρ ()
mapʳᵀ-liftS ξ {Γ = Γ , C} ρ Z = refl
mapʳᵀ-liftS ξ {Γ = Γ , C} ρ (S x) =
  mapʳᵀ-liftS ξ (λ y → ρ (S y)) x

mapʳᵀ-ext : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (ρ : Γ →ʳ Γ')
  → ∀ {B} (x : renameCtx ξ (Γ , A) ∋ B)
  → mapʳᵀ ξ (ext ρ) x
    ≡ ext (mapʳᵀ ξ ρ) x
mapʳᵀ-ext ξ ρ Z = refl
mapʳᵀ-ext ξ {A = A} ρ (S x) = mapʳᵀ-liftS ξ {A = A} ρ x

mapʳᵀ-∋ : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
  {Γ Γ' : Ctx Δ}
  (ρ : Γ →ʳ Γ')
  {A : Type Δ}
  (x : Γ ∋ A)
  → mapʳᵀ ξ ρ (renameᵗ-∋ ξ x) ≡ renameᵗ-∋ ξ (ρ x)
mapʳᵀ-∋ ξ ρ Z = refl
mapʳᵀ-∋ ξ ρ (S x) =
  mapʳᵀ-∋ ξ (λ y → ρ (S y)) x

cast-renameCtx-extᵗ-⇑ᶜ-Z : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
  {Γ : Ctx Δ} {B : Type Δ}
  → substEq
      (λ Ψ → Ψ ∋ renameᵗ (extᵗ ξ) (renameᵗ S_ B))
      (renameCtx-extᵗ-⇑ᶜ ξ (Γ , B))
      Z
    ≡
    substEq
      (λ T → ⇑ᶜ (renameCtx ξ (Γ , B)) ∋ T)
      (sym (renameᵗ-shift ξ B))
      Z
cast-renameCtx-extᵗ-⇑ᶜ-Z ξ {Γ} {B}
  rewrite renameCtx-extᵗ-⇑ᶜ ξ Γ
        | renameᵗ-shift ξ B = refl

cast-renameCtx-extᵗ-⇑ᶜ-S : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
  {Γ : Ctx Δ} {B : Type Δ} {A : Type (Δ' ,α)}
  (x : renameCtx (extᵗ ξ) (⇑ᶜ Γ) ∋ A)
  → substEq
      (λ Ψ → Ψ ∋ A)
      (renameCtx-extᵗ-⇑ᶜ ξ (Γ , B))
      (S x)
    ≡
    S (substEq
        (λ Ψ → Ψ ∋ A)
        (renameCtx-extᵗ-⇑ᶜ ξ Γ)
        x)
cast-renameCtx-extᵗ-⇑ᶜ-S ξ {Γ} {B} x
  rewrite renameCtx-extᵗ-⇑ᶜ ξ Γ
        | renameᵗ-shift ξ B = refl

cast-∋-Sᵗ : ∀ {Δ} {Γ : Ctx Δ} {A B C : Type Δ}
  (p : A ≡ B)
  (x : Γ ∋ A)
  → substEq (λ T → Γ , C ∋ T) p (S x)
    ≡
    S (substEq (λ T → Γ ∋ T) p x)
cast-∋-Sᵗ refl x = refl

cast-substCtx-↑ᵗ-S : ∀ {Δ} {Γ : Ctx Δ} {B : Type Δ} {A : Type (Δ ,α)}
  (x : substCtx ↑ᵗ Γ ∋ A)
  → substEq
      (λ Ψ → Ψ ∋ A)
      (substCtx-↑ᵗ (Γ , B))
      (S x)
    ≡
    S (substEq
        (λ Ψ → Ψ ∋ A)
        (substCtx-↑ᵗ Γ)
        x)
cast-substCtx-↑ᵗ-S {Γ = Γ} {B = B} x
  rewrite substCtx-↑ᵗ Γ
        | substᵗ-↑ᵗ B = refl

cast-substCtx-↑ᵗ-Z : ∀ {Δ} {Γ : Ctx Δ} {B : Type Δ}
  → substEq
      (λ Ψ → Ψ ∋ substᵗ ↑ᵗ B)
      (substCtx-↑ᵗ (Γ , B))
      Z
    ≡
    substEq
      (λ T → (renameCtx S_ Γ , renameᵗ S_ B) ∋ T)
      (sym (substᵗ-↑ᵗ B))
      Z
cast-substCtx-↑ᵗ-Z {Γ = Γ} {B = B}
  rewrite substCtx-↑ᵗ Γ
        | substᵗ-↑ᵗ B = refl

⇑ˢ-castᵗ : ∀ {Δ} {Γ Γ' : Ctx Δ}
  (σ : Γ →ˢ Γ')
  {A B : Type (Δ ,α)}
  (p : A ≡ B)
  (x : ⇑ᶜ Γ ∋ A)
  → ⇑ˢ σ (substEq (λ T → ⇑ᶜ Γ ∋ T) p x)
    ≡ substEq (λ T → Δ ,α ; ⇑ᶜ Γ' ⊢ T) p (⇑ˢ σ x)
⇑ˢ-castᵗ σ refl x = refl

cast↑-∋-substᵗ-∋ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  (x : Γ ∋ A)
  → cast↑-∋
      (substEq
        (λ T → substCtx ↑ᵗ Γ ∋ T)
        (substᵗ-↑ᵗ A)
        (substᵗ-∋ ↑ᵗ x))
    ≡
    renameᵗ-∋ S_ x
cast↑-∋-substᵗ-∋ {Γ = ∅} ()
cast↑-∋-substᵗ-∋ {Γ = Γ , B} {A = B} Z
  rewrite substCtx-↑ᵗ Γ
        | substᵗ-↑ᵗ B = refl
cast↑-∋-substᵗ-∋ {Γ = Γ , B} {A = A} (S x) =
  trans
    (cong cast↑-∋
      (cast-∋-Sᵗ
        {Γ = substCtx ↑ᵗ Γ}
        {C = substᵗ ↑ᵗ B}
        (substᵗ-↑ᵗ A)
        (substᵗ-∋ ↑ᵗ x)))
    (trans
      (cast-substCtx-↑ᵗ-S
        {Γ = Γ}
        {B = B}
        (substEq
          (λ T → substCtx ↑ᵗ Γ ∋ T)
          (substᵗ-↑ᵗ A)
          (substᵗ-∋ ↑ᵗ x)))
      (cong S_ (cast↑-∋-substᵗ-∋ {Γ = Γ} {A = A} x)))

⇑ʳ-castᵗ : ∀ {Δ} {Γ Γ' : Ctx Δ}
  (ρ : Γ →ʳ Γ')
  {A B : Type (Δ ,α)}
  (p : A ≡ B)
  (x : ⇑ᶜ Γ ∋ A)
  → ⇑ʳ ρ (substEq (λ T → ⇑ᶜ Γ ∋ T) p x)
    ≡ substEq (λ T → ⇑ᶜ Γ' ∋ T) p (⇑ʳ ρ x)
⇑ʳ-castᵗ ρ refl x = refl

cast-renameCtx-extᵗ-⇑ᶜ-renameᵗ-∋S : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
  {Γ : Ctx Δ} {B : Type Δ}
  (y : Γ ∋ B)
  → substEq
      (λ Ψ → Ψ ∋ renameᵗ (extᵗ ξ) (renameᵗ S_ B))
      (renameCtx-extᵗ-⇑ᶜ ξ Γ)
      (renameᵗ-∋ (extᵗ ξ) (renameᵗ-∋ S_ y))
    ≡
    substEq
      (λ T → ⇑ᶜ (renameCtx ξ Γ) ∋ T)
      (sym (renameᵗ-shift ξ B))
      (renameᵗ-∋ S_ (renameᵗ-∋ ξ y))
cast-renameCtx-extᵗ-⇑ᶜ-renameᵗ-∋S ξ {Γ = Γ , B} {B = B} Z
  rewrite renameCtx-extᵗ-⇑ᶜ ξ Γ
        | renameᵗ-shift ξ B = refl
cast-renameCtx-extᵗ-⇑ᶜ-renameᵗ-∋S ξ {Γ = Γ , C} {B = B} (S y) =
  trans
    (cast-renameCtx-extᵗ-⇑ᶜ-S ξ
      {Γ = Γ} {B = C}
      (renameᵗ-∋ (extᵗ ξ) (renameᵗ-∋ S_ y)))
    (trans
      (cong S_ (cast-renameCtx-extᵗ-⇑ᶜ-renameᵗ-∋S ξ {Γ = Γ} {B = B} y))
      (sym
        (cast-∋-Sᵗ
          {Γ = ⇑ᶜ (renameCtx ξ Γ)}
          {C = renameᵗ S_ (renameᵗ ξ C)}
          (sym (renameᵗ-shift ξ B))
          (renameᵗ-∋ S_ (renameᵗ-∋ ξ y)))))

mapʳᵀ-extᵗ-⇑ʳ-coh : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
  {Γ Γ' : Ctx Δ}
  (ρ : Γ →ʳ Γ')
  → ∀ {A} (x : renameCtx (extᵗ ξ) (⇑ᶜ Γ) ∋ A)
  → substEq (λ Ψ → Ψ ∋ A)
      (renameCtx-extᵗ-⇑ᶜ ξ Γ')
      (mapʳᵀ (extᵗ ξ) (⇑ʳ ρ) x)
    ≡
    ⇑ʳ (mapʳᵀ ξ ρ)
      (substEq (λ Ψ → Ψ ∋ A)
        (renameCtx-extᵗ-⇑ᶜ ξ Γ)
        x)
mapʳᵀ-extᵗ-⇑ʳ-coh ξ {Γ = ∅} ρ ()
mapʳᵀ-extᵗ-⇑ʳ-coh ξ {Γ = Γ , B} ρ Z
  rewrite cast-renameCtx-extᵗ-⇑ᶜ-Z ξ {Γ = Γ} {B = B} =
  trans
    (cast-renameCtx-extᵗ-⇑ᶜ-renameᵗ-∋S ξ (ρ Z))
    (sym (⇑ʳ-castᵗ
      (mapʳᵀ ξ ρ)
      (sym (renameᵗ-shift ξ B))
      Z))
mapʳᵀ-extᵗ-⇑ʳ-coh ξ {Γ = Γ , B} ρ (S x)
  rewrite cast-renameCtx-extᵗ-⇑ᶜ-S ξ {Γ = Γ} {B = B} x =
  mapʳᵀ-extᵗ-⇑ʳ-coh ξ (λ y → ρ (S y)) x

rename-substEq : ∀ {Δ} {Γ' Γ'' : Ctx Δ}
  (ρ : Γ' →ʳ Γ'')
  {A B : Type Δ}
  (p : A ≡ B)
  (M : Δ ; Γ' ⊢ A)
  → rename ρ (substEq (λ T → Δ ; Γ' ⊢ T) p M)
    ≡ substEq (λ T → Δ ; Γ'' ⊢ T) p (rename ρ M)
rename-substEq ρ refl M = refl

rename-substEqᶜ : ∀ {Δ} {Γ₁ Γ₁' Γ₂ Γ₂' : Ctx Δ} {A : Type Δ}
  (p₁ : Γ₁ ≡ Γ₁')
  (p₂ : Γ₂ ≡ Γ₂')
  (f : Γ₁' →ʳ Γ₂')
  (g : Γ₁ →ʳ Γ₂)
  (coh : ∀ {B} (x : Γ₁ ∋ B)
      → substEq (λ Ψ → Ψ ∋ B) p₂ (g x)
        ≡ f (substEq (λ Ψ → Ψ ∋ B) p₁ x))
  (M : Δ ; Γ₁ ⊢ A)
  → rename f (substEq (λ Ψ → Δ ; Ψ ⊢ A) p₁ M)
    ≡ substEq (λ Ψ → Δ ; Ψ ⊢ A) p₂ (rename g M)
rename-substEqᶜ refl refl f g coh M =
  rename-cong (λ x → sym (coh x)) M

subst-substEqᶜ : ∀ {Δ}
  {Γ₁ Γ₁' Γ₂ Γ₂' : Ctx Δ}
  {A : Type Δ}
  (p₁ : Γ₁ ≡ Γ₁')
  (p₂ : Γ₂ ≡ Γ₂')
  (σ₁ : Γ₁' →ˢ Γ₂')
  (σ₂ : Γ₁ →ˢ Γ₂)
  (coh : ∀ {B} (x : Γ₁ ∋ B)
      → substEq (λ Ψ → Δ ; Ψ ⊢ B) p₂ (σ₂ x)
        ≡ σ₁ (substEq (λ Ψ → Ψ ∋ B) p₁ x))
  (M : Δ ; Γ₁ ⊢ A)
  → subst σ₁ (substEq (λ Ψ → Δ ; Ψ ⊢ A) p₁ M)
    ≡ substEq (λ Ψ → Δ ; Ψ ⊢ A) p₂ (subst σ₂ M)
subst-substEqᶜ refl refl σ₁ σ₂ coh M =
  subst-cong (λ x → sym (coh x)) M

substEq-cancel : ∀ {A : Set} (P : A → Set)
  {x y : A}
  (p : x ≡ y)
  (u : P y)
  → substEq P p (substEq P (sym p) u) ≡ u
substEq-cancel P refl u = refl

substEq-cancel-sym : ∀ {A : Set} (P : A → Set)
  {x y : A}
  (p : x ≡ y)
  (u : P x)
  → substEq P (sym p) (substEq P p u) ≡ u
substEq-cancel-sym P refl u = refl

substEq-compose : ∀ {A : Set} (P : A → Set)
  {x y z : A}
  (p : y ≡ z)
  (q : x ≡ y)
  (u : P x)
  → substEq P p (substEq P q u) ≡ substEq P (trans q p) u
substEq-compose P refl refl u = refl

trans-assoc : ∀ {A : Set} {x y z w : A}
  (p : x ≡ y)
  (q : y ≡ z)
  (r : z ≡ w)
  → trans p (trans q r) ≡ trans (trans p q) r
trans-assoc refl refl refl = refl

trans-sym-left : ∀ {A : Set} {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  → trans (sym p) (trans p q) ≡ q
trans-sym-left refl q = refl

uip-≡ : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip-≡ refl refl = refl

substEq-id : ∀ {A : Set} (P : A → Set) {x : A}
  (p : x ≡ x)
  (u : P x)
  → substEq P p u ≡ u
substEq-id P refl u = refl

substᵀ-substEqᶜ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (p : Γ ≡ Γ')
  (M : Δ ; Γ ⊢ A)
  → substᵀ τ (substEq (λ Ψ → Δ ; Ψ ⊢ A) p M)
    ≡
    substEq
      (λ Ψ → Δ' ; Ψ ⊢ substᵗ τ A)
      (cong (substCtx τ) p)
      (substᵀ τ M)
substᵀ-substEqᶜ τ refl M = refl

renameᵀ-substEqᶜ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (p : Γ ≡ Γ')
  (M : Δ ; Γ ⊢ A)
  → renameᵀ ρ (substEq (λ Ψ → Δ ; Ψ ⊢ A) p M)
    ≡
    substEq
      (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ρ A)
      (cong (renameCtx ρ) p)
      (renameᵀ ρ M)
renameᵀ-substEqᶜ ρ refl M = refl

substᵀ-substEqᵗ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ : Ctx Δ} {A B : Type Δ}
  (p : A ≡ B)
  (M : Δ ; Γ ⊢ A)
  → substᵀ τ (substEq (λ T → Δ ; Γ ⊢ T) p M)
    ≡
    substEq
      (λ T → Δ' ; substCtx τ Γ ⊢ T)
      (cong (substᵗ τ) p)
      (substᵀ τ M)
substᵀ-substEqᵗ τ refl M = refl

renameᵀ-substEqᵗ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ')
  {Γ : Ctx Δ} {A B : Type Δ}
  (p : A ≡ B)
  (M : Δ ; Γ ⊢ A)
  → renameᵀ ρ (substEq (λ T → Δ ; Γ ⊢ T) p M)
    ≡
    substEq
      (λ T → Δ' ; renameCtx ρ Γ ⊢ T)
      (cong (renameᵗ ρ) p)
      (renameᵀ ρ M)
renameᵀ-substEqᵗ ρ refl M = refl

cast-var-term : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  (p : Γ ≡ Γ')
  (x : Γ ∋ A)
  → substEq (λ Ψ → Δ ; Ψ ⊢ A) p (` x)
    ≡ ` (substEq (λ Ψ → Ψ ∋ A) p x)
cast-var-term refl x = refl

cast-var-type-term : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ}
  (p : A ≡ B)
  (x : Γ ∋ A)
  → substEq (λ T → Δ ; Γ ⊢ T) p (` x)
    ≡ ` (substEq (λ T → Γ ∋ T) p x)
cast-var-type-term refl x = refl

cast-ctx-type-term : ∀ {Θ} {Γ Γ' : Ctx Θ} {A B : Type Θ}
  (pΓ : Γ ≡ Γ')
  (pT : A ≡ B)
  (M : Θ ; Γ ⊢ A)
  → substEq (λ Ψ → Θ ; Ψ ⊢ B) pΓ
      (substEq (λ T → Θ ; Γ ⊢ T) pT M)
    ≡
    substEq (λ T → Θ ; Γ' ⊢ T) pT
      (substEq (λ Ψ → Θ ; Ψ ⊢ A) pΓ M)
cast-ctx-type-term refl refl M = refl

cast-app-type-term : ∀ {Θ} {Γ : Ctx Θ}
  {A A' B B' : Type Θ}
  (pA : A ≡ A')
  (pB : B ≡ B')
  (L : Θ ; Γ ⊢ A ⇒ B)
  (M : Θ ; Γ ⊢ A)
  → substEq (λ T → Θ ; Γ ⊢ T) pB (L · M)
    ≡
    substEq (λ T → Θ ; Γ ⊢ T) (cong₂ _⇒_ pA pB) L
      · substEq (λ T → Θ ; Γ ⊢ T) pA M
cast-app-type-term refl refl L M = refl

cast-app-ctx-term : ∀ {Θ} {Γ Γ' : Ctx Θ} {A B : Type Θ}
  (p : Γ ≡ Γ')
  (L : Θ ; Γ ⊢ A ⇒ B)
  (M : Θ ; Γ ⊢ A)
  → substEq (λ Ψ → Θ ; Ψ ⊢ B) p (L · M)
    ≡
    substEq (λ Ψ → Θ ; Ψ ⊢ A ⇒ B) p L
      · substEq (λ Ψ → Θ ; Ψ ⊢ A) p M
cast-app-ctx-term refl L M = refl

cast-suc-ctx-term : ∀ {Θ} {Γ Γ' : Ctx Θ}
  (p : Γ ≡ Γ')
  (N : Θ ; Γ ⊢ `Nat)
  → substEq (λ Ψ → Θ ; Ψ ⊢ `Nat) p (`suc N)
    ≡
    `suc (substEq (λ Ψ → Θ ; Ψ ⊢ `Nat) p N)
cast-suc-ctx-term refl N = refl

cast-suc-type-term : ∀ {Θ} {Γ : Ctx Θ}
  (p : `Nat {Θ} ≡ `Nat)
  (N : Θ ; Γ ⊢ `Nat)
  → substEq (λ T → Θ ; Γ ⊢ T) p (`suc N)
    ≡
    `suc N
cast-suc-type-term refl N = refl

cast-if-ctx-term : ∀ {Θ} {Γ Γ' : Ctx Θ} {A : Type Θ}
  (p : Γ ≡ Γ')
  (L : Θ ; Γ ⊢ `Bool)
  (M N : Θ ; Γ ⊢ A)
  → substEq (λ Ψ → Θ ; Ψ ⊢ A) p (`if_then_else L M N)
    ≡
    `if_then_else
      (substEq (λ Ψ → Θ ; Ψ ⊢ `Bool) p L)
      (substEq (λ Ψ → Θ ; Ψ ⊢ A) p M)
      (substEq (λ Ψ → Θ ; Ψ ⊢ A) p N)
cast-if-ctx-term refl L M N = refl

cast-if-type-term : ∀ {Θ} {Γ : Ctx Θ} {A B : Type Θ}
  (p : A ≡ B)
  (L : Θ ; Γ ⊢ `Bool)
  (M N : Θ ; Γ ⊢ A)
  → substEq (λ T → Θ ; Γ ⊢ T) p (`if_then_else L M N)
    ≡
    `if_then_else
      L
      (substEq (λ T → Θ ; Γ ⊢ T) p M)
      (substEq (λ T → Θ ; Γ ⊢ T) p N)
cast-if-type-term refl L M N = refl

cast-case-nat-ctx-term : ∀ {Θ} {Γ Γ' : Ctx Θ} {A : Type Θ}
  (p : Γ ≡ Γ')
  (L : Θ ; Γ ⊢ `Nat)
  (M : Θ ; Γ ⊢ A)
  (N : Θ ; Γ , `Nat ⊢ A)
  → substEq (λ Ψ → Θ ; Ψ ⊢ A) p (`case-nat L M N)
    ≡
    `case-nat
      (substEq (λ Ψ → Θ ; Ψ ⊢ `Nat) p L)
      (substEq (λ Ψ → Θ ; Ψ ⊢ A) p M)
      (substEq (λ Ψ → Θ ; Ψ ⊢ A) (cong (λ Ψ → Ψ , `Nat) p) N)
cast-case-nat-ctx-term refl L M N = refl

cast-case-nat-type-term : ∀ {Θ} {Γ : Ctx Θ} {A B : Type Θ}
  (p : A ≡ B)
  (L : Θ ; Γ ⊢ `Nat)
  (M : Θ ; Γ ⊢ A)
  (N : Θ ; Γ , `Nat ⊢ A)
  → substEq (λ T → Θ ; Γ ⊢ T) p (`case-nat L M N)
    ≡
    `case-nat
      L
      (substEq (λ T → Θ ; Γ ⊢ T) p M)
      (substEq (λ T → Θ ; Γ , `Nat ⊢ T) p N)
cast-case-nat-type-term refl L M N = refl

cast-ƛ-ctx-term : ∀ {Θ} {Γ Γ' : Ctx Θ} {A B : Type Θ}
  (p : Γ ≡ Γ')
  (N : Θ ; Γ , A ⊢ B)
  → substEq (λ Ψ → Θ ; Ψ ⊢ A ⇒ B) p (ƛ A ˙ N)
    ≡
    ƛ A ˙ substEq (λ Ψ → Θ ; Ψ ⊢ B) (cong (λ Ψ → Ψ , A) p) N
cast-ƛ-ctx-term refl N = refl

cast-ƛ-type-term : ∀ {Θ} {Γ : Ctx Θ} {A A' B B' : Type Θ}
  (pA : A ≡ A')
  (pB : B ≡ B')
  (N : Θ ; Γ , A ⊢ B)
  → substEq (λ T → Θ ; Γ ⊢ T) (cong₂ _⇒_ pA pB) (ƛ A ˙ N)
    ≡
    ƛ A' ˙
      substEq (λ Ψ → Θ ; Ψ ⊢ B')
        (cong (λ T → Γ , T) pA)
        (substEq (λ T → Θ ; Γ , A ⊢ T) pB N)
cast-ƛ-type-term refl refl N = refl

cast-∙-type-term : ∀ {Θ} {Γ : Ctx Θ}
  {A A' : Type (Θ ,α)} {B B' : Type Θ}
  (pA : A ≡ A')
  (pB : B ≡ B')
  (M : Θ ; Γ ⊢ `∀ A)
  → substEq (λ T → Θ ; Γ ⊢ T) (cong₂ _[_]ᵗ pA pB) (M ∙ B)
    ≡
    substEq (λ T → Θ ; Γ ⊢ T) (cong `∀_ pA) M ∙ B'
cast-∙-type-term refl refl M = refl

cast-∙-ctx-term : ∀ {Θ} {Γ Γ' : Ctx Θ}
  {A : Type (Θ ,α)} {B : Type Θ}
  (p : Γ ≡ Γ')
  (M : Θ ; Γ ⊢ `∀ A)
  → substEq (λ Ψ → Θ ; Ψ ⊢ A [ B ]ᵗ) p (M ∙ B)
    ≡
    substEq (λ Ψ → Θ ; Ψ ⊢ `∀ A) p M ∙ B
cast-∙-ctx-term refl M = refl

cast-Λ-type-term : ∀ {Θ} {Γ : Ctx Θ}
  {A A' : Type (Θ ,α)}
  (pA : A ≡ A')
  (N : Θ ,α ; ⇑ᶜ Γ ⊢ A)
  → substEq (λ T → Θ ; Γ ⊢ T) (cong `∀_ pA) (Λ N)
    ≡
    Λ (substEq (λ T → Θ ,α ; ⇑ᶜ Γ ⊢ T) pA N)
cast-Λ-type-term refl N = refl

cast-Λ-ctx-term : ∀ {Θ} {Γ Γ' : Ctx Θ}
  {A : Type (Θ ,α)}
  (pΓ : Γ ≡ Γ')
  (N : Θ ,α ; ⇑ᶜ Γ ⊢ A)
  → substEq (λ Ψ → Θ ; Ψ ⊢ `∀ A) pΓ (Λ N)
    ≡
    Λ (substEq (λ Ψ → Θ ,α ; Ψ ⊢ A) (cong ⇑ᶜ pΓ) N)
cast-Λ-ctx-term refl N = refl

SubstWk-[]ᵗ-coh→ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  (A : Type (Δ ,α))
  (B : Type Δ)
  → trans
      (substᵗ-[]ᵗ σ A B)
      (trans
        (cong₂ _[_]ᵗ
          (SubstWk-typeEq (swk-ext wk) A)
          (SubstWk-typeEq wk B))
        (sym (renameᵗ-[]ᵗ ξ A B)))
    ≡
    SubstWk-typeEq wk (A [ B ]ᵗ)
SubstWk-[]ᵗ-coh→ {σ = σ} {ξ = ξ} wk A B =
  uip-≡
    (trans
      (substᵗ-[]ᵗ σ A B)
      (trans
        (cong₂ _[_]ᵗ
          (SubstWk-typeEq (swk-ext wk) A)
          (SubstWk-typeEq wk B))
        (sym (renameᵗ-[]ᵗ ξ A B))))
    (SubstWk-typeEq wk (A [ B ]ᵗ))

SubstWk-[]ᵗ-coh : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  (A : Type (Δ ,α))
  (B : Type Δ)
  → trans
      (sym (substᵗ-[]ᵗ σ A B))
      (SubstWk-typeEq wk (A [ B ]ᵗ))
    ≡
    trans
      (cong₂ _[_]ᵗ
        (SubstWk-typeEq (swk-ext wk) A)
        (SubstWk-typeEq wk B))
      (sym (renameᵗ-[]ᵗ ξ A B))
SubstWk-[]ᵗ-coh {σ = σ} {ξ = ξ} wk A B =
  trans
    (cong (λ q → trans (sym (substᵗ-[]ᵗ σ A B)) q)
      (sym (SubstWk-[]ᵗ-coh→ wk A B)))
    (trans-sym-left (substᵗ-[]ᵗ σ A B)
      (trans
        (cong₂ _[_]ᵗ
          (SubstWk-typeEq (swk-ext wk) A)
          (SubstWk-typeEq wk B))
        (sym (renameᵗ-[]ᵗ ξ A B))))

cast↑-substᵀ↑ᵗ-var : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  (x : Γ ∋ A)
  → cast↑ (substᵀ ↑ᵗ (` x)) ≡ ⇑ᵀ (` x)
cast↑-substᵀ↑ᵗ-var {Γ = Γ} {A = A} x =
  trans
    (cong cast↑ᶜ
      (cast-var-type-term
        (substᵗ-↑ᵗ A)
        (substᵗ-∋ ↑ᵗ x)))
    (trans
      (cast↑ᶜ-var
        (substEq
          (λ T → substCtx ↑ᵗ Γ ∋ T)
          (substᵗ-↑ᵗ A)
          (substᵗ-∋ ↑ᵗ x)))
      (cong `_ (cast↑-∋-substᵗ-∋ x)))

-- Generalized form of cast↑-substᵀ↑ᵗ (parameterized by a SubstWk witness).
cast-substᵀ-renameᵀ-Λ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type (Δ ,α)}
  (N : Δ ,α ; ⇑ᶜ Γ ⊢ A)
  (ih : castWk (swk-ext wk) (substᵀ (extsᵗ σ) N) ≡ renameᵀ (extᵗ ξ) N)
  → castWk wk (substᵀ σ (Λ N)) ≡ renameᵀ ξ (Λ N)
cast-substᵀ-renameᵀ-Λ {Δ' = Δ'} {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} N ih =
  trans step-cast step-ih
  where
  pΓ : substCtx σ Γ ≡ renameCtx ξ Γ
  pΓ = SubstWk-ctxEq wk Γ

  pA : substᵗ (extsᵗ σ) A ≡ renameᵗ (extᵗ ξ) A
  pA = SubstWk-typeEq (swk-ext wk) A

  p∀ : substᵗ σ (`∀ A) ≡ renameᵗ ξ (`∀ A)
  p∀ = cong `∀_ pA

  pS : substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ ⇑ᶜ (substCtx σ Γ)
  pS = substCtx-extsᵗ-⇑ᶜ σ Γ

  pR : renameCtx (extᵗ ξ) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx ξ Γ)
  pR = renameCtx-extᵗ-⇑ᶜ ξ Γ

  pΓ⇑ : substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ renameCtx (extᵗ ξ) (⇑ᶜ Γ)
  pΓ⇑ = SubstWk-ctxEq (swk-ext wk) (⇑ᶜ Γ)

  pL : substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx ξ Γ)
  pL = trans pS (cong ⇑ᶜ pΓ)

  pRHS : substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx ξ Γ)
  pRHS = trans pΓ⇑ pR

  pBridge : pL ≡ pRHS
  pBridge = uip-≡ pL pRHS

  X : Δ' ,α ; substCtx (extsᵗ σ) (⇑ᶜ Γ) ⊢ substᵗ (extsᵗ σ) A
  X = substᵀ (extsᵗ σ) N

  body0 : Δ' ,α ; ⇑ᶜ (substCtx σ Γ) ⊢ substᵗ (extsᵗ σ) A
  body0 = substEq (_ ;_⊢ _) pS X

  step-cast :
      castWk wk (substᵀ σ (Λ N))
    ≡
      Λ (substEq (_ ;_⊢ _) pR (castWk (swk-ext wk) X))
  step-cast =
    trans
      (cong
        (substEq (λ Ψ → Δ' ; Ψ ⊢ `∀ renameᵗ (extᵗ ξ) A) pΓ)
        (cast-Λ-type-term pA body0))
      (trans
        (cast-Λ-ctx-term pΓ (substEq (λ T → Δ' ,α ; ⇑ᶜ (substCtx σ Γ) ⊢ T) pA body0))
        (cong Λ_
          (trans
            (cong
              (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ renameᵗ (extᵗ ξ) A) (cong ⇑ᶜ pΓ))
              (sym (cast-ctx-type-term pS pA X)))
            (trans
              (substEq-compose
                (λ Ψ → Δ' ,α ; Ψ ⊢ renameᵗ (extᵗ ξ) A)
                (cong ⇑ᶜ pΓ)
                pS
                (substEq (λ T → Δ' ,α ; substCtx (extsᵗ σ) (⇑ᶜ Γ) ⊢ T) pA X))
              (trans
                (cong
                  (λ p → substEq (λ Ψ → Δ' ,α ; Ψ ⊢ renameᵗ (extᵗ ξ) A) p
                    (substEq (λ T → Δ' ,α ; substCtx (extsᵗ σ) (⇑ᶜ Γ) ⊢ T) pA X))
                  pBridge)
                (sym
                  (substEq-compose
                    (λ Ψ → Δ' ,α ; Ψ ⊢ renameᵗ (extᵗ ξ) A)
                    pR
                    pΓ⇑
                    (substEq (λ T → Δ' ,α ; substCtx (extsᵗ σ) (⇑ᶜ Γ) ⊢ T) pA X))))))))

  step-ih :
      Λ (substEq (_ ;_⊢ _) pR (castWk (swk-ext wk) X))
    ≡
      renameᵀ ξ (Λ N)
  step-ih =
    cong Λ_ (cong (substEq (_ ;_⊢ _) pR) ih)

cast-substᵀ-renameᵀ-∙ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type (Δ ,α)}
  (M : Δ ; Γ ⊢ `∀ A)
  (B : Type Δ)
  (ih : castWk wk (substᵀ σ M) ≡ renameᵀ ξ M)
  → castWk wk (substᵀ σ (M ∙ B)) ≡ renameᵀ ξ (M ∙ B)
cast-substᵀ-renameᵀ-∙ {Δ' = Δ'} {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} M B ih =
  trans step-cast step-ih
  where
  pΓ : substCtx σ Γ ≡ renameCtx ξ Γ
  pΓ = SubstWk-ctxEq wk Γ

  pA : substᵗ (extsᵗ σ) A ≡ renameᵗ (extᵗ ξ) A
  pA = SubstWk-typeEq (swk-ext wk) A

  pB : substᵗ σ B ≡ renameᵗ ξ B
  pB = SubstWk-typeEq wk B

  p∀ : substᵗ σ (`∀ A) ≡ renameᵗ ξ (`∀ A)
  p∀ = cong `∀_ pA

  pAB : substᵗ σ (A [ B ]ᵗ) ≡ renameᵗ ξ (A [ B ]ᵗ)
  pAB = SubstWk-typeEq wk (A [ B ]ᵗ)

  pSub : (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ ≡ substᵗ σ (A [ B ]ᵗ)
  pSub = sym (substᵗ-[]ᵗ σ A B)

  pRen : renameᵗ (extᵗ ξ) A [ renameᵗ ξ B ]ᵗ ≡ renameᵗ ξ (A [ B ]ᵗ)
  pRen = sym (renameᵗ-[]ᵗ ξ A B)

  p∙ : (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ
        ≡ renameᵗ (extᵗ ξ) A [ renameᵗ ξ B ]ᵗ
  p∙ = cong₂ _[_]ᵗ pA pB

  X : Δ' ; substCtx σ Γ ⊢ (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ
  X = substᵀ σ M ∙ substᵗ σ B

  Mcast : Δ' ; renameCtx ξ Γ ⊢ `∀ substᵗ (extsᵗ σ) A
  Mcast = substEq (λ Ψ → Δ' ; Ψ ⊢ `∀ substᵗ (extsᵗ σ) A) pΓ (substᵀ σ M)

  appT : Δ' ; renameCtx ξ Γ ⊢ `∀ renameᵗ (extᵗ ξ) A
    → Δ' ; renameCtx ξ Γ ⊢ renameᵗ (extᵗ ξ) A [ renameᵗ ξ B ]ᵗ
  appT N = _∙_ {A = renameᵗ (extᵗ ξ) A} N (renameᵗ ξ B)

  step-cast :
      castWk wk (substᵀ σ (M ∙ B))
    ≡ substEq (λ T → Δ' ; renameCtx ξ Γ ⊢ T) pRen
        (appT (castWk wk (substᵀ σ M)))
  step-cast =
    trans
      (cong
        (substEq (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ξ (A [ B ]ᵗ)) pΓ)
        (substEq-compose (λ T → Δ' ; substCtx σ Γ ⊢ T) pAB pSub X))
      (trans
        (cong
          (substEq (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ξ (A [ B ]ᵗ)) pΓ)
          (cong
            (λ p → substEq (λ T → Δ' ; substCtx σ Γ ⊢ T) p X)
            (SubstWk-[]ᵗ-coh wk A B)))
        (trans
          (cong
            (substEq (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ξ (A [ B ]ᵗ)) pΓ)
            (sym (substEq-compose (λ T → Δ' ; substCtx σ Γ ⊢ T) pRen p∙ X)))
          (trans
            (cast-ctx-type-term
              pΓ
              pRen
              (substEq (λ T → Δ' ; substCtx σ Γ ⊢ T) p∙ X))
            (trans
              (cong
                (substEq (λ T → Δ' ; renameCtx ξ Γ ⊢ T) pRen)
                (cast-ctx-type-term pΓ p∙ X))
              (trans
                (cong
                  (substEq (λ T → Δ' ; renameCtx ξ Γ ⊢ T) pRen)
                  (cong
                    (substEq
                      (λ T → Δ' ; renameCtx ξ Γ ⊢ T)
                      p∙)
                    (cast-∙-ctx-term pΓ (substᵀ σ M))))
                (trans
                  (cong
                    (substEq (λ T → Δ' ; renameCtx ξ Γ ⊢ T) pRen)
                    (cast-∙-type-term pA pB Mcast))
                  (cong
                    (substEq (λ T → Δ' ; renameCtx ξ Γ ⊢ T) pRen)
                    (cong
                      appT
                      (sym (cast-ctx-type-term pΓ p∀ (substᵀ σ M)))))))))))

  step-ih :
      substEq (λ T → Δ' ; renameCtx ξ Γ ⊢ T) pRen
        (appT (castWk wk (substᵀ σ M)))
    ≡ renameᵀ ξ (M ∙ B)
  step-ih =
    cong
      (substEq (λ T → Δ' ; renameCtx ξ Γ ⊢ T) pRen)
      (cong appT ih)

castWk-suc : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ}
  (N : Δ' ; substCtx σ Γ ⊢ `Nat)
  → castWk wk (`suc N) ≡ `suc (castWk wk N)
castWk-suc {σ = σ} {ξ = ξ} wk {Γ = Γ} N
  rewrite SubstWk-ctxEq wk Γ = refl

castWk-if : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type Δ}
  (L : Δ' ; substCtx σ Γ ⊢ `Bool)
  (M N : Δ' ; substCtx σ Γ ⊢ substᵗ σ A)
  → castWk wk (`if_then_else {A = substᵗ σ A} L M N)
    ≡ `if_then_else {A = renameᵗ ξ A} (castWk wk L) (castWk wk M) (castWk wk N)
castWk-if {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} L M N
  rewrite SubstWk-ctxEq wk Γ
        | SubstWk-typeEq wk A = refl

castWk-case-nat : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type Δ}
  (L : Δ' ; substCtx σ Γ ⊢ `Nat)
  (M : Δ' ; substCtx σ Γ ⊢ substᵗ σ A)
  (N : Δ' ; substCtx σ Γ , `Nat ⊢ substᵗ σ A)
  → castWk wk (`case-nat {A = substᵗ σ A} L M N)
    ≡ `case-nat {A = renameᵗ ξ A}
        (castWk wk L)
        (castWk wk M)
        (castWk wk {Γ = Γ , `Nat} {A = A} N)
castWk-case-nat {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} L M N
  rewrite SubstWk-ctxEq wk Γ
        | SubstWk-typeEq wk A = refl

castWk-ƛ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A B : Type Δ}
  (N : Δ' ; substCtx σ Γ , substᵗ σ A ⊢ substᵗ σ B)
  → castWk wk (ƛ substᵗ σ A ˙ N)
    ≡ ƛ renameᵗ ξ A ˙ castWk wk {Γ = Γ , A} {A = B} N
castWk-ƛ {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} {B = B} N
  rewrite SubstWk-ctxEq wk Γ
        | SubstWk-typeEq wk A
        | SubstWk-typeEq wk B = refl

castWk-· : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A B : Type Δ}
  (L : Δ' ; substCtx σ Γ ⊢ substᵗ σ (A ⇒ B))
  (M : Δ' ; substCtx σ Γ ⊢ substᵗ σ A)
  → castWk wk (L · M)
    ≡ castWk wk {A = A ⇒ B} L · castWk wk {A = A} M
castWk-· {Δ' = Δ'} {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} {B = B} L M =
  trans
    (cong
      (substEq (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ξ B) (SubstWk-ctxEq wk Γ))
      (cast-app-type-term
        (SubstWk-typeEq wk A)
        (SubstWk-typeEq wk B)
        L M))
    (cast-app-ctx-term
      (SubstWk-ctxEq wk Γ)
      (substEq (λ T → Δ' ; substCtx σ Γ ⊢ T)
        (SubstWk-typeEq wk (A ⇒ B))
        L)
      (substEq (λ T → Δ' ; substCtx σ Γ ⊢ T)
        (SubstWk-typeEq wk A)
        M))

cast-subst-var-test : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type Δ}
  (x : Γ ∋ A)
  → castWk wk (substᵀ σ (` x)) ≡ renameᵀ ξ (` x)
cast-subst-var-test {Δ' = Δ'} {σ = σ} {ξ = ξ} wk {Γ = Γ} {A = A} x =
  trans
    (cong
      (substEq (λ Ψ → Δ' ; Ψ ⊢ renameᵗ ξ A) (SubstWk-ctxEq wk Γ))
      (cast-var-type-term
        (SubstWk-typeEq wk A)
        (substᵗ-∋ σ x)))
    (trans
      (cast-var-term
        (SubstWk-ctxEq wk Γ)
        (substEq
          (λ T → substCtx σ Γ ∋ T)
          (SubstWk-typeEq wk A)
          (substᵗ-∋ σ x)))
      (cong `_ (castWk-∋-substᵗ-∋ wk x)))

cast-substᵀ-renameᵀ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {ξ : Δ ⇒ʳ Δ'}
  (wk : SubstWk σ ξ)
  {Γ : Ctx Δ} {A : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → castWk wk (substᵀ σ M) ≡ renameᵀ ξ M
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk {Γ = Γ} `zero
  rewrite SubstWk-ctxEq wk Γ = refl
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk {Γ = Γ} `true
  rewrite SubstWk-ctxEq wk Γ = refl
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk {Γ = Γ} `false
  rewrite SubstWk-ctxEq wk Γ = refl
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk (`suc M) =
  trans
    (castWk-suc wk (substᵀ σ M))
    (cong `suc_ (cast-substᵀ-renameᵀ wk M))
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk {Γ = Γ} (`case-nat L M N) =
  trans
    (castWk-case-nat wk (substᵀ σ L) (substᵀ σ M) (substᵀ σ N))
    step
  where
  step : `case-nat
           (castWk wk (substᵀ σ L))
           (castWk wk (substᵀ σ M))
           (castWk wk {Γ = Γ , `Nat} {A = _} (substᵀ σ N))
       ≡ `case-nat (renameᵀ ξ L) (renameᵀ ξ M) (renameᵀ ξ N)
  step
    rewrite cast-substᵀ-renameᵀ wk L
          | cast-substᵀ-renameᵀ wk M
          | cast-substᵀ-renameᵀ wk N = refl
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk (`if_then_else L M N) =
  trans
    (castWk-if wk (substᵀ σ L) (substᵀ σ M) (substᵀ σ N))
    step
  where
  step : `if_then_else
           (castWk wk (substᵀ σ L))
           (castWk wk (substᵀ σ M))
           (castWk wk (substᵀ σ N))
       ≡ `if_then_else (renameᵀ ξ L) (renameᵀ ξ M) (renameᵀ ξ N)
  step
    rewrite cast-substᵀ-renameᵀ wk L
          | cast-substᵀ-renameᵀ wk M
          | cast-substᵀ-renameᵀ wk N = refl
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk (` x) = cast-subst-var-test wk x
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk (ƛ A ˙ N) =
  trans
    (castWk-ƛ wk (substᵀ σ N))
    (cong (ƛ renameᵗ ξ A ˙_) (cast-substᵀ-renameᵀ wk N))
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk (L · M) =
  trans
    (castWk-· wk (substᵀ σ L) (substᵀ σ M))
    (cong₂ _·_ (cast-substᵀ-renameᵀ wk L) (cast-substᵀ-renameᵀ wk M))
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk (Λ N) =
  cast-substᵀ-renameᵀ-Λ wk N (cast-substᵀ-renameᵀ (swk-ext wk) N)
cast-substᵀ-renameᵀ {σ = σ} {ξ = ξ} wk (_∙_ {A = A} M B) =
  cast-substᵀ-renameᵀ-∙ wk {A = A} M B (cast-substᵀ-renameᵀ wk M)

substᵀ-ren-renameᵀ : ∀ {Δ Δ' Γ A} (ρ : Δ ⇒ʳ Δ') (M : Δ ; Γ ⊢ A)
  → castWk (swk-ren ρ) (substᵀ (renᵀ ρ) M) ≡ renameᵀ ρ M
substᵀ-ren-renameᵀ ρ M = cast-substᵀ-renameᵀ (swk-ren ρ) M

cast↑-substᵀ↑ᵗ-generalized : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → castWk swk-↑ (substᵀ ↑ᵗ M) ≡ ⇑ᵀ M
cast↑-substᵀ↑ᵗ-generalized M = cast-substᵀ-renameᵀ swk-↑ M

castWk-swk-↑-cast↑ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  (M : Δ ,α ; substCtx ↑ᵗ Γ ⊢ substᵗ ↑ᵗ A)
  → castWk swk-↑ M ≡ cast↑ M
castWk-swk-↑-cast↑ {Δ = Δ} {Γ = Γ} {A = A} M =
  trans
    (cong
      (substEq (λ Ψ → Δ ,α ; Ψ ⊢ renameᵗ S_ A) (SubstWk-ctxEq swk-↑ Γ))
      (cong
        (λ p → substEq (λ T → Δ ,α ; substCtx ↑ᵗ Γ ⊢ T) p M)
        (uip-≡ (SubstWk-typeEq swk-↑ A) (substᵗ-↑ᵗ A))))
    (cong
      (λ p → substEq
        (λ Ψ → Δ ,α ; Ψ ⊢ renameᵗ S_ A)
        p
        (substEq (λ T → Δ ,α ; substCtx ↑ᵗ Γ ⊢ T) (substᵗ-↑ᵗ A) M))
      (uip-≡ (SubstWk-ctxEq swk-↑ Γ) (substCtx-↑ᵗ Γ)))

cast↑-substᵀ↑ᵗ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → cast↑ (substᵀ ↑ᵗ M) ≡ ⇑ᵀ M
cast↑-substᵀ↑ᵗ M =
  trans
    (sym (castWk-swk-↑-cast↑ (substᵀ ↑ᵗ M)))
    (cast↑-substᵀ↑ᵗ-generalized M)

mutual
  rename-mapʳᵀ-renameᵀ-Λ-body : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
    {Γ Γ' : Ctx Δ}
    {A : Type (Δ ,α)}
    (ρ : Γ →ʳ Γ')
    (N : Δ ,α ; ⇑ᶜ Γ ⊢ A)
    → rename (⇑ʳ (mapʳᵀ ξ ρ))
        (substEq (_ ;_⊢ _)
          (renameCtx-extᵗ-⇑ᶜ ξ Γ)
          (renameᵀ (extᵗ ξ) N))
      ≡
      substEq (_ ;_⊢ _)
        (renameCtx-extᵗ-⇑ᶜ ξ Γ')
        (renameᵀ (extᵗ ξ) (rename (⇑ʳ ρ) N))
  rename-mapʳᵀ-renameᵀ-Λ-body ξ {Γ = Γ} {Γ' = Γ'} ρ N =
    trans
      (rename-substEqᶜ
        (renameCtx-extᵗ-⇑ᶜ ξ Γ)
        (renameCtx-extᵗ-⇑ᶜ ξ Γ')
        (⇑ʳ (mapʳᵀ ξ ρ))
        (mapʳᵀ (extᵗ ξ) (⇑ʳ ρ))
        (mapʳᵀ-extᵗ-⇑ʳ-coh ξ ρ)
        (renameᵀ (extᵗ ξ) N))
      (cong
        (substEq (_ ;_⊢ _) (renameCtx-extᵗ-⇑ᶜ ξ Γ'))
        (rename-mapʳᵀ-renameᵀ (extᵗ ξ) (⇑ʳ ρ) N))

  rename-mapʳᵀ-renameᵀ : ∀ {Δ Δ'} (ξ : Δ ⇒ʳ Δ')
    {Γ Γ' : Ctx Δ} {A : Type Δ}
    (ρ : Γ →ʳ Γ')
    (M : Δ ; Γ ⊢ A)
    → rename (mapʳᵀ ξ ρ) (renameᵀ ξ M)
      ≡ renameᵀ ξ (rename ρ M)
  rename-mapʳᵀ-renameᵀ ξ ρ `zero = refl
  rename-mapʳᵀ-renameᵀ ξ ρ `true = refl
  rename-mapʳᵀ-renameᵀ ξ ρ `false = refl
  rename-mapʳᵀ-renameᵀ ξ ρ (`suc M) =
    cong `suc_ (rename-mapʳᵀ-renameᵀ ξ ρ M)
  rename-mapʳᵀ-renameᵀ ξ ρ (`case-nat L M N)
    rewrite rename-mapʳᵀ-renameᵀ ξ ρ L
          | rename-mapʳᵀ-renameᵀ ξ ρ M =
    cong (`case-nat (renameᵀ ξ (rename ρ L)) (renameᵀ ξ (rename ρ M)))
      (trans
        (sym (rename-cong (mapʳᵀ-ext ξ {A = `Nat} ρ) (renameᵀ ξ N)))
        (rename-mapʳᵀ-renameᵀ ξ (ext ρ) N))
  rename-mapʳᵀ-renameᵀ ξ ρ (`if_then_else L M N)
    rewrite rename-mapʳᵀ-renameᵀ ξ ρ L
          | rename-mapʳᵀ-renameᵀ ξ ρ M
          | rename-mapʳᵀ-renameᵀ ξ ρ N = refl
  rename-mapʳᵀ-renameᵀ ξ ρ (` x) = cong `_ (mapʳᵀ-∋ ξ ρ x)
  rename-mapʳᵀ-renameᵀ ξ ρ (ƛ A ˙ N) =
    cong (ƛ renameᵗ ξ A ˙_)
      (trans
        (sym (rename-cong (mapʳᵀ-ext ξ {A = A} ρ) (renameᵀ ξ N)))
        (rename-mapʳᵀ-renameᵀ ξ (ext ρ) N))
  rename-mapʳᵀ-renameᵀ ξ ρ (L · M)
    rewrite rename-mapʳᵀ-renameᵀ ξ ρ L
          | rename-mapʳᵀ-renameᵀ ξ ρ M = refl
  rename-mapʳᵀ-renameᵀ ξ ρ (Λ N) =
    cong Λ_ (rename-mapʳᵀ-renameᵀ-Λ-body ξ ρ N)
  rename-mapʳᵀ-renameᵀ {Δ' = Δ'} ξ {Γ = Γ} {Γ' = Γ'} ρ (_∙_ {A = A} M B) =
    trans
      (rename-substEq
        {Δ = Δ'}
        {Γ' = renameCtx ξ Γ}
        {Γ'' = renameCtx ξ Γ'}
        (mapʳᵀ ξ ρ)
        {A = (renameᵗ (extᵗ ξ) A) [ renameᵗ ξ B ]ᵗ}
        {B = renameᵗ ξ (A [ B ]ᵗ)}
        (sym (renameᵗ-[]ᵗ ξ A B))
        (renameᵀ ξ M ∙ renameᵗ ξ B))
      (cong
        (substEq (λ T → Δ' ; renameCtx ξ Γ' ⊢ T)
          (sym (renameᵗ-[]ᵗ ξ A B)))
        (cong (_∙ renameᵗ ξ B) (rename-mapʳᵀ-renameᵀ ξ ρ M)))

⇑ʳ-⇑ˢ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ}
  (ρ : Γ₂ →ʳ Γ₃)
  (σ : Γ₁ →ˢ Γ₂)
  → ∀ {A} (x : ⇑ᶜ Γ₁ ∋ A)
  → rename (⇑ʳ ρ) (⇑ˢ σ x) ≡ ⇑ˢ (λ y → rename ρ (σ y)) x
⇑ʳ-⇑ˢ {Γ₁ = ∅} ρ σ ()
⇑ʳ-⇑ˢ {Γ₁ = Γ₁ , B} ρ σ Z =
  trans
    (rename-cong (λ x → sym (mapʳᵀ-S ρ x)) (⇑ᵀ (σ Z)))
    (rename-mapʳᵀ-renameᵀ S_ ρ (σ Z))
⇑ʳ-⇑ˢ {Γ₁ = Γ₁ , B} ρ σ (S x) =
  ⇑ʳ-⇑ˢ ρ (λ y → σ (S y)) x

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

--------------------------------------------------------------------------------
-- Commuting theorems: mixed term/type substitution (generalized over τ)
--------------------------------------------------------------------------------

-- Map a term substitution through a type substitution.
substᵀ-map : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ') {Γ Γ' : Ctx Δ}
  → Γ →ˢ Γ'
  → substCtx τ Γ →ˢ substCtx τ Γ'
substᵀ-map τ {Γ = ∅} σ ()
substᵀ-map τ {Γ = Γ , A} σ Z = substᵀ τ (σ Z)
substᵀ-map τ {Γ = Γ , A} σ (S x) = substᵀ-map τ (λ y → σ (S y)) x

substᵀ-map-∋ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ') {Γ Γ' : Ctx Δ}
  (σ : Γ →ˢ Γ') {A} (x : Γ ∋ A)
  → substᵀ-map τ σ (substᵗ-∋ τ x) ≡ substᵀ τ (σ x)
substᵀ-map-∋ τ σ Z = refl
substᵀ-map-∋ τ σ (S x) = substᵀ-map-∋ τ (λ y → σ (S y)) x

mapʳˢ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ') {Γ Γ' : Ctx Δ}
  → Γ →ʳ Γ'
  → substCtx τ Γ →ʳ substCtx τ Γ'
mapʳˢ τ {Γ = ∅} ρ ()
mapʳˢ τ {Γ = Γ , A} ρ Z = substᵗ-∋ τ (ρ Z)
mapʳˢ τ {Γ = Γ , A} ρ (S x) = mapʳˢ τ (λ y → ρ (S y)) x

mapʳˢ-liftS : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (ρ : Γ →ʳ Γ')
  → ∀ {B} (x : substCtx τ Γ ∋ B)
  → mapʳˢ τ (λ y → S_ {B = A} (ρ y)) x
    ≡ S_ {B = substᵗ τ A} (mapʳˢ τ ρ x)
mapʳˢ-liftS τ {Γ = ∅} ρ ()
mapʳˢ-liftS τ {Γ = Γ , C} ρ Z = refl
mapʳˢ-liftS τ {Γ = Γ , C} ρ (S x) =
  mapʳˢ-liftS τ (λ y → ρ (S y)) x

mapʳˢ-ext : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (ρ : Γ →ʳ Γ')
  → ∀ {B} (x : substCtx τ (Γ , A) ∋ B)
  → mapʳˢ τ (ext {A = A} ρ) x
    ≡ ext {A = substᵗ τ A} (mapʳˢ τ ρ) x
mapʳˢ-ext τ {A = A} ρ Z = refl
mapʳˢ-ext τ {A = A} ρ (S x) = mapʳˢ-liftS τ {A = A} ρ x

mapʳˢ-∋ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ}
  (ρ : Γ →ʳ Γ')
  {A}
  (x : Γ ∋ A)
  → mapʳˢ τ ρ (substᵗ-∋ τ x) ≡ substᵗ-∋ τ (ρ x)
mapʳˢ-∋ τ ρ Z = refl
mapʳˢ-∋ τ ρ (S x) =
  mapʳˢ-∋ τ (λ y → ρ (S y)) x

substᵗ-shift : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ') (B : Type Δ)
  → substᵗ (extsᵗ τ) (renameᵗ S_ B) ≡ renameᵗ S_ (substᵗ τ B)
substᵗ-shift τ B =
  trans
    (ren-subᵗ S_ (extsᵗ τ) B)
    (sym (sub-renᵗ S_ τ B))

cast-substCtx-extsᵗ-⇑ᶜ-Z : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ : Ctx Δ} {B : Type Δ}
  → substEq
      (λ Ψ → Ψ ∋ substᵗ (extsᵗ τ) (renameᵗ S_ B))
      (substCtx-extsᵗ-⇑ᶜ τ (Γ , B))
      Z
    ≡
    substEq
      (λ T → ⇑ᶜ (substCtx τ (Γ , B)) ∋ T)
      (sym (substᵗ-shift τ B))
      Z
cast-substCtx-extsᵗ-⇑ᶜ-Z τ {Γ} {B}
  rewrite substCtx-extsᵗ-⇑ᶜ τ Γ
        | ren-subᵗ S_ (extsᵗ τ) B
        | sym (sub-renᵗ S_ τ B) = refl

cast-substCtx-extsᵗ-⇑ᶜ-S : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ : Ctx Δ} {B : Type Δ} {A : Type (Δ' ,α)}
  (x : substCtx (extsᵗ τ) (⇑ᶜ Γ) ∋ A)
  → substEq
      (λ Ψ → Ψ ∋ A)
      (substCtx-extsᵗ-⇑ᶜ τ (Γ , B))
      (S x)
    ≡
    S (substEq
        (λ Ψ → Ψ ∋ A)
        (substCtx-extsᵗ-⇑ᶜ τ Γ)
        x)
cast-substCtx-extsᵗ-⇑ᶜ-S τ {Γ} {B} x
  rewrite substCtx-extsᵗ-⇑ᶜ τ Γ
        | ren-subᵗ S_ (extsᵗ τ) B
        | sym (sub-renᵗ S_ τ B) = refl

cast-substCtx-extsᵗ-⇑ᶜ-substᵗ-∋S : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ : Ctx Δ} {B : Type Δ}
  (y : Γ ∋ B)
  → substEq
      (λ Ψ → Ψ ∋ substᵗ (extsᵗ τ) (renameᵗ S_ B))
      (substCtx-extsᵗ-⇑ᶜ τ Γ)
      (substᵗ-∋ (extsᵗ τ) (renameᵗ-∋ S_ y))
    ≡
    substEq
      (λ T → ⇑ᶜ (substCtx τ Γ) ∋ T)
      (sym (substᵗ-shift τ B))
      (renameᵗ-∋ S_ (substᵗ-∋ τ y))
cast-substCtx-extsᵗ-⇑ᶜ-substᵗ-∋S τ {Γ = Γ , B} {B = B} Z
  rewrite substCtx-extsᵗ-⇑ᶜ τ Γ
        | ren-subᵗ S_ (extsᵗ τ) B
        | sym (sub-renᵗ S_ τ B) = refl
cast-substCtx-extsᵗ-⇑ᶜ-substᵗ-∋S τ {Γ = Γ , C} {B = B} (S y) =
  trans
    (cast-substCtx-extsᵗ-⇑ᶜ-S τ
      {Γ = Γ} {B = C}
      (substᵗ-∋ (extsᵗ τ) (renameᵗ-∋ S_ y)))
    (trans
      (cong S_ (cast-substCtx-extsᵗ-⇑ᶜ-substᵗ-∋S τ {Γ = Γ} {B = B} y))
      (sym
        (cast-∋-Sᵗ
          {Γ = ⇑ᶜ (substCtx τ Γ)}
          {C = renameᵗ S_ (substᵗ τ C)}
          (sym (substᵗ-shift τ B))
          (renameᵗ-∋ S_ (substᵗ-∋ τ y)))))

mapʳˢ-extᵗ-⇑ʳ-coh : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ}
  (ρ : Γ →ʳ Γ')
  → ∀ {A} (x : substCtx (extsᵗ τ) (⇑ᶜ Γ) ∋ A)
  → substEq (λ Ψ → Ψ ∋ A)
      (substCtx-extsᵗ-⇑ᶜ τ Γ')
      (mapʳˢ (extsᵗ τ) (⇑ʳ ρ) x)
    ≡
    ⇑ʳ (mapʳˢ τ ρ)
      (substEq (λ Ψ → Ψ ∋ A)
        (substCtx-extsᵗ-⇑ᶜ τ Γ)
        x)
mapʳˢ-extᵗ-⇑ʳ-coh τ {Γ = ∅} ρ ()
mapʳˢ-extᵗ-⇑ʳ-coh τ {Γ = Γ , B} ρ Z
  rewrite cast-substCtx-extsᵗ-⇑ᶜ-Z τ {Γ = Γ} {B = B} =
  trans
    (cast-substCtx-extsᵗ-⇑ᶜ-substᵗ-∋S τ (ρ Z))
    (sym (⇑ʳ-castᵗ
      (mapʳˢ τ ρ)
      (sym (substᵗ-shift τ B))
      Z))
mapʳˢ-extᵗ-⇑ʳ-coh τ {Γ = Γ , B} ρ (S x)
  rewrite cast-substCtx-extsᵗ-⇑ᶜ-S τ {Γ = Γ} {B = B} x =
  mapʳˢ-extᵗ-⇑ʳ-coh τ (λ y → ρ (S y)) x

mapʳˢ-S : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ : Ctx Δ}
  {B : Type Δ}
  → ∀ {A} (x : substCtx τ Γ ∋ A)
  → mapʳˢ τ (S_ {B = B}) x ≡ S_ {B = substᵗ τ B} x
mapʳˢ-S τ {Γ = ∅} ()
mapʳˢ-S τ {Γ = Γ , B₀} {B = B} Z = refl
mapʳˢ-S τ {Γ = Γ , B₀} {B = B} (S x) =
  trans
    (mapʳˢ-liftS τ {A = B} (S_ {B = B₀}) x)
    (cong (S_ {B = substᵗ τ B}) (mapʳˢ-S τ {B = B₀} x))

mutual
  substᵀ-rename-Λ-body : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
    {Γ Γ' : Ctx Δ}
    {A : Type (Δ ,α)}
    (ρ : Γ →ʳ Γ')
    (N : Δ ,α ; ⇑ᶜ Γ ⊢ A)
    → substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ τ Γ')
        (substᵀ (extsᵗ τ) (rename (⇑ʳ ρ) N))
      ≡
      rename (⇑ʳ (mapʳˢ τ ρ))
        (substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ τ Γ)
          (substᵀ (extsᵗ τ) N))
  substᵀ-rename-Λ-body {Δ = Δ} {Δ' = Δ'} τ {Γ = Γ} {Γ' = Γ'} {A = A} ρ N =
    trans
      (cong
        (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) A)
          (substCtx-extsᵗ-⇑ᶜ τ Γ'))
        (substᵀ-rename (extsᵗ τ) (⇑ʳ ρ) N))
      (sym
        (rename-substEqᶜ
          (substCtx-extsᵗ-⇑ᶜ τ Γ)
          (substCtx-extsᵗ-⇑ᶜ τ Γ')
          (⇑ʳ (mapʳˢ τ ρ))
          (mapʳˢ (extsᵗ τ) (⇑ʳ ρ))
          (mapʳˢ-extᵗ-⇑ʳ-coh τ ρ)
          (substᵀ (extsᵗ τ) N)))

  substᵀ-rename : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
    {Γ Γ' : Ctx Δ} {A : Type Δ}
    (ρ : Γ →ʳ Γ')
    (M : Δ ; Γ ⊢ A)
    → substᵀ τ (rename ρ M)
      ≡ rename (mapʳˢ τ ρ) (substᵀ τ M)
  substᵀ-rename τ ρ `zero = refl
  substᵀ-rename τ ρ `true = refl
  substᵀ-rename τ ρ `false = refl
  substᵀ-rename τ ρ (`suc M) =
    cong `suc_ (substᵀ-rename τ ρ M)
  substᵀ-rename τ ρ (`case-nat L M N)
    rewrite substᵀ-rename τ ρ L
          | substᵀ-rename τ ρ M =
    cong
      (`case-nat (rename (mapʳˢ τ ρ) (substᵀ τ L))
                 (rename (mapʳˢ τ ρ) (substᵀ τ M)))
      (trans
        (substᵀ-rename τ (ext ρ) N)
        (rename-cong (mapʳˢ-ext τ {A = `Nat} ρ) (substᵀ τ N)))
  substᵀ-rename τ ρ (`if_then_else L M N)
    rewrite substᵀ-rename τ ρ L
          | substᵀ-rename τ ρ M
          | substᵀ-rename τ ρ N = refl
  substᵀ-rename τ ρ (` x) =
    cong `_ (sym (mapʳˢ-∋ τ ρ x))
  substᵀ-rename τ ρ (ƛ A ˙ N) =
    cong
      (ƛ substᵗ τ A ˙_)
      (trans
        (substᵀ-rename τ (ext ρ) N)
        (rename-cong (mapʳˢ-ext τ {A = A} ρ) (substᵀ τ N)))
  substᵀ-rename τ ρ (L · M)
    rewrite substᵀ-rename τ ρ L
          | substᵀ-rename τ ρ M = refl
  substᵀ-rename τ ρ (Λ N) =
    cong Λ_ (substᵀ-rename-Λ-body τ ρ N)
  substᵀ-rename {Δ' = Δ'} τ {Γ = Γ} {Γ' = Γ'} ρ (_∙_ {A = A} M B) =
    trans
      (cong
        (substEq
          (λ T → Δ' ; substCtx τ Γ' ⊢ T)
          (sym (substᵗ-[]ᵗ τ A B)))
        (cong (_∙ substᵗ τ B) (substᵀ-rename τ ρ M)))
      (sym
        (rename-substEq
          (mapʳˢ τ ρ)
          (sym (substᵗ-[]ᵗ τ A B))
          (substᵀ τ M ∙ substᵗ τ B)))

substᵀ-⇑ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ') {Γ : Ctx Δ} {A B : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → substᵀ τ (⇑ {B = B} M) ≡ ⇑ {B = substᵗ τ B} (substᵀ τ M)
substᵀ-⇑ τ {B = B} M =
  trans
    (substᵀ-rename τ (S_ {B = B}) M)
    (rename-cong (mapʳˢ-S τ {B = B}) (substᵀ τ M))

substᵀ-map-shift : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} (σ : Γ →ˢ Γ')
  {A : Type Δ} {B : Type Δ'} (x : substCtx τ Γ ∋ B)
  → substᵀ-map τ (λ y → ⇑ {B = A} (σ y)) x
    ≡ ⇑ {B = substᵗ τ A} (substᵀ-map τ σ x)
substᵀ-map-shift τ {Γ = ∅} σ ()
substᵀ-map-shift τ {Γ = Γ , C} σ {A = A} Z = substᵀ-⇑ τ (σ Z)
substᵀ-map-shift τ {Γ = Γ , C} σ {A = A} (S x) =
  substᵀ-map-shift τ (λ y → σ (S y)) {A = A} x

substᵀ-map-exts : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (σ : Γ →ˢ Γ')
  → ∀ {B : Type Δ'} (x : substCtx τ (Γ , A) ∋ B)
  → substᵀ-map τ (exts {A = A} σ) x
    ≡ exts {A = substᵗ τ A} (substᵀ-map τ σ) x
substᵀ-map-exts τ σ Z = refl
substᵀ-map-exts τ {Γ = Γ} {Γ' = Γ'} {A = A} σ (S x) =
  substᵀ-map-shift τ σ {A = A} x

substᵀ-map-exts-subst : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ} {B : Type Δ'}
  (σ : Γ →ˢ Γ')
  (N : Δ' ; substCtx τ (Γ , A) ⊢ B)
  → subst (exts {A = substᵗ τ A} (substᵀ-map τ σ)) N
    ≡ subst (substᵀ-map τ (exts {A = A} σ)) N
substᵀ-map-exts-subst τ {Γ = Γ} {Γ' = Γ'} {A = A} σ N =
  sym (subst-cong (substᵀ-map-exts τ {A = A} σ) N)

substᵀ-map-tail : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} {B : Type Δ}
  (σ : (Γ , B) →ˢ Γ')
  → ∀ {A} (x : substCtx τ Γ ∋ A)
  → substᵀ-map τ (λ y → σ (S y)) x
    ≡ substᵀ-map τ σ (S x)
substᵀ-map-tail τ {Γ = ∅} σ ()
substᵀ-map-tail τ {Γ = Γ , C} σ Z = refl
substᵀ-map-tail τ {Γ = Γ , C} σ (S x) =
  substᵀ-map-tail τ (λ y → σ (S y)) x

--------------------------------------------------------------------------------
-- Binder-lifted coherence helpers
--------------------------------------------------------------------------------

subst-substEq : ∀ {Δ} {Γ Γ' : Ctx Δ} (σ : Γ →ˢ Γ')
  {A B : Type Δ}
  (p : A ≡ B)
  (M : Δ ; Γ ⊢ A)
  → subst σ (substEq (λ T → Δ ; Γ ⊢ T) p M)
    ≡ substEq (λ T → Δ ; Γ' ⊢ T) p (subst σ M)
subst-substEq σ refl M = refl

substᵀ-extsᵗ-⇑ᵀ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ : Ctx Δ}
  {A : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → substEq
      (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ A))
      (substCtx-extsᵗ-⇑ᶜ τ Γ)
      (substᵀ (extsᵗ τ) (⇑ᵀ M))
    ≡
    substEq
      (λ T → Δ' ,α ; ⇑ᶜ (substCtx τ Γ) ⊢ T)
      (sym (substᵗ-shift τ A))
      (⇑ᵀ (substᵀ τ M))

data ShiftSubst : ∀ {Δ Δ'}
  (σ : Δ ⇒ˢ Δ')
  (σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)) → Set where
  shift-subst : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
    (eq↑ : σ↑ ≡ extsᵗ σ)
    → ShiftSubst σ σ↑

shiftSubst-exts : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') → ShiftSubst σ (extsᵗ σ)
shiftSubst-exts σ = shift-subst refl

shiftSubst-ext : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  → ShiftSubst σ σ↑
  → ShiftSubst (extsᵗ σ) (extsᵗ σ↑)
shiftSubst-ext (shift-subst eq↑) = shift-subst (cong extsᵗ eq↑)

shiftSubst-substCtx-⇑ᶜ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  (Γ : Ctx Δ)
  → substCtx σ↑ (⇑ᶜ Γ) ≡ ⇑ᶜ (substCtx σ Γ)
shiftSubst-substCtx-⇑ᶜ {σ = σ} (shift-subst eq↑) Γ
  rewrite eq↑ = substCtx-extsᵗ-⇑ᶜ σ Γ

shiftSubst-shift : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  (A : Type Δ)
  → substᵗ σ↑ (renameᵗ S_ A) ≡ renameᵗ S_ (substᵗ σ A)
shiftSubst-shift {σ = σ} (shift-subst eq↑) A
  rewrite eq↑ = substᵗ-shift σ A

shiftSubst-substCtx-renameS : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  (Γ : Ctx Δ)
  → substCtx σ↑ (renameCtx S_ Γ) ≡ renameCtx S_ (substCtx σ Γ)
shiftSubst-substCtx-renameS w Γ = shiftSubst-substCtx-⇑ᶜ w Γ

shiftSubst-renameS : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  (A : Type Δ)
  → substᵗ σ↑ (renameᵗ S_ A) ≡ renameᵗ S_ (substᵗ σ A)
shiftSubst-renameS w A = shiftSubst-shift w A

shiftSubst-tyVar-coh-ext : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  (β : TyVar (Δ ,α))
  → extsᵗ σ↑ (extᵗ ξ β) ≡ renameᵗ (extᵗ ξ') (σ↑ β)
shiftSubst-tyVar-coh-ext {σ = σ} (shift-subst eq↑) {ξ = ξ} {ξ' = ξ'} ty-coh Z
  rewrite eq↑ = refl
shiftSubst-tyVar-coh-ext {σ = σ} (shift-subst eq↑) {ξ = ξ} {ξ' = ξ'} ty-coh (S α)
  rewrite eq↑ =
  trans
    (cong (renameᵗ S_) (ty-coh (` α)))
    (sym (renameᵗ-shift ξ' (σ α)))

shiftSubst-ty-coh-ext : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  (A : Type (Δ ,α))
  → substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A) ≡ renameᵗ (extᵗ ξ') (substᵗ σ↑ A)
shiftSubst-ty-coh-ext {σ = σ} (shift-subst eq↑) {ξ = ξ} {ξ' = ξ'} ty-coh A
  rewrite eq↑ =
  trans
    (ren-subᵗ (extᵗ ξ) (extsᵗ (extsᵗ σ)) A)
    (trans
      (substᵗ-cong A (shiftSubst-tyVar-coh-ext (shift-subst refl) ty-coh))
      (sym (sub-renᵗ (extᵗ ξ') (extsᵗ σ) A)))

shiftSubst-substᵗ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  (A : Type (Δ ,α))
  → substᵗ σ↑ A ≡ substᵗ (extsᵗ σ) A
shiftSubst-substᵗ (shift-subst eq↑) A
  rewrite eq↑ = refl

shiftSubst-ty-coh-ext* : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  (A : Type (Δ ,α))
  → substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A) ≡ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A)
shiftSubst-ty-coh-ext* w {ξ = ξ} {ξ' = ξ'} ty-coh A =
  trans
    (shiftSubst-ty-coh-ext w ty-coh A)
    (cong (renameᵗ (extᵗ ξ')) (shiftSubst-substᵗ w A))

shiftSubst-ctx-coh : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  (Γ : Ctx Δ)
  → substCtx σ↑ (renameCtx ξ Γ) ≡ renameCtx ξ' (substCtx σ Γ)
shiftSubst-ctx-coh w ty-coh ∅ = refl
shiftSubst-ctx-coh w ty-coh (Γ , A) =
  cong₂ _,_
    (shiftSubst-ctx-coh w ty-coh Γ)
    (ty-coh A)

shiftSubst-ctx-coh-ext : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  (Γ : Ctx (Δ ,α))
  → substCtx (extsᵗ σ↑) (renameCtx (extᵗ ξ) Γ) ≡ renameCtx (extᵗ ξ') (substCtx σ↑ Γ)
shiftSubst-ctx-coh-ext w ty-coh ∅ = refl
shiftSubst-ctx-coh-ext w ty-coh (Γ , A) =
  cong₂ _,_
    (shiftSubst-ctx-coh-ext w ty-coh Γ)
    (shiftSubst-ty-coh-ext w ty-coh A)

cast-ctxEq-S : ∀ {Δ} {Γ Γ' : Ctx Δ} {B B' A : Type Δ}
  (pΓ : Γ ≡ Γ')
  (pB : B ≡ B')
  (x : Γ ∋ A)
  → substEq
      (λ Ψ → Ψ ∋ A)
      (cong₂ _,_ pΓ pB)
      (S x)
    ≡
    S (substEq
        (λ Ψ → Ψ ∋ A)
        pΓ
        x)
cast-ctxEq-S refl refl x = refl

shiftSubst-∋-coh : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  {Γ : Ctx Δ}
  {A : Type Δ}
  (x : Γ ∋ A)
  → substEq
      (λ Ψ → Ψ ∋ substᵗ σ↑ (renameᵗ ξ A))
      (shiftSubst-ctx-coh w ty-coh Γ)
      (substᵗ-∋ σ↑ (renameᵗ-∋ ξ x))
    ≡
    substEq
      (λ T → renameCtx ξ' (substCtx σ Γ) ∋ T)
      (sym (ty-coh A))
      (renameᵗ-∋ ξ' (substᵗ-∋ σ x))
shiftSubst-∋-coh {σ = σ} {σ↑ = σ↑} w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = ∅} ()
shiftSubst-∋-coh {σ = σ} {σ↑ = σ↑} w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ , B} {A = B} Z
  rewrite shiftSubst-ctx-coh w ty-coh Γ
        | ty-coh B = refl
shiftSubst-∋-coh {σ = σ} {σ↑ = σ↑} w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ , B} {A = A} (S x) =
  trans
    (cast-ctxEq-S
      (shiftSubst-ctx-coh w ty-coh Γ)
      (ty-coh B)
      (substᵗ-∋ σ↑ (renameᵗ-∋ ξ x)))
    (trans
      (cong S_ (shiftSubst-∋-coh w ty-coh x))
      (sym
        (cast-∋-Sᵗ
          {Γ = renameCtx ξ' (substCtx σ Γ)}
          {C = renameᵗ ξ' (substᵗ σ B)}
          (sym (ty-coh A))
          (renameᵗ-∋ ξ' (substᵗ-∋ σ x)))))

postulate
  substᵀ-shiftSubst-renameᵀ-core-∙ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
    (w : ShiftSubst σ σ↑)
    {ξ : Δ ⇒ʳ (Δ ,α)}
    {ξ' : Δ' ⇒ʳ (Δ' ,α)}
    (ty-coh : ∀ (A : Type Δ)
      → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
    {Γ : Ctx Δ}
    {A : Type (Δ ,α)}
    (M : Δ ; Γ ⊢ `∀ A)
    (B : Type Δ)
    → substEq
        (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ (A [ B ]ᵗ)))
        (shiftSubst-ctx-coh w ty-coh Γ)
        (substᵀ σ↑ (renameᵀ ξ (M ∙ B)))
      ≡
      substEq
        (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
        (sym (ty-coh (A [ B ]ᵗ)))
        (renameᵀ ξ' (substᵀ σ (M ∙ B)))

substᵀ-shiftSubst-renameᵀ-core : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  {Γ : Ctx Δ}
  {A : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → substEq
      (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
      (shiftSubst-ctx-coh w ty-coh Γ)
      (substᵀ σ↑ (renameᵀ ξ M))
    ≡
    substEq
      (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
      (sym (ty-coh A))
      (renameᵀ ξ' (substᵀ σ M))
substᵀ-shiftSubst-renameᵀ-core w ty-coh {Γ = Γ} `zero
  rewrite shiftSubst-ctx-coh w ty-coh Γ
        | ty-coh `Nat = refl
substᵀ-shiftSubst-renameᵀ-core w ty-coh {Γ = Γ} `true
  rewrite shiftSubst-ctx-coh w ty-coh Γ
        | ty-coh `Bool = refl
substᵀ-shiftSubst-renameᵀ-core w ty-coh {Γ = Γ} `false
  rewrite shiftSubst-ctx-coh w ty-coh Γ
        | ty-coh `Bool = refl
substᵀ-shiftSubst-renameᵀ-core {Δ' = Δ'} {σ = σ} {σ↑ = σ↑} w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ} (`suc M) =
  trans
    (cast-suc-ctx-term
      (shiftSubst-ctx-coh w ty-coh Γ)
      (substᵀ σ↑ (renameᵀ ξ M)))
    (trans
      (cong `suc_ (substᵀ-shiftSubst-renameᵀ-core w ty-coh M))
      (trans
        (cong `suc_
          (substEq-id
            (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
            (sym (ty-coh `Nat))
            (renameᵀ ξ' (substᵀ σ M))))
        (sym
          (cast-suc-type-term
            {Θ = Δ' ,α}
            {Γ = renameCtx ξ' (substCtx σ Γ)}
            (sym (ty-coh `Nat))
            (renameᵀ ξ' (substᵀ σ M))))))
substᵀ-shiftSubst-renameᵀ-core
  {Δ' = Δ'} {σ = σ} {σ↑ = σ↑}
  w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ} {A = A}
  (`case-nat L M N) =
  trans
    (cast-case-nat-ctx-term
      (shiftSubst-ctx-coh w ty-coh Γ)
      (substᵀ σ↑ (renameᵀ ξ L))
      (substᵀ σ↑ (renameᵀ ξ M))
      (substᵀ σ↑ (renameᵀ ξ N)))
    (trans
      step-ih
      (sym
        (cast-case-nat-type-term
          {Θ = Δ' ,α}
          {Γ = renameCtx ξ' (substCtx σ Γ)}
          (sym (ty-coh A))
          (renameᵀ ξ' (substᵀ σ L))
          (renameᵀ ξ' (substᵀ σ M))
          (renameᵀ ξ' (substᵀ σ N)))))
  where
  pΓ : substCtx σ↑ (renameCtx ξ Γ) ≡ renameCtx ξ' (substCtx σ Γ)
  pΓ = shiftSubst-ctx-coh w ty-coh Γ

  pΓN : substCtx σ↑ (renameCtx ξ Γ) , `Nat ≡ renameCtx ξ' (substCtx σ Γ) , `Nat
  pΓN = cong (λ Ψ → Ψ , `Nat) pΓ

  pΓN' : substCtx σ↑ (renameCtx ξ (Γ , `Nat)) ≡ renameCtx ξ' (substCtx σ (Γ , `Nat))
  pΓN' = shiftSubst-ctx-coh w ty-coh (Γ , `Nat)

  pΓN-coh : pΓN ≡ pΓN'
  pΓN-coh = uip-≡ pΓN pΓN'

  qL : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ `Nat)
          pΓ
          (substᵀ σ↑ (renameᵀ ξ L))
       ≡
       renameᵀ ξ' (substᵀ σ L)
  qL =
    trans
      (substᵀ-shiftSubst-renameᵀ-core w ty-coh L)
      (substEq-id
        (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
        (sym (ty-coh `Nat))
        (renameᵀ ξ' (substᵀ σ L)))

  qM : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          pΓ
          (substᵀ σ↑ (renameᵀ ξ M))
       ≡
       substEq
         (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
         (sym (ty-coh A))
         (renameᵀ ξ' (substᵀ σ M))
  qM = substᵀ-shiftSubst-renameᵀ-core w ty-coh M

  qN' : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          pΓN'
          (substᵀ σ↑ (renameᵀ ξ N))
       ≡
       substEq
         (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , `Nat)) ⊢ T)
         (sym (ty-coh A))
         (renameᵀ ξ' (substᵀ σ N))
  qN' = substᵀ-shiftSubst-renameᵀ-core w ty-coh N

  qN : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          pΓN
          (substᵀ σ↑ (renameᵀ ξ N))
       ≡
       substEq
         (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , `Nat)) ⊢ T)
         (sym (ty-coh A))
         (renameᵀ ξ' (substᵀ σ N))
  qN =
    trans
      (cong
        (λ p → substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          p
          (substᵀ σ↑ (renameᵀ ξ N)))
        pΓN-coh)
      qN'

  step-ih : `case-nat
              (substEq
                (λ Ψ → Δ' ,α ; Ψ ⊢ `Nat)
                pΓ
                (substᵀ σ↑ (renameᵀ ξ L)))
              (substEq
                (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
                pΓ
                (substᵀ σ↑ (renameᵀ ξ M)))
              (substEq
                (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
                pΓN
                (substᵀ σ↑ (renameᵀ ξ N)))
            ≡
            `case-nat
              (renameᵀ ξ' (substᵀ σ L))
              (substEq
                (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
                (sym (ty-coh A))
                (renameᵀ ξ' (substᵀ σ M)))
              (substEq
                (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , `Nat)) ⊢ T)
                (sym (ty-coh A))
                (renameᵀ ξ' (substᵀ σ N)))
  step-ih rewrite qL | qM | qN = refl
substᵀ-shiftSubst-renameᵀ-core
  {Δ' = Δ'} {σ = σ} {σ↑ = σ↑}
  w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ} {A = A}
  (`if_then_else L M N) =
  trans
    (cast-if-ctx-term
      (shiftSubst-ctx-coh w ty-coh Γ)
      (substᵀ σ↑ (renameᵀ ξ L))
      (substᵀ σ↑ (renameᵀ ξ M))
      (substᵀ σ↑ (renameᵀ ξ N)))
    (trans
      step-ih
      (sym
        (cast-if-type-term
          {Θ = Δ' ,α}
          {Γ = renameCtx ξ' (substCtx σ Γ)}
          (sym (ty-coh A))
          (renameᵀ ξ' (substᵀ σ L))
          (renameᵀ ξ' (substᵀ σ M))
          (renameᵀ ξ' (substᵀ σ N)))))
  where
  qL : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ `Bool)
          (shiftSubst-ctx-coh w ty-coh Γ)
          (substᵀ σ↑ (renameᵀ ξ L))
       ≡
       renameᵀ ξ' (substᵀ σ L)
  qL =
    trans
      (substᵀ-shiftSubst-renameᵀ-core w ty-coh L)
      (substEq-id
        (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
        (sym (ty-coh `Bool))
        (renameᵀ ξ' (substᵀ σ L)))

  qM : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          (shiftSubst-ctx-coh w ty-coh Γ)
          (substᵀ σ↑ (renameᵀ ξ M))
       ≡
       substEq
         (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
         (sym (ty-coh A))
         (renameᵀ ξ' (substᵀ σ M))
  qM = substᵀ-shiftSubst-renameᵀ-core w ty-coh M

  qN : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          (shiftSubst-ctx-coh w ty-coh Γ)
          (substᵀ σ↑ (renameᵀ ξ N))
       ≡
       substEq
         (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
         (sym (ty-coh A))
         (renameᵀ ξ' (substᵀ σ N))
  qN = substᵀ-shiftSubst-renameᵀ-core w ty-coh N

  step-ih : `if_then_else
              (substEq
                (λ Ψ → Δ' ,α ; Ψ ⊢ `Bool)
                (shiftSubst-ctx-coh w ty-coh Γ)
                (substᵀ σ↑ (renameᵀ ξ L)))
              (substEq
                (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
                (shiftSubst-ctx-coh w ty-coh Γ)
                (substᵀ σ↑ (renameᵀ ξ M)))
              (substEq
                (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
                (shiftSubst-ctx-coh w ty-coh Γ)
                (substᵀ σ↑ (renameᵀ ξ N)))
            ≡
            `if_then_else
              (renameᵀ ξ' (substᵀ σ L))
              (substEq
                (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
                (sym (ty-coh A))
                (renameᵀ ξ' (substᵀ σ M)))
              (substEq
                (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
                (sym (ty-coh A))
                (renameᵀ ξ' (substᵀ σ N)))
  step-ih rewrite qL | qM | qN = refl
substᵀ-shiftSubst-renameᵀ-core
  {Δ' = Δ'} {σ = σ} {σ↑ = σ↑}
  w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ} {A = A}
  (` x) =
  trans
    (cast-var-term
      (shiftSubst-ctx-coh w ty-coh Γ)
      (substᵗ-∋ σ↑ (renameᵗ-∋ ξ x)))
    (trans
      (cong `_ (shiftSubst-∋-coh w ty-coh x))
      (sym
        (cast-var-type-term
          (sym (ty-coh A))
          (renameᵗ-∋ ξ' (substᵗ-∋ σ x)))))
substᵀ-shiftSubst-renameᵀ-core
  {Δ' = Δ'} {σ = σ} {σ↑ = σ↑}
  w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ} {A = A ⇒ B}
  (ƛ A ˙ N) =
  trans
    (cast-ƛ-ctx-term pΓ (substᵀ σ↑ (renameᵀ ξ N)))
    (trans
      (cong (ƛ substᵗ σ↑ (renameᵗ ξ A) ˙_) body-coh)
      (trans
        (sym (cast-ƛ-type-term (sym pA) (sym pB) renN))
        (cong
          (λ p → substEq
            (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
            p
            (ƛ renameᵗ ξ' (substᵗ σ A) ˙ renN))
          (sym pArr))))
  where
  pΓ : substCtx σ↑ (renameCtx ξ Γ) ≡ renameCtx ξ' (substCtx σ Γ)
  pΓ = shiftSubst-ctx-coh w ty-coh Γ

  pA : substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A)
  pA = ty-coh A

  pB : substᵗ σ↑ (renameᵗ ξ B) ≡ renameᵗ ξ' (substᵗ σ B)
  pB = ty-coh B

  pArr : sym (ty-coh (A ⇒ B)) ≡ cong₂ _⇒_ (sym pA) (sym pB)
  pArr = uip-≡ (sym (ty-coh (A ⇒ B))) (cong₂ _⇒_ (sym pA) (sym pB))

  pΓL : substCtx σ↑ (renameCtx ξ Γ , renameᵗ ξ A)
      ≡ renameCtx ξ' (substCtx σ Γ) , substᵗ σ↑ (renameᵗ ξ A)
  pΓL = cong (λ Ψ → Ψ , substᵗ σ↑ (renameᵗ ξ A)) pΓ

  pΓR : renameCtx ξ' (substCtx σ Γ) , substᵗ σ↑ (renameᵗ ξ A)
      ≡ renameCtx ξ' (substCtx σ Γ) , renameᵗ ξ' (substᵗ σ A)
  pΓR = cong (λ T → renameCtx ξ' (substCtx σ Γ) , T) pA

  pΓR-sym : sym pΓR
      ≡ cong (λ T → renameCtx ξ' (substCtx σ Γ) , T) (sym pA)
  pΓR-sym =
    uip-≡
      (sym pΓR)
      (cong (λ T → renameCtx ξ' (substCtx σ Γ) , T) (sym pA))

  pΓN : substCtx σ↑ (renameCtx ξ (Γ , A))
      ≡ renameCtx ξ' (substCtx σ (Γ , A))
  pΓN = shiftSubst-ctx-coh w ty-coh (Γ , A)

  pΓ-coh : trans pΓL pΓR ≡ pΓN
  pΓ-coh = uip-≡ (trans pΓL pΓR) pΓN

  X : Δ' ,α ; substCtx σ↑ (renameCtx ξ (Γ , A)) ⊢ substᵗ σ↑ (renameᵗ ξ B)
  X = substᵀ σ↑ (renameᵀ ξ N)

  renN : Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , A)) ⊢ renameᵗ ξ' (substᵗ σ B)
  renN = renameᵀ ξ' (substᵀ σ N)

  ihN : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
          pΓN
          X
      ≡
      substEq
        (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , A)) ⊢ T)
        (sym pB)
        renN
  ihN = substᵀ-shiftSubst-renameᵀ-core w ty-coh N

  k : substEq
        (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
        pΓR
        (substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
          pΓL
          X)
      ≡
      substEq
        (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , A)) ⊢ T)
        (sym pB)
        renN
  k =
    trans
      (substEq-compose
        (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
        pΓR
        pΓL
        X)
      (trans
        (cong
          (λ p → substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
            p
            X)
          pΓ-coh)
        ihN)

  body-coh : substEq
               (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
               pΓL
               X
           ≡
           substEq
             (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
             (cong (λ T → renameCtx ξ' (substCtx σ Γ) , T) (sym pA))
             (substEq
               (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , A)) ⊢ T)
               (sym pB)
               renN)
  body-coh =
    trans
      (sym
        (substEq-cancel-sym
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
          pΓR
          (substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
            pΓL
            X)))
      (trans
        (cong
          (substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
            (sym pΓR))
          k)
        (cong
          (λ p → substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ B))
            p
            (substEq
              (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ (Γ , A)) ⊢ T)
              (sym pB)
              renN))
          pΓR-sym))
substᵀ-shiftSubst-renameᵀ-core
  {Δ' = Δ'} {σ = σ} {σ↑ = σ↑}
  w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ} {A = B}
  (_·_ {A = A} {B = B} L M) =
  trans
    (cast-app-ctx-term
      (shiftSubst-ctx-coh w ty-coh Γ)
      (substᵀ σ↑ (renameᵀ ξ L))
      (substᵀ σ↑ (renameᵀ ξ M)))
    (trans
      (cong₂ _·_ qL qM)
      (sym (cast-app-type-term (sym pA) (sym pB) renL renM)))
  where
  pA : substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A)
  pA = ty-coh A

  pB : substᵗ σ↑ (renameᵗ ξ B) ≡ renameᵗ ξ' (substᵗ σ B)
  pB = ty-coh B

  pArr : sym (ty-coh (A ⇒ B)) ≡ cong₂ _⇒_ (sym pA) (sym pB)
  pArr = uip-≡ (sym (ty-coh (A ⇒ B))) (cong₂ _⇒_ (sym pA) (sym pB))

  renL : Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ renameᵗ ξ' (substᵗ σ (A ⇒ B))
  renL = renameᵀ ξ' (substᵀ σ L)

  renM : Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ renameᵗ ξ' (substᵗ σ A)
  renM = renameᵀ ξ' (substᵀ σ M)

  qL : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ (A ⇒ B)))
          (shiftSubst-ctx-coh w ty-coh Γ)
          (substᵀ σ↑ (renameᵀ ξ L))
       ≡
       substEq
         (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
         (cong₂ _⇒_ (sym pA) (sym pB))
         renL
  qL =
    trans
      (substᵀ-shiftSubst-renameᵀ-core w ty-coh L)
      (cong
        (λ p → substEq
          (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
          p
          renL)
        pArr)

  qM : substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          (shiftSubst-ctx-coh w ty-coh Γ)
          (substᵀ σ↑ (renameᵀ ξ M))
       ≡
       substEq
         (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
         (sym pA)
         renM
  qM = substᵀ-shiftSubst-renameᵀ-core w ty-coh M
substᵀ-shiftSubst-renameᵀ-core
  {Δ = Δ} {Δ' = Δ'} {σ = σ} {σ↑ = σ↑}
  w {ξ = ξ} {ξ' = ξ'} ty-coh {Γ = Γ} {A = `∀ A}
  (Λ N) =
  trans
    stepL
    (trans
      (cong Λ_ body-main)
      (sym stepR))
  where
  pΓ : substCtx σ↑ (renameCtx ξ Γ) ≡ renameCtx ξ' (substCtx σ Γ)
  pΓ = shiftSubst-ctx-coh w ty-coh Γ

  ty-coh↑ : ∀ (T : Type (Δ ,α))
    → substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) T) ≡ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) T)
  ty-coh↑ = shiftSubst-ty-coh-ext* w ty-coh

  pA : substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A) ≡ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A)
  pA = ty-coh↑ A

  p∀ : sym (ty-coh (`∀ A)) ≡ cong `∀_ (sym pA)
  p∀ = uip-≡ (sym (ty-coh (`∀ A))) (cong `∀_ (sym pA))

  pRξ : renameCtx (extᵗ ξ) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx ξ Γ)
  pRξ = renameCtx-extᵗ-⇑ᶜ ξ Γ

  pSξ : substCtx (extsᵗ σ↑) (⇑ᶜ (renameCtx ξ Γ)) ≡ ⇑ᶜ (substCtx σ↑ (renameCtx ξ Γ))
  pSξ = substCtx-extsᵗ-⇑ᶜ σ↑ (renameCtx ξ Γ)

  pSσ : substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ ⇑ᶜ (substCtx σ Γ)
  pSσ = substCtx-extsᵗ-⇑ᶜ σ Γ

  pRσ : renameCtx (extᵗ ξ') (⇑ᶜ (substCtx σ Γ)) ≡ ⇑ᶜ (renameCtx ξ' (substCtx σ Γ))
  pRσ = renameCtx-extᵗ-⇑ᶜ ξ' (substCtx σ Γ)

  pS2 : substCtx (extsᵗ σ↑) (renameCtx (extᵗ ξ) (⇑ᶜ Γ))
      ≡ substCtx (extsᵗ σ↑) (⇑ᶜ (renameCtx ξ Γ))
  pS2 = cong (substCtx (extsᵗ σ↑)) pRξ

  pR2 : renameCtx (extᵗ ξ') (substCtx (extsᵗ σ) (⇑ᶜ Γ))
      ≡ renameCtx (extᵗ ξ') (⇑ᶜ (substCtx σ Γ))
  pR2 = cong (renameCtx (extᵗ ξ')) pSσ

  pL : substCtx (extsᵗ σ↑) (renameCtx (extᵗ ξ) (⇑ᶜ Γ))
      ≡ ⇑ᶜ (renameCtx ξ' (substCtx σ Γ))
  pL = trans pS2 (trans pSξ (cong ⇑ᶜ pΓ))

  pQ : renameCtx (extᵗ ξ') (substCtx (extsᵗ σ) (⇑ᶜ Γ))
      ≡ ⇑ᶜ (renameCtx ξ' (substCtx σ Γ))
  pQ = trans pR2 pRσ

  pΓ↑ : substCtx (extsᵗ σ↑) (renameCtx (extᵗ ξ) (⇑ᶜ Γ))
      ≡ renameCtx (extᵗ ξ') (substCtx (extsᵗ σ) (⇑ᶜ Γ))
  pΓ↑ = shiftSubst-ctx-coh (shiftSubst-ext w) ty-coh↑ (⇑ᶜ Γ)

  pBridge : pL ≡ trans pΓ↑ pQ
  pBridge = uip-≡ pL (trans pΓ↑ pQ)

  X : Δ' ,α ,α ; substCtx (extsᵗ σ↑) (renameCtx (extᵗ ξ) (⇑ᶜ Γ))
      ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A)
  X = substᵀ (extsᵗ σ↑) (renameᵀ (extᵗ ξ) N)

  Y : Δ' ,α ,α ; renameCtx (extᵗ ξ') (substCtx (extsᵗ σ) (⇑ᶜ Γ))
      ⊢ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A)
  Y = renameᵀ (extᵗ ξ') (substᵀ (extsᵗ σ) N)

  ihN : substEq
          (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
          pΓ↑
          X
      ≡
      substEq
        (λ T → Δ' ,α ,α ; renameCtx (extᵗ ξ') (substCtx (extsᵗ σ) (⇑ᶜ Γ)) ⊢ T)
        (sym pA)
        Y
  ihN = substᵀ-shiftSubst-renameᵀ-core (shiftSubst-ext w) ty-coh↑ N

  bodyLpre : Δ' ,α ,α ; substCtx (extsᵗ σ↑) (⇑ᶜ (renameCtx ξ Γ))
      ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A)
  bodyLpre =
    substᵀ (extsᵗ σ↑)
      (substEq
        (λ Ψ → Δ ,α ,α ; Ψ ⊢ renameᵗ (extᵗ ξ) A)
        pRξ
        (renameᵀ (extᵗ ξ) N))

  bodyL0 : Δ' ,α ,α ; ⇑ᶜ (substCtx σ↑ (renameCtx ξ Γ))
      ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A)
  bodyL0 =
    substEq
      (_ ;_⊢ _)
      pSξ
      bodyLpre

  bodyR0 : Δ' ,α ,α ; ⇑ᶜ (renameCtx ξ' (substCtx σ Γ))
      ⊢ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A)
  bodyR0 =
    substEq
      (_ ;_⊢ _)
      (renameCtx-extᵗ-⇑ᶜ ξ' (substCtx σ Γ))
      (renameᵀ (extᵗ ξ')
        (substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ σ) A)
          (substCtx-extsᵗ-⇑ᶜ σ Γ)
          (substᵀ (extsᵗ σ) N)))

  stepL : substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ (`∀ A)))
            pΓ
            (substᵀ σ↑ (renameᵀ ξ (Λ N)))
        ≡
        Λ (substEq
          (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
          pL
          X)
  stepL =
    trans
      (cast-Λ-ctx-term pΓ bodyL0)
      (cong Λ_
        (trans
          (substEq-compose
            (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
            (cong ⇑ᶜ pΓ)
            pSξ
            bodyLpre)
          (trans
            (cong
              (substEq
                (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
                (trans pSξ (cong ⇑ᶜ pΓ)))
              (substᵀ-substEqᶜ (extsᵗ σ↑) pRξ (renameᵀ (extᵗ ξ) N)))
            (trans
              (substEq-compose
                (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
                (trans pSξ (cong ⇑ᶜ pΓ))
                pS2
                X)
              (cong
                (λ p → substEq
                  (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
                  p
                  X)
                (uip-≡ (trans pS2 (trans pSξ (cong ⇑ᶜ pΓ))) pL))))))

  qBodyR : bodyR0
        ≡
        substEq
          (λ Ψ → Δ' ,α ,α ; Ψ ⊢ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A))
          pQ
          Y
  qBodyR =
    trans
      (cong
        (substEq
          (λ Ψ → Δ' ,α ,α ; Ψ ⊢ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A))
          (renameCtx-extᵗ-⇑ᶜ ξ' (substCtx σ Γ)))
        (renameᵀ-substEqᶜ (extᵗ ξ') (substCtx-extsᵗ-⇑ᶜ σ Γ) (substᵀ (extsᵗ σ) N)))
      (substEq-compose
        (λ Ψ → Δ' ,α ,α ; Ψ ⊢ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A))
        (renameCtx-extᵗ-⇑ᶜ ξ' (substCtx σ Γ))
        pR2
        Y)

  stepR : substEq
            (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
            (sym (ty-coh (`∀ A)))
            (renameᵀ ξ' (substᵀ σ (Λ N)))
        ≡
        Λ
          (substEq
            (λ T → Δ' ,α ,α ; ⇑ᶜ (renameCtx ξ' (substCtx σ Γ)) ⊢ T)
            (sym pA)
            (substEq
              (λ Ψ → Δ' ,α ,α ; Ψ ⊢ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A))
              pQ
              Y))
  stepR =
    trans
      (cong
        (λ p → substEq
          (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
          p
          (renameᵀ ξ' (substᵀ σ (Λ N))))
        p∀)
      (trans
        (cast-Λ-type-term (sym pA) bodyR0)
        (cong Λ_
          (cong
            (substEq
              (λ T → Δ' ,α ,α ; ⇑ᶜ (renameCtx ξ' (substCtx σ Γ)) ⊢ T)
              (sym pA))
            qBodyR)))

  body-main : substEq
                (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
                pL
                X
            ≡
            substEq
              (λ T → Δ' ,α ,α ; ⇑ᶜ (renameCtx ξ' (substCtx σ Γ)) ⊢ T)
              (sym pA)
              (substEq
                (λ Ψ → Δ' ,α ,α ; Ψ ⊢ renameᵗ (extᵗ ξ') (substᵗ (extsᵗ σ) A))
                pQ
                Y)
  body-main =
    trans
      (cong
        (λ p → substEq
          (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
          p
          X)
        pBridge)
      (trans
        (sym
          (substEq-compose
            (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
            pQ
            pΓ↑
            X))
        (trans
          (cong
            (substEq
              (λ Ψ → Δ' ,α ,α ; Ψ ⊢ substᵗ (extsᵗ σ↑) (renameᵗ (extᵗ ξ) A))
              pQ)
            ihN)
          (cast-ctx-type-term pQ (sym pA) Y)))
substᵀ-shiftSubst-renameᵀ-core w ty-coh (_∙_ {A = A} M B) =
  substᵀ-shiftSubst-renameᵀ-core-∙ w ty-coh M B

substᵀ-shiftSubst-renameᵀ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {ξ : Δ ⇒ʳ (Δ ,α)}
  {ξ' : Δ' ⇒ʳ (Δ' ,α)}
  (ctx-coh : ∀ (Γ : Ctx Δ)
    → substCtx σ↑ (renameCtx ξ Γ) ≡ renameCtx ξ' (substCtx σ Γ))
  (ty-coh : ∀ (A : Type Δ)
    → substᵗ σ↑ (renameᵗ ξ A) ≡ renameᵗ ξ' (substᵗ σ A))
  {Γ : Ctx Δ}
  {A : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → substEq
      (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
      (ctx-coh Γ)
      (substᵀ σ↑ (renameᵀ ξ M))
    ≡
    substEq
      (λ T → Δ' ,α ; renameCtx ξ' (substCtx σ Γ) ⊢ T)
      (sym (ty-coh A))
      (renameᵀ ξ' (substᵀ σ M))
substᵀ-shiftSubst-renameᵀ
  {Δ' = Δ'} {σ = σ} {σ↑ = σ↑}
  w {ξ = ξ} {ξ' = ξ'} ctx-coh ty-coh {Γ = Γ} {A = A} M =
  trans
    (cong
      (λ (p : substCtx σ↑ (renameCtx ξ Γ) ≡ renameCtx ξ' (substCtx σ Γ)) →
        substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ ξ A))
          p
          (substᵀ σ↑ (renameᵀ ξ M)))
      (uip-≡ (ctx-coh Γ) (shiftSubst-ctx-coh w ty-coh Γ)))
    (substᵀ-shiftSubst-renameᵀ-core w ty-coh M)

substᵀ-shiftSubst-⇑ᵀ : ∀ {Δ Δ'} {σ : Δ ⇒ˢ Δ'} {σ↑ : (Δ ,α) ⇒ˢ (Δ' ,α)}
  (w : ShiftSubst σ σ↑)
  {Γ : Ctx Δ}
  {A : Type Δ}
  (M : Δ ; Γ ⊢ A)
  → substEq
      (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ σ↑ (renameᵗ S_ A))
      (shiftSubst-substCtx-⇑ᶜ w Γ)
      (substᵀ σ↑ (⇑ᵀ M))
    ≡
    substEq
      (λ T → Δ' ,α ; ⇑ᶜ (substCtx σ Γ) ⊢ T)
      (sym (shiftSubst-shift w A))
      (⇑ᵀ (substᵀ σ M))
substᵀ-shiftSubst-⇑ᵀ {σ = σ} {σ↑ = σ↑} w M =
  substᵀ-shiftSubst-renameᵀ {σ = σ} {σ↑ = σ↑} w {ξ = S_} {ξ' = S_}
    (shiftSubst-substCtx-renameS {σ = σ} {σ↑ = σ↑} w)
    (shiftSubst-renameS {σ = σ} {σ↑ = σ↑} w)
    M

substᵀ-extsᵗ-⇑ᵀ τ M = substᵀ-shiftSubst-⇑ᵀ (shiftSubst-exts τ) M

--------------------------------------------------------------------------------
-- Main mixed commutation theorem
--------------------------------------------------------------------------------

-- NOTE:
-- The earlier SCC-break attempt replaced the problematic `map-Z -> Λ-body (` Z)`
-- edge with a standalone postulate. That removed the immediate cycle but did not
-- provide a constructive recursion principle for this strongly connected block.
-- Here we use an explicit fuel index to make the `map-Z` bridge consume one step,
-- giving the termination checker a decreasing argument across the cycle.
private
  subᵀ-sub-Λ-body-Z-base : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
    {Γ Γ' : Ctx Δ}
    {B : Type Δ}
    (σ : (Γ , B) →ˢ Γ')
    → subst (⇑ˢ (substᵀ-map τ σ))
        (substEq
          (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
          (substCtx-extsᵗ-⇑ᶜ τ (Γ , B))
          (substᵀ (extsᵗ τ) (` (Z {Γ = renameCtx S_ Γ} {A = renameᵗ S_ B}))))
      ≡
      substEq
        (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
        (substCtx-extsᵗ-⇑ᶜ τ Γ')
        (substᵀ (extsᵗ τ) (subst (⇑ˢ σ) (` Z)))
  subᵀ-sub-Λ-body-Z-base {Δ' = Δ'} τ {Γ = Γ} {Γ' = Γ'} {B = B} σ =
    trans leftFix (trans z-body (sym rightFix))
    where
    pΓ : substCtx (extsᵗ τ) (⇑ᶜ (Γ , B)) ≡ ⇑ᶜ (substCtx τ (Γ , B))
    pΓ = substCtx-extsᵗ-⇑ᶜ τ (Γ , B)

    pΓ' : substCtx (extsᵗ τ) (⇑ᶜ Γ') ≡ ⇑ᶜ (substCtx τ Γ')
    pΓ' = substCtx-extsᵗ-⇑ᶜ τ Γ'

    T : Type (Δ' ,α)
    T = substᵗ (extsᵗ τ) (renameᵗ S_ B)

    zVar : ⇑ᶜ (Γ , B) ∋ renameᵗ S_ B
    zVar = Z

    x0 : substCtx (extsᵗ τ) (⇑ᶜ (Γ , B)) ∋ T
    x0 = substᵗ-∋ (extsᵗ τ) zVar

    kL1 : substᵀ (extsᵗ τ) (` zVar) ≡ ` x0
    kL1 = refl

    kL2 : x0 ≡ Z
    kL2 = refl

    leftFix :
        subst (⇑ˢ (substᵀ-map τ σ))
          (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ (substᵀ (extsᵗ τ) (` zVar)))
      ≡
        ⇑ˢ (substᵀ-map τ σ)
          (substEq (λ Ψ → Ψ ∋ T) pΓ x0)
    leftFix =
      trans
        (cong
          (subst (⇑ˢ (substᵀ-map τ σ)))
          (trans
            (cong (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ) kL1)
            (cast-var-term pΓ x0)))
        (cong
          (⇑ˢ (substᵀ-map τ σ))
          (cong (substEq (λ Ψ → Ψ ∋ T) pΓ) kL2))

    kR1 : subst (⇑ˢ σ) (` Z) ≡ ⇑ˢ σ Z
    kR1 = refl

    kR2 : substᵀ (extsᵗ τ) (⇑ˢ σ Z) ≡ substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z
    kR2 = refl

    rightFix :
        substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ'
          (substᵀ (extsᵗ τ) (subst (⇑ˢ σ) (` Z)))
      ≡
        substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ'
          (substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z)
    rightFix =
      cong
        (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ')
        (trans (cong (substᵀ (extsᵗ τ)) kR1) kR2)

    kMap0 : substᵀ-map τ σ Z ≡ substᵀ τ (σ Z)
    kMap0 = refl

    kShiftZ :
        ⇑ˢ (substᵀ-map τ σ) (substEq (λ Ψ → Ψ ∋ T) pΓ Z)
      ≡
        substEq
          (λ T' → Δ' ,α ; ⇑ᶜ (substCtx τ Γ') ⊢ T')
          (sym (substᵗ-shift τ B))
          (⇑ᵀ (substᵀ τ (σ Z)))
    kShiftZ =
      trans
        (trans
          (cong
            (⇑ˢ (substᵀ-map τ σ))
            (cast-substCtx-extsᵗ-⇑ᶜ-Z τ {Γ = Γ} {B = B}))
          (⇑ˢ-castᵗ (substᵀ-map τ σ) (sym (substᵗ-shift τ B)) Z))
        (cong
          (substEq
            (λ T' → Δ' ,α ; ⇑ᶜ (substCtx τ Γ') ⊢ T')
            (sym (substᵗ-shift τ B)))
          (cong ⇑ᵀ kMap0))

    kMapZ :
        substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ'
          (substᵀ (extsᵗ τ) (⇑ᵀ (σ Z)))
      ≡
        substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ'
          (substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z)
    kMapZ = cong (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ') kR2

    z-body :
        ⇑ˢ (substᵀ-map τ σ)
          (substEq (λ Ψ → Ψ ∋ T) pΓ Z)
      ≡
        substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ'
          (substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z)
    z-body =
      trans
        kShiftZ
        (trans
          (sym (substᵀ-extsᵗ-⇑ᵀ τ (σ Z)))
          kMapZ)

  mutual
    subᵀ-sub-Λ-body-fuel : ∀ (fuel : ℕ) {Δ Δ'} (τ : Δ ⇒ˢ Δ')
      {Γ Γ' : Ctx Δ}
      {A : Type (Δ ,α)}
      (σ : Γ →ˢ Γ')
      (N : Δ ,α ; ⇑ᶜ Γ ⊢ A)
      → subst (⇑ˢ (substᵀ-map τ σ))
          (substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ τ Γ)
            (substᵀ (extsᵗ τ) N))
        ≡
        substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ τ Γ')
          (substᵀ (extsᵗ τ) (subst (⇑ˢ σ) N))
  
    substᵀ-map-⇑ˢ-fuel : ∀ (fuel : ℕ) {Δ Δ'} (τ : Δ ⇒ˢ Δ')
      {Γ Γ' : Ctx Δ}
      (σ : Γ →ˢ Γ')
      → ∀ {A} (x : substCtx (extsᵗ τ) (⇑ᶜ Γ) ∋ A)
      → substᵀ-map (extsᵗ τ) (⇑ˢ σ) x
        ≡ substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ A)
            (sym (substCtx-extsᵗ-⇑ᶜ τ Γ'))
            (⇑ˢ (substᵀ-map τ σ)
              (substEq (λ Ψ → Ψ ∋ A)
                (substCtx-extsᵗ-⇑ᶜ τ Γ)
                x))
  
    subᵀ-sub-fuel : ∀ (fuel : ℕ) {Δ Δ'} (τ : Δ ⇒ˢ Δ')
      {Γ Γ' : Ctx Δ} {A : Type Δ}
      (σ : Γ →ˢ Γ')
      (M : Δ ; Γ ⊢ A)
      → subst (substᵀ-map τ σ) (substᵀ τ M)
        ≡ substᵀ τ (subst σ M)
  
    substᵀ-map-⇑ˢ-fuel-Z-core : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
      {Γ Γ' : Ctx Δ}
      {B : Type Δ}
      (σ : (Γ , B) →ˢ Γ')
      (bridge :
          subst (⇑ˢ (substᵀ-map τ σ))
              (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
                (substCtx-extsᵗ-⇑ᶜ τ (Γ , B))
                (substᵀ (extsᵗ τ) (` (Z {Γ = renameCtx S_ Γ} {A = renameᵗ S_ B}))))
        ≡
        substEq (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
          (substCtx-extsᵗ-⇑ᶜ τ Γ')
          (substᵀ (extsᵗ τ) (subst (⇑ˢ σ) (` Z))))
      → substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z
        ≡ substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
            (sym (substCtx-extsᵗ-⇑ᶜ τ Γ'))
            (⇑ˢ (substᵀ-map τ σ)
              (substEq (λ Ψ → Ψ ∋ substᵗ (extsᵗ τ) (renameᵗ S_ B))
                (substCtx-extsᵗ-⇑ᶜ τ (Γ , B))
                Z))
  
    substᵀ-map-⇑ˢ-fuel fuel τ {Γ = ∅} σ ()
    substᵀ-map-⇑ˢ-fuel zero {Δ = Δ} {Δ' = Δ'} τ {Γ = Γ , B} {Γ' = Γ'} σ Z =
      substᵀ-map-⇑ˢ-fuel-Z-core τ {Γ = Γ} {Γ' = Γ'} {B = B} σ
        (subᵀ-sub-Λ-body-Z-base τ σ)
    substᵀ-map-⇑ˢ-fuel (suc fuel) {Δ = Δ} {Δ' = Δ'} τ {Γ = Γ , B} {Γ' = Γ'} σ Z =
      substᵀ-map-⇑ˢ-fuel-Z-core τ {Γ = Γ} {Γ' = Γ'} {B = B} σ
        (subᵀ-sub-Λ-body-fuel fuel τ σ (` Z))
    substᵀ-map-⇑ˢ-fuel fuel {Δ' = Δ'} τ {Γ = Γ , B} {Γ' = Γ'} σ (S x)
      rewrite cast-substCtx-extsᵗ-⇑ᶜ-S τ {Γ = Γ} {B = B} x =
      trans
        (substᵀ-map-⇑ˢ-fuel fuel τ {Γ = Γ} {Γ' = Γ'} (λ y → σ (S y)) x)
        (cong
          (substEq (_ ;_⊢ _) (sym (substCtx-extsᵗ-⇑ᶜ τ Γ')))
          (sym
            (⇑ˢ-cong
              (λ z → sym (substᵀ-map-tail τ σ z))
              (substEq (λ Ψ → Ψ ∋ _)
              (substCtx-extsᵗ-⇑ᶜ τ Γ)
              x))))

    substᵀ-map-⇑ˢ-fuel-Z-core {Δ' = Δ'} τ {Γ = Γ} {Γ' = Γ'} {B = B} σ bridge =
      sym
        (trans
          (cong
            (substEq
              (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
              (sym (substCtx-extsᵗ-⇑ᶜ τ Γ')))
            z-body)
          (substEq-cancel-sym
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
            (substCtx-extsᵗ-⇑ᶜ τ Γ')
            (substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z)))
      where
      z-body :
          ⇑ˢ (substᵀ-map τ σ)
            (substEq (λ Ψ → Ψ ∋ substᵗ (extsᵗ τ) (renameᵗ S_ B))
              (substCtx-extsᵗ-⇑ᶜ τ (Γ , B))
              Z)
        ≡
          substEq
            (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) (renameᵗ S_ B))
            (substCtx-extsᵗ-⇑ᶜ τ Γ')
            (substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z)
      z-body = trans leftFix (trans bridge rightFix)
        where
        pΓ : substCtx (extsᵗ τ) (⇑ᶜ (Γ , B)) ≡ ⇑ᶜ (substCtx τ (Γ , B))
        pΓ = substCtx-extsᵗ-⇑ᶜ τ (Γ , B)
  
        pΓ' : substCtx (extsᵗ τ) (⇑ᶜ Γ') ≡ ⇑ᶜ (substCtx τ Γ')
        pΓ' = substCtx-extsᵗ-⇑ᶜ τ Γ'
  
        T : Type (Δ' ,α)
        T = substᵗ (extsᵗ τ) (renameᵗ S_ B)
  
        zVar : ⇑ᶜ (Γ , B) ∋ renameᵗ S_ B
        zVar = Z
  
        x0 : substCtx (extsᵗ τ) (⇑ᶜ (Γ , B)) ∋ T
        x0 = substᵗ-∋ (extsᵗ τ) zVar
  
        kL1 : substᵀ (extsᵗ τ) (` zVar) ≡ ` x0
        kL1 = refl
  
        kL2 : x0 ≡ Z
        kL2 = refl
  
        leftFix :
            ⇑ˢ (substᵀ-map τ σ)
              (substEq (λ Ψ → Ψ ∋ T) pΓ x0)
          ≡
            subst (⇑ˢ (substᵀ-map τ σ))
              (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ (substᵀ (extsᵗ τ) (` zVar)))
        leftFix =
          sym
            (trans
              (cong
                (subst (⇑ˢ (substᵀ-map τ σ)))
                (trans
                  (cong (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ) kL1)
                  (cast-var-term pΓ x0)))
              (cong
                (⇑ˢ (substᵀ-map τ σ))
                (cong (substEq (λ Ψ → Ψ ∋ T) pΓ) kL2)))
  
        kR1 : subst (⇑ˢ σ) (` Z) ≡ ⇑ˢ σ Z
        kR1 = refl
  
        kR2 : substᵀ (extsᵗ τ) (⇑ˢ σ Z) ≡ substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z
        kR2 = refl
  
        rightFix :
            substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ'
              (substᵀ (extsᵗ τ) (subst (⇑ˢ σ) (` Z)))
          ≡
            substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ'
              (substᵀ-map (extsᵗ τ) (⇑ˢ σ) Z)
        rightFix =
          cong
            (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ T) pΓ')
            (trans (cong (substᵀ (extsᵗ τ)) kR1) kR2)

    subᵀ-sub-Λ-body-fuel fuel {Δ = Δ} {Δ' = Δ'} τ {Γ = Γ} {Γ' = Γ'} {A = A} σ N =
      trans
        (subst-substEqᶜ
          (substCtx-extsᵗ-⇑ᶜ τ Γ)
          (substCtx-extsᵗ-⇑ᶜ τ Γ')
          (⇑ˢ (substᵀ-map τ σ))
          (substᵀ-map (extsᵗ τ) (⇑ˢ σ))
          coh
          (substᵀ (extsᵗ τ) N))
        (cong
          (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ substᵗ (extsᵗ τ) A) (substCtx-extsᵗ-⇑ᶜ τ Γ'))
          (subᵀ-sub-fuel fuel (extsᵗ τ) (⇑ˢ σ) N))
      where
      coh : ∀ {B} (x : substCtx (extsᵗ τ) (⇑ᶜ Γ) ∋ B)
        → substEq (λ Ψ → Δ' ,α ; Ψ ⊢ B)
            (substCtx-extsᵗ-⇑ᶜ τ Γ')
            (substᵀ-map (extsᵗ τ) (⇑ˢ σ) x)
          ≡
          ⇑ˢ (substᵀ-map τ σ)
            (substEq (λ Ψ → Ψ ∋ B)
              (substCtx-extsᵗ-⇑ᶜ τ Γ)
              x)
      coh {B = B} x =
        trans
          (cong
            (substEq (λ Ψ → Δ' ,α ; Ψ ⊢ B)
              (substCtx-extsᵗ-⇑ᶜ τ Γ'))
            (substᵀ-map-⇑ˢ-fuel fuel τ σ x))
          (substEq-cancel
            (λ Ψ → Δ' ,α ; Ψ ⊢ B)
            (substCtx-extsᵗ-⇑ᶜ τ Γ')
            (⇑ˢ (substᵀ-map τ σ)
              (substEq (λ Ψ → Ψ ∋ B)
              (substCtx-extsᵗ-⇑ᶜ τ Γ)
              x)))
  
    subᵀ-sub-fuel fuel τ σ `zero = refl
    subᵀ-sub-fuel fuel τ σ `true = refl
    subᵀ-sub-fuel fuel τ σ `false = refl
    subᵀ-sub-fuel fuel τ σ (`suc M) rewrite subᵀ-sub-fuel fuel τ σ M = refl
    subᵀ-sub-fuel fuel τ σ (`case-nat L M N)
      rewrite subᵀ-sub-fuel fuel τ σ L
            | subᵀ-sub-fuel fuel τ σ M =
      cong (`case-nat (substᵀ τ (subst σ L)) (substᵀ τ (subst σ M)))
        (trans
          (substᵀ-map-exts-subst τ {A = `Nat} σ (substᵀ τ N))
          (subᵀ-sub-fuel fuel τ (exts σ) N))
    subᵀ-sub-fuel fuel τ σ (`if_then_else L M N)
      rewrite subᵀ-sub-fuel fuel τ σ L
            | subᵀ-sub-fuel fuel τ σ M
            | subᵀ-sub-fuel fuel τ σ N = refl
    subᵀ-sub-fuel fuel τ σ (` x) = substᵀ-map-∋ τ σ x
    subᵀ-sub-fuel fuel τ σ (ƛ A ˙ N) =
      cong (ƛ substᵗ τ A ˙_)
        (trans
          (substᵀ-map-exts-subst τ {A = A} σ (substᵀ τ N))
          (subᵀ-sub-fuel fuel τ (exts σ) N))
    subᵀ-sub-fuel fuel τ σ (L · M)
      rewrite subᵀ-sub-fuel fuel τ σ L
            | subᵀ-sub-fuel fuel τ σ M = refl
    subᵀ-sub-fuel fuel τ {Γ = Γ} {Γ' = Γ'} σ (Λ N) =
      cong Λ_ (subᵀ-sub-Λ-body-fuel fuel τ σ N)
    subᵀ-sub-fuel fuel {Δ' = Δ'} τ {Γ = Γ} {Γ' = Γ'} σ (_∙_ {A = A} M B) =
      trans
        (subst-substEq (substᵀ-map τ σ)
          (sym (substᵗ-[]ᵗ τ A B))
          (substᵀ τ M ∙ substᵗ τ B))
        (cong
          (substEq
            (λ T → Δ' ; substCtx τ Γ' ⊢ T)
            (sym (substᵗ-[]ᵗ τ A B)))
          (cong (_∙ substᵗ τ B) (subᵀ-sub-fuel fuel τ σ M)))

subᵀ-sub-Λ-body : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ}
  {A : Type (Δ ,α)}
  (σ : Γ →ˢ Γ')
  (N : Δ ,α ; ⇑ᶜ Γ ⊢ A)
  → subst (⇑ˢ (substᵀ-map τ σ))
      (substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ τ Γ)
        (substᵀ (extsᵗ τ) N))
    ≡
    substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ τ Γ')
      (substᵀ (extsᵗ τ) (subst (⇑ˢ σ) N))
subᵀ-sub-Λ-body τ σ N = subᵀ-sub-Λ-body-fuel zero τ σ N

substᵀ-map-⇑ˢ : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ}
  (σ : Γ →ˢ Γ')
  → ∀ {A} (x : substCtx (extsᵗ τ) (⇑ᶜ Γ) ∋ A)
  → substᵀ-map (extsᵗ τ) (⇑ˢ σ) x
    ≡ substEq
        (λ Ψ → Δ' ,α ; Ψ ⊢ A)
        (sym (substCtx-extsᵗ-⇑ᶜ τ Γ'))
        (⇑ˢ (substᵀ-map τ σ)
          (substEq (λ Ψ → Ψ ∋ A)
            (substCtx-extsᵗ-⇑ᶜ τ Γ)
            x))
substᵀ-map-⇑ˢ τ σ x = substᵀ-map-⇑ˢ-fuel zero τ σ x

subᵀ-sub : ∀ {Δ Δ'} (τ : Δ ⇒ˢ Δ')
  {Γ Γ' : Ctx Δ} {A : Type Δ}
  (σ : Γ →ˢ Γ')
  (M : Δ ; Γ ⊢ A)
  → subst (substᵀ-map τ σ) (substᵀ τ M)
    ≡ substᵀ τ (subst σ M)
subᵀ-sub τ σ M = subᵀ-sub-fuel zero τ σ M

substᵀ-map↑ᵗ-⇑ˢ-coh : ∀ {Δ} {Γ₂ Γ₃ : Ctx Δ}
  (τ : Γ₂ →ˢ Γ₃)
  → ∀ {A} (x : substCtx ↑ᵗ Γ₂ ∋ A)
  → substEq (λ Ψ → Δ ,α ; Ψ ⊢ A)
      (substCtx-↑ᵗ Γ₃)
      (substᵀ-map ↑ᵗ τ x)
    ≡
    ⇑ˢ τ
      (substEq (λ Ψ → Ψ ∋ A)
        (substCtx-↑ᵗ Γ₂)
        x)
substᵀ-map↑ᵗ-⇑ˢ-coh {Γ₂ = ∅} τ ()
substᵀ-map↑ᵗ-⇑ˢ-coh {Δ = Δ} {Γ₂ = Γ , B} {Γ₃ = Γ₃} τ Z =
  trans leftToCanonical (sym rightToCanonical)
  where
  pΓ₃ : substCtx ↑ᵗ Γ₃ ≡ renameCtx S_ Γ₃
  pΓ₃ = substCtx-↑ᵗ Γ₃

  pB : substᵗ ↑ᵗ B ≡ renameᵗ S_ B
  pB = substᵗ-↑ᵗ B

  L0 : Δ ,α ; renameCtx S_ Γ₃ ⊢ substᵗ ↑ᵗ B
  L0 = substEq
        (λ Ψ → Δ ,α ; Ψ ⊢ substᵗ ↑ᵗ B)
        pΓ₃
        (substᵀ-map ↑ᵗ τ Z)

  P : Type (Δ ,α) → Set
  P T = Δ ,α ; renameCtx S_ Γ₃ ⊢ T

  leftToCanonical :
      substEq (λ Ψ → Δ ,α ; Ψ ⊢ substᵗ ↑ᵗ B)
        pΓ₃
        (substᵀ-map ↑ᵗ τ Z)
    ≡
      substEq P (sym pB) (⇑ᵀ (τ Z))
  leftToCanonical =
    trans
      (sym (substEq-cancel-sym P pB L0))
      (cong
        (substEq P (sym pB))
        (trans
          (sym (cast-ctx-type-term pΓ₃ pB (substᵀ ↑ᵗ (τ Z))))
          (cast↑-substᵀ↑ᵗ (τ Z))))

  rightToCanonical :
      ⇑ˢ τ
        (substEq
          (λ Ψ → Ψ ∋ substᵗ ↑ᵗ B)
          (substCtx-↑ᵗ (Γ , B))
          Z)
    ≡
      substEq P (sym pB) (⇑ᵀ (τ Z))
  rightToCanonical =
    trans
      (cong (⇑ˢ τ) (cast-substCtx-↑ᵗ-Z {Γ = Γ} {B = B}))
      (⇑ˢ-castᵗ τ (sym pB) Z)
substᵀ-map↑ᵗ-⇑ˢ-coh {Γ₂ = Γ , B} {Γ₃ = Γ₃} τ {A = A} (S x) =
  trans
    (substᵀ-map↑ᵗ-⇑ˢ-coh
      {Γ₂ = Γ}
      {Γ₃ = Γ₃}
      (λ y → τ (S y))
      x)
    (sym
      (cong
        (⇑ˢ τ)
        (cast-substCtx-↑ᵗ-S {Γ = Γ} {B = B} x)))

subst-⇑ˢ-cast↑ : ∀ {Δ} {Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (τ : Γ₂ →ˢ Γ₃)
  (N : Δ ,α ; substCtx ↑ᵗ Γ₂ ⊢ substᵗ ↑ᵗ A)
  → subst (⇑ˢ τ) (cast↑ N)
    ≡ cast↑ (subst (substᵀ-map ↑ᵗ τ) N)
subst-⇑ˢ-cast↑ {Γ₂ = Γ₂} {Γ₃ = Γ₃} {A = A} τ N =
  trans
    (subst-substEqᶜ
      (substCtx-↑ᵗ Γ₂)
      (substCtx-↑ᵗ Γ₃)
      (⇑ˢ τ)
      (substᵀ-map ↑ᵗ τ)
      (substᵀ-map↑ᵗ-⇑ˢ-coh τ)
      (substEq
        (λ T → _ ,α ; substCtx ↑ᵗ Γ₂ ⊢ T)
        (substᵗ-↑ᵗ A)
        N))
    (cong
      (substEq (λ Ψ → _ ,α ; Ψ ⊢ renameᵗ S_ A) (substCtx-↑ᵗ Γ₃))
      (subst-substEq
        (substᵀ-map ↑ᵗ τ)
        (substᵗ-↑ᵗ A)
        N))

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

subst-⇑ˢ-⇑ᵀ : ∀ {Δ} {Γ₂ Γ₃ : Ctx Δ} {A : Type Δ}
  (τ : Γ₂ →ˢ Γ₃)
  (M : Δ ; Γ₂ ⊢ A)
  → subst (⇑ˢ τ) (⇑ᵀ M) ≡ ⇑ᵀ (subst τ M)
subst-⇑ˢ-⇑ᵀ τ M =
  trans
    (cong (subst (⇑ˢ τ)) (sym (cast↑-substᵀ↑ᵗ M)))
    (trans
      (subst-⇑ˢ-cast↑ τ (substᵀ ↑ᵗ M))
      (trans
        (cong cast↑ (subᵀ-sub ↑ᵗ τ M))
        (cast↑-substᵀ↑ᵗ (subst τ M))))

⇑ˢ-subst : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ}
  (σ : Γ₁ →ˢ Γ₂)
  (τ : Γ₂ →ˢ Γ₃)
  → ∀ {A} (x : ⇑ᶜ Γ₁ ∋ A)
  → subst (⇑ˢ τ) (⇑ˢ σ x) ≡ ⇑ˢ (σ ⨟ τ) x
⇑ˢ-subst {Γ₁ = ∅} σ τ ()
⇑ˢ-subst {Γ₁ = Γ₁ , B} σ τ Z =
  subst-⇑ˢ-⇑ᵀ τ (σ Z)
⇑ˢ-subst {Γ₁ = Γ₁ , B} σ τ (S x) =
  ⇑ˢ-subst (λ y → σ (S y)) τ x

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
