module StaticGradualGuarantee where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Agda.Builtin.List using (_∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Types
open import Contexts
open import GTLC

_⊑ˢ_ : Ctx → Ctx → Set
Γ ⊑ˢ Γ′ = ∀ x A → Γ ∋ x ⦂ A → ∃[ A′ ] (Γ′ ∋ x ⦂ A′) × (A′ ⊑ A)

extend-⊑ˢ : ∀ {Γ Γ′ A A′} → A′ ⊑ A → Γ ⊑ˢ Γ′ → (A ∷ Γ) ⊑ˢ (A′ ∷ Γ′)
extend-⊑ˢ {A′ = A₀} A′⊑A Γ⊑Γ′ zero A Z = A₀ , Z , A′⊑A
extend-⊑ˢ A′⊑A Γ⊑Γ′ (suc x) B (S ∋x) =
  (Γ⊑Γ′ x B ∋x .proj₁) , S (Γ⊑Γ′ x B ∋x .proj₂ .proj₁) , (Γ⊑Γ′ x B ∋x .proj₂ .proj₂)

static-gradual-guarantee
  : ∀ {Γ Γ′ M M′ A}
  → Γ ⊢ M ⦂ A
  → M′ ⊑ᵀ M
  → Γ ⊑ˢ Γ′
  → ∃[ A′ ] (Γ′ ⊢ M′ ⦂ A′) × (A′ ⊑ A)
static-gradual-guarantee (⊢` {x = x} ∋x) ⊑` Γ⊑Γ′
  with Γ⊑Γ′ x _ ∋x
... | A′ , ∋x′ , A′⊑A =
  A′ , ⊢` ∋x′ , A′⊑A

static-gradual-guarantee ⊢$ ⊑$ Γ⊑Γ′ =
  ℕ , ⊢$ , ⊑-ℕ

static-gradual-guarantee (⊢ƛ {A = A} {N = N} {B = B} N⦂B)
                            (⊑ƛ {A = A′} A′⊑A N′⊑N)
                            Γ⊑Γ′
  with static-gradual-guarantee N⦂B N′⊑N (extend-⊑ˢ A′⊑A Γ⊑Γ′)
... | B′ , N′⦂B′ , B′⊑B =
  (A′ ⇒ B′) , ⊢ƛ N′⦂B′ , ⊑-⇒ A′⊑A B′⊑B

static-gradual-guarantee (⊢· {A = A} {A′ = Aarg} {B = B} L⦂A⇒B M⦂Aarg Aarg~A)
                            (⊑· L′⊑L M′⊑M)
                            Γ⊑Γ′
  with static-gradual-guarantee L⦂A⇒B L′⊑L Γ⊑Γ′
     | static-gradual-guarantee M⦂Aarg M′⊑M Γ⊑Γ′
... | ★ , L′⦂★ , _ | A′ , M′⦂A′ , _ =
  ★ , ⊢·★ L′⦂★ M′⦂A′ , ⊑-★
... | (A₀ ⇒ B₀) , L′⦂A₀⇒B₀ , (⊑-⇒ A₀⊑A B₀⊑B)
    | A′ , M′⦂A′ , A′⊑Aarg =
  B₀ , ⊢· L′⦂A₀⇒B₀ M′⦂A′ (app-consistency A′⊑Aarg Aarg~A A₀⊑A) , B₀⊑B

static-gradual-guarantee (⊢·★ {A = A} L⦂★ M⦂A)
                            (⊑· L′⊑L M′⊑M)
                            Γ⊑Γ′
  with static-gradual-guarantee L⦂★ L′⊑L Γ⊑Γ′
     | static-gradual-guarantee M⦂A M′⊑M Γ⊑Γ′
... | ★ , L′⦂★ , _ | A′ , M′⦂A′ , _ =
  ★ , ⊢·★ L′⦂★ M′⦂A′ , ⊑-★
