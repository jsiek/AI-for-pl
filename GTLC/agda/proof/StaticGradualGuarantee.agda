module proof.StaticGradualGuarantee where

-- File Charter:
--   * Private proof of the static gradual guarantee for GTLC.
--   * Exposed at the public surface via `MetaTheory.agda`.

open import Data.Product using (∃-syntax; _×_; _,_)
open import Types
open import Contexts
open import GTLC
open import proof.StaticGradualGuaranteeDefinitions

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
  with static-gradual-guarantee N⦂B N′⊑N
         (extend-⊑ˢ A′⊑A Γ⊑Γ′)
... | B′ , N′⦂B′ , B′⊑B =
  (A′ ⇒ B′) , ⊢ƛ N′⦂B′ , ⊑-⇒ A′⊑A B′⊑B

static-gradual-guarantee
  (⊢· {A = A} {A′ = Aarg} {B = B} L⦂A⇒B M⦂Aarg Aarg~A)
                            (⊑· L′⊑L M′⊑M)
                            Γ⊑Γ′
  with static-gradual-guarantee L⦂A⇒B L′⊑L Γ⊑Γ′
     | static-gradual-guarantee M⦂Aarg M′⊑M Γ⊑Γ′
... | ★ , L′⦂★ , _ | A′ , M′⦂A′ , _ =
  ★ , ⊢·★ L′⦂★ M′⦂A′ , ⊑-★
... | (A₀ ⇒ B₀) , L′⦂A₀⇒B₀ , (⊑-⇒ A₀⊑A B₀⊑B)
    | A′ , M′⦂A′ , A′⊑Aarg =
  B₀
  , ⊢· L′⦂A₀⇒B₀ M′⦂A′
      (app-consistency A′⊑Aarg Aarg~A A₀⊑A)
  , B₀⊑B

static-gradual-guarantee (⊢·★ {A = A} L⦂★ M⦂A)
                            (⊑· L′⊑L M′⊑M)
                            Γ⊑Γ′
  with static-gradual-guarantee L⦂★ L′⊑L Γ⊑Γ′
     | static-gradual-guarantee M⦂A M′⊑M Γ⊑Γ′
... | ★ , L′⦂★ , _ | A′ , M′⦂A′ , _ =
  ★ , ⊢·★ L′⦂★ M′⦂A′ , ⊑-★
