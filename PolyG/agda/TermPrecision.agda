module TermPrecision where

-- File Charter:
--   * Term precision for PolyCν (thesis Fig. 10.25 and 10.26), ∀ν
--     fragment: Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p, with the more precise term on the
--     left.
--   * Δ⊑ records, for each type variable, whether it is abstract or known
--     with a precision derivation q : B ⊑ B′ between the two known types.
--     Γ⊑ gives a precision derivation for each term variable.
--   * The rules are structural, plus the four one-sided cast rules (an
--     upcast or a downcast on either side).  Only source forms appear:
--     no seals, injections, or proxies with a nonempty stack.

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)

open import Types
open import Terms

------------------------------------------------------------------------
-- Precision contexts
------------------------------------------------------------------------

data PInfo : Set where
  absᵖ   : PInfo
  knownᵖ : Prec → PInfo   -- X ≅ q, with q read in the outer context

PEnv : Set
PEnv = List PInfo

psize : PEnv → ℕ
psize [] = zero
psize (_ ∷ Δ⊑) = suc (psize Δ⊑)

⇑ᵖ : Prec → Prec
⇑ᵖ = substᵖ ↑ₙ

infix 4 _∋_≅ᵖ_

data _∋_≅ᵖ_ : PEnv → Var → Prec → Set where
  Z≅ᵖ : ∀ {Δ⊑ q} → (knownᵖ q ∷ Δ⊑) ∋ zero ≅ᵖ ⇑ᵖ q
  S≅ᵖ : ∀ {Δ⊑ I i q} → Δ⊑ ∋ i ≅ᵖ q → (I ∷ Δ⊑) ∋ suc i ≅ᵖ ⇑ᵖ q

PCtx : Set
PCtx = List Prec

infix 4 _∋_⦂ᵖ_

data _∋_⦂ᵖ_ : PCtx → ℕ → Prec → Set where
  Zᵖ : ∀ {Γ⊑ p} → (p ∷ Γ⊑) ∋ zero ⦂ᵖ p
  Sᵖ : ∀ {Γ⊑ p q x} → Γ⊑ ∋ x ⦂ᵖ p → (q ∷ Γ⊑) ∋ suc x ⦂ᵖ p

⤊ᵖ : PCtx → PCtx
⤊ᵖ Γ⊑ = map ⇑ᵖ Γ⊑

------------------------------------------------------------------------
-- Term precision
------------------------------------------------------------------------

infix 4 _∣_⊢_⊑_⦂_

data _∣_⊢_⊑_⦂_ (Δ⊑ : PEnv) : PCtx → Term → Term → Prec → Set where
  ⊑` : ∀ {Γ⊑ x p} →
    Γ⊑ ∋ x ⦂ᵖ p →
    Δ⊑ ∣ Γ⊑ ⊢ ` x ⊑ ` x ⦂ p

  ⊑letv : ∀ {Γ⊑ M M′ N N′ p q} →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p →
    Δ⊑ ∣ (p ∷ Γ⊑) ⊢ N ⊑ N′ ⦂ q →
    Δ⊑ ∣ Γ⊑ ⊢ letv M N ⊑ letv M′ N′ ⦂ q

  ⊑seal : ∀ {Γ⊑ X M M′ q} →
    Δ⊑ ∋ X ≅ᵖ q →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ q →
    Δ⊑ ∣ Γ⊑ ⊢ seal (tvar X) M ⊑ seal (tvar X) M′ ⦂ ‵⊑ (tvar X)

  ⊑unseal : ∀ {Γ⊑ X M M′ q} →
    Δ⊑ ∋ X ≅ᵖ q →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ ‵⊑ (tvar X) →
    Δ⊑ ∣ Γ⊑ ⊢ unseal (tvar X) M ⊑ unseal (tvar X) M′ ⦂ q

  ⊑is : ∀ {Γ⊑ G M M′} →
    WfGround (psize Δ⊑) G →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ ★⊑ →
    Δ⊑ ∣ Γ⊑ ⊢ is G M ⊑ is G M′ ⦂ 𝔹⊑

  ⊑true : ∀ {Γ⊑} →
    Δ⊑ ∣ Γ⊑ ⊢ true ⊑ true ⦂ 𝔹⊑

  ⊑false : ∀ {Γ⊑} →
    Δ⊑ ∣ Γ⊑ ⊢ false ⊑ false ⦂ 𝔹⊑

  ⊑if : ∀ {Γ⊑ L L′ M M′ N N′ q} →
    Δ⊑ ∣ Γ⊑ ⊢ L ⊑ L′ ⦂ 𝔹⊑ →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ q →
    Δ⊑ ∣ Γ⊑ ⊢ N ⊑ N′ ⦂ q →
    Δ⊑ ∣ Γ⊑ ⊢ if L M N ⊑ if L′ M′ N′ ⦂ q

  ⊑ƛ : ∀ {Γ⊑ A A′ M M′ p q} →
    psize Δ⊑ ⊢ p ⦂ A ⊑ A′ →
    Δ⊑ ∣ (p ∷ Γ⊑) ⊢ M ⊑ M′ ⦂ q →
    Δ⊑ ∣ Γ⊑ ⊢ ƛ A M ⊑ ƛ A′ M′ ⦂ p ⇒⊑ q

  ⊑· : ∀ {Γ⊑ L L′ M M′ p q} →
    Δ⊑ ∣ Γ⊑ ⊢ L ⊑ L′ ⦂ p ⇒⊑ q →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p →
    Δ⊑ ∣ Γ⊑ ⊢ L · M ⊑ L′ · M′ ⦂ q

  ⊑Λν : ∀ {Γ⊑ M M′ p} →
    (absᵖ ∷ Δ⊑) ∣ ⤊ᵖ Γ⊑ ⊢ M ⊑ M′ ⦂ p →
    Δ⊑ ∣ Γ⊑ ⊢ Λν [] M ⊑ Λν [] M′ ⦂ ∀⊑ p

  -- the labels ℓ and ℓ′ are arbitrary
  ⊑inst : ∀ {Γ⊑ M M′ B B′ ℓ ℓ′ N N′ p q r} →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ ∀⊑ p →
    psize Δ⊑ ⊢ q ⦂ B ⊑ B′ →
    (knownᵖ q ∷ Δ⊑) ∣ (p ∷ ⤊ᵖ Γ⊑) ⊢ N ⊑ N′ ⦂ ⇑ᵖ r →
    Δ⊑ ∣ Γ⊑ ⊢ inst M B ℓ N ⊑ inst M′ B′ ℓ′ N′ ⦂ r

  -- the four cast rules: AC = BC ∘ AB, with A ⊑ B ⊑ C
  ⊑upL : ∀ {Γ⊑ M M′ AB BC AC A B C} →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ AC →
    psize Δ⊑ ⊢ AB ⦂ A ⊑ B →
    psize Δ⊑ ⊢ BC ⦂ B ⊑ C →
    psize Δ⊑ ⊢ AC ⦂ A ⊑ C →
    Δ⊑ ∣ Γ⊑ ⊢ cast up AB M ⊑ M′ ⦂ BC

  ⊑downL : ∀ {Γ⊑ M M′ AB BC AC A B C} →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ BC →
    psize Δ⊑ ⊢ AB ⦂ A ⊑ B →
    psize Δ⊑ ⊢ BC ⦂ B ⊑ C →
    psize Δ⊑ ⊢ AC ⦂ A ⊑ C →
    Δ⊑ ∣ Γ⊑ ⊢ cast down AB M ⊑ M′ ⦂ AC

  ⊑upR : ∀ {Γ⊑ M M′ AB BC AC A B C} →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ AB →
    psize Δ⊑ ⊢ AB ⦂ A ⊑ B →
    psize Δ⊑ ⊢ BC ⦂ B ⊑ C →
    psize Δ⊑ ⊢ AC ⦂ A ⊑ C →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ cast up BC M′ ⦂ AC

  ⊑downR : ∀ {Γ⊑ M M′ AB BC AC A B C} →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ AC →
    psize Δ⊑ ⊢ AB ⦂ A ⊑ B →
    psize Δ⊑ ⊢ BC ⦂ B ⊑ C →
    psize Δ⊑ ⊢ AC ⦂ A ⊑ C →
    Δ⊑ ∣ Γ⊑ ⊢ M ⊑ cast down BC M′ ⦂ AB
