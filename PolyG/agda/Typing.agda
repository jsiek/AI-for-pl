module Typing where

-- File Charter:
--   * Typing of PolyCν terms (thesis Fig. 10.9), ∀ν fragment, including
--     the runtime forms: seals from the store, injections and proxies.
--   * Σ ∣ Δ ∣ Γ ⊢ M ⦂ A: Σ types the seals created so far, Δ records the
--     abstract and known type variables, Γ types the term variables.
--   * A proxy Λν cs M is typed by typing the stack of casts applied to
--     its body.  In `inst M B N` the result type is not allowed to
--     mention the new type variable.

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)

open import Types
open import Terms

------------------------------------------------------------------------
-- Term contexts
------------------------------------------------------------------------

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_

data _∋_⦂_ : Ctx → ℕ → Ty → Set where
  Z : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  S : ∀ {Γ A B x} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

-- moving a term context under a type binder
⤊ : Ctx → Ctx
⤊ Γ = map ⇑ᵗ Γ

------------------------------------------------------------------------
-- The type a name stands for: a known type variable or a seal
------------------------------------------------------------------------

data NameTy (Σ : Store) (Δ : TyEnv) : Name → Ty → Set where
  nt-var  : ∀ {i A} → Δ ∋ i ≅ A → NameTy Σ Δ (tvar i) A
  nt-seal : ∀ {s A} → Σ ∋ˢ s ⦂ A → NameTy Σ Δ (tseal s) A

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⦂_

data _∣_∣_⊢_⦂_ (Σ : Store) (Δ : TyEnv) : Ctx → Term → Ty → Set where
  ⊢` : ∀ {Γ x A} →
    Γ ∋ x ⦂ A →
    Σ ∣ Δ ∣ Γ ⊢ ` x ⦂ A

  ⊢℧ : ∀ {Γ A} →
    Σ ∣ Δ ∣ Γ ⊢ ℧ ⦂ A

  ⊢true : ∀ {Γ} →
    Σ ∣ Δ ∣ Γ ⊢ true ⦂ 𝔹

  ⊢false : ∀ {Γ} →
    Σ ∣ Δ ∣ Γ ⊢ false ⦂ 𝔹

  ⊢if : ∀ {Γ L M N A} →
    Σ ∣ Δ ∣ Γ ⊢ L ⦂ 𝔹 →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ A →
    Σ ∣ Δ ∣ Γ ⊢ N ⦂ A →
    Σ ∣ Δ ∣ Γ ⊢ if L M N ⦂ A

  ⊢ƛ : ∀ {Γ A B M} →
    Σ ∣ Δ ∣ (A ∷ Γ) ⊢ M ⦂ B →
    Σ ∣ Δ ∣ Γ ⊢ ƛ A M ⦂ A ⇒ B

  ⊢· : ∀ {Γ L M A B} →
    Σ ∣ Δ ∣ Γ ⊢ L ⦂ A ⇒ B →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ A →
    Σ ∣ Δ ∣ Γ ⊢ L · M ⦂ B

  ⊢letv : ∀ {Γ M N A B} →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ A →
    Σ ∣ Δ ∣ (A ∷ Γ) ⊢ N ⦂ B →
    Σ ∣ Δ ∣ Γ ⊢ letv M N ⦂ B

  ⊢seal : ∀ {Γ α M A} →
    NameTy Σ Δ α A →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ A →
    Σ ∣ Δ ∣ Γ ⊢ seal α M ⦂ ‵ α

  ⊢unseal : ∀ {Γ α M A} →
    NameTy Σ Δ α A →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ ‵ α →
    Σ ∣ Δ ∣ Γ ⊢ unseal α M ⦂ A

  ⊢is : ∀ {Γ G M} →
    WfGround (tsize Δ) G →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ ★ →
    Σ ∣ Δ ∣ Γ ⊢ is G M ⦂ 𝔹

  ⊢inj : ∀ {Γ G M} →
    WfGround (tsize Δ) G →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ groundTy G →
    Σ ∣ Δ ∣ Γ ⊢ inj G M ⦂ ★

  ⊢up : ∀ {Γ p M A B} →
    tsize Δ ⊢ p ⦂ A ⊑ B →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ A →
    Σ ∣ Δ ∣ Γ ⊢ cast up p M ⦂ B

  ⊢down : ∀ {Γ p M A B} →
    tsize Δ ⊢ p ⦂ A ⊑ B →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ B →
    Σ ∣ Δ ∣ Γ ⊢ cast down p M ⦂ A

  ⊢Λν : ∀ {Γ cs M A} →
    Σ ∣ (abs ∷ Δ) ∣ ⤊ Γ ⊢ stack cs M ⦂ A →
    Σ ∣ Δ ∣ Γ ⊢ Λν cs M ⦂ ∀ν A

  ⊢inst : ∀ {Γ M B N A C} →
    Σ ∣ Δ ∣ Γ ⊢ M ⦂ ∀ν A →
    WfTy (tsize Δ) B →
    Σ ∣ (known B ∷ Δ) ∣ (A ∷ ⤊ Γ) ⊢ N ⦂ ⇑ᵗ C →
    Σ ∣ Δ ∣ Γ ⊢ inst M B N ⦂ C
