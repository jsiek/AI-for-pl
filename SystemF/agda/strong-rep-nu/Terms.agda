module strong-rep-nu.Terms where

-- File Charter:
--   * THE TERM SYNTAX, THE TYPING JUDGEMENT, AND VALUES.  §1 `Var` and
--     `Term` (last constructor: the boundary `_⟪_,_⟫`), `Ctx`, `_∋_⦂_`,
--     `⤊`.  §2 `Inert`/`Active`.  §3 `Value`, stated BEFORE the typing
--     judgement because `⊢Λ` reads it.  §4 `_∣_⊢_⦂_` with `env` and
--     `⊢Λ`, plus `value-var-visible`.  §5 `β-seven`.
--   * NO OPERATIONS AND NO METATHEORY: see strong-rep-nu.TermSubst,
--     .Reduction, .TypeCheck and the proof/ tree.
--   * FOUR LAWS.  (1) `env` TAKES `BoundaryWf Δ Θ Δᵢ Δᶜ`; the two
--     induced contexts are its outputs, never computed.  (2) It
--     compares all three sides by the REPRESENTATION each denotes
--     (`_⊢_≈_⊣_`), and a boundary's interior is TERM-CLOSED.
--     (3) Classification is by the CONVERSION CONSTRUCTOR alone.
--     (4) THE VALUE RESTRICTION: `⊢Λ` requires `Value N`, and there is
--     no ξ-Λ.
-- Commentary: Commentary.md § Terms.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; TyVar; Renameᵗ; renameᵗ; extᵗ;
         ⇑ᵗ; _[_]ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary

private
  variable
    Δ Δ′ : Ctxᵗ
    A B : Ty
    X Y : ℕ

------------------------------------------------------------------------
-- 1.  Terms
------------------------------------------------------------------------

Var : Set
Var = ℕ

infix  9 `_
infix  9 $_
infixl 7 _·_
infix  6 ƛ_∙_
infix  5 _⟪_,_⟫
infix  5 ν_·_⟨_⟩

data Term : Set where
  `_      : Var → Term
  $_      : ℕ → Term
  `true   : Term
  `false  : Term
  ƛ_∙_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  ν_·_⟨_⟩ : Ty → Term → Conv → Term
  _⟪_,_⟫  : Term → Boundary → Conv → Term

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → Var → Ty → Set where
  here  : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  there : ∀ {Γ x A B} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

⤊ : Ctx → Ctx
⤊ Γ = map ⇑ᵗ Γ

------------------------------------------------------------------------
-- 2.  Classification — ACTIVE / INERT, by the CONVERSION constructor
------------------------------------------------------------------------

-- Inert  = { s ↦ t , ∀ s , seal X , id-at-a-variable }
-- Active = { unseal X , id-at-base }
data Inert : Conv → Set where
  I-idv  : ∀ {X}   → Inert (id (` X))
  I-seal : ∀ {X}   → Inert (seal X)
  I-fun  : ∀ {s t} → Inert (s ↦ t)
  I-all  : ∀ {s}   → Inert (`∀ s)

data Active : Conv → Set where
  A-idb    : ∀ {A} → Base A → Active (id A)
  A-unseal : ∀ {X} → Active (unseal X)

-- Totality over TYPED conversions: the payload restriction on `id`
-- makes classification a match on the TYPING derivation.
act-or-inert : ∀ {Δ c A B} → Δ ⊢ c ∶ A ⇝ B → Active c ⊎ Inert c
act-or-inert (conv-id b)      = inj₁ (A-idb b)
act-or-inert (conv-idv tv)    = inj₂ I-idv
act-or-inert (conv-seal o)    = inj₂ I-seal
act-or-inert (conv-unseal o)  = inj₁ A-unseal
act-or-inert (conv-fun s t)   = inj₂ I-fun
act-or-inert (conv-all s)     = inj₂ I-all

act-not-inert : ∀ {c} → Active c → Inert c → ⊥
act-not-inert (A-idb ()) I-idv
act-not-inert A-unseal ()

------------------------------------------------------------------------
-- 3.  Values
------------------------------------------------------------------------

-- V-Λ carries `Value N`, which `⊢Λ` makes automatic here; it is kept so
-- that `Value` stays strong-rep-var's relation verbatim.
-- Commentary.md § Terms.agda / §3
data Value : Term → Set where
  V-$  : ∀ {n} → Value ($ n)
  V-true : Value `true
  V-false : Value `false
  V-ƛ  : ∀ {A N} → Value (ƛ A ∙ N)
  V-Λ  : ∀ {N} → Value N → Value (Λ N)
  V-⟪⟫ : ∀ {M Θ c} → Value M → Inert c → Value (M ⟪ Θ , c ⟫)

------------------------------------------------------------------------
-- 4.  The typing judgment
------------------------------------------------------------------------

infix 3 _∣_⊢_⦂_
data _∣_⊢_⦂_ : Ctxᵗ → Ctx → Term → Ty → Set where

  ⊢` : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Δ Γ n} → Δ ∣ Γ ⊢ $ n ⦂ `ℕ

  ⊢true : ∀ {Δ Γ} → Δ ∣ Γ ⊢ `true ⦂ `𝔹

  ⊢false : ∀ {Δ Γ} → Δ ∣ Γ ⊢ `false ⦂ `𝔹

  ⊢ƛ : ∀ {Δ Γ A B N} → Δ ⊢ᵗ A → Δ ∣ A ∷ Γ ⊢ N ⦂ B
     → Δ ∣ Γ ⊢ ƛ A ∙ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Δ Γ A B L M}
    → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B)
    → Δ ∣ Γ ⊢ M ⦂ A
    → Δ ∣ Γ ⊢ L · M ⦂ B

  -- THE VALUE RESTRICTION (strong-rep-nu's first experiment): a type
  -- abstraction's body must ALREADY be a value.
  -- Commentary.md § Terms.agda / §4 — ⊢Λ
  ⊢Λ : ∀ {Δ Γ C N} → Value N → underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C
    → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C

  -- (ν). Instantiate `L : ∀ C` at a fresh cell holding `A`'s
  -- representation `R` and convert with `c`.  `c` is read on the
  -- conversion context of `TyBetaBoundary` at `allocate R Δ` — the
  -- context the `Nu` rules leave — and ANY `c` whose types line up is
  -- accepted (the compiler writes `reveal 0 C`, strong-rep-nu.Compile).
  -- Commentary.md § Terms.agda / §4 — ⊢ν
  ⊢ν : ∀ {Δ Δᵢ Δᶜ Γ A R L C Cₑ B c}
     → Δ ⊢ᵗ A
     → Δ ⊢ᶜ A ~ R
     → Δ ∣ Γ ⊢ L ⦂ `∀ C
     → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
     → Δᶜ ⊢ c ∶ C ⇝ Cₑ
     → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ
     → Δ ⊢ᵗ B
       --------------------------------------------
     → Δ ∣ Γ ⊢ ν A · L ⟨ c ⟩ ⦂ B

  -- (env). The boundary scope witness supplies both contexts, and the
  -- three sides are compared by the representation each denotes.
  -- Commentary.md § Terms.agda / §4 — env
  env : ∀ {Δ Δᵢ Δᶜ Γ Θ c M Bᵢ Cᵢ Cₑ Bₑ}
      → BoundaryWf Δ Θ Δᵢ Δᶜ
      → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
      → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
      → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
      → Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ
      → Δ ⊢ᵗ Bₑ
        --------------------------------------------
      → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

-- A value's variable type is VISIBLE on its own type context, so a
-- boundary can never conceal the slot its conversion names.
value-var-visible : ∀ {Δ V X}
  → Value V → Δ ∣ [] ⊢ V ⦂ ` X → Δ ∋tv X
value-var-visible (V-⟪⟫ _ _) (env _ _ _ _ _ (wf-var tv)) = tv

------------------------------------------------------------------------
-- 5. Concrete boundary typing
------------------------------------------------------------------------

β-seven : Term
β-seven = ($ 7) ⟪ TyBetaBoundary , id `ℕ ⟫

-- typed at the context Nu-Λ LEAVES: the cell for ℕ has been allocated
β-seven-⊢ : allocate `ℕ empty ∣ [] ⊢ β-seven ⦂ `ℕ
β-seven-⊢ =
  env TyBeta-bw ⊢$ (conv-id base-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      wf-ℕ
