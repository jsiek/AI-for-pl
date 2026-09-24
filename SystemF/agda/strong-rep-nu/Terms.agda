module strong-rep-nu.Terms where

-- File Charter:
--   * THE TERM SYNTAX, THE TYPING JUDGEMENT, AND VALUES.  §1 `Var` and
--     `Term` (last constructor: the boundary `_⟪_,_⟫`), `Ctx`, `_∋_⦂_`,
--     `⤊`.  §2 `InertTail`/`Inert`/`Active`.  §3 `Simple`/`Value` —
--     AT MOST ONE BOUNDARY on a value — stated BEFORE the typing
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

-- A boundary over a SIMPLE value has a non-variable source type, so its
-- conversion is a TAIL.  Inert tails: everything but the identity at a
-- base type, which `Drop$`/`Drop-true`/`Drop-false` remove.
data InertTail : Tail → Set where
  I-idv      : ∀ {X}   → InertTail (mid (id (` X)))
  I-fun      : ∀ {s t} → InertTail (mid (s ↦ t))
  I-all      : ∀ {s}   → InertTail (mid (`∀ s))
  I-seal     : ∀ {X}   → InertTail (seal X)
  I-seal-seq : ∀ {t X} → InertTail (t ⨾seal X)

data Inert : Conv → Set where
  I-tail : ∀ {t} → InertTail t → Inert (tail t)

-- Active = { id-at-base , unseal X , unseal X ; c }
data Active : Conv → Set where
  A-idb        : ∀ {A} → Base A → Active ⌞ id A ⌟
  A-unseal     : ∀ {X} → Active (unseal X)
  A-unseal-seq : ∀ {X c} → Active (unseal X ⨾ c)

-- Totality over TYPED conversions: the payload restriction on `id`
-- makes classification a match on the TYPING derivation.
act-or-inert : ∀ {Δ c A B} → Δ ⊢ c ∶ A ⇝ B → Active c ⊎ Inert c
act-or-inert (conv-tail (conv-mid (conv-id b)))   = inj₁ (A-idb b)
act-or-inert (conv-tail (conv-mid (conv-idv tv))) = inj₂ (I-tail I-idv)
act-or-inert (conv-tail (conv-mid (conv-fun s t))) = inj₂ (I-tail I-fun)
act-or-inert (conv-tail (conv-mid (conv-all s)))   = inj₂ (I-tail I-all)
act-or-inert (conv-tail (conv-seal d))             = inj₂ (I-tail I-seal)
act-or-inert (conv-tail (conv-seal-seq t d n))     =
  inj₂ (I-tail I-seal-seq)
act-or-inert (conv-unseal d)             = inj₁ A-unseal
act-or-inert (conv-unseal-seq d c n m)   = inj₁ A-unseal-seq

act-not-inert : ∀ {c} → Active c → Inert c → ⊥
act-not-inert (A-idb ()) (I-tail I-idv)

------------------------------------------------------------------------
-- 3.  Values — at most ONE boundary
------------------------------------------------------------------------

-- A SIMPLE value is a value that is not a boundary; a value is a simple
-- value, or a simple value under ONE inert boundary.  A second boundary
-- on a value is a `Merge` redex.  `S-Λ` carries `Value N`, which `⊢Λ`
-- makes automatic.
-- Commentary.md § Terms.agda / §3
mutual
  data Simple : Term → Set where
    S-$     : ∀ {n} → Simple ($ n)
    S-true  : Simple `true
    S-false : Simple `false
    S-ƛ     : ∀ {A N} → Simple (ƛ A ∙ N)
    S-Λ     : ∀ {N} → Value N → Simple (Λ N)

  data Value : Term → Set where
    V-simple : ∀ {U} → Simple U → Value U
    V-⟪⟫     : ∀ {U Θ t} → Simple U → InertTail t
      → Value (U ⟪ Θ , tail t ⟫)

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
value-var-visible (V-simple S-$) ()
value-var-visible (V-simple S-true) ()
value-var-visible (V-simple S-false) ()
value-var-visible (V-simple S-ƛ) ()
value-var-visible (V-simple (S-Λ v)) ()

------------------------------------------------------------------------
-- 5. Concrete boundary typing
------------------------------------------------------------------------

β-seven : Term
β-seven = ($ 7) ⟪ TyBetaBoundary , ⌞ id `ℕ ⌟ ⟫

-- typed at the context Nu-Λ LEAVES: the cell for ℕ has been allocated
β-seven-⊢ : allocate `ℕ empty ∣ [] ⊢ β-seven ⦂ `ℕ
β-seven-⊢ =
  env TyBeta-bw ⊢$ (conv-tail (conv-mid (conv-id base-ℕ)))
      (`ℕ , same-ℕ , same-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      wf-ℕ
