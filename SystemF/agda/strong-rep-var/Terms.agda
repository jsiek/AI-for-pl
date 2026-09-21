module strong-rep-var.Terms where

-- File Charter:
--   * THE TERM SYNTAX, THE TYPING JUDGEMENT, AND VALUES.  §1 is `Var`
--     (= ℕ) and `Term`, whose last constructor is the boundary
--     `_⟪_,_⟫`, together with the ordinary term context `Ctx`, its
--     lookup `_∋_⦂_` and the type-binder lift `⤊`.  §2 is
--     `_∣_⊢_⦂_`, the typing judgement, whose boundary rule is `env`.
--     §3 classifies a conversion as `Inert` or `Active`, with
--     `act-or-inert` and `act-not-inert`.  §4 is `Value` and
--     `value-var-visible`; §5 the concrete `β-seven`/`β-seven-⊢`.
--   * NO OPERATIONS AND NO METATHEORY.  Renaming and substitution on
--     terms are strong-rep-var.TermSubst; reduction is
-- strong-rep-var.Reduction; the
--     decision procedures that BUILD these derivations are
--     strong-rep-var.TypeCheck; canonical forms, preservation and progress are
--     under strong-rep-var.proof (the public theorem statements being
--     strong-rep-var.Preservation, strong-rep-var.Progress,
-- strong-rep-var.TypeSafety).
--   * THREE LAWS A READER MUST KNOW.  (1) `env` never COMPUTES the two
--     contexts a boundary scope induces: it takes `BoundaryWf Δ Θ Δᵢ Δᶜ`
--     (strong-rep-var.Boundary) and the two contexts are its outputs — the
--     retired `interior`/`convCtx` functions are gone.  (2) The three
--     sides can spell the same semantic type differently, so `env`
--     compares them by the REPRESENTATION each denotes:
--     `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` at equal representation depth, and
--     `SameTyExt (numBinds Θ) Δ Bₑ Δᶜ Cₑ`, which additionally crosses
--     the boundary scope's own bind prefix (strong-rep-var.Ctx §5).  A
--     boundary's interior is TERM-CLOSED — `Δᵢ ∣ [] ⊢ M ⦂ Bᵢ` — which is what
--     lets strong-rep-var.TermSubst leave wrappers alone.  (3) Classification
--     in §3 is by the CONVERSION CONSTRUCTOR alone: no source or target type
--     is inspected and no slot arithmetic occurs, so `id` at a variable
--     is inert and `id` at a base type is active.  `V-Λ` carries
--     `Value N` because reduction goes UNDER `Λ` (`ξ-Λ`); without it
--     both "values don't step" and determinism are false
--     (notes/DECISIONS.md, the Id-layer RULING of 2026-09-05,
--     repair 3).
--
-- A boundary is  M ⟪ Θ , c ⟫  with ONE frame change:
--
--   Θ : Boundary   a parallel block of representation-variable binders and
--                  a sequential list of ordinary-variable binders and
--                  anti-binders. `BoundaryWf Δ Θ Δᵢ Δᶜ` produces the
--                  interior context Δᵢ and conversion context Δᶜ.
--
--   c : Conv       the conversion checked on Δᶜ. Its source is related to
--                  the interior term's type through `_⊢_≈_⊣_`; its
--                  target is
--                  related to the exterior type the same way.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-var.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; TyVar; Renameᵗ; renameᵗ; extᵗ;
         ⇑ᵗ; _[_]ᵗ)
open import strong-rep-var.Ctx
open import strong-rep-var.Conversion
open import strong-rep-var.Boundary

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

data Term : Set where
  `_      : Var → Term
  $_      : ℕ → Term
  `true   : Term
  `false  : Term
  ƛ_∙_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _·[_,_] : Term → Ty → Ty → Term
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
-- 2.  The typing judgment
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

  ⊢Λ : ∀ {Δ Γ C N} → underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C
    → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C

  ⊢·[] : ∀ {Δ Γ A B L} → Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A
       → Δ ∣ Γ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

  -- (env). The boundary scope witness supplies both contexts. Since ordinary
  -- variables may be inserted and removed, the same semantic type can have
  -- different ordinary de Bruijn spellings on the three sides. `_⊢_≈_⊣_`
  -- compares the equal-depth interior and conversion contexts. `SameTyExt`
  -- additionally crosses the boundary scope's representation bind prefix when
  -- comparing the exterior and conversion contexts.
  env : ∀ {Δ Δᵢ Δᶜ Γ Θ c M Bᵢ Cᵢ Cₑ Bₑ}
      → BoundaryWf Δ Θ Δᵢ Δᶜ
      → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
      → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
      → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
      → SameTyExt (numBinds Θ) Δ Bₑ Δᶜ Cₑ
      → Δ ⊢ᵗ Bₑ
        --------------------------------------------
      → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

------------------------------------------------------------------------
-- 3.  Classification — ACTIVE / INERT, by the CONVERSION constructor
------------------------------------------------------------------------

-- Inert  = { s ↦ t , ∀ s , seal X , id-at-a-variable }
-- Active = { unseal X , id-at-base }
-- No source or target type is inspected and no slot arithmetic occurs.
data Inert : Conv → Set where
  I-idv  : ∀ {X}   → Inert (id (` X))
  I-seal : ∀ {X}   → Inert (seal X)
  I-fun  : ∀ {s t} → Inert (s ↦ t)
  I-all  : ∀ {s}   → Inert (`∀ s)

data Active : Conv → Set where
  A-idb    : ∀ {A} → Base A → Active (id A)
  A-unseal : ∀ {X} → Active (unseal X)

-- Totality over TYPED conversions: the payload restriction on `id` makes
-- classification a match on the TYPING derivation (the untypeable compound
-- identities are never classified at all).
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
-- 4.  Values
------------------------------------------------------------------------

-- V-Λ carries `Value N`.  Reduction goes UNDER Λ (ξ-Λ in
-- strong-rep-var.Reduction),
-- so without this premise `Λ N` would be a value for every N and both
-- "values don't step" and determinism would be false — the defect the
-- IdLayerProbe machine-checked (notes/DECISIONS.md, repair 3).
data Value : Term → Set where
  V-$  : ∀ {n} → Value ($ n)
  V-true : Value `true
  V-false : Value `false
  V-ƛ  : ∀ {A N} → Value (ƛ A ∙ N)
  V-Λ  : ∀ {N} → Value N → Value (Λ N)
  V-⟪⟫ : ∀ {M Θ c} → Value M → Inert c → Value (M ⟪ Θ , c ⟫)

-- A value's variable type is VISIBLE on the value's bind type context, because
-- `env`'s last conjunct checks it there.  So a boundary can never conceal
-- the slot its bind conversion names.
value-var-visible : ∀ {Δ V X}
  → Value V → Δ ∣ [] ⊢ V ⦂ ` X → Δ ∋tv X
value-var-visible (V-⟪⟫ _ _) (env _ _ _ _ _ (wf-var tv)) = tv

------------------------------------------------------------------------
-- 5. Concrete boundary typing
------------------------------------------------------------------------

β-seven : Term
β-seven = ($ 7) ⟪ TyBetaBoundary , id `ℕ ⟫

β-seven-⊢ : empty ∣ [] ⊢ β-seven ⦂ `ℕ
β-seven-⊢ =
  env TyBeta-bw ⊢$ (conv-id base-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      wf-ℕ
