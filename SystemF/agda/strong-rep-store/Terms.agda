module strong-rep-store.Terms where

-- File Charter:
--   * THE TERM SYNTAX, THE TYPING JUDGEMENT, AND VALUES.  §1 is `Var`
--     (= ℕ) and `Term`, whose last constructor is the boundary
--     `_⟪_,_⟫`, together with the ordinary term context `Ctx`, its
--     lookup `_∋_⦂_` and the type-binder lift `⤊`.  §2 is
--     classifies a conversion as `Inert` or `Active`, with
--     `act-or-inert` and `act-not-inert`; §3 is `Value`, which comes
--     BEFORE the typing judgement because `⊢Λ` reads it.  §4 is
--     `_∣_⊢_⦂_`, the typing judgement, whose boundary rule is `env` and
--     whose `⊢Λ` rule carries the VALUE RESTRICTION `Value N` (the
--     strong-rep-store experiment), and `value-var-visible`; §5 the
--     concrete `β-seven`/`β-seven-⊢`.
--   * NO OPERATIONS AND NO METATHEORY.  Renaming and substitution on
--     terms are strong-rep-store.TermSubst; reduction is
-- strong-rep-store.Reduction; the
--     decision procedures that BUILD these derivations are
--     strong-rep-store.TypeCheck; canonical forms, preservation and progress are
--     under strong-rep-store.proof (the public theorem statements being
--     strong-rep-store.Preservation, strong-rep-store.Progress,
-- strong-rep-store.TypeSafety).
--   * FOUR LAWS A READER MUST KNOW.  (1) `env` never COMPUTES the two
--     contexts a boundary scope induces: it takes `BoundaryWf Δ Θ Δᵢ Δᶜ`
--     (strong-rep-store.Boundary) and the two contexts are its outputs — the
--     retired `interior`/`convCtx` functions are gone.  (2) The three
--     sides can spell the same semantic type differently, so `env`
--     compares them by the REPRESENTATION each denotes, by one and the
--     same relation on both sides: `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` inside and
--     `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` outside (strong-rep-store.Ctx §5; the bind-prefix
--     crossing `SameTyExt` went with the bind block).  A
--     boundary's interior is TERM-CLOSED — `Δᵢ ∣ [] ⊢ M ⦂ Bᵢ` — which is what
--     lets strong-rep-store.TermSubst leave wrappers alone.  (3) Classification
--     in §3 is by the CONVERSION CONSTRUCTOR alone: no source or target type
--     is inspected and no slot arithmetic occurs, so `id` at a variable
--     is inert and `id` at a base type is active.  (4) THE VALUE
--     RESTRICTION: `⊢Λ` requires `Value N`, and there is NO `ξ-Λ` —
--     reduction never goes under a `Λ`.  This is where
--     strong-rep-store departs from strong-rep-var, whose `⊢Λ` accepted
--     any body and whose `ξ-Λ` reduced under the binder (the reason
--     `V-Λ` carries `Value N` there; notes/DECISIONS.md, repair 3).
--
-- A boundary is  M ⟪ Θ , c ⟫  with ONE frame change:
--
--   Θ : Boundary   a sequential list of ordinary-variable binders and
--                  anti-binders — `Boundary = List Change`, nothing else
--                  since the representation binders moved to the ambient
--                  store. `BoundaryWf Δ Θ Δᵢ Δᶜ` produces the interior
--                  context Δᵢ and conversion context Δᶜ.
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

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; TyVar; Renameᵗ; renameᵗ; extᵗ;
         ⇑ᵗ; _[_]ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary

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
-- 2.  Classification — ACTIVE / INERT, by the CONVERSION constructor
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
-- 3.  Values
------------------------------------------------------------------------

-- V-Λ carries `Value N`.  In strong-rep-var it was FORCED: reduction
-- went under Λ (ξ-Λ), so without the premise `Λ N` was a value for
-- every N and both "values don't step" and determinism failed
-- (notes/DECISIONS.md, repair 3).  strong-rep-store has no ξ-Λ and its
-- ⊢Λ rule (§4) demands `Value N` OUTRIGHT, so on well-typed terms the
-- premise is automatic; it is kept so that `Value` stays the
-- strong-rep-var relation verbatim and so that `TyBeta`'s premise keeps
-- meaning the same thing on untyped terms.
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

  -- THE VALUE RESTRICTION (strong-rep-store's first experiment).  A type
  -- abstraction's body must ALREADY be a value: there is no ξ-Λ rule in
  -- strong-rep-store.Reduction, so a `Λ` over a redex would be stuck.
  -- With the premise, `Λ N` is a value the moment it is well typed
  -- (V-Λ, §3), and `TyBeta`'s own `Value N` premise is discharged by the
  -- typing derivation.
  ⊢Λ : ∀ {Δ Γ C N} → Value N → underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C
    → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C

  ⊢·[] : ∀ {Δ Γ A B L} → Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A
       → Δ ∣ Γ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

  -- (env). The boundary scope witness supplies both contexts. Since ordinary
  -- variables may be inserted and removed, the same semantic type can have
  -- different ordinary de Bruijn spellings on the three sides. `_⊢_≈_⊣_`
  -- compares them by the representation each denotes.  (Since experiment
  -- 2 a boundary carries no bind block, so the exterior and the conversion
  -- context share one store and the exterior comparison is the same
  -- relation — `SameTyExt` is gone.)
  env : ∀ {Δ Δᵢ Δᶜ Γ Θ c M Bᵢ Cᵢ Cₑ Bₑ}
      → BoundaryWf Δ Θ Δᵢ Δᶜ
      → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
      → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
      → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
      → Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ
      → Δ ⊢ᵗ Bₑ
        --------------------------------------------
      → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

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

-- typed at the context TyBeta LEAVES: the cell for ℕ has been allocated
β-seven-⊢ : allocate `ℕ empty ∣ [] ⊢ β-seven ⦂ `ℕ
β-seven-⊢ =
  env TyBeta-bw ⊢$ (conv-id base-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      wf-ℕ
