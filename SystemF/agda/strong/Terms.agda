module strong.Terms where

-- Strong System F — the TERMS, the typing judgement, and values.
--
-- A boundary is  M ⟪ Θ , c ⟫  with ONE frame change:
--
--   Θ : CtxMorph   a parallel block of representation-variable binders and
--                  a sequential list of ordinary-variable binders and
--                  anti-binders. `MorphWf Δ Θ Δᵢ Δᶜ` produces the
--                  interior context Δᵢ and conversion context Δᶜ.
--
--   c : Conv       the conversion checked on Δᶜ. Its source is related to
--                  the interior term's type through `SameTy`; its target is
--                  related to the exterior type the same way.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ;
         ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph

private
  variable
    Δ Δ′ : Ctxᵗ
    A B : Ty
    X Y : ℕ

------------------------------------------------------------------------
-- 1.  Terms
------------------------------------------------------------------------

infix  9 `_
infix  9 $_
infixl 7 _·_
infix  6 ƛ_∙_
infix  5 _⟪_,_⟫

data Term : Set where
  `_      : ℕ → Term
  $_      : ℕ → Term
  `true   : Term
  `false  : Term
  ƛ_∙_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _·[_,_] : Term → Ty → Ty → Term
  _⟪_,_⟫  : Term → CtxMorph → Conv → Term

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → ℕ → Ty → Set where
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

  -- (env). The morphism witness supplies both contexts. Since ordinary
  -- variables may be inserted and removed, the same semantic type can have
  -- different ordinary de Bruijn spellings on the three sides. `SameTy`
  -- compares the equal-depth interior and conversion contexts. `SameTyExt`
  -- additionally crosses the morphism's representation bind prefix when
  -- comparing the exterior and conversion contexts.
  env : ∀ {Δ Δᵢ Δᶜ Γ Θ c M Bᵢ Cᵢ Cₑ Bₑ}
      → MorphWf Δ Θ Δᵢ Δᶜ
      → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
      → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
      → SameTy Δᵢ Bᵢ Δᶜ Cᵢ
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

-- V-Λ carries `Value N`.  Reduction goes UNDER Λ (ξ-Λ in strong.Reduction),
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
β-seven = ($ 7) ⟪ TyBetaMorph , id `ℕ ⟫

β-seven-⊢ : empty ∣ [] ⊢ β-seven ⦂ `ℕ
β-seven-⊢ =
  env TyBeta-mw ⊢$ (conv-id base-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      wf-ℕ
