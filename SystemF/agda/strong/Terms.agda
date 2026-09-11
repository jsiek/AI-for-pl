module strong.Terms where

-- Strong System F — v3 TERMS, TYPING, and the STRATIFIED VALUES.
--
-- v3 (notes/notes-v3.md) has TWO runtime forms where v2 had one combined
-- boundary `M ⟪ Θ , c ⟫`:
--
--   M ⟦ b ⟧   a SCOPE BOUNDARY  ᵇ[M]  — M under a boundary tag b
--             (strong.CtxMorph): intro / reveal / conceal.  A boundary is
--             TERM-CLOSED (its body types at Γ = []).
--   M ⟨ c ⟩   a CONVERSION  M⟨c⟩ — c applied to M (strong.Conversion).
--             NOT term-closed: substitution descends into M.
--
-- The type context Δ (strong.Ctx) is unchanged from v2 and already IS v3's
-- Γ: `unmasked abst`/`unmasked (bind A)`/`masked …` are v3's
-- `X`/`X=A`/`locked …`.  Conversions are unchanged too; v3's `+X`/`-X` are
-- v2's `unseal`/`seal`.
--
-- The one place v3 differs on conversions is the ACTIVE/INERT cut
-- (notes §"Conversions"): `id` is ACTIVE in v3 (at a variable too), so it
-- is never pushed out of a boundary — it is eliminated by `V⟨id⟩ -→ V`.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph

private
  variable
    Δ Δ′ : Ctxᵗ
    A B : Ty
    X Y : ℕ
    χ : VarSet

------------------------------------------------------------------------
-- 1.  Terms
------------------------------------------------------------------------

infix  9 `_
infix  9 $_
infixl 7 _·_
infix  6 ƛ_∙_
infix  5 _⟦_⟧
infix  5 _⟨_⟩

data Term : Set where
  `_      : ℕ → Term              -- x
  $_      : ℕ → Term              -- k (numeral, type ℕ)
  ƛ_∙_    : Ty → Term → Term      -- λx:A. N
  _·_     : Term → Term → Term    -- L · M
  Λ_      : Term → Term           -- ΛX. N
  _·[_,_] : Term → Ty → Ty → Term -- L @B[A]   (B the ∀-body, A the argument)
  _⟦_⟧    : Term → Bnd → Term     -- ᵇ[M]      scope boundary
  _⟨_⟩    : Term → Conv → Term    -- M⟨c⟩      conversion

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

  ⊢ƛ : ∀ {Δ Γ A B N} → Δ ⊢ᵗ A → Δ ∣ A ∷ Γ ⊢ N ⦂ B
     → Δ ∣ Γ ⊢ ƛ A ∙ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Δ Γ A B L M} → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B) → Δ ∣ Γ ⊢ M ⦂ A
     → Δ ∣ Γ ⊢ L · M ⦂ B

  ⊢Λ : ∀ {Δ Γ C N} → (unmasked abst ∷ Δ) ∣ ⤊ Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C

  ⊢·[] : ∀ {Δ Γ A B L} → Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A
       → Δ ∣ Γ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

  -- CONVERSION.  c relates the interior type A to the exterior type B; the
  -- term context Γ is unchanged (M⟨c⟩ is not term-closed).
  ⊢⟨⟩ : ∀ {Δ Γ M c A B}
      → Δ ∣ Γ ⊢ M ⦂ A → Δ ⊢ c ∶ A ⇝ B
        --------------------------------
      → Δ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  -- INTRO  ⁺ˣ⁼ᴬ[M].  A fresh binder X=A is added; the interior sees B
  -- shifted past it (⇑ᵗ B), so names(b) = {0} ∉ FV of the interior type by
  -- construction.  The body is term-closed.
  ⊢intro : ∀ {Δ Γ M A B}
      → Δ ⊢ᵗ A → Δ ⊢ᵗ B
      → (unmasked (bind A) ∷ Δ) ∣ [] ⊢ M ⦂ ⇑ᵗ B
        ---------------------------------------------
      → Δ ∣ Γ ⊢ M ⟦ intro A ⟧ ⦂ B

  -- REVEAL  ⁺χ[M].  χ is unlocked for the interior; χ ∩ FV(B) = ∅.
  ⊢reveal : ∀ {Δ Γ M χ B}
      → χ ∉FVs B → Δ ⊢ᵗ B
      → unlockχ χ Δ ∣ [] ⊢ M ⦂ B
        ------------------------------
      → Δ ∣ Γ ⊢ M ⟦ reveal χ ⟧ ⦂ B

  -- CONCEAL  ⁻χ[M].  χ is locked for the interior; χ ∩ FV(B) = ∅.
  ⊢conceal : ∀ {Δ Γ M χ B}
      → χ ∉FVs B → Δ ⊢ᵗ B
      → lockχ χ Δ ∣ [] ⊢ M ⦂ B
        ------------------------------
      → Δ ∣ Γ ⊢ M ⟦ conceal χ ⟧ ⦂ B

------------------------------------------------------------------------
-- 3.  ACTIVE / INERT conversions  (v3 §"Conversions")
------------------------------------------------------------------------

-- Inert  = { c ↦ d , ∀ c , -X (seal) }   — pushed out of a conceal boundary
-- Active = { id (any payload) , +X (unseal) } — eliminated in place
data Inert : Conv → Set where
  I-seal : ∀ {X}   → Inert (seal X)
  I-fun  : ∀ {s t} → Inert (s ↦ t)
  I-all  : ∀ {s}   → Inert (`∀ s)

data Active : Conv → Set where
  A-id     : ∀ {A} → Active (id A)
  A-unseal : ∀ {X} → Active (unseal X)

act-or-inert : (c : Conv) → Active c ⊎ Inert c
act-or-inert (id A)     = inj₁ A-id
act-or-inert (seal X)   = inj₂ I-seal
act-or-inert (unseal X) = inj₁ A-unseal
act-or-inert (s ↦ t)    = inj₂ I-fun
act-or-inert (`∀ s)     = inj₂ I-all

act-not-inert : ∀ {c} → Active c → Inert c → ⊥
act-not-inert A-id ()
act-not-inert A-unseal ()

------------------------------------------------------------------------
-- 4.  Values  (the stratified grammar of notes §"Values")
------------------------------------------------------------------------

-- Vˢ ::= λx:A.N | ΛX.N
-- V⁻ ::= Vˢ | ⁻χ[Vˢ]                       (χ ≠ ∅)
-- Vᶜ ::= V⁻ | Vᶜ⟨c→d⟩ | Vᶜ⟨∀X.c⟩ | Vᶜ⟨-X⟩
-- V⁺ ::= Vᶜ | [V⁺]⁺ˣ⁼ᴬ | [V⁺]⁺χ            (χ ≠ ∅)
-- V  ::= k | V⁺
--
-- DEVIATION FROM THE NOTES, DELIBERATE.  `SΛ` carries `Value N` — reduction
-- goes UNDER Λ (ξ-Λ, strong.Reduction), so without it `Λ N` would be a
-- value for every N and both "values don't step" and determinism would be
-- false (the same defect v2 fixed; notes v2's V-Λ).
mutual
  data Simple : Term → Set where          -- Vˢ
    Sƛ : ∀ {A N} → Simple (ƛ A ∙ N)
    SΛ : ∀ {N}   → Value N → Simple (Λ N)

  data Neg : Term → Set where             -- V⁻
    Ns : ∀ {M}   → Simple M → Neg M
    Nc : ∀ {χ M} → NonEmpty χ → Simple M → Neg (M ⟦ conceal χ ⟧)

  data Cnv : Term → Set where             -- Vᶜ
    Cn    : ∀ {M}     → Neg M → Cnv M
    Cfun  : ∀ {M s t} → Cnv M → Cnv (M ⟨ s ↦ t ⟩)
    Call  : ∀ {M s}   → Cnv M → Cnv (M ⟨ `∀ s ⟩)
    Cseal : ∀ {M X}   → Cnv M → Cnv (M ⟨ seal X ⟩)

  data Pos : Term → Set where             -- V⁺
    Pc      : ∀ {M}   → Cnv M → Pos M
    Pintro  : ∀ {M A} → Pos M → Pos (M ⟦ intro A ⟧)
    Preveal : ∀ {χ M} → NonEmpty χ → Pos M → Pos (M ⟦ reveal χ ⟧)

  data Value : Term → Set where           -- V
    V$ : ∀ {n} → Value ($ n)
    Vp : ∀ {M} → Pos M → Value M

-- Convenience injections up the tower.
simple→value : ∀ {M} → Simple M → Value M
simple→value s = Vp (Pc (Cn (Ns s)))

neg→value : ∀ {M} → Neg M → Value M
neg→value n = Vp (Pc (Cn n))

cnv→value : ∀ {M} → Cnv M → Value M
cnv→value c = Vp (Pc c)
