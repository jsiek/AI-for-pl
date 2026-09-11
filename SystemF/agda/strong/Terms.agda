module strong.Terms where

-- Strong System F — v3 TERMS, TYPING, and the STRATIFIED VALUES.
--
-- v3 (notes/notes-v3.md) has TWO runtime forms where v2 had one combined
-- boundary `M ⟪ Θ , c ⟫`:
--
--   ν b [ M ]  a SCOPE BOUNDARY  ᵇ[M]  — M under a boundary tag b
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

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool)
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

-- Primitive binary operators ⊕ ::= + | × (notes §"Source Terms").
data Prim : Set where
  p+ : Prim
  p× : Prim

-- THE COLOUR ANNOTATION ⟪ χ ⟫.  Every SOURCE form (notes-v3 §"Source
-- Terms") carries the set of type variables in scope at that node; the
-- literals `$ n` / `# v` do not (they mention no type variable), and
-- neither do the two RUNTIME forms `ν b [ M ]` / `M ⟨ c ⟩`.  The typing
-- rules below demand `χ ≡ scopeᵗ Δ` at every annotated node, and reduction
-- only ever TRANSPORTS an annotation (`renᴹ` maps it, strong.TermSubst) —
-- never recomputes it.  Preservation then forces the colour set at each
-- source node to be the one it was born with.
infix  9 `_⟪_⟫
infix  9 $_
infix  9 #_
infixl 8 _•_[_]⟪_⟫
infixl 7 _·_⟪_⟫
infixl 6 _⊕[_]_⟪_⟫
infix  6 ƛ_∙_⟪_⟫
infix  6 Λ_⟪_⟫
infix  5 ν_[_]
infix  5 _⟨_⟩

data Term : Set where
  `_⟪_⟫     : ℕ → VarSet → Term           -- x
  $_        : ℕ → Term                    -- k = n  (numeral, type ℕ)
  #_        : Bool → Term                 -- k = b  (boolean, type 𝔹)
  _⊕[_]_⟪_⟫ : Term → Prim → Term → VarSet → Term  -- M ⊕ N
  ƛ_∙_⟪_⟫   : Ty → Term → VarSet → Term   -- λx:A. N
  _·_⟪_⟫    : Term → Term → VarSet → Term -- L · M
  Λ_⟪_⟫     : Term → VarSet → Term        -- ΛX. N
  _•_[_]⟪_⟫ : Term → Ty → Ty → VarSet → Term -- L •B[A]  (writes ]⟪χ⟫)
  ν_[_]     : Bnd → Term → Term           -- ᵇ[M]  scope boundary
  _⟨_⟩      : Term → Conv → Term          -- M⟨c⟩  conversion

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

  -- EVERY SOURCE RULE CARRIES `χ ≡ scopeᵗ Δ`: the annotation lists exactly
  -- the type variables nameable at this node.  This is the whole of the
  -- colour discipline; nothing else in the judgment changes.

  ⊢` : ∀ {Δ Γ x A χ} → Γ ∋ x ⦂ A → χ ≡ scopeᵗ Δ
     → Δ ∣ Γ ⊢ ` x ⟪ χ ⟫ ⦂ A

  ⊢$ : ∀ {Δ Γ n} → Δ ∣ Γ ⊢ $ n ⦂ `ℕ

  ⊢# : ∀ {Δ Γ v} → Δ ∣ Γ ⊢ # v ⦂ `𝔹

  ⊢⊕ : ∀ {Δ Γ M N p χ} → Δ ∣ Γ ⊢ M ⦂ `ℕ → Δ ∣ Γ ⊢ N ⦂ `ℕ → χ ≡ scopeᵗ Δ
     → Δ ∣ Γ ⊢ M ⊕[ p ] N ⟪ χ ⟫ ⦂ `ℕ

  ⊢ƛ : ∀ {Δ Γ A B N χ} → Δ ⊢ᵗ A → Δ ∣ A ∷ Γ ⊢ N ⦂ B → χ ≡ scopeᵗ Δ
     → Δ ∣ Γ ⊢ ƛ A ∙ N ⟪ χ ⟫ ⦂ (A ⇒ B)

  ⊢· : ∀ {Δ Γ A B L M χ} → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B) → Δ ∣ Γ ⊢ M ⦂ A → χ ≡ scopeᵗ Δ
     → Δ ∣ Γ ⊢ L · M ⟪ χ ⟫ ⦂ B

  -- The Λ node's own annotation is the EXTERIOR scope; the body's nodes
  -- carry `scopeᵗ (unmasked abst ∷ Δ) = 0 ∷ map suc (scopeᵗ Δ)` — the new
  -- colour, plus the old ones shifted.
  ⊢Λ : ∀ {Δ Γ C N χ} → (unmasked abst ∷ Δ) ∣ ⤊ Γ ⊢ N ⦂ C → χ ≡ scopeᵗ Δ
     → Δ ∣ Γ ⊢ Λ N ⟪ χ ⟫ ⦂ `∀ C

  ⊢•[] : ∀ {Δ Γ A B L χ} → Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A → χ ≡ scopeᵗ Δ
       → Δ ∣ Γ ⊢ L • B [ A ]⟪ χ ⟫ ⦂ B [ A ]ᵗ

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
      → Δ ∣ Γ ⊢ ν intro A [ M ] ⦂ B

  -- REVEAL  ⁺χ[M].  χ is unlocked for the interior; χ ∩ FV(B) = ∅.
  -- The premise `Δ ∋lks χ` says the tag tells the truth: every slot it
  -- unlocks WAS locked.  Without it the dual crossing of AppBnd re-locks
  -- the argument's own variables and Preservation fails (CtxMorph §2b).
  ⊢reveal : ∀ {Δ Γ M χ B}
      → χ ∉FVs B → Δ ⊢ᵗ B → Δ ∋lks χ
      → unlockχ χ Δ ∣ [] ⊢ M ⦂ B
        ------------------------------
      → Δ ∣ Γ ⊢ ν reveal χ [ M ] ⦂ B

  -- CONCEAL  ⁻χ[M].  χ is locked for the interior; χ ∩ FV(B) = ∅.
  -- Dually to ⊢reveal, `Δ ∋tvs χ` says every slot the tag locks WAS
  -- nameable (CtxMorph §2b).
  ⊢conceal : ∀ {Δ Γ M χ B}
      → χ ∉FVs B → Δ ⊢ᵗ B → Δ ∋tvs χ
      → lockχ χ Δ ∣ [] ⊢ M ⦂ B
        ------------------------------
      → Δ ∣ Γ ⊢ ν conceal χ [ M ] ⦂ B

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

-- The constants k ::= n | b.
data Const : Term → Set where
  const-$ : ∀ {n} → Const ($ n)
  const-# : ∀ {v} → Const (# v)

-- Vˢ ::= λx:A.N | ΛX.N
-- V⁻ ::= Vˢ | ⁻χ[Vˢ]                       (χ ≠ ∅)
-- Vᶜ ::= V⁻ | Vᶜ⟨c→d⟩ | Vᶜ⟨∀X.c⟩ | Vᶜ⟨-X⟩
-- V⁺ ::= Vᶜ | [V⁺]⁺ˣ⁼ᴬ | [V⁺]⁺χ            (χ ≠ ∅)
-- V  ::= k | V⁺                            (k = numeral or boolean)
--
-- DEVIATION FROM THE NOTES, DELIBERATE.  `SΛ` carries `Value N` — reduction
-- goes UNDER Λ (ξ-Λ, strong.Reduction), so without it `Λ N` would be a
-- value for every N and both "values don't step" and determinism would be
-- false (the same defect v2 fixed; notes v2's V-Λ).
mutual
  data Simple : Term → Set where          -- Vˢ
    Sƛ : ∀ {A N χ} → Simple (ƛ A ∙ N ⟪ χ ⟫)
    SΛ : ∀ {N χ}   → Value N → Simple (Λ N ⟪ χ ⟫)

  data Neg : Term → Set where             -- V⁻
    Ns : ∀ {M}   → Simple M → Neg M
    Nc : ∀ {χ M} → NonEmpty χ → Simple M → Neg (ν conceal χ [ M ])

  data Cnv : Term → Set where             -- Vᶜ
    Cn    : ∀ {M}     → Neg M → Cnv M
    Cfun  : ∀ {M s t} → Cnv M → Cnv (M ⟨ s ↦ t ⟩)
    Call  : ∀ {M s}   → Cnv M → Cnv (M ⟨ `∀ s ⟩)
    Cseal : ∀ {M X}   → Cnv M → Cnv (M ⟨ seal X ⟩)

  data Pos : Term → Set where             -- V⁺
    Pc      : ∀ {M}   → Cnv M → Pos M
    Pintro  : ∀ {M A} → Pos M → Pos (ν intro A [ M ])
    Preveal : ∀ {χ M} → NonEmpty χ → Pos M → Pos (ν reveal χ [ M ])

  data Value : Term → Set where           -- V
    Vk : ∀ {k} → Const k → Value k
    Vp : ∀ {M} → Pos M → Value M

-- Convenience injections up the tower.
simple→value : ∀ {M} → Simple M → Value M
simple→value s = Vp (Pc (Cn (Ns s)))

neg→value : ∀ {M} → Neg M → Value M
neg→value n = Vp (Pc (Cn n))

cnv→value : ∀ {M} → Cnv M → Value M
cnv→value c = Vp (Pc c)
