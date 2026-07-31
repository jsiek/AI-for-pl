module TypeNarrow where

-- File Charter:
--   * Defines intrinsically scoped imprecision contexts.
--   * Defines two-context type narrowing without a coercion index.
--   * Excludes type-store, mode-environment, seal, and unseal structure.
--   * Exposes endpoint well-formedness for two-context narrowing.

open import Data.Empty using (⊥)
open import Data.Nat using (_<_; zero; suc; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Coercions using
  ( ModeEnv
  ; id-onlyᵈ
  ; extᵈ
  ; genᵈ
  )

------------------------------------------------------------------------
-- Intrinsically scoped imprecision contexts
------------------------------------------------------------------------

data ImpCtx : TyCtx → TyCtx → Set where
  []ᵢ : ImpCtx zero zero

  bothᵢ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ
    → ImpCtx (suc Δᴸ) (suc Δᴿ)

  freshᴸ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ
    → ImpCtx (suc Δᴸ) Δᴿ

  freshᴿ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ
    → ImpCtx Δᴸ (suc Δᴿ)

infix 4 _⊢_≈ˣ_
infix 4 _⊢★_

data _⊢_≈ˣ_ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ → TyVar → TyVar → Set where

  hereᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      ------------------------------------
    → bothᵢ Φ ⊢ zero ≈ˣ zero

  both-thereᵢ : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈ˣ Y
      ----------------------------------------
    → bothᵢ Φ ⊢ suc X ≈ˣ suc Y

  freshᴸ-thereᵢ : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈ˣ Y
      ----------------------------------------
    → freshᴸ Φ ⊢ suc X ≈ˣ Y

  freshᴿ-thereᵢ : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈ˣ Y
      ----------------------------------------
    → freshᴿ Φ ⊢ X ≈ˣ suc Y

data _⊢★_ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ → Tag → Set where

  here★ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      ----------------------
    → freshᴿ Φ ⊢★ ＇ zero

  both-there★ : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★ ＇ X
      -------------------------
    → bothᵢ Φ ⊢★ ＇ suc X

  freshᴸ-there★ : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★ ＇ X
      -----------------------
    → freshᴸ Φ ⊢★ ＇ X

  freshᴿ-there★ : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★ ＇ X
      -------------------------
    → freshᴿ Φ ⊢★ ＇ suc X

  base★ : ∀ {Δᴸ Δᴿ ι} {Φ : ImpCtx Δᴸ Δᴿ}
      -----------------
    → Φ ⊢★ ‵ ι

  fun★ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      -------------
    → Φ ⊢★ ★⇒★

≈ˣ-left-bound : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ X ≈ˣ Y
  → X < Δᴸ
≈ˣ-left-bound hereᵢ = s≤s z≤n
≈ˣ-left-bound (both-thereᵢ X≈Y) = s≤s (≈ˣ-left-bound X≈Y)
≈ˣ-left-bound (freshᴸ-thereᵢ X≈Y) = s≤s (≈ˣ-left-bound X≈Y)
≈ˣ-left-bound (freshᴿ-thereᵢ X≈Y) = ≈ˣ-left-bound X≈Y

≈ˣ-right-bound : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ X ≈ˣ Y
  → Y < Δᴿ
≈ˣ-right-bound hereᵢ = s≤s z≤n
≈ˣ-right-bound (both-thereᵢ X≈Y) = s≤s (≈ˣ-right-bound X≈Y)
≈ˣ-right-bound (freshᴸ-thereᵢ X≈Y) = ≈ˣ-right-bound X≈Y
≈ˣ-right-bound (freshᴿ-thereᵢ X≈Y) = s≤s (≈ˣ-right-bound X≈Y)

★-right-bound : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢★ ＇ X
  → X < Δᴿ
★-right-bound here★ = s≤s z≤n
★-right-bound (both-there★ X⊑★) = s≤s (★-right-bound X⊑★)
★-right-bound (freshᴸ-there★ X⊑★) = ★-right-bound X⊑★
★-right-bound (freshᴿ-there★ X⊑★) = s≤s (★-right-bound X⊑★)

idᵢ : ∀ Δ → ImpCtx Δ Δ
idᵢ zero = []ᵢ
idᵢ (suc Δ) = bothᵢ (idᵢ Δ)

------------------------------------------------------------------------
-- The coercion mode induced on the right
------------------------------------------------------------------------

precisionMode : ∀ {Δᴸ Δᴿ} → ImpCtx Δᴸ Δᴿ → ModeEnv
precisionMode []ᵢ = id-onlyᵈ
precisionMode (bothᵢ Φ) = extᵈ (precisionMode Φ)
precisionMode (freshᴸ Φ) = precisionMode Φ
precisionMode (freshᴿ Φ) = genᵈ (precisionMode Φ)

------------------------------------------------------------------------
-- Smart extension at a polymorphic boundary
------------------------------------------------------------------------

data SmartExtensionᵢ : ∀ {Δᴸ Δᴿ}
    → (Φ : ImpCtx Δᴸ Δᴿ)
    → ImpCtx Δᴸ (suc Δᴿ)
    → Set where

  freshᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      -------------------------------------
    → SmartExtensionᵢ Φ (freshᴿ Φ)

  reuseᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      -------------------------------------------
    → SmartExtensionᵢ (freshᴸ Φ) (bothᵢ Φ)

instance
  fresh-extensionᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → SmartExtensionᵢ Φ (freshᴿ Φ)
  fresh-extensionᵢ = freshᵢ

------------------------------------------------------------------------
-- Atomic two-context narrowing
------------------------------------------------------------------------

infix 4 _⊢_≈ᵃ_

_⊢_≈ᵃ_ : ∀ {Δᴸ Δᴿ A B}
  → ImpCtx Δᴸ Δᴿ → Atom A → Atom B → Set
Φ ⊢ (＇ X) ≈ᵃ (＇ Y) = Φ ⊢ X ≈ˣ Y
Φ ⊢ (＇ X) ≈ᵃ (‵ ι) = ⊥
Φ ⊢ (＇ X) ≈ᵃ ★ = ⊥
Φ ⊢ (‵ ι) ≈ᵃ (＇ Y) = ⊥
Φ ⊢ (‵ ι) ≈ᵃ (‵ κ) = ι ≡ κ
Φ ⊢ (‵ ι) ≈ᵃ ★ = ⊥
Φ ⊢ ★ ≈ᵃ (＇ Y) = ⊥
Φ ⊢ ★ ≈ᵃ (‵ ι) = ⊥
Φ ⊢ ★ ≈ᵃ ★ = ⊤

------------------------------------------------------------------------
-- Two-context narrowing
------------------------------------------------------------------------

infix 4 _⊢_⊒_
infixr 6 _↦_

data _⊢_⊒_ {Δᴸ Δᴿ} (Φ : ImpCtx Δᴸ Δᴿ) :
    Ty → Ty → Set where

  idᵃ : ∀ {A B} (a : Atom A) (b : Atom B)
    → WfTy Δᴸ A
    → WfTy Δᴿ B
    → Φ ⊢ a ≈ᵃ b
      ----------------
    → Φ ⊢ A ⊒ B

  _↦_ : ∀ {A A′ B B′}
    → Φ ⊢ A ⊒ A′
    → Φ ⊢ B ⊒ B′
      ----------------------------
    → Φ ⊢ (A ⇒ B) ⊒ (A′ ⇒ B′)

  ∀ⁿ_ : ∀ {A B}
    → bothᵢ Φ ⊢ A ⊒ B
      -----------------------
    → Φ ⊢ (`∀ A) ⊒ (`∀ B)

  untag : ∀ {G A}
    → Φ ⊢★ G
    → G ꞉ A
      ---------------
    → Φ ⊢ ★ ⊒ A

  gen : ∀ {A B}
    → NonVar A
    → zero ∈ᵗ A
    → freshᴿ Φ ⊢ B ⊒ A
    → B ≢ ★
      -------------------
    → Φ ⊢ B ⊒ (`∀ A)

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

⊒-src-wf : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ⊒ B
  → WfTy Δᴸ A
⊒-src-wf (idᵃ _ _ hA _ _) = hA
⊒-src-wf (p ↦ q) = wf⇒ (⊒-src-wf p) (⊒-src-wf q)
⊒-src-wf (∀ⁿ p) = wf∀ (⊒-src-wf p)
⊒-src-wf (untag _ _) = wf★
⊒-src-wf (gen _ _ p _) = ⊒-src-wf p

untag-tgt-wf : ∀ {Δᴸ Δᴿ G A} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢★ G
  → G ꞉ A
  → WfTy Δᴿ A
untag-tgt-wf here★ (tag-var zero) = wfVar (s≤s z≤n)
untag-tgt-wf (both-there★ G⊑★) (tag-var (suc X)) =
  wfVar (★-right-bound (both-there★ G⊑★))
untag-tgt-wf (freshᴸ-there★ G⊑★) (tag-var X) =
  wfVar (★-right-bound (freshᴸ-there★ G⊑★))
untag-tgt-wf (freshᴿ-there★ G⊑★) (tag-var (suc X)) =
  wfVar (★-right-bound (freshᴿ-there★ G⊑★))
untag-tgt-wf base★ (tag-base ι) = wfBase
untag-tgt-wf fun★ tag-fun = wf⇒ wf★ wf★

⊒-tgt-wf : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ⊒ B
  → WfTy Δᴿ B
⊒-tgt-wf (idᵃ _ _ _ hB _) = hB
⊒-tgt-wf (p ↦ q) = wf⇒ (⊒-tgt-wf p) (⊒-tgt-wf q)
⊒-tgt-wf (∀ⁿ p) = wf∀ (⊒-tgt-wf p)
⊒-tgt-wf (untag G⊑★ G꞉A) = untag-tgt-wf G⊑★ G꞉A
⊒-tgt-wf (gen _ _ p _) = wf∀ (⊒-tgt-wf p)

⊒-wf : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ⊒ B
  → WfTy Δᴸ A × WfTy Δᴿ B
⊒-wf p = ⊒-src-wf p , ⊒-tgt-wf p
