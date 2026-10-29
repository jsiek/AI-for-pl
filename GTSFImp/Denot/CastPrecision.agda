module Denot.CastPrecision where

-- File Charter:
--   * Term precision for the cast calculus, the relation on which the
--     denotational fundamental lemma is proved
--     (notes/denotational-dgg.md, Section 7a).
--   * Two contexts: left terms in Δ, right terms in Δ′, related by a
--     variable correspondence `Φ` (`Denot.Precision`).  A left-only `Λ`
--     relates its body to the right term itself, unshifted.
--   * It covers the terms that elaboration produces: no conversions, no
--     `blame`, no runtime seals.  Those occur only after reduction, and
--     the denotational proof never relates such terms.
--   * Casts are related by a two-sided rule and a one-sided right rule.
--     Neither relates the casts to each other: the premises are only
--     that the casts are in eager normal form (`Denot.EagerCast`) and sit
--     at related types.  The cast monotonicity lemma makes them sound.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Fin using (zero)

open import Types
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms
open import Primitives
  using (Const; Prim; addℕ; and𝔹; κℕ; κ𝔹; constTy; primArgTy;
         primResultTy)
open import Denot.Precision
open import Denot.EagerCast

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

record PrecEntry {Δ Δ′} (Φ : Corr Δ Δ′) : Set where
  constructor ⟪_,_,_⟫
  field
    leftTy  : Ty Δ
    rightTy : Ty Δ′
    precTy  : Φ ⊢ leftTy ⊑ rightTy

open PrecEntry public

PrecCtx : ∀ {Δ Δ′} → Corr Δ Δ′ → Set
PrecCtx Φ = List (PrecEntry Φ)

infix 4 _∋ᵖ_⦂_

data _∋ᵖ_⦂_ {Δ Δ′} {Φ : Corr Δ Δ′} :
    PrecCtx Φ → ℕ → PrecEntry Φ → Set where
  Zᵖ : ∀ {γ e} → (e ∷ γ) ∋ᵖ zeroℕ ⦂ e
  Sᵖ : ∀ {γ e e′ x} → γ ∋ᵖ x ⦂ e → (e′ ∷ γ) ∋ᵖ sucℕ x ⦂ e

-- the context under a `Λ` on both sides: both types shift
data LiftPair {Δ Δ′} {Φ : Corr Δ Δ′} :
    PrecCtx Φ → PrecCtx (pair Φ) → Set where
  lp-[] : LiftPair [] []
  lp-∷ : ∀ {γ γ′ A B p p′}
    → LiftPair γ γ′
    → LiftPair (⟪ A , B , p ⟫ ∷ γ) (⟪ ⇑ᵗ A , ⇑ᵗ B , p′ ⟫ ∷ γ′)

-- the context under a left-only `Λ`: only the left type shifts
data LiftOnly {Δ Δ′} {Φ : Corr Δ Δ′} :
    PrecCtx Φ → PrecCtx (only Φ) → Set where
  lo-[] : LiftOnly [] []
  lo-∷ : ∀ {γ γ′ A B p p′}
    → LiftOnly γ γ′
    → LiftOnly (⟪ A , B , p ⟫ ∷ γ) (⟪ ⇑ᵗ A , B , p′ ⟫ ∷ γ′)

------------------------------------------------------------------------
-- Base types
------------------------------------------------------------------------

constTy-⊑ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} (κ : Const)
  → Φ ⊢ constTy κ ⊑ constTy κ
constTy-⊑ (κℕ n) = ι⊑ι
constTy-⊑ (κ𝔹 b) = ι⊑ι

primArgTy-⊑ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} (op : Prim)
  → Φ ⊢ primArgTy op ⊑ primArgTy op
primArgTy-⊑ addℕ = ι⊑ι
primArgTy-⊑ and𝔹 = ι⊑ι

primResultTy-⊑ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} (op : Prim)
  → Φ ⊢ primResultTy op ⊑ primResultTy op
primResultTy-⊑ addℕ = ι⊑ι
primResultTy-⊑ and𝔹 = ι⊑ι

------------------------------------------------------------------------
-- Term precision
------------------------------------------------------------------------

infix 4 _∣_⊢_⊑_⦂_⊑_∶_

data _∣_⊢_⊑_⦂_⊑_∶_ {Δ Δ′} (Φ : Corr Δ Δ′) (γ : PrecCtx Φ) :
    Term Δ → Term Δ′ → (A : Ty Δ) (B : Ty Δ′) → Φ ⊢ A ⊑ B → Set where

  x⊑x : ∀ {x A B p}
    → γ ∋ᵖ x ⦂ ⟪ A , B , p ⟫
      ------------------------------------
    → Φ ∣ γ ⊢ ` x ⊑ ` x ⦂ A ⊑ B ∶ p

  ƛ⊑ƛ : ∀ {N N′ A A′ B B′ pA pB}
    → Φ ∣ ⟪ A , A′ , pA ⟫ ∷ γ ⊢ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
      ------------------------------------------------------
    → Φ ∣ γ ⊢ ƛ N ⊑ ƛ N′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {L L′ M M′ A A′ B B′ pA pB}
    → Φ ∣ γ ⊢ L ⊑ L′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ ⇒⊑⇒ pA pB
    → Φ ∣ γ ⊢ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA
      ------------------------------------------
    → Φ ∣ γ ⊢ L · M ⊑ L′ · M′ ⦂ B ⊑ B′ ∶ pB

  Λ⊑Λ : ∀ {γ′ V V′ A B p}
    → LiftPair γ γ′
    → Value V
    → Value V′
    → pair Φ ∣ γ′ ⊢ V ⊑ V′ ⦂ A ⊑ B ∶ p
      --------------------------------------------------
    → Φ ∣ γ ⊢ Λ V ⊑ Λ V′ ⦂ `∀ A ⊑ `∀ B ∶ ∀⊑∀ p

  Λ⊑ : ∀ {γ′ V N′ A B p}
    → (Anv : NonVar A)
    → (z∈A : zero ∈ᵗ A)
    → LiftOnly γ γ′
    → Value V
    → only Φ ∣ γ′ ⊢ V ⊑ N′ ⦂ A ⊑ B ∶ p
      --------------------------------------------------
    → Φ ∣ γ ⊢ Λ V ⊑ N′ ⦂ `∀ A ⊑ B ∶ ∀⊑ Anv z∈A p

  •⊑• : ∀ {M M′ T T′ A B p}
    → Φ ∣ γ ⊢ M ⊑ M′ ⦂ `∀ A ⊑ `∀ B ∶ ∀⊑∀ p
    → Φ ⊢ T ⊑ T′
    → (r : Φ ⊢ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ)
      ------------------------------------------------------------
    → Φ ∣ γ ⊢ M ⦂∀ A [ T ] ⊑ M′ ⦂∀ B [ T′ ] ⦂ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ ∶ r

  •⊑ : ∀ {M M′ T A B p Anv z∈A}
    → Φ ∣ γ ⊢ M ⊑ M′ ⦂ `∀ A ⊑ B ∶ ∀⊑ Anv z∈A p
    → Φ ⊢ T ⊑ ★
    → (r : Φ ⊢ A [ T ]ᵗ ⊑ B)
      ----------------------------------------------
    → Φ ∣ γ ⊢ M ⦂∀ A [ T ] ⊑ M′ ⦂ A [ T ]ᵗ ⊑ B ∶ r

  κ⊑κ : ∀ (κ : Const)
      ------------------------------------------------------
    → Φ ∣ γ ⊢ $ κ ⊑ $ κ ⦂ constTy κ ⊑ constTy κ ∶ constTy-⊑ κ

  ⊕⊑⊕ : ∀ {L L′ M M′}
    → (op : Prim)
    → Φ ∣ γ ⊢ L ⊑ L′ ⦂ primArgTy op ⊑ primArgTy op ∶ primArgTy-⊑ op
    → Φ ∣ γ ⊢ M ⊑ M′ ⦂ primArgTy op ⊑ primArgTy op ∶ primArgTy-⊑ op
      ------------------------------------------------------------------
    → Φ ∣ γ ⊢ L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′
        ⦂ primResultTy op ⊑ primResultTy op ∶ primResultTy-⊑ op

  -- the two-sided cast rule
  ⟨⟩⊑⟨⟩ : ∀ {M M′ C C′ A A′ p} {ν : Env∼ Δ} {ν′ : Env∼ Δ′}
    → Φ ∣ γ ⊢ M ⊑ M′ ⦂ C ⊑ C′ ∶ p
    → (c : ν ⊢ C ∼ A)
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → Eager c
    → Eager c′
    → (r : Φ ⊢ A ⊑ A′)
      ------------------------------------------
    → Φ ∣ γ ⊢ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ A′ ∶ r

  -- the one-sided right cast rule
  ⊑⟨⟩ : ∀ {M M′ A C′ A′ p} {ν′ : Env∼ Δ′}
    → Φ ∣ γ ⊢ M ⊑ M′ ⦂ A ⊑ C′ ∶ p
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → Eager c′
    → (r : Φ ⊢ A ⊑ A′)
      ------------------------------------
    → Φ ∣ γ ⊢ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ A′ ∶ r
