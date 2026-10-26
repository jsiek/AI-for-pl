module strong-rep-nu.Reduction where

-- File Charter:
--   * §1 `_⊢_-→_∣_`, the ten rules — TyBeta, Beta, Wrap, TyWrap,
--     Merge, Id and the congruences
--     ξ-·₁, ξ-·₂, ξ-ν, ξ-⟪⟫ (NO ξ-Λ) —
--     with `TyBeta-ℕ`, the multi-step `_⊢_-→*_` and `runCtx`.
--     §2 `value-¬step`.  (The proof of determinism, `det`, is
--     strong-rep-nu.proof.Determinism; its statement is TypeSafety.)
--   * THE STORE CHANGE.  A step returns the change `δ : Alloc` it made
--     to the store, so the contractum lives at `apply δ Δ` and each
--     congruence shifts the redex's siblings by `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]`.
--   * THE CROSSING-SPELLING LAW.  When a rule MOVES a conversion to
--     another boundary's position, it is RESPELLED there by
--     `respellᶜ` (strong-rep-nu.Conversion §2b): each name to the new
--     position's name for the same representation variable, computed
--     PER NAME FROM THE SCOPES ALONE.  Three conversions move: Wrap's
--     `s`, Merge's `t₁` and `c₂`.  So Wrap reads no context, and Merge
--     reads only the merged conversion context, for composition.
-- Commentary: Commentary.md § Reduction.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ; Base; base-ℕ; base-𝔹)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.TermSubst

------------------------------------------------------------------------
-- 1.  The rules
------------------------------------------------------------------------

-- the small-step relation, indexed by the store change it made
-- Commentary.md § Reduction.agda / `_⊢_-→_∣_` — the store change
infix 2 _⊢_-→_∣_
data _⊢_-→_∣_ : Ctxᵗ → Term → Term → Alloc → Set where

  -- a boundary is BORN: `ν` mints THE BINDER of the event, and the
  -- conversion is the one `ν` carries (the compiler wrote it).
  -- Commentary.md § Reduction.agda / TyBeta
  TyBeta : ∀ {Δ A R N c} → Value N
    → Δ ⊢ᶜ A ~ R
      --------------------------------------------------
    → Δ ⊢ ν A · (Λ N) ⟨ c ⟩ -→ N ⟪ inst [] , c ⟫ ∣ new R

  -- beta, FRAME-EXACT: the substitution carries the ƛ's annotation A
  -- Commentary.md § Reduction.agda / Beta
  Beta : ∀ {Δ A N W} → Value W
      ----------------------------------------
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ ∣ none

  -- THE CROSSING: the application is pushed in one layer and the
  -- argument acquires the DUAL.  The crossed `s` moves to the dual's
  -- position, where other scopes overlap, and is RESPELLED there: from
  -- Θ's conversion reading, through Θ's interior, into the dual's.
  -- The crossed value carries ONE boundary, so its interior is SIMPLE.
  -- Commentary.md § Reduction.agda / Wrap
  Wrap : ∀ {Δ V W Θ s t} → Simple V → Value W
      -----------------------------------------------
    → Δ ⊢ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · W
        -→ (V · (W ⟪ dual Θ , respellᶜ Θ Θ (dual Θ) s ⟫)) ⟪ Θ , t ⟫
         ∣ none

  -- `ν` OVER A BOUNDARY — the ∀-conversion analogue of Wrap.  Under
  -- the one-boundary invariant the interior of a `∀`-value's boundary
  -- is a `Λ`, so this ONE clause and `TyBeta` are total over canonical
  -- `∀`-values.  The contractum STACKS: the outer layer is `ν`'s own
  -- `⟪ inst [] , c ⟫`, the middle layer the crossed frame read under
  -- the new name (`liftᴮ Θ`) with the crossed conversion `s` moved
  -- VERBATIM; `Merge` fuses them on the next step.
  -- Commentary.md § Reduction.agda / TyWrap
  TyWrap : ∀ {Δ N Θ s c A R} → Value N
    → Δ ⊢ᶜ A ~ R
      ------------------------------------------------
    → Δ ⊢ ν A · ((Λ N) ⟪ Θ , ⌞ `∀ s ⌟ ⟫) ⟨ c ⟩
        -→ (N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫ ∣ new R

  -- MERGE — a boundary directly over a value's boundary.  Both frames
  -- are kept, MERGED as `Θ₁ ++ Θ₂`; both conversions move to the merged
  -- frame's position, are RESPELLED there (the inner one back through
  -- the dual of Θ₂ to the exterior first), and are COMPOSED, which
  -- reads the merged conversion context.  Subsumes the retired
  -- `CancelR` (`seal X` then `unseal X`) and `IdPush` (`id X` then
  -- `unseal X`).
  -- Commentary.md § Reduction.agda / Merge
  Merge : ∀ {Δ Δ⋉ᶜ U Θ₁ Θ₂ t₁ c₂}
    → Simple U → InertTail t₁
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
      -------------------------------------------------
    → Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫
        -→ U ⟪ Θ₁ ++ Θ₂ ,
               Δ⋉ᶜ ⊢ respellᶜ Θ₁ (dual Θ₂) (Θ₁ ++ Θ₂) (tail t₁)
                   ⨟ respellᶜ Θ₂ [] (Θ₁ ++ Θ₂) c₂ ⟫ ∣ none

  -- an identity boundary at a base type, over a simple value (which
  -- typing makes a literal: a numeral at ℕ, `true`/`false` at 𝔹)
  Id : ∀ {Δ U Θ A} → Simple U → Base A
      ----------------------------------
    → Δ ⊢ U ⟪ Θ , ⌞ id A ⌟ ⟫ -→ U ∣ none

  -- THE CONGRUENCES pass the store change up and shift the SIBLINGS
  -- by it.  Commentary.md § Reduction.agda / The congruences
  ξ-·₁ : ∀ {Δ L L′ M δ} → Δ ⊢ L -→ L′ ∣ δ
      -------------------------------
    → Δ ⊢ L · M -→ L′ · ↑ᴹ[ δ ] M ∣ δ

  ξ-·₂ : ∀ {Δ V M M′ δ} → Value V → Δ ⊢ M -→ M′ ∣ δ
      -------------------------------
    → Δ ⊢ V · M -→ ↑ᴹ[ δ ] V · M′ ∣ δ

  ξ-ν : ∀ {Δ L L′ A c δ} → Δ ⊢ L -→ L′ ∣ δ
      ---------------------------------------
    → Δ ⊢ ν A · L ⟨ c ⟩ -→ ν A · L′ ⟨ c ⟩ ∣ δ

  -- (NO ξ-Λ: nothing reduces under a type binder — see `⊢Λ`.)
  ξ-⟪⟫  : ∀ {Δ Δᵢ M M′ Θ c δ} → Δ ⊢ⁱ Θ ⇒ Δᵢ
        → Δᵢ ⊢ M -→ M′ ∣ δ
          -------------------------------------------
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ ∣ δ

-- Concrete instantiation check: the ordinary argument `ℕ` translates to
-- representation payload `ℕ`, and `inst []` is TyBetaBoundary.
TyBeta-ℕ : empty ⊢ ν `ℕ · (Λ ($ 7)) ⟨ ⌞ id `ℕ ⌟ ⟩
  -→ ($ 7) ⟪ TyBetaBoundary , ⌞ id `ℕ ⌟ ⟫ ∣ new `ℕ
TyBeta-ℕ = TyBeta (V-simple S-$) same-ℕ

-- A run needs no store index: each step's change is applied to the
-- context the tail runs at.
infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N δ} → Δ ⊢ L -→ M ∣ δ → apply δ Δ ⊢ M -→* N
    → Δ ⊢ L -→* N

infixr 2 _then_

-- The context a run ENDS at: every step's change applied in order.
runCtx : ∀ {Δ M N} → Δ ⊢ M -→* N → Ctxᵗ
runCtx {Δ = Δ} done = Δ
runCtx (_then_ {δ = δ} st sts) = runCtx sts

------------------------------------------------------------------------
-- 2.  VALUES DON'T STEP
------------------------------------------------------------------------

-- the `S-Λ` case is absurd outright: there is no ξ-Λ; a `Merge` needs
-- a boundary over a boundary, which is not a value
value-¬step : ∀ {Δ M M′ δ} → Value M → Δ ⊢ M -→ M′ ∣ δ → ⊥
value-¬step (V-simple S-$) ()
value-¬step (V-simple S-true) ()
value-¬step (V-simple S-false) ()
value-¬step (V-simple S-ƛ) ()
value-¬step (V-simple (S-Λ v)) ()
value-¬step (V-⟪⟫ u I-idv) (Id u′ ())
value-¬step (V-⟪⟫ () it) (Merge u it′ r⋉)
value-¬step (V-⟪⟫ u it) (ξ-⟪⟫ rel st) = value-¬step (V-simple u) st
