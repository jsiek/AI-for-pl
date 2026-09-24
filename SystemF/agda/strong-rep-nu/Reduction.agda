module strong-rep-nu.Reduction where

-- File Charter:
--   * §1 `_⊢_-→_∣_`, the twelve rules — Nu-Λ, Beta, Peel, Nu-⟪Λ⟫,
--     Merge, Drop$, Drop-true, Drop-false and the congruences
--     ξ-·-l, ξ-·-r, ξ-ν, ξ-⟪⟫ (NO ξ-Λ) —
--     with `Nu-ℕ`, the multi-step `_⊢_-→*_` and `runCtx`.
--     §2 `value-¬step`.  (The proof of determinism, `det`, is
--     strong-rep-nu.proof.Determinism; its statement is TypeSafety.)
--   * THE STORE CHANGE.  A step returns the change `δ : Alloc` it made
--     to the store, so the contractum lives at `apply δ Δ` and each
--     congruence shifts the redex's siblings by `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]`.
--   * THE CROSSING-SPELLING LAW.  When a rule MOVES a subterm between
--     two name maps, the moved spelling is CARRIED as a named premise
--     and PINNED by `SameConv` or `_⊢_≈_⊣_`, never computed by a fixed
--     renaming.  Three spellings are carried: Peel's `s′`, Merge's
--     `t₁′` and `c₂′`.
-- Commentary: Commentary.md § Reduction.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ;
         _[_]ᵗ)
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
  -- Commentary.md § Reduction.agda / Nu-Λ
  Nu-Λ : ∀ {Δ A R N c} → Value N
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ν A · (Λ N) ⟨ c ⟩ -→ N ⟪ inst [] , c ⟫ ∣ new R

  -- beta, FRAME-EXACT: the substitution carries the ƛ's annotation A
  -- Commentary.md § Reduction.agda / Beta
  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ ∣ none

  -- THE CROSSING: the application is pushed in one layer and the
  -- argument acquires the DUAL, whose spelling `s′` the rule carries.
  -- The crossed value carries ONE boundary, so its interior is SIMPLE.
  -- Commentary.md § Reduction.agda / Peel
  Peel : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Simple V → Value W
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
    → SameConv Δᵈ s′ Δᶜ s
    → Δ ⊢ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · W
        -→ (V · (W ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫ ∣ none

  -- `ν` OVER A BOUNDARY — the ∀-conversion analogue of Peel.  Under
  -- the one-boundary invariant the interior of a `∀`-value's boundary
  -- is a `Λ`, so this ONE clause and `Nu-Λ` are total over canonical
  -- `∀`-values.  The contractum STACKS: the outer layer is `ν`'s own
  -- `⟪ inst [] , c ⟫`, the middle layer the crossed frame read under
  -- the new name (`liftᴮ Θ`) with the crossed conversion `s` moved
  -- VERBATIM; `Merge` fuses them on the next step.
  -- Commentary.md § Reduction.agda / Nu-⟪Λ⟫
  Nu-⟪Λ⟫ : ∀ {Δ Δᶜ N Θ s c A R Bᵢ Bₑ} → Value N
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ν A · ((Λ N) ⟪ Θ , ⌞ `∀ s ⌟ ⟫) ⟨ c ⟩
        -→ (N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫ ∣ new R

  -- MERGE — a boundary directly over a value's boundary.  Both frames
  -- are kept, MERGED as `Θ₁ ++ Θ₂`; both conversions are weakened at
  -- the merged frame's conversion context `Δ⋉ᶜ` (the carried `t₁′`,
  -- `c₂′`) and COMPOSED there.  Subsumes the retired `CancelR`
  -- (`seal X` then `unseal X`) and `IdPush` (`id X` then `unseal X`).
  -- Commentary.md § Reduction.agda / Merge
  Merge : ∀ {Δ Δᵢ Δ₁ᶜ Δ₂ᶜ Δ⋉ᶜ U Θ₁ Θ₂ t₁ t₁′ c₂ c₂′}
    → Simple U → InertTail t₁
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
    → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
    → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
    → Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫
        -→ U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫ ∣ none

  -- an identity boundary at a base type, over a literal
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , ⌞ id A ⌟ ⟫ -→ $ n ∣ none

  Drop-true : ∀ {Δ Θ}
    → Δ ⊢ `true ⟪ Θ , ⌞ id `𝔹 ⌟ ⟫ -→ `true ∣ none

  Drop-false : ∀ {Δ Θ}
    → Δ ⊢ `false ⟪ Θ , ⌞ id `𝔹 ⌟ ⟫ -→ `false ∣ none

  -- THE CONGRUENCES pass the store change up and shift the SIBLINGS
  -- by it.  Commentary.md § Reduction.agda / The congruences
  ξ-·-l : ∀ {Δ L L′ M δ} → Δ ⊢ L -→ L′ ∣ δ
    → Δ ⊢ L · M -→ L′ · ↑ᴹ[ δ ] M ∣ δ
  ξ-·-r : ∀ {Δ V M M′ δ} → Value V → Δ ⊢ M -→ M′ ∣ δ
    → Δ ⊢ V · M -→ ↑ᴹ[ δ ] V · M′ ∣ δ
  ξ-ν : ∀ {Δ L L′ A c δ} → Δ ⊢ L -→ L′ ∣ δ
    → Δ ⊢ ν A · L ⟨ c ⟩ -→ ν A · L′ ⟨ c ⟩ ∣ δ
  -- (NO ξ-Λ: nothing reduces under a type binder — see `⊢Λ`.)
  ξ-⟪⟫  : ∀ {Δ Δᵢ M M′ Θ c δ} → Δ ⊢ⁱ Θ ⇒ Δᵢ
        → Δᵢ ⊢ M -→ M′ ∣ δ
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ ∣ δ

-- Concrete instantiation check: the ordinary argument `ℕ` translates to
-- representation payload `ℕ`, and `inst []` is TyBetaBoundary.
Nu-ℕ : empty ⊢ ν `ℕ · (Λ ($ 7)) ⟨ ⌞ id `ℕ ⌟ ⟩
  -→ ($ 7) ⟪ TyBetaBoundary , ⌞ id `ℕ ⌟ ⟫ ∣ new `ℕ
Nu-ℕ = Nu-Λ (V-simple S-$) same-ℕ

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
value-¬step (V-⟪⟫ u I-idv) (Drop$ ())
value-¬step (V-⟪⟫ () it) (Merge u it′ ri r₁ r₂ r⋉ sc₁ sc₂)
value-¬step (V-⟪⟫ u it) (ξ-⟪⟫ rel st) = value-¬step (V-simple u) st
