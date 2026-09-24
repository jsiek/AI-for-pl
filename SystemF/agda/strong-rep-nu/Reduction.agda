module strong-rep-nu.Reduction where

-- File Charter:
--   * §1 `_⊢_-→_∣_`, the fourteen rules — Nu-Λ, Beta, Peel,
--     Nu-⟪Λ⟫, Nu-⟪⟫, CancelR, Drop$, Drop-true, Drop-false,
--     IdPush and the congruences ξ-·-l, ξ-·-r, ξ-ν, ξ-⟪⟫ (NO ξ-Λ) —
--     with `Nu-ℕ`, the multi-step `_⊢_-→*_` and `runCtx`.
--     §2 `value-¬step`.  (The proof of determinism, `det`, is
--     strong-rep-nu.proof.Determinism; its statement is TypeSafety.)
--   * THE STORE CHANGE.  A step returns the change `δ : Alloc` it made
--     to the store, so the contractum lives at `apply δ Δ` and each
--     congruence shifts the redex's siblings by `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]`.
--   * THE CROSSING-SPELLING LAW.  When a rule MOVES a subterm between
--     two name maps, the moved spelling is CARRIED as a named premise
--     and PINNED by `SameConv` or `_⊢_≈_⊣_`, never computed by a fixed
--     renaming.  Five spellings are carried today.
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
  -- Commentary.md § Reduction.agda / Peel
  Peel : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Value V → Value W
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
    → SameConv Δᵈ s′ Δᶜ s
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        -→ (V · (W ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫ ∣ none

  -- `ν` OVER A BOUNDARY — the ∀-conversion analogue of Peel, SPLIT IN
  -- TWO on the crossed boundary's interior.  Both STACK rather than
  -- fuse: the outer layer is `ν`'s own `⟪ inst [] , c ⟫`, the middle
  -- layer is the crossed frame read under the new name (`liftᴮ Θ`)
  -- with the crossed conversion `s` moved VERBATIM.  No rule computes
  -- a conversion from `c`.  Together they are total over canonical
  -- `∀`-values.
  -- Commentary.md § Reduction.agda / Nu-⟪Λ⟫, Nu-⟪⟫
  --
  -- the interior is `Λ N`: instantiate on the spot.
  Nu-⟪Λ⟫ : ∀ {Δ Δᶜ N Θ s c A R Bᵢ Bₑ} → Value N
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ν A · ((Λ N) ⟪ Θ , `∀ s ⟫) ⟨ c ⟩
        -→ (N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫ ∣ new R

  -- the interior is a boundary: push a `ν` at the new name inward one
  -- layer, masking that name in the MOVED boundary's own change list
  -- (the snoc `++ (unbind 0 0 ∷ [])`).  The pushed `ν` allocates an
  -- ALIAS cell when it fires, and ITS conversion is the reveal of the
  -- inner body `Bᵢ′`, minted here: the one run-time reveal left.
  -- `s″` and `Bᵢ′` are the two carried re-spellings.
  -- Commentary.md § Reduction.agda / Nu-⟪⟫
  Nu-⟪⟫ : ∀ {Δ Δᵢ Δᵢ⁺ Δᶜ Δ′ᶜ Δ″ᶜ W Θ′ s′ s″ Θ s c A R Bᵢ Bᵢ′ Bₑ}
    → Value W
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
    → allocate R Δ ⊢ⁱ inst Θ ⇒ Δᵢ⁺
    → Δᵢ⁺ ⊢ᶜ (renᴮᴿ suc Θ′ ++ (unbind 0 0 ∷ [])) ⇒ Δ″ᶜ
    → SameConv (underΛ Δ″ᶜ) s″ (underΛ (renNameCtx suc Δ″ᶜ Δ′ᶜ)) s′
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ν A · ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ⟨ c ⟩
        -→ ((ν (` 0)
               · (renᴹᴿ suc W ⟪ (renᴮᴿ suc Θ′ ++ (unbind 0 0 ∷ [])) , `∀ s″ ⟫)
               ⟨ reveal 0 (renameᵗ (extᵗ suc) Bᵢ′) ⟩)
              ⟪ liftᴮ Θ , s ⟫)
             ⟪ inst [] , c ⟫ ∣ new R

  -- CANCEL — a conceal directly under the binder it names.  Both
  -- frames are kept, MERGED as `Θ₁ ++ Θ₂`, and the matched pair is
  -- neutralised to ONE identity; `A′` is the carried re-spelling.
  -- Commentary.md § Reduction.agda / CancelR
  CancelR : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ V Θ₁ Θ₂ X Y A′ Aᵢ}
    → Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ₁ᶜ ∋ X := Aᵢ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
    → Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ V ⟪ Θ₁ ++ Θ₂ , mkId A′ ⟫ ∣ none

  -- an identity boundary at a base type, over a literal
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n ∣ none

  Drop-true : ∀ {Δ Θ}
    → Δ ⊢ `true ⟪ Θ , id `𝔹 ⟫ -→ `true ∣ none

  Drop-false : ∀ {Δ Θ}
    → Δ ⊢ `false ⟪ Θ , id `𝔹 ⟫ -→ `false ∣ none

  -- IDPUSH — the transparent-layer rule: the reveal moves onto the
  -- MERGED frame `Θ₁ ++ Θ₂` and the transparent layer is CONSUMED.
  -- `X′` is the carried re-spelling.
  -- Commentary.md § Reduction.agda / IdPush
  IdPush : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ V Θ₁ Θ₂ X X′ Y} → Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
    → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ V ⟪ Θ₁ ++ Θ₂ , unseal X′ ⟫ ∣ none

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
Nu-ℕ : empty ⊢ ν `ℕ · (Λ ($ 7)) ⟨ id `ℕ ⟩
  -→ ($ 7) ⟪ TyBetaBoundary , id `ℕ ⟫ ∣ new `ℕ
Nu-ℕ = Nu-Λ V-$ same-ℕ

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

-- the `V-Λ` case is absurd outright: there is no ξ-Λ
value-¬step : ∀ {Δ M M′ δ} → Value M → Δ ⊢ M -→ M′ ∣ δ → ⊥
value-¬step (V-⟪⟫ v I-idv) (Drop$ ())
value-¬step (V-⟪⟫ v ic)    (ξ-⟪⟫ rel st) = value-¬step v st
value-¬step (V-Λ v)        ()
