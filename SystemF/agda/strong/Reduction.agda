module strong.Reduction where

-- Strong System F v8 — store-passing small-step reduction.
--
-- `Σ ∣ Δ ⊢ M —→ N ⊣ Σ′`: only `Alloc` extends the store, and the
-- ξ-rules propagate the extension, so an allocation discharges in one
-- step from any evaluation position — no per-frame hoisting.  There is
-- no ξ-Λ (Λ bodies are values) and no scope or store bookkeeping in any
-- rule: `Merge` is a bare composition, `Wrap` needs no dual scope (the
-- contravariant `arr` component carries the dual crossings), and
-- `TyBeta`/`TyWrap` allocate through `ν` with the crossing inside the
-- built conversion.  The Λ's bound address becomes the ν's binder, so
-- the body `V` is untouched in both.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types using (Ty; `_; `ℕ; `𝔹)
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst

⟦_⟧ᵖ : Prim → ℕ → ℕ → ℕ
⟦ p+ ⟧ᵖ m n = m + n
⟦ p× ⟧ᵖ m n = m * n

infix 2 _∣_⊢_—→_⊣_
data _∣_⊢_—→_⊣_ : Store → Ctxᵗ → Term → Term → Store → Set where

  Beta : ∀ {Σ Δ A N W}
    → Value W
    → Σ ∣ Δ ⊢ (ƛ A ∙ N) · W —→ N [ W ∶ A ]ᵐ ⊣ Σ

  PrimBeta : ∀ {Σ Δ p m n}
    → Σ ∣ Δ ⊢ ($ m) ⊕[ p ] ($ n) —→ $ (⟦ p ⟧ᵖ m n) ⊣ Σ

  -- The Λ's bound address becomes the ν's; the crossing is inside the
  -- built conversion, whose S is A itself (the representation reads
  -- back to A on the concealed exterior).
  TyBeta : ∀ {Σ Δ V B A R}
    → Value V → Σ ∣ Δ ⊢⌊ A ⌋ R
    → Σ ∣ Δ ⊢ (Λ V) • B [ A ]
        —→ ν R ∙ (V ⟨ revTy zero (bse zero) A B ⟩) ⊣ Σ

  -- Immediate discharge: the fresh address is the next store level, and
  -- the snoc disturbs no existing level.
  Alloc : ∀ {Σ Δ R M}
    → Σ ∣ Δ ⊢ ν R ∙ M —→ M [ lvl (length Σ) ]ᵃᴹ ⊣ (Σ ∷ʳ R)

  -- The boundary's body is matched as a λ: its annotation is the
  -- INTERIOR domain, which `arr` needs for its contravariant component.
  Wrap : ∀ {Σ Δ A N c W c₁ c₂}
    → Value ((ƛ A ∙ N) ⟨ c ⟩) → Value W
    → arr A c ≡ just (c₁ , c₂)
    → Σ ∣ Δ ⊢ ((ƛ A ∙ N) ⟨ c ⟩) · W
        —→ ((ƛ A ∙ N) · (W ⟨ c₁ ⟩)) ⟨ c₂ ⟩ ⊣ Σ

  -- `instReveal` reads `d`'s SOURCE off the context, so the rule hands
  -- it the store and the context `d` is typed in: `interior c Δ` is the
  -- conversion's own interior — the same walk `ξ-⟨⟩` uses — and
  -- `allView` puts `d` one `bind` further in (proof.AllTyping).
  TyWrap : ∀ {Σ Δ Δᵢ V c B A d R}
    → Value ((Λ V) ⟨ c ⟩)
    → allView c ≡ just d → Σ ∣ Δ ⊢⌊ A ⌋ R
    → interior c Δ ≡ just Δᵢ
    → Σ ∣ Δ ⊢ ((Λ V) ⟨ c ⟩) • B [ A ]
        —→ ν R ∙ (V ⟨ instReveal Σ (bind ∷ stk Δᵢ ∥ bas Δᵢ)
                        zero (bse zero) A d ⟩) ⊣ Σ

  Merge : ∀ {Σ Δ M c d}
    → Value (M ⟨ c ⟩)
    → Σ ∣ Δ ⊢ (M ⟨ c ⟩) ⟨ d ⟩ —→ M ⟨ c ⨟ d ⟩ ⊣ Σ

  Const : ∀ {Σ Δ k c A}
    → Literal k → base c ≡ just A
    → Σ ∣ Δ ⊢ k ⟨ c ⟩ —→ k ⊣ Σ

  ξ-⊕-l : ∀ {Σ Σ′ Δ L L′ M p}
    → Σ ∣ Δ ⊢ L —→ L′ ⊣ Σ′
    → Σ ∣ Δ ⊢ L ⊕[ p ] M —→ L′ ⊕[ p ] M ⊣ Σ′
  ξ-⊕-r : ∀ {Σ Σ′ Δ V M M′ p}
    → Value V → Σ ∣ Δ ⊢ M —→ M′ ⊣ Σ′
    → Σ ∣ Δ ⊢ V ⊕[ p ] M —→ V ⊕[ p ] M′ ⊣ Σ′
  ξ-·-l : ∀ {Σ Σ′ Δ L L′ M}
    → Σ ∣ Δ ⊢ L —→ L′ ⊣ Σ′
    → Σ ∣ Δ ⊢ L · M —→ L′ · M ⊣ Σ′
  ξ-·-r : ∀ {Σ Σ′ Δ V M M′}
    → Value V → Σ ∣ Δ ⊢ M —→ M′ ⊣ Σ′
    → Σ ∣ Δ ⊢ V · M —→ V · M′ ⊣ Σ′
  ξ-•[] : ∀ {Σ Σ′ Δ L L′ B A}
    → Σ ∣ Δ ⊢ L —→ L′ ⊣ Σ′
    → Σ ∣ Δ ⊢ L • B [ A ] —→ L′ • B [ A ] ⊣ Σ′
  -- No ξ-Λ: Λ bodies are values.  No ξ-ν: an allocation in evaluation
  -- position discharges by `Alloc` before its body runs.
  ξ-⟨⟩ : ∀ {Σ Σ′ Δ Δᵢ M M′ c}
    → interior c Δ ≡ just Δᵢ
    → Σ ∣ Δᵢ ⊢ M —→ M′ ⊣ Σ′
    → Σ ∣ Δ ⊢ M ⟨ c ⟩ —→ M′ ⟨ c ⟩ ⊣ Σ′

infix 2 _∣_⊢_—↠_⊣_
infixr 3 _then_
data _∣_⊢_—↠_⊣_ : Store → Ctxᵗ → Term → Term → Store → Set where
  done   : ∀ {Σ Δ M} → Σ ∣ Δ ⊢ M —↠ M ⊣ Σ
  _then_ : ∀ {Σ Σ₁ Σ₂ Δ L M N}
    → Σ ∣ Δ ⊢ L —→ M ⊣ Σ₁
    → Σ₁ ∣ Δ ⊢ M —↠ N ⊣ Σ₂
    → Σ ∣ Δ ⊢ L —↠ N ⊣ Σ₂
