module strong.Reduction where

-- Strong System F v7 — small-step reduction for combined boundaries.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types using (Ty; `_; `ℕ; `𝔹)
open import strong.RepresentationTypes using (RepTy; shiftByᴿ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst

⟦_⟧ᵖ : Prim → ℕ → ℕ → ℕ
⟦ p+ ⟧ᵖ m n = m + n
⟦ p× ⟧ᵖ m n = m * n

infix 2 _⊢_-→_
data _⊢_-→_ : Ctxᵗ → Term → Term → Set where
  Beta : ∀ {Δ A N W}
    → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ

  PrimBeta : ∀ {Δ p m n}
    → Δ ⊢ ($ m) ⊕[ p ] ($ n) -→ $ (⟦ p ⟧ᵖ m n)

  TyBeta : ∀ {Δ V B A R}
    → Value V → Δ ⊢⌊ A ⌋ R
    → Δ ⊢ (Λ V) • B [ A ]
        -→ ν repBind R ∷ [] , reveal zero ∷ []
              [ V ∣ revTy zero zero A B ]

  Wrap : ∀ {Δ Θ χ V c W c₁ c₂}
    → Value (ν Θ , χ [ V ∣ c ]) → Value W
    → arr c ≡ just (c₁ , c₂)
    → Δ ⊢ (ν Θ , χ [ V ∣ c ]) · W
        -→ ν Θ , χ
              [ V ·
                  (ν [] , dual χ
                    [ renAnchᴹ (shiftAnchor (length Θ)) W ∣ c₁ ])
              ∣ c₂ ]

  TyWrap : ∀ {Δ Θ χ V c B A d R}
    → Value V → allView c ≡ just d → Δ ⊢⌊ A ⌋ R
    → Δ ⊢ (ν Θ , χ [ Λ V ∣ c ]) • B [ A ]
        -→ ν (Θ ++ (repBind (shiftByᴿ (length Θ) R) ∷ []))
              , (shiftScope 1 χ ++ (reveal zero ∷ []))
              [ V ∣ instReveal zero zero (` zero) d ]

  Merge : ∀ {Δ Θ₁ Θ₂ χ₁ χ₂ V c d}
    → Value (ν Θ₂ , χ₂ [ V ∣ c ])
    → Δ ⊢ ν Θ₁ , χ₁ [ ν Θ₂ , χ₂ [ V ∣ c ] ∣ d ]
        -→ ν (Θ₁ ++ Θ₂)
              , (shiftScope (length Θ₂) χ₁ ++ χ₂)
              [ V ∣ c ⨟ renConv (λ X → X) (shiftAnchor (length Θ₂)) d ]

  Const : ∀ {Δ Θ χ k A}
    → Literal k → Base A
    → Δ ⊢ ν Θ , χ [ k ∣ id A ] -→ k

  ξ-⊕-l : ∀ {Δ L L′ M p}
    → Δ ⊢ L -→ L′
    → Δ ⊢ L ⊕[ p ] M -→ L′ ⊕[ p ] M
  ξ-⊕-r : ∀ {Δ V M M′ p}
    → Value V → Δ ⊢ M -→ M′
    → Δ ⊢ V ⊕[ p ] M -→ V ⊕[ p ] M′
  ξ-·-l : ∀ {Δ L L′ M}
    → Δ ⊢ L -→ L′ → Δ ⊢ L · M -→ L′ · M
  ξ-·-r : ∀ {Δ V M M′}
    → Value V → Δ ⊢ M -→ M′
    → Δ ⊢ V · M -→ V · M′
  ξ-•[] : ∀ {Δ L L′ B A}
    → Δ ⊢ L -→ L′
    → Δ ⊢ L • B [ A ] -→ L′ • B [ A ]
  ξ-Λ : ∀ {Δ N N′}
    → (name zero ∷ abst ∷ Δ) ⊢ N -→ N′
    → Δ ⊢ Λ N -→ Λ N′
  ξ-ν : ∀ {Δ ΔΘ Δᵢ Θ χ M M′ c}
    → Δ ⊢ˢ Θ ⇒ ΔΘ → ΔΘ ⊢χ χ ⇒ Δᵢ
    → Δᵢ ⊢ M -→ M′
    → Δ ⊢ ν Θ , χ [ M ∣ c ] -→ ν Θ , χ [ M′ ∣ c ]

infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N}
    → Δ ⊢ L -→ M → Δ ⊢ M -→* N → Δ ⊢ L -→* N

infixr 2 _then_
