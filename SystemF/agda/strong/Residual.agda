module strong.Residual where

-- Strong System F v7 — one-hole term contexts and one-step residuals.
-- These definitions are public because ColorPreservation states its theorem
-- directly in terms of plug/decompose contexts.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; length; _++_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types using (Ty; `_; ⇑ᵗ)
open import strong.RepresentationTypes using (Renameᴿ; extᴿ; shiftByᴿ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- One-hole contexts and plugging
------------------------------------------------------------------------

data TermCtx : Set where
  □          : TermCtx
  _⊕L[_]_    : TermCtx → Prim → Term → TermCtx
  _⊕R[_]_    : Term → Prim → TermCtx → TermCtx
  ƛC_∙_      : Ty → TermCtx → TermCtx
  _·L_       : TermCtx → Term → TermCtx
  _·R_       : Term → TermCtx → TermCtx
  ΛC_        : TermCtx → TermCtx
  _•C_[_]    : TermCtx → Ty → Ty → TermCtx
  νC_,_[_∣_] : Store → Scope → TermCtx → Conv → TermCtx

plug : TermCtx → Term → Term
plug □ M                    = M
plug (C ⊕L[ p ] N) M       = plug C M ⊕[ p ] N
plug (L ⊕R[ p ] C) M       = L ⊕[ p ] plug C M
plug (ƛC A ∙ C) M          = ƛ A ∙ plug C M
plug (C ·L N) M            = plug C M · N
plug (L ·R C) M            = L · plug C M
plug (ΛC C) M              = Λ (plug C M)
plug (C •C B [ A ]) M      = plug C M • B [ A ]
plug (νC Θ , χ [ C ∣ c ]) M = ν Θ , χ [ plug C M ∣ c ]

infixr 5 _○_
_○_ : TermCtx → TermCtx → TermCtx
□ ○ D = D
(C ⊕L[ p ] N) ○ D = (C ○ D) ⊕L[ p ] N
(L ⊕R[ p ] C) ○ D = L ⊕R[ p ] (C ○ D)
(ƛC A ∙ C) ○ D = ƛC A ∙ (C ○ D)
(C ·L N) ○ D = (C ○ D) ·L N
(L ·R C) ○ D = L ·R (C ○ D)
(ΛC C) ○ D = ΛC (C ○ D)
(C •C B [ A ]) ○ D = (C ○ D) •C B [ A ]
(νC Θ , χ [ C ∣ c ]) ○ D = νC Θ , χ [ C ○ D ∣ c ]

------------------------------------------------------------------------
-- The type context at a hole
------------------------------------------------------------------------

infix 3 _⊢C_⊣_
data _⊢C_⊣_ : Ctxᵗ → TermCtx → Ctxᵗ → Set where
  frame-□ : ∀ {Δ} → Δ ⊢C □ ⊣ Δ
  frame-⊕L : ∀ {Δ Δ′ C p N}
    → Δ ⊢C C ⊣ Δ′ → Δ ⊢C C ⊕L[ p ] N ⊣ Δ′
  frame-⊕R : ∀ {Δ Δ′ L p C}
    → Δ ⊢C C ⊣ Δ′ → Δ ⊢C L ⊕R[ p ] C ⊣ Δ′
  frame-ƛ : ∀ {Δ Δ′ A C}
    → Δ ⊢C C ⊣ Δ′ → Δ ⊢C ƛC A ∙ C ⊣ Δ′
  frame-·L : ∀ {Δ Δ′ C N}
    → Δ ⊢C C ⊣ Δ′ → Δ ⊢C C ·L N ⊣ Δ′
  frame-·R : ∀ {Δ Δ′ L C}
    → Δ ⊢C C ⊣ Δ′ → Δ ⊢C L ·R C ⊣ Δ′
  frame-Λ : ∀ {Δ Δ′ C}
    → (name zero ∷ abst ∷ Δ) ⊢C C ⊣ Δ′
    → Δ ⊢C ΛC C ⊣ Δ′
  frame-• : ∀ {Δ Δ′ C B A}
    → Δ ⊢C C ⊣ Δ′ → Δ ⊢C C •C B [ A ] ⊣ Δ′
  frame-ν : ∀ {Δ ΔΘ Δᵢ Δ′ Θ χ C c}
    → Δ ⊢ˢ Θ ⇒ ΔΘ → ΔΘ ⊢χ χ ⇒ Δᵢ
    → Δᵢ ⊢C C ⊣ Δ′
    → Δ ⊢C νC Θ , χ [ C ∣ c ] ⊣ Δ′

------------------------------------------------------------------------
-- Substitution at a focused body node
------------------------------------------------------------------------

idImg : ℕ → Img
idImg x = ivar x

betaEnv : Term → Ty → ℕ → Img
betaEnv V A zero    = ival V A
betaEnv V A (suc x) = ivar x

substCtx : (ℕ → Img) → TermCtx → TermCtx
substCtx σ □ = □
substCtx σ (C ⊕L[ p ] N) = substCtx σ C ⊕L[ p ] substᵐ σ N
substCtx σ (L ⊕R[ p ] C) = substᵐ σ L ⊕R[ p ] substCtx σ C
substCtx σ (ƛC A ∙ C) = ƛC A ∙ substCtx (extImg σ) C
substCtx σ (C ·L N) = substCtx σ C ·L substᵐ σ N
substCtx σ (L ·R C) = substᵐ σ L ·R substCtx σ C
substCtx σ (ΛC C) = ΛC (substCtx (λ x → underΛ (σ x)) C)
substCtx σ (C •C B [ A ]) = substCtx σ C •C B [ A ]
substCtx σ (νC Θ , χ [ C ∣ c ]) = νC Θ , χ [ C ∣ c ]

holeEnv : (ℕ → Img) → TermCtx → ℕ → Img
holeEnv σ □ = σ
holeEnv σ (C ⊕L[ p ] N) = holeEnv σ C
holeEnv σ (L ⊕R[ p ] C) = holeEnv σ C
holeEnv σ (ƛC A ∙ C) = holeEnv (extImg σ) C
holeEnv σ (C ·L N) = holeEnv σ C
holeEnv σ (L ·R C) = holeEnv σ C
holeEnv σ (ΛC C) = holeEnv (λ x → underΛ (σ x)) C
holeEnv σ (C •C B [ A ]) = holeEnv σ C
holeEnv σ (νC Θ , χ [ C ∣ c ]) = idImg

data Stable : (ℕ → Img) → Term → Set where
  stable-var : ∀ {σ x y} → σ x ≡ ivar y → Stable σ (` x)
  stable-⊕   : ∀ {σ L p M} → Stable σ (L ⊕[ p ] M)
  stable-ƛ   : ∀ {σ A N} → Stable σ (ƛ A ∙ N)
  stable-·   : ∀ {σ L M} → Stable σ (L · M)
  stable-Λ   : ∀ {σ N} → Stable σ (Λ N)
  stable-•   : ∀ {σ L B A} → Stable σ (L • B [ A ])

------------------------------------------------------------------------
-- Renaming an occurrence context in an argument copied beneath Λ
------------------------------------------------------------------------

renAnchCtx : Renameᴿ → TermCtx → TermCtx
renAnchCtx ρ □ = □
renAnchCtx ρ (C ⊕L[ p ] N) = renAnchCtx ρ C ⊕L[ p ] renAnchᴹ ρ N
renAnchCtx ρ (L ⊕R[ p ] C) = renAnchᴹ ρ L ⊕R[ p ] renAnchCtx ρ C
renAnchCtx ρ (ƛC A ∙ C) = ƛC A ∙ renAnchCtx ρ C
renAnchCtx ρ (C ·L N) = renAnchCtx ρ C ·L renAnchᴹ ρ N
renAnchCtx ρ (L ·R C) = renAnchᴹ ρ L ·R renAnchCtx ρ C
renAnchCtx ρ (ΛC C) = ΛC (renAnchCtx (extᴿ ρ) C)
renAnchCtx ρ (C •C B [ A ]) = renAnchCtx ρ C •C B [ A ]
renAnchCtx ρ (νC Θ , χ [ C ∣ c ]) =
  νC renStore ρ Θ , renBoundaryScope ρ Θ χ
    [ renAnchCtx (extendAnchor (length Θ) ρ) C
    ∣ renConv (λ X → X) (extendAnchor (length Θ) ρ) c ]

data SourceNode : Term → Set where
  node-var : ∀ {x} → SourceNode (` x)
  node-⊕   : ∀ {L p M} → SourceNode (L ⊕[ p ] M)
  node-ƛ   : ∀ {A N} → SourceNode (ƛ A ∙ N)
  node-·   : ∀ {L M} → SourceNode (L · M)
  node-Λ   : ∀ {N} → SourceNode (Λ N)
  node-•   : ∀ {L B A} → SourceNode (L • B [ A ])

data ImageResidual : ℕ → Img → TermCtx → Term
                   → TermCtx → Term → Set where
  image-here : ∀ {A C M}
    → SourceNode M
    → ImageResidual zero (ival (plug C M) A) C M C M
  image-Λ : ∀ {k V A C M D N}
    → ImageResidual k (ival V A) C M D N
    → ImageResidual (suc k) (underΛ (ival V A)) C M
        (νC [] , conceal zero ∷ []
          [ renAnchCtx suc D ∣ id (⇑ᵗ A) ])
        (renAnchᴹ suc N)

data CopyResidual (k : ℕ) (σ : ℕ → Img) : Term → TermCtx → Term
                  → TermCtx → Term → Set where
  copy-var : ∀ {x C M D N}
    → ImageResidual k (σ x) C M D N
    → CopyResidual k σ (` x) C M D N
  copy-⊕L : ∀ {L p P C M D N}
    → CopyResidual k σ L C M D N
    → CopyResidual k σ (L ⊕[ p ] P) C M
        (D ⊕L[ p ] substᵐ σ P) N
  copy-⊕R : ∀ {L p P C M D N}
    → CopyResidual k σ P C M D N
    → CopyResidual k σ (L ⊕[ p ] P) C M
        (substᵐ σ L ⊕R[ p ] D) N
  copy-ƛ : ∀ {A P C M D N}
    → CopyResidual k (extImg σ) P C M D N
    → CopyResidual k σ (ƛ A ∙ P) C M (ƛC A ∙ D) N
  copy-·L : ∀ {L P C M D N}
    → CopyResidual k σ L C M D N
    → CopyResidual k σ (L · P) C M (D ·L substᵐ σ P) N
  copy-·R : ∀ {L P C M D N}
    → CopyResidual k σ P C M D N
    → CopyResidual k σ (L · P) C M (substᵐ σ L ·R D) N
  copy-Λ : ∀ {P C M D N}
    → CopyResidual (suc k) (λ x → underΛ (σ x)) P C M D N
    → CopyResidual k σ (Λ P) C M (ΛC D) N
  copy-• : ∀ {L B A C M D N}
    → CopyResidual k σ L C M D N
    → CopyResidual k σ (L • B [ A ]) C M (D •C B [ A ]) N

------------------------------------------------------------------------
-- Residuals of one reduction step
------------------------------------------------------------------------

data Residual : ∀ {Δ L N} → Δ ⊢ L -→ N
              → TermCtx → Term → TermCtx → Term → Set where
  residual-β-body : ∀ {Δ A C M W}
    (vW : Value W)
    → Stable (holeEnv (betaEnv W A) C) M
    → Residual (Beta {Δ = Δ} {A = A} {N = plug C M} {W = W} vW)
        ((ƛC A ∙ C) ·L W) M
        (substCtx (betaEnv W A) C)
        (substᵐ (holeEnv (betaEnv W A) C) M)

  residual-β-arg : ∀ {Δ A P C M D N}
    (vW : Value (plug C M))
    → CopyResidual zero (betaEnv (plug C M) A) P C M D N
    → Residual (Beta {Δ = Δ} {A = A} {N = P}
                  {W = plug C M} vW)
        ((ƛ A ∙ P) ·R C) M D N

  residual-TyBeta : ∀ {Δ V B A R C M}
    (vV : Value V) (q : Δ ⊢⌊ A ⌋ R)
    → V ≡ plug C M → SourceNode M
    → Residual (TyBeta {Δ = Δ} {V = V} {B = B} {A = A} {R = R} vV q)
        ((ΛC C) •C B [ A ]) M
        (νC repBind R ∷ [] , reveal zero ∷ []
          [ C ∣ revTy zero zero A B ]) M

  residual-Wrap-body : ∀ {Δ Θ χ V c W c₁ c₂ C M}
    (vB : Value (ν Θ , χ [ V ∣ c ])) (vW : Value W)
    (eq : arr c ≡ just (c₁ , c₂))
    → V ≡ plug C M → SourceNode M
    → Residual (Wrap {Δ = Δ} {Θ = Θ} {χ = χ} {V = V} {c = c}
                  {W = W} {c₁ = c₁} {c₂ = c₂} vB vW eq)
        ((νC Θ , χ [ C ∣ c ]) ·L W) M
        (νC Θ , χ
          [ C ·L (ν [] , dual χ
              [ renAnchᴹ (shiftAnchor (length Θ)) W ∣ c₁ ])
          ∣ c₂ ]) M

  residual-Wrap-arg : ∀ {Δ Θ χ V c W c₁ c₂ C M}
    (vB : Value (ν Θ , χ [ V ∣ c ])) (vW : Value W)
    (eq : arr c ≡ just (c₁ , c₂))
    → W ≡ plug C M → SourceNode M
    → Residual (Wrap {Δ = Δ} {Θ = Θ} {χ = χ} {V = V} {c = c}
                  {W = W} {c₁ = c₁} {c₂ = c₂} vB vW eq)
        ((ν Θ , χ [ V ∣ c ]) ·R C) M
        (νC Θ , χ
          [ V ·R (νC [] , dual χ
              [ renAnchCtx (shiftAnchor (length Θ)) C ∣ c₁ ])
          ∣ c₂ ])
        (renAnchᴹ (shiftAnchor (length Θ)) M)

  residual-TyWrap : ∀
    {Δ Θ χ V c B A d R C M}
    (vV : Value V) (eq : allView c ≡ just d)
    (q : Δ ⊢⌊ A ⌋ R)
    → V ≡ plug C M → SourceNode M
    → Residual (TyWrap {Δ = Δ} {Θ = Θ} {χ = χ} {V = V}
                  {c = c} {B = B} {A = A} {d = d} {R = R} vV eq q)
        ((νC Θ , χ [ ΛC C ∣ c ]) •C B [ A ]) M
        (νC (Θ ++ (repBind (shiftByᴿ (length Θ) R) ∷ []))
          , (shiftScope 1 χ ++ (reveal zero ∷ []))
          [ C ∣ instReveal zero zero (` zero) d ]) M

  residual-Merge : ∀ {Δ Θ₁ Θ₂ χ₁ χ₂ V c d C M}
    (v : Value (ν Θ₂ , χ₂ [ V ∣ c ]))
    → V ≡ plug C M → SourceNode M
    → Residual (Merge {Δ = Δ} {Θ₁ = Θ₁} {Θ₂ = Θ₂}
                  {χ₁ = χ₁}
                  {χ₂ = χ₂} {V = V} {c = c} {d = d} v)
        (νC Θ₁ , χ₁ [ νC Θ₂ , χ₂ [ C ∣ c ] ∣ d ]) M
        (νC (Θ₁ ++ Θ₂)
          , (shiftScope (length Θ₂) χ₁ ++ χ₂)
          [ C ∣ c ⨟ renConv (λ X → X) (shiftAnchor (length Θ₂)) d ]) M

  residual-ξ-⊕L : ∀ {Δ L L′ P p r C M D N}
    → Residual r C M D N
    → Residual (ξ-⊕-l {Δ = Δ} {L = L} {L′ = L′} {M = P} {p = p} r)
        (C ⊕L[ p ] P) M (D ⊕L[ p ] P) N
  residual-ξ-⊕R : ∀ {Δ V P P′ p r C M D N}
    (v : Value V) → Residual r C M D N
    → Residual (ξ-⊕-r {Δ = Δ} {V = V} {M = P} {M′ = P′}
                  {p = p} v r)
        (V ⊕R[ p ] C) M (V ⊕R[ p ] D) N
  residual-ξ-·L : ∀ {Δ L L′ P r C M D N}
    → Residual r C M D N
    → Residual (ξ-·-l {Δ = Δ} {L = L} {L′ = L′} {M = P} r)
        (C ·L P) M (D ·L P) N
  residual-ξ-·R : ∀ {Δ V P P′ r C M D N}
    (v : Value V) → Residual r C M D N
    → Residual (ξ-·-r {Δ = Δ} {V = V} {M = P} {M′ = P′} v r)
        (V ·R C) M (V ·R D) N
  residual-ξ-• : ∀ {Δ L L′ B A r C M D N}
    → Residual r C M D N
    → Residual (ξ-•[] {Δ = Δ} {L = L} {L′ = L′} {B = B} {A = A} r)
        (C •C B [ A ]) M (D •C B [ A ]) N
  residual-ξ-Λ : ∀ {Δ P P′ r C M D N}
    → Residual r C M D N
    → Residual (ξ-Λ {Δ = Δ} {N = P} {N′ = P′} r)
        (ΛC C) M (ΛC D) N
  residual-ξ-ν : ∀ {Δ ΔΘ Δᵢ Θ χ P P′ c r C M D N}
    (s : Δ ⊢ˢ Θ ⇒ ΔΘ) (ch : ΔΘ ⊢χ χ ⇒ Δᵢ)
    → Residual r C M D N
    → Residual (ξ-ν {Δ = Δ} {ΔΘ = ΔΘ} {Δᵢ = Δᵢ} {Θ = Θ}
                  {χ = χ} {M = P} {M′ = P′} {c = c} s ch r)
        (νC Θ , χ [ C ∣ c ]) M (νC Θ , χ [ D ∣ c ]) N

------------------------------------------------------------------------
-- Residuals through a reduction sequence
------------------------------------------------------------------------

data Residuals : ∀ {Δ L N} → Δ ⊢ L -→* N
               → TermCtx → Term → TermCtx → Term → Set where
  residuals-done : ∀ {Δ C M}
    → SourceNode M
    → Residuals (done {Δ = Δ} {M = plug C M}) C M C M
  residuals-step : ∀ {Δ L P Q r rs C M D N E O}
    → Residual {Δ = Δ} {L = L} {N = P} r C M D N
    → Residuals {Δ = Δ} {L = P} {N = Q} rs D N E O
    → Residuals (r then rs) C M E O
