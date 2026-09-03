module strong.Reduction where

-- Strong System F — the reduction relation on runtime terms (de Bruijn):
-- the substitution machinery, values, the computation rules, the ξ congruences,
-- and the reflexive-transitive closure _-↠_.  Worked examples live in
-- strong.Examples.

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import strong.Types
open import strong.Terms

private
  variable
    A B B₁ B₂ B₃ C D : Ty
    L L′ M M′ N V W F : Term
    n X Y : ℕ

------------------------------------------------------------------------
-- Renaming and substitution on terms
------------------------------------------------------------------------

-- rename the TYPE variables of a term (descends under Λ / reveal with extᵗ)
renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ (` x)            = ` x
renameᵀ ρ ($ n)            = $ n
renameᵀ ρ (ƛ A ∙ N)        = ƛ (renameᵗ ρ A) ∙ renameᵀ ρ N
renameᵀ ρ (L · M)          = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N)            = Λ (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (L ·[ B , A ])   = renameᵀ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renameᵀ ρ (M ↑[ A , B ])   = renameᵀ (extᵗ ρ) M ↑[ renameᵗ ρ A , renameᵗ (extᵗ ρ) B ]
renameᵀ ρ (M ↓[ X , A , B ]) = renameᵀ ρ M ↓[ ρ X , renameᵗ ρ A , renameᵗ ρ B ]

⇑ᵀ : Term → Term
⇑ᵀ = renameᵀ suc

-- rename the TERM variables of a term (identity on conceal bodies — a conceal
-- starts a fresh term scope, so no outer term variable reaches it)
extⁿ : (ℕ → ℕ) → (ℕ → ℕ)
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renameᵀᵐ : (ℕ → ℕ) → Term → Term
renameᵀᵐ ρ (` x)              = ` (ρ x)
renameᵀᵐ ρ ($ n)              = $ n
renameᵀᵐ ρ (ƛ A ∙ N)          = ƛ A ∙ renameᵀᵐ (extⁿ ρ) N
renameᵀᵐ ρ (L · M)            = renameᵀᵐ ρ L · renameᵀᵐ ρ M
renameᵀᵐ ρ (Λ N)              = Λ (renameᵀᵐ ρ N)
renameᵀᵐ ρ (L ·[ B , A ])     = renameᵀᵐ ρ L ·[ B , A ]
renameᵀᵐ ρ (M ↑[ A , B ])     = renameᵀᵐ ρ M ↑[ A , B ]
renameᵀᵐ ρ (M ↓[ X , A , B ]) = M ↓[ X , A , B ]

⇑ᵀᵐ : Term → Term
⇑ᵀᵐ = renameᵀᵐ suc

-- term substitution (Beta): σ maps term-variable indices to terms.  Under a λ
-- it extends; under a TYPE binder (Λ / reveal) it shifts its values' type
-- variables; it is the identity on conceal bodies.
extsᵀᵐ : (ℕ → Term) → (ℕ → Term)
extsᵀᵐ σ zero    = ` zero
extsᵀᵐ σ (suc x) = ⇑ᵀᵐ (σ x)

substᵀᵐ : (ℕ → Term) → Term → Term
substᵀᵐ σ (` x)              = σ x
substᵀᵐ σ ($ n)              = $ n
substᵀᵐ σ (ƛ A ∙ N)          = ƛ A ∙ substᵀᵐ (extsᵀᵐ σ) N
substᵀᵐ σ (L · M)            = substᵀᵐ σ L · substᵀᵐ σ M
substᵀᵐ σ (Λ N)              = Λ (substᵀᵐ (λ x → ⇑ᵀ (σ x)) N)
substᵀᵐ σ (L ·[ B , A ])     = substᵀᵐ σ L ·[ B , A ]
substᵀᵐ σ (M ↑[ A , B ])     = substᵀᵐ (λ x → ⇑ᵀ (σ x)) M ↑[ A , B ]
substᵀᵐ σ (M ↓[ X , A , B ]) = M ↓[ X , A , B ]

-- single substitution:  N [ W ]  replaces the outermost term variable by W
infix 8 _[_]ᵐ
_[_]ᵐ : Term → Term → Term
N [ W ]ᵐ = substᵀᵐ (λ { zero → W ; (suc x) → ` x }) N

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GVal : Term → Set    -- G : functions, type abstractions, and reveals of them
data Value : Term → Set   -- V : constants, G's, and conceals of values

data GVal where
  G-ƛ : GVal (ƛ A ∙ N)
  G-Λ : Value V → GVal (Λ V)
  G-↑ : GVal V → GVal (V ↑[ A , B ])

data Value where
  V-$ : Value ($ n)
  V-G : GVal V → Value V
  V-↓ : Value V → Value (V ↓[ X , A , B ])

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

infix 2 _-→_
data _-→_ : Term → Term → Set where

  -- TyBeta:  (ΛX.V) @B[A]  →  V ↑[X:=A]@B   (X was Λ-bound at index 0, now reveal-bound)
  β-Λ  : Value V → (Λ V) ·[ B , A ] -→ V ↑[ A , B ]

  -- Beta:  (λx:A.N) · W  →  N[x:=W]
  β-ƛ  : Value W → (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- WrapReveal:  F↑[X:=A]@(B₁→B₂) · W  →  (F · W↓[X:=A]@B₁) ↑[X:=A]@B₂
  -- (prefix design)  The reveal's body F is typed in rvld A ∷ Δ, so the fresh
  -- variable sits at index 0 with representation A — shift-free.  W is sealed on
  -- that variable; its conceal body lives in the prefix (rvld A ∷ Δ) ↓ 0 = Δ,
  -- which is exactly W's own context, so W and B₁ need NO shifting.
  β-↑  : GVal F → Value W
       → (F ↑[ A , B₁ ⇒ B₂ ]) · W
         -→ (F · (W ↓[ 0 , A , B₁ ])) ↑[ A , B₂ ]

  -- RevealCnst:  k ↑[X:=A]@B  →  k
  β-$↑ : ($ n) ↑[ A , B ] -→ $ n

  -- WrapConceal:  F↓[X:=A]@(B₁→B₂) · W  →  (F · W↑[X:=A]@B₁) ↓[X:=A]@B₂
  -- (prefix design)  The conceal body F lives in the prefix Δ ↓ X.  The argument
  -- W lives in the ambient Δ, so to move it into the prefix — where X sits at the
  -- rep slot — its type variables are reindexed down by X (λ j → j ∸ X); it is
  -- then re-revealed on that fresh reveal.  B₁ is the X-at-0 annotation, already
  -- over rvld A ∷ (Δ ↓ X), so it is unchanged.
  -- NOTE: sealing external data into the prefix inherently needs this downshift;
  --   its exact form is pinned down by the reduction-sequence examples.
  β-↓· : Value F → Value W
       → (F ↓[ X , A , B₁ ⇒ B₂ ]) · W
         -→ (F · ((renameᵀ (λ j → j ∸ X) W) ↑[ A , B₁ ])) ↓[ X , A , B₂ ]

  -- Cancel:  V↓[X:=A]@B ↑[X:=A]@B  →  V   (conceal on the reveal's own variable,
  -- index 0)  (prefix design)  V's conceal body already lives in the prefix
  -- (rvld A ∷ Δ) ↓ 0 = Δ, so nothing was shifted up and nothing is shifted down.
  β-cancel : Value V → (V ↓[ 0 , A , B ]) ↑[ C , D ] -→ V

  -- Drop:  V↓[Y:=B]@C ↑[X:=A]@D  →  V↓[Y:=B]@C   (conceal on a *different*
  -- variable, index suc X)  (prefix design)  The conceal body and its
  -- annotations live in the prefix (rvld A ∷ Δ) ↓ suc X = Δ ↓ X, which excludes
  -- the reveal's variable 0; so V, B, C cannot mention it and need no occurs
  -- check.  Removing the reveal only decrements the concealed index suc X to X.
  β-drop : Value V → (V ↓[ suc X , B , C ]) ↑[ A , D ] -→ V ↓[ X , B , C ]

  -- TyWrapRevl:  F↑[X:=A]@(∀Z.B) [C]  →  F[C]↑[X:=A]@(B[Z:=C])
  -- The type application floats inside the reveal and is applied to F; the
  -- argument C is shifted past the revealed X (⇑ᵗ), and the reveal's annotation
  -- becomes the ∀-body B with Z instantiated to that shifted C.
  β-↑[] : GVal F
        → (F ↑[ A , `∀ B ]) ·[ B₃ , C ]
          -→ (F ·[ B , ⇑ᵗ C ]) ↑[ A , B [ ⇑ᵗ C ]ᵗ ]

  -- TyWrapCncl:  F↓[X:=A]@(∀Z.B) [C]  →  F[C']↓[X:=A]@(B[Z:=C''])
  -- (prefix design)  The type application floats inside the conceal, whose body F
  -- lives in the prefix Δ ↓ X with the CONCRETE type (∀B)[A]ᵗ, i.e. F : ∀(B⁺)
  -- where B⁺ = the ∀-body of (∀B)[A]ᵗ.  So the tapp uses annotation B⁺ and the
  -- argument C moved into the prefix by downTyEnv X A (the concealed X becomes its
  -- rep A; deeper variables shift down).  The re-conceal keeps the X-at-0 frame:
  -- its ∀-body annotation B is instantiated at C moved into that frame (X ↦ 0, the
  -- rep slot; deeper ↦ Y ∸ X), i.e. renameᵗ (_∸ X) C.
  -- NOTE: the delicate rule — its X>0 reindexing is derived from the typing but
  --   example-tested only at X=0 (Example 3); preservation is the real check.
  β-↓[] : Value F
        → (F ↓[ X , A , `∀ B ]) ·[ B₃ , C ]
          -→ (F ·[ substᵗ (extsᵗ (singleTyEnv A)) B , substᵗ (downTyEnv X A) C ])
               ↓[ X , A , B [ renameᵗ (λ j → j ∸ X) C ]ᵗ ]

  -- ξ congruences (the frames)
  ξ-·-l : L -→ L′ → L · M -→ L′ · M
  ξ-·-r : Value V → M -→ M′ → V · M -→ V · M′
  ξ-↑   : M -→ M′ → M ↑[ A , B ] -→ M′ ↑[ A , B ]
  ξ-↓   : M -→ M′ → M ↓[ X , A , B ] -→ M′ ↓[ X , A , B ]
  ξ-·[] : L -→ L′ → L ·[ B , A ] -→ L′ ·[ B , A ]
  ξ-Λ   : M -→ M′ → Λ M -→ Λ M′

-- (δ is absent: the term language has no arithmetic operator, so there is no
--  n₁ ⊕ n₂ → n rule.)

------------------------------------------------------------------------
-- Reduction sequences
------------------------------------------------------------------------

infix  3 _-↠_
infixr 2 _-→⟨_⟩_
infix  3 _∎

data _-↠_ : Term → Term → Set where
  _∎     : (M : Term) → M -↠ M
  _-→⟨_⟩_ : (L : Term) {M N : Term} → L -→ M → M -↠ N → L -↠ N
