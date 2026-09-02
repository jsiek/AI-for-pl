module strong.Reduction where

-- Strong System F — the reduction relation on runtime terms (de Bruijn).
--
-- This is the first increment: the substitution machinery, values, and the
-- computation rules whose de Bruijn form is verified by a full example
-- (TyBeta, WrapReveal, Beta, RevealCnst) plus the ξ congruences.  The remaining
-- rules are collected in the "deferred" note at the bottom, each with the
-- specific index-shift / re-reveal-rename it needs.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (¬_; yes; no)
open import strong.Types
open import strong.Terms
open import strong.ConcealCtx using (_∈ᵗ_; fv-var; fv-⇒l; fv-⇒r; fv-∀)

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

-- predᵗ : downshift a type-variable renaming (removes index 0).  Used by Cancel
-- and Drop, which delete the reveal's variable (valid because it is unused).
predᵗ : ℕ → ℕ
predᵗ zero    = zero
predᵗ (suc i) = i

-- redirect X : the re-reveal renaming used by WrapConceal.  It sends the
-- concealed variable X to the fresh reveal's index 0, and every other variable
-- up past it.
redirect : ℕ → ℕ → ℕ
redirect X y with X ≟ y
... | yes _ = zero
... | no  _ = suc y

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
-- Free type variables of a term (for Drop's occurs check)
------------------------------------------------------------------------

data _∈ᵀ_ : ℕ → Term → Set where
  ∈ƛ-A : Y ∈ᵗ A → Y ∈ᵀ (ƛ A ∙ N)
  ∈ƛ-N : Y ∈ᵀ N → Y ∈ᵀ (ƛ A ∙ N)
  ∈·-l : Y ∈ᵀ L → Y ∈ᵀ (L · M)
  ∈·-r : Y ∈ᵀ M → Y ∈ᵀ (L · M)
  ∈Λ   : suc Y ∈ᵀ N → Y ∈ᵀ (Λ N)
  ∈t-B : suc Y ∈ᵗ B → Y ∈ᵀ (L ·[ B , A ])
  ∈t-A : Y ∈ᵗ A → Y ∈ᵀ (L ·[ B , A ])
  ∈t-L : Y ∈ᵀ L → Y ∈ᵀ (L ·[ B , A ])
  ∈↑-A : Y ∈ᵗ A → Y ∈ᵀ (M ↑[ A , B ])
  ∈↑-B : suc Y ∈ᵗ B → Y ∈ᵀ (M ↑[ A , B ])
  ∈↑-M : suc Y ∈ᵀ M → Y ∈ᵀ (M ↑[ A , B ])
  ∈↓-X : X ∈ᵀ (M ↓[ X , A , B ])
  ∈↓-A : Y ∈ᵗ A → Y ∈ᵀ (M ↓[ X , A , B ])
  ∈↓-B : Y ∈ᵗ B → Y ∈ᵀ (M ↓[ X , A , B ])
  ∈↓-M : Y ∈ᵀ M → Y ∈ᵀ (M ↓[ X , A , B ])

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
  -- W moves inside the reveal (⇑ᵀ), and is sealed on the reveal's variable
  -- (index 0), whose representation there is ⇑ᵗ A.
  β-↑  : GVal F → Value W
       → (F ↑[ A , B₁ ⇒ B₂ ]) · W
         -→ (F · (⇑ᵀ W ↓[ 0 , ⇑ᵗ A , B₁ ])) ↑[ A , B₂ ]

  -- RevealCnst:  k ↑[X:=A]@B  →  k
  β-$↑ : ($ n) ↑[ A , B ] -→ $ n

  -- WrapConceal:  F↓[X:=A]@(B₁→B₂) · W  →  (F · W↑[X:=A]@B₁) ↓[X:=A]@B₂
  -- The inner reveal re-reveals the concealed X: `redirect X` sends W's (and
  -- B₁'s) references to X onto the fresh reveal's index 0.
  β-↓· : Value F → Value W
       → (F ↓[ X , A , B₁ ⇒ B₂ ]) · W
         -→ (F · (renameᵀ (redirect X) W ↑[ A , renameᵗ (redirect X) B₁ ])) ↓[ X , A , B₂ ]

  -- Cancel:  V↓[X:=A]@B ↑[X:=A]@B  →  V   (conceal on the reveal's own variable,
  -- i.e. index 0; the reveal's variable is deleted, so V is downshifted)
  β-cancel : Value V → (V ↓[ 0 , A , B ]) ↑[ C , D ] -→ renameᵀ predᵗ V

  -- Drop:  V↓[Y:=B]@C ↑[X:=A]@D  →  V↓[Y:=B]@C   (conceal on a *different*
  -- variable, index suc X, with the reveal's variable 0 not free in V, B, C)
  β-drop : Value V → ¬ (0 ∈ᵀ V) → ¬ (0 ∈ᵗ B) → ¬ (0 ∈ᵗ C)
         → (V ↓[ suc X , B , C ]) ↑[ A , D ]
         -→ (renameᵀ predᵗ V) ↓[ X , renameᵗ predᵗ B , renameᵗ predᵗ C ]

  -- TyWrapRevl:  F↑[X:=A]@(∀Z.B) [C]  →  F[C]↑[X:=A]@(B[Z:=C])
  -- The type application floats inside the reveal and is applied to F; the
  -- argument C is shifted past the revealed X (⇑ᵗ), and the reveal's annotation
  -- becomes the ∀-body B with Z instantiated to that shifted C.
  β-↑[] : GVal F
        → (F ↑[ A , `∀ B ]) ·[ B₃ , C ]
          -→ (F ·[ B , ⇑ᵗ C ]) ↑[ A , B [ ⇑ᵗ C ]ᵗ ]

  -- TyWrapCncl:  F↓[X:=A]@(∀Z.B) [C]  →  F[C[X:=A]]↓[X:=A]@(B[Z:=C])
  -- The type application floats inside the conceal; since X is blocked there, the
  -- argument is C with X's representation substituted (C[X:=A]); the conceal's
  -- annotation becomes the ∀-body B with Z instantiated to the original C.
  β-↓[] : Value F
        → (F ↓[ X , A , `∀ B ]) ·[ B₃ , C ]
          -→ (F ·[ B , C [ X := A ]ᵗ ]) ↓[ X , A , B [ C ]ᵗ ]

  -- Commute:  V↓[Y:=B]@C ↑[X:=A]@D → (V↑[X:=A[Y:=B]]@C[Y:=B]) ↓[Y:=B]@C[X:=A]
  -- The X ∈ V counterpart of Drop (conceal on a *different* variable, index
  -- suc Y).  The wrappers swap; V itself is unchanged (both contexts place X at
  -- index 0 and Y at index suc Y), while the representations and annotations are
  -- substituted, and Y's representation B is downshifted past the removed reveal.
  -- NOTE: unlike the other rules, no example in the notes takes this branch
  -- (Examples 1–6 all reduce via Drop or Cancel), so the exact index arithmetic
  -- here is only pinned down once the Preservation proof forces it.
  β-commute : Value V → 0 ∈ᵀ V
            → (V ↓[ suc Y , B , C ]) ↑[ A , D ]
              -→ (V ↑[ A [ Y := renameᵗ predᵗ B ]ᵗ , C [ suc Y := B ]ᵗ ])
                   ↓[ Y , renameᵗ predᵗ B , C [ A ]ᵗ ]

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

------------------------------------------------------------------------
-- Example 4:  (ΛX. λx:X. 7) [ℕ] · 5  -↠  7
------------------------------------------------------------------------

_ : ((Λ (ƛ ` 0 ∙ $ 7)) ·[ (` 0 ⇒ `ℕ) , `ℕ ]) · ($ 5) -↠ $ 7
_ =
    ((Λ (ƛ ` 0 ∙ $ 7)) ·[ (` 0 ⇒ `ℕ) , `ℕ ]) · ($ 5)
  -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                 -- TyBeta
    ((ƛ ` 0 ∙ $ 7) ↑[ `ℕ , (` 0 ⇒ `ℕ) ]) · ($ 5)
  -→⟨ β-↑ G-ƛ V-$ ⟩                            -- WrapReveal
    ((ƛ ` 0 ∙ $ 7) · ($ 5 ↓[ 0 , `ℕ , ` 0 ])) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-ƛ (V-↓ V-$)) ⟩                    -- Beta
    ($ 7) ↑[ `ℕ , `ℕ ]
  -→⟨ β-$↑ ⟩                                   -- RevealCnst
    $ 7
  ∎

------------------------------------------------------------------------
-- Example 6:  (ΛX. λw:ℕ. (ΛY. w) [X→X]) [ℕ] · 5  -↠  5   (uses Drop, Cancel)
------------------------------------------------------------------------

_ : ((Λ (ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ]))) ·[ (`ℕ ⇒ `ℕ) , `ℕ ]) · ($ 5) -↠ $ 5
_ =
    ((Λ (ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ]))) ·[ (`ℕ ⇒ `ℕ) , `ℕ ]) · ($ 5)
  -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                       -- TyBeta
    ((ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ])) ↑[ `ℕ , (`ℕ ⇒ `ℕ) ]) · ($ 5)
  -→⟨ β-↑ G-ƛ V-$ ⟩                                  -- WrapReveal
    ((ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ])) · ($ 5 ↓[ 0 , `ℕ , `ℕ ])) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-ƛ (V-↓ V-$)) ⟩                          -- Beta (conceal pushed under Λ: ⇑ᵀ)
    ((Λ ($ 5 ↓[ 1 , `ℕ , `ℕ ])) ·[ `ℕ , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-Λ (V-↓ V-$)) ⟩                          -- TyBeta (into the conceal)
    (($ 5 ↓[ 1 , `ℕ , `ℕ ]) ↑[ (` 0 ⇒ ` 0) , `ℕ ]) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-drop V-$ (λ ()) (λ ()) (λ ())) ⟩        -- Drop
    ($ 5 ↓[ 0 , `ℕ , `ℕ ]) ↑[ `ℕ , `ℕ ]
  -→⟨ β-cancel V-$ ⟩                                 -- Cancel
    $ 5
  ∎

------------------------------------------------------------------------
-- Example 5:  (ΛX. λf:(X→X)→X. f · (λx:X.x)) [ℕ] · (λg:ℕ→ℕ. g·42)  -↠  42
--   (uses WrapConceal and Cancel)
------------------------------------------------------------------------

private
  g42 : Term        -- λg:ℕ→ℕ. g · 42
  g42 = ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · ($ 42))
  idX : Term        -- λx:X. x
  idX = ƛ ` 0 ∙ ` 0

  _ : ((Λ (ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX)))
         ·[ (((` 0 ⇒ ` 0) ⇒ ` 0) ⇒ ` 0) , `ℕ ]) · g42
      -↠ $ 42
  _ =
      ((Λ (ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX)))
         ·[ (((` 0 ⇒ ` 0) ⇒ ` 0) ⇒ ` 0) , `ℕ ]) · g42
    -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                         -- TyBeta
      ((ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX))
         ↑[ `ℕ , (((` 0 ⇒ ` 0) ⇒ ` 0) ⇒ ` 0) ]) · g42
    -→⟨ β-↑ G-ƛ (V-G G-ƛ) ⟩                             -- WrapReveal
      ((ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX))
         · (g42 ↓[ 0 , `ℕ , ((` 0 ⇒ ` 0) ⇒ ` 0) ])) ↑[ `ℕ , ` 0 ]
    -→⟨ ξ-↑ (β-ƛ (V-↓ (V-G G-ƛ))) ⟩                     -- Beta
      ((g42 ↓[ 0 , `ℕ , ((` 0 ⇒ ` 0) ⇒ ` 0) ]) · idX) ↑[ `ℕ , ` 0 ]
    -→⟨ ξ-↑ (β-↓· (V-G G-ƛ) (V-G G-ƛ)) ⟩               -- WrapConceal
      ((g42 · (idX ↑[ `ℕ , (` 0 ⇒ ` 0) ])) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
    -→⟨ ξ-↑ (ξ-↓ (β-ƛ (V-G (G-↑ G-ƛ)))) ⟩              -- Beta
      (((idX ↑[ `ℕ , (` 0 ⇒ ` 0) ]) · ($ 42)) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
    -→⟨ ξ-↑ (ξ-↓ (β-↑ G-ƛ V-$)) ⟩                       -- WrapReveal
      (((idX · ($ 42 ↓[ 0 , `ℕ , ` 0 ])) ↑[ `ℕ , ` 0 ]) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
    -→⟨ ξ-↑ (ξ-↓ (ξ-↑ (β-ƛ (V-↓ V-$)))) ⟩              -- Beta
      ((($ 42 ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
    -→⟨ ξ-↑ (ξ-↓ (β-cancel V-$)) ⟩                      -- Cancel
      ($ 42 ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
    -→⟨ β-cancel V-$ ⟩                                  -- Cancel
      $ 42
    ∎

------------------------------------------------------------------------
-- Example 3:  (ΛX. λf:(∀Z.Z→Z). f [X]) [𝔹] · ((ΛY. ΛZ. λz:Z. z) [ℕ])
--   -↠  (λz:Z. z) ↑[Z:=𝔹] ↑[Y:=ℕ]     (uses TyWrapCncl, TyWrapRevl, Cancel)
------------------------------------------------------------------------

private
  zz : Term         -- λz:Z. z
  zz = ƛ ` 0 ∙ ` 0
  fX : Term         -- λf:(∀Z.Z→Z). f [X]
  fX = ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ((` 0) ·[ (` 0 ⇒ ` 0) , ` 0 ])

  _ : ((Λ fX) ·[ ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) , `𝔹 ])
        · ((Λ (Λ zz)) ·[ (`∀ (` 0 ⇒ ` 0)) , `ℕ ])
      -↠ (zz ↑[ `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ]
  _ =
      ((Λ fX) ·[ ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) , `𝔹 ])
        · ((Λ (Λ zz)) ·[ (`∀ (` 0 ⇒ ` 0)) , `ℕ ])
    -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                              -- TyBeta (function)
      (fX ↑[ `𝔹 , ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) ])
        · ((Λ (Λ zz)) ·[ (`∀ (` 0 ⇒ ` 0)) , `ℕ ])
    -→⟨ ξ-·-r (V-G (G-↑ G-ƛ)) (β-Λ (V-G (G-Λ (V-G G-ƛ)))) ⟩  -- TyBeta (argument)
      (fX ↑[ `𝔹 , ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) ])
        · ((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ])
    -→⟨ β-↑ G-ƛ (V-G (G-↑ (G-Λ (V-G G-ƛ)))) ⟩                -- WrapReveal
      (fX · (((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]) ↓[ 0 , `𝔹 , (`∀ (` 0 ⇒ ` 0)) ]))
        ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
    -→⟨ ξ-↑ (β-ƛ (V-↓ (V-G (G-↑ (G-Λ (V-G G-ƛ)))))) ⟩        -- Beta
      ((((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]) ↓[ 0 , `𝔹 , (`∀ (` 0 ⇒ ` 0)) ])
        ·[ (` 0 ⇒ ` 0) , ` 0 ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
    -→⟨ ξ-↑ (β-↓[] (V-G (G-↑ (G-Λ (V-G G-ƛ))))) ⟩            -- TyWrapCncl
      ((((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]) ·[ (` 0 ⇒ ` 0) , `𝔹 ])
        ↓[ 0 , `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
    -→⟨ ξ-↑ (ξ-↓ (β-↑[] (G-Λ (V-G G-ƛ)))) ⟩                 -- TyWrapRevl
      ((((Λ zz) ·[ (` 0 ⇒ ` 0) , `𝔹 ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ])
        ↓[ 0 , `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
    -→⟨ ξ-↑ (ξ-↓ (ξ-↑ (β-Λ (V-G G-ƛ)))) ⟩                   -- TyBeta
      (((zz ↑[ `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ])
        ↓[ 0 , `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
    -→⟨ β-cancel (V-G (G-↑ (G-↑ G-ƛ))) ⟩                     -- Cancel
      (zz ↑[ `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ]
    ∎

------------------------------------------------------------------------
-- A Commute step (the one rule no whole-program example reaches).
--
--   (λx:X. x) ↓[Y:=ℕ]@(X→X)  ↑[X:=ℕ]@(X→X)
--     -→  (λx:X. x) ↑[X:=ℕ]@(X→X)  ↓[Y:=ℕ]@(ℕ→ℕ)
--
-- The concealed value λx:X.x mentions the revealed variable X (so ¬Drop), and
-- the conceal is on a *different* variable Y at index suc 0 (so ¬Cancel), which
-- is exactly the Commute branch.  Well typed under an outer Y:=ℕ (context
-- [rvld ℕ]); both sides have type ℕ→ℕ.  The reveal moves inside the conceal;
-- its representation stays ℕ, and the conceal's annotation X→X becomes (X→X)[X:=ℕ]
-- = ℕ→ℕ.
------------------------------------------------------------------------

private
  _ : ((ƛ ` 0 ∙ ` 0) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (` 0 ⇒ ` 0) ]
      -→ ((ƛ ` 0 ∙ ` 0) ↑[ `ℕ , (` 0 ⇒ ` 0) ]) ↓[ 0 , `ℕ , (`ℕ ⇒ `ℕ) ]
  _ = β-commute (V-G G-ƛ) (∈ƛ-A fv-var)
