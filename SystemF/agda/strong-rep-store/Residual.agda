module strong-rep-store.Residual where

-- File Charter:
--   * ONE-HOLE TERM CONTEXTS, THE SCOPE MAP AT A HOLE, AND RESIDUALS.
--     This is the layer the COLOR PRESERVATION theorem
--     (strong-rep-store.ColorPreservation) is stated in.  §1 is `TermCtx`
--     with `plug`; §2 is `_⊢C_⊣_`, the type context AT THE HOLE — the
--     hole's SCOPE MAP is its `names`; §3 renames a context in the two
--     universes exactly as `renᴹ²` renames a term, and reads off the
--     renaming that reaches the hole; §4 pushes `Beta`'s substitution
--     through a context; §5 is `Residual`, ONE STEP, and §6 `Residuals`,
--     a whole run.
--   * WHAT A RESIDUAL RECORDS (2026-09-21, the v7 restatement).  A
--     position is a pair `(C , M)`, the hole and the node in it.  A step
--     moves a retained node to a new position `(D , N)`, and every move
--     in this calculus except `TyBeta`'s refinement is
--     REPRESENTATION-ONLY (proof/ShiftAudit §3): the node is `M` renamed
--     by some `ren² idᵗ ρ`, so the residual relation carries that `ρ` —
--     the representation renaming that reaches the hole — as an index.
--     `Residuals` composes them along a run.  The theorem then says the
--     scope map at `D` is the scope map at `C` under `ρ`.
--   * WHICH NODES HAVE RESIDUALS.  The nodes of the redex itself are
--     CONSUMED — the application node `Peel` pushes through a boundary,
--     the `Λ` and `·[]` nodes `TyBeta` eliminates, the `ƛ` and `·` nodes
--     of `Beta`, the boundary nodes every boundary rule re-mints.  Every
--     node strictly inside a retained subterm has exactly one residual,
--     except that a term variable `Beta` substitutes is replaced by a copy
--     of the argument (`CopyResidual`), and `Drop$`/`Drop-true`/
--     `Drop-false` consume their literal with its boundary — a literal
--     has no scope to preserve (proof/ShiftAudit §7, "vacuous").
--   * THIS MODULE PROVES NOTHING.  The sanity lemma that `plug D N` is the
--     step's contractum, and the theorem, are strong-rep-store.proof.
--     ColorPreservation once the statement is approved.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-store.Types
  using (Ty; `_; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction

private
  variable
    k : ℕ
    Δ Δ′ Δᵢ : Ctxᵗ
    A B : Ty
    L N P W : Term
    Θ : Boundary
    c : Conv
    ρ : Renameᵗ

------------------------------------------------------------------------
-- 1. One-hole contexts
------------------------------------------------------------------------

infixl 7 _·L_ _·R_
infix  6 ƛC_∙_
infix  5 _⟪C_,_⟫

data TermCtx : Set where
  □        : TermCtx
  ƛC_∙_    : Ty → TermCtx → TermCtx
  _·L_     : TermCtx → Term → TermCtx
  _·R_     : Term → TermCtx → TermCtx
  ΛC_      : TermCtx → TermCtx
  _·C[_,_] : TermCtx → Ty → Ty → TermCtx
  _⟪C_,_⟫  : TermCtx → Boundary → Conv → TermCtx

plug : TermCtx → Term → Term
plug □ M                 = M
plug (ƛC A ∙ C) M        = ƛ A ∙ plug C M
plug (C ·L N) M          = plug C M · N
plug (L ·R C) M          = L · plug C M
plug (ΛC C) M            = Λ (plug C M)
plug (C ·C[ B , A ]) M   = plug C M ·[ B , A ]
plug (C ⟪C Θ , c ⟫) M    = plug C M ⟪ Θ , c ⟫

------------------------------------------------------------------------
-- 2. The type context at the hole.  Its `names` is the hole's SCOPE MAP:
--    which ordinary type variables are live there (the positions) and
--    which representation variable each denotes (the entries).  `ƛ`, `·`
--    and `·[]` frames bind no type variable; `Λ` binds one in both
--    universes; a boundary frame moves to the INTERIOR its boundary scope
--    relates the frame's context to.
------------------------------------------------------------------------

infix 3 _⊢C_⊣_
data _⊢C_⊣_ : Ctxᵗ → TermCtx → Ctxᵗ → Set where
  frame-□   : Δ ⊢C □ ⊣ Δ
  frame-ƛ   : ∀ {C} → Δ ⊢C C ⊣ Δ′ → Δ ⊢C ƛC A ∙ C ⊣ Δ′
  frame-·L  : ∀ {C} → Δ ⊢C C ⊣ Δ′ → Δ ⊢C C ·L N ⊣ Δ′
  frame-·R  : ∀ {C} → Δ ⊢C C ⊣ Δ′ → Δ ⊢C L ·R C ⊣ Δ′
  frame-Λ   : ∀ {C} → underΛ Δ ⊢C C ⊣ Δ′ → Δ ⊢C ΛC C ⊣ Δ′
  frame-·[] : ∀ {C} → Δ ⊢C C ⊣ Δ′ → Δ ⊢C C ·C[ B , A ] ⊣ Δ′
  frame-⟪⟫  : ∀ {C} → Δ ⊢ⁱ Θ ⇒ Δᵢ → Δᵢ ⊢C C ⊣ Δ′
    → Δ ⊢C C ⟪C Θ , c ⟫ ⊣ Δ′

------------------------------------------------------------------------
-- 3. Renaming a context in the two universes, clause for clause with
--    `renᴹ²`, and the renaming that reaches its hole: `Λ` frames extend
--    both components, a boundary frame extends the representation
--    component past its bind block.
------------------------------------------------------------------------

renCtx² : TyRename → TermCtx → TermCtx
renCtx² ρ □               = □
renCtx² ρ (ƛC A ∙ C)      = ƛC renameᵗ (ordinary ρ) A ∙ renCtx² ρ C
renCtx² ρ (C ·L N)        = renCtx² ρ C ·L renᴹ² ρ N
renCtx² ρ (L ·R C)        = renᴹ² ρ L ·R renCtx² ρ C
renCtx² ρ (ΛC C)          = ΛC (renCtx² (underΛ-ren ρ) C)
renCtx² ρ (C ·C[ B , A ]) =
  renCtx² ρ C ·C[ renameᵗ (extᵗ (ordinary ρ)) B
                , renameᵗ (ordinary ρ) A ]
renCtx² ρ (C ⟪C Θ , c ⟫)  =
  renCtx² (underReps-ren (numBinds Θ) ρ) C
    ⟪C renᴮ² ρ Θ , renᶜ (ordinary ρ) c ⟫

holeRen² : TyRename → TermCtx → TyRename
holeRen² ρ □               = ρ
holeRen² ρ (ƛC A ∙ C)      = holeRen² ρ C
holeRen² ρ (C ·L N)        = holeRen² ρ C
holeRen² ρ (L ·R C)        = holeRen² ρ C
holeRen² ρ (ΛC C)          = holeRen² (underΛ-ren ρ) C
holeRen² ρ (C ·C[ B , A ]) = holeRen² ρ C
holeRen² ρ (C ⟪C Θ , c ⟫)  = holeRen² (underReps-ren (numBinds Θ) ρ) C

-- The representation-only move `ρ`, as the rules write it, and the
-- representation renaming it delivers to the hole of `C`.
moveᴿ : Renameᵗ → TyRename
moveᴿ ρ = ren² idᵗ ρ

holeᴿ : Renameᵗ → TermCtx → Renameᵗ
holeᴿ ρ C = represent (holeRen² (moveᴿ ρ) C)

------------------------------------------------------------------------
-- 4. `Beta`'s substitution through a context, clause for clause with
--    `substᵐ`: a boundary frame is term-closed, so the substitution stops
--    there.  `holeEnv` is the substitution that reaches the hole, and
--    `Stable` says the node in the hole SURVIVES it — every node but a
--    substituted variable.
------------------------------------------------------------------------

substCtx : (Var → Img) → TermCtx → TermCtx
substCtx σ □               = □
substCtx σ (ƛC A ∙ C)      = ƛC A ∙ substCtx (extᴵ σ) C
substCtx σ (C ·L N)        = substCtx σ C ·L substᵐ σ N
substCtx σ (L ·R C)        = substᵐ σ L ·R substCtx σ C
substCtx σ (ΛC C)          = ΛC (substCtx (λ x → ⇑ᴵ (σ x)) C)
substCtx σ (C ·C[ B , A ]) = substCtx σ C ·C[ B , A ]
substCtx σ (C ⟪C Θ , c ⟫)  = C ⟪C Θ , c ⟫

holeEnv : (Var → Img) → TermCtx → Var → Img
holeEnv σ □               = σ
holeEnv σ (ƛC A ∙ C)      = holeEnv (extᴵ σ) C
holeEnv σ (C ·L N)        = holeEnv σ C
holeEnv σ (L ·R C)        = holeEnv σ C
holeEnv σ (ΛC C)          = holeEnv (λ x → ⇑ᴵ (σ x)) C
holeEnv σ (C ·C[ B , A ]) = holeEnv σ C
holeEnv σ (C ⟪C Θ , c ⟫)  = ivar

data Stable (σ : Var → Img) : Term → Set where
  stable-var   : ∀ {x y} → σ x ≡ ivar y → Stable σ (` x)
  stable-$     : ∀ {n} → Stable σ ($ n)
  stable-true  : Stable σ `true
  stable-false : Stable σ `false
  stable-ƛ     : Stable σ (ƛ A ∙ N)
  stable-·     : Stable σ (L · N)
  stable-Λ     : Stable σ (Λ N)
  stable-·[]   : Stable σ (L ·[ B , A ])
  stable-⟪⟫    : Stable σ (N ⟪ Θ , c ⟫)

-- A copy of the argument, at one substituted occurrence.  Each `Λ` the
-- occurrence sits under wraps the copy in that binder's dual
-- (`crossΛᴹ`, strong-rep-store.TermSubst §5): the position moves inside
-- one more boundary frame and one more representation-only `suc`.
--
-- THE DEPTH INDEX (2026-09-21, restored from v7 during the proof).  The
-- ℕ counts the `Λ`s the copy walk has descended, and `image-here`
-- demands it be zero.  Without it the relation admits a WRONG-POSITION
-- derivation: when the β-redex's argument is itself a `crossΛᴹ`-shaped
-- wrapper, `⇑ᴵ (ival V A)` is again an `ival`, so a depth-1 occurrence
-- could match `image-here` and claim the UNWRAPPED source position at
-- the ambient one `Λ` in — and for that derivation the color equation
-- is false.  The index pins the leaf to the walk's actual depth.
data ImageResidual : ℕ → Img → TermCtx → Term → Renameᵗ → TermCtx
                   → Term → Set where
  image-here : ∀ {C M}
    → ImageResidual zero (ival (plug C M) A) C M idᵗ C M
  image-Λ : ∀ {k V C M D N}
    → ImageResidual k (ival V A) C M ρ D N
    → ImageResidual (suc k) (⇑ᴵ (ival V A)) C M (holeᴿ suc D ∘ ρ)
        (renCtx² (moveᴿ suc) D
           ⟪C boundary (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
        (renᴹ² (holeRen² (moveᴿ suc) D) N)

-- Positions inside a copy of the argument, followed through the body
-- to the occurrence that receives it.  The body's binders extend the
-- substitution exactly as `substᵐ` does; a boundary in the body receives
-- no copy.
data CopyResidual (k : ℕ) (σ : Var → Img)
  : Term → TermCtx → Term → Renameᵗ → TermCtx → Term → Set where
  copy-var : ∀ {x C M D N}
    → ImageResidual k (σ x) C M ρ D N
    → CopyResidual k σ (` x) C M ρ D N
  copy-ƛ : ∀ {C M D N}
    → CopyResidual k (extᴵ σ) P C M ρ D N
    → CopyResidual k σ (ƛ A ∙ P) C M ρ (ƛC A ∙ D) N
  copy-·L : ∀ {C M D N}
    → CopyResidual k σ L C M ρ D N
    → CopyResidual k σ (L · P) C M ρ (D ·L substᵐ σ P) N
  copy-·R : ∀ {C M D N}
    → CopyResidual k σ P C M ρ D N
    → CopyResidual k σ (L · P) C M ρ (substᵐ σ L ·R D) N
  copy-Λ : ∀ {C M D N}
    → CopyResidual (suc k) (λ x → ⇑ᴵ (σ x)) P C M ρ D N
    → CopyResidual k σ (Λ P) C M ρ (ΛC D) N
  copy-·[] : ∀ {C M D N}
    → CopyResidual k σ L C M ρ D N
    → CopyResidual k σ (L ·[ B , A ]) C M ρ (D ·C[ B , A ]) N

------------------------------------------------------------------------
-- 5. Residuals of one step.  `Residual r C M ρ D N`: the step `r` moves
--    the node `M` in hole `C` to hole `D` as `N`, and the representation
--    renaming that reaches the hole is `ρ`.  The site-by-site moves are
--    proof/ShiftAudit §1's table; `ρ` is that table's third column.
------------------------------------------------------------------------

data Residual : ∀ {Δ L L′} → Δ ⊢ L -→ L′
              → TermCtx → Term → Renameᵗ → TermCtx → Term → Set where

  -- TyBeta: the body stays where it is; its `Λ` slot BECOMES the
  -- boundary scope's bind slot (refinement `abstR → bindR R`, no move).
  residual-TyBeta : ∀ {R C M}
    (vN : Value (plug C M)) (pA : Δ ⊢ᶜ A ~ R)
    → Residual (TyBeta {Δ = Δ} {B = B} {A = A} {N = plug C M} vN pA)
        ((ΛC C) ·C[ B , A ]) M idᵗ
        (C ⟪C instantiate R (boundary []) , reveal 0 B ⟫) M

  -- Beta, the body: a node the substitution does not replace.
  residual-Beta-body : ∀ {C M}
    (vW : Value W)
    → Stable (holeEnv (betaEnv W A) C) M
    → Residual (Beta {Δ = Δ} {A = A} {N = plug C M} {W = W} vW)
        ((ƛC A ∙ C) ·L W) M idᵗ
        (substCtx (betaEnv W A) C)
        (substᵐ (holeEnv (betaEnv W A) C) M)

  -- Beta, the argument: one residual per occurrence that receives it.
  residual-Beta-arg : ∀ {C M D N}
    (vW : Value (plug C M))
    → CopyResidual zero (betaEnv (plug C M) A) P C M ρ D N
    → Residual (Beta {Δ = Δ} {A = A} {N = P} {W = plug C M} vW)
        ((ƛ A ∙ P) ·R C) M ρ D N

  -- Peel, the function: it keeps its frame.
  residual-Peel-fun : ∀ {Δᶜ Δᵈ C M s s′ t}
    (vV : Value (plug C M)) (vW : Value W)
    (rc : Δ ⊢ᶜ Θ ⇒ Δᶜ) (ri : Δ ⊢ⁱ Θ ⇒ Δᵢ)
    (rd : Δᵢ ⊢ᶜ dualBoundary Θ ⇒ Δᵈ) (sc : SameConv Δᵈ s′ Δᶜ s)
    → Residual (Peel {V = plug C M} {W = W} {t = t} vV vW rc ri rd sc)
        ((C ⟪C Θ , s ↦ t ⟫) ·L W) M idᵗ
        ((C ·L (renᴹ² (moveᴿ (wkN (numBinds Θ))) W
                  ⟪ dualBoundary Θ , s′ ⟫)) ⟪C Θ , t ⟫) M

  -- Peel, the argument: it crosses into the dual, past the bind block,
  -- by the representation-only `wkN (numBinds Θ)`.
  residual-Peel-arg : ∀ {Δᶜ Δᵈ V C M s s′ t}
    (vV : Value V) (vW : Value (plug C M))
    (rc : Δ ⊢ᶜ Θ ⇒ Δᶜ) (ri : Δ ⊢ⁱ Θ ⇒ Δᵢ)
    (rd : Δᵢ ⊢ᶜ dualBoundary Θ ⇒ Δᵈ) (sc : SameConv Δᵈ s′ Δᶜ s)
    → Residual (Peel {V = V} {W = plug C M} {t = t} vV vW rc ri rd sc)
        ((V ⟪ Θ , s ↦ t ⟫) ·R C) M (holeᴿ (wkN (numBinds Θ)) C)
        ((V ·R (renCtx² (moveᴿ (wkN (numBinds Θ))) C
                  ⟪C dualBoundary Θ , s′ ⟫)) ⟪C Θ , t ⟫)
        (renᴹ² (holeRen² (moveᴿ (wkN (numBinds Θ))) C) M)

  -- TyPeelR-Λ: as TyBeta, one boundary in — the body's `Λ` slot becomes
  -- the instantiated scope's new bind slot.
  residual-TyPeelR-Λ : ∀ {Δᶜ C M s R Bᵢ Bₑ}
    (vN : Value (plug C M))
    (rc : Δ ⊢ᶜ Θ ⇒ Δᶜ) (⊢s : underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ)
    (pA : Δ ⊢ᶜ A ~ R)
    → Residual (TyPeelR-Λ {N = plug C M} {B = B} vN rc ⊢s pA)
        (((ΛC C) ⟪C Θ , `∀ s ⟫) ·C[ B , A ]) M idᵗ
        (C ⟪C instantiate R Θ , instReveal 0 s ⟫) M

  -- TyPeelR-⟪⟫: the inner boundary's body is pushed one layer in, past
  -- the new bind, by the representation-only `extN (numBinds Θ′) suc`.
  residual-TyPeelR-⟪⟫ : ∀ {Δᵢ⁺ Δᶜ Δ′ᶜ Δ″ᶜ C M Θ′ s′ s″ s R Bᵢ Bᵢ′ Bₑ}
    (vW : Value (plug C M))
    (ri : Δ ⊢ⁱ Θ ⇒ Δᵢ) (rc : Δ ⊢ᶜ Θ ⇒ Δᶜ)
    (rc′ : Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ)
    (ri⁺ : Δ ⊢ⁱ instantiate R Θ ⇒ Δᵢ⁺)
    (rc″ : Δᵢ⁺ ⊢ᶜ addLock0 (renᴮ² (moveᴿ suc) Θ′) ⇒ Δ″ᶜ)
    (sc : SameConv (underΛ Δ″ᶜ) s″
            (underΛ (renNameCtx (extN (numBinds Θ′) suc) Δ″ᶜ Δ′ᶜ)) s′)
    (⊢s : underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ)
    (sm : underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ)
    (pA : Δ ⊢ᶜ A ~ R)
    → Residual (TyPeelR-⟪⟫ {W = plug C M} {B = B}
                 vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA)
        (((C ⟪C Θ′ , `∀ s′ ⟫) ⟪C Θ , `∀ s ⟫) ·C[ B , A ]) M
        (holeᴿ (extN (numBinds Θ′) suc) C)
        (((renCtx² (moveᴿ (extN (numBinds Θ′) suc)) C
             ⟪C addLock0 (renᴮ² (moveᴿ suc) Θ′) , `∀ s″ ⟫)
            ·C[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
           ⟪C instantiate R Θ , instReveal 0 s ⟫)
        (renᴹ² (holeRen² (moveᴿ (extN (numBinds Θ′) suc)) C) M)

  -- CancelR and IdPush: the value keeps its frame under both the merged
  -- and the rewound scope (proof/ShiftAudit §6).
  residual-CancelR : ∀ {Δ₁ᶜ Δ⋉ᶜ Δᶜ C M Θ₁ Θ₂ X Y A′ Aᵢ}
    (vV : Value (plug C M))
    (ri : Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) (rc₁ : Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
    (lX : Δ₁ᶜ ∋ X := Aᵢ)
    (rc⋉ : extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
    (sm : Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ)
    (rc₂ : Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) (lY : Δᶜ ∋ Y := A)
    → Residual (CancelR {V = plug C M} vV ri rc₁ lX rc⋉ sm rc₂ lY)
        ((C ⟪C Θ₁ , seal X ⟫) ⟪C Θ₂ , unseal Y ⟫) M idᵗ
        ((C ⟪C Θ₁ ⋉ Θ₂ , mkId A′ ⟫) ⟪C rewind Θ₂ , mkId A ⟫) M

  residual-IdPush : ∀ {Δ₁ᶜ Δ⋉ᶜ Δᶜ C M Θ₁ Θ₂ X X′ Y}
    (vV : Value (plug C M))
    (ri : Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) (rc₁ : Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
    (rc⋉ : extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
    (sm : Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ)
    (rc₂ : Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) (lY : Δᶜ ∋ Y := A)
    → Residual (IdPush {V = plug C M} vV ri rc₁ rc⋉ sm rc₂ lY)
        ((C ⟪C Θ₁ , id (` X) ⟫) ⟪C Θ₂ , unseal Y ⟫) M idᵗ
        ((C ⟪C Θ₁ ⋉ Θ₂ , unseal X′ ⟫) ⟪C rewind Θ₂ , mkId A ⟫) M

  -- (Drop$, Drop-true, Drop-false: no residual — the literal is consumed
  -- with its boundary.)

  -- The ξ rules: the position is inside the stepping subterm, or in the
  -- sibling that stands still.
  residual-ξ-·-l : ∀ {L′ C M D N} {r : Δ ⊢ L -→ L′}
    → Residual r C M ρ D N
    → Residual (ξ-·-l {M = P} r) (C ·L P) M ρ (D ·L P) N
  residual-ξ-·-l-sib : ∀ {L′ C M} (r : Δ ⊢ L -→ L′)
    → Residual (ξ-·-l {M = plug C M} r) (L ·R C) M idᵗ (L′ ·R C) M
  residual-ξ-·-r : ∀ {V P′ C M D N} {r : Δ ⊢ P -→ P′}
    (v : Value V) → Residual r C M ρ D N
    → Residual (ξ-·-r v r) (V ·R C) M ρ (V ·R D) N
  residual-ξ-·-r-sib : ∀ {P′ C M} (v : Value (plug C M))
    (r : Δ ⊢ P -→ P′)
    → Residual (ξ-·-r v r) (C ·L P) M idᵗ (C ·L P′) M
  residual-ξ-·[] : ∀ {L′ C M D N} {r : Δ ⊢ L -→ L′}
    → Residual r C M ρ D N
    → Residual (ξ-·[] {B = B} {A = A} r)
        (C ·C[ B , A ]) M ρ (D ·C[ B , A ]) N
  residual-ξ-⟪⟫ : ∀ {M′ C O D O′} {r : Δᵢ ⊢ N -→ M′}
    (ri : Δ ⊢ⁱ Θ ⇒ Δᵢ) → Residual r C O ρ D O′
    → Residual (ξ-⟪⟫ {c = c} ri r) (C ⟪C Θ , c ⟫) O ρ (D ⟪C Θ , c ⟫) O′

------------------------------------------------------------------------
-- 6. Residuals through a run: the renamings compose.
------------------------------------------------------------------------

data Residuals : ∀ {Δ L L′} → Δ ⊢ L -→* L′
               → TermCtx → Term → Renameᵗ → TermCtx → Term → Set where
  residuals-done : ∀ {C M}
    → Residuals (done {Δ = Δ} {M = plug C M}) C M idᵗ C M
  residuals-step : ∀ {L′ L″ C M ρ′ D N E O}
    {r : Δ ⊢ L -→ L′} {rs : Δ ⊢ L′ -→* L″}
    → Residual r C M ρ D N
    → Residuals rs D N ρ′ E O
    → Residuals (r then rs) C M (ρ′ ∘ ρ) E O
